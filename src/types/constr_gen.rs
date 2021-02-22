//! generate typing constraints

use im::HashMap;
use im::vector::Vector as IVector;
use im::vector as ivector;

use crate::lang::Ident;
use crate::lang::IfcapExpr;
use crate::lang::IfcapStmt;

use super::IfcapEnv;
use super::IfcapType;
use super::IfcapType::*;
use super::LabelVar;
use super::TypeConstraint;
use super::InferenceError;
use super::InferenceError::*;

/// state for constraint generation; contains fresh label and type variable IDs
/// as well as the global scheduler resource
struct NameContext {
    next_label_id: i32,
    next_tyvar_id: i32,
    sched_resource: LabelVar
}

impl NameContext {
    fn new() -> NameContext {
        NameContext { next_label_id: 1, next_tyvar_id: 1, sched_resource: LabelVar(0) }
    }

    fn fresh_label(&mut self) -> LabelVar {
        let id = self.next_label_id;
        self.next_label_id += 1;
        LabelVar(id)
    }

    fn fresh_tyvar(&mut self) -> IfcapType {
        let id = self.next_label_id;
        self.next_label_id += 1;
        IfcapType::TypeVar { id: id, sec_label: self.fresh_label() }
    }

    fn fresh_tyvar_with_label(&mut self, label: LabelVar) -> IfcapType {
        let id = self.next_label_id;
        self.next_label_id += 1;
        IfcapType::TypeVar { id: id, sec_label: label }
    }
}

/// output context for expression constraints
struct ExprOutputContext {
    expr_type: IfcapType,
    constraints: IVector<TypeConstraint>
}

/// infer type for expression; takes type environment and input context, returns expression type
fn infer_type_expr(
    name_ctx: &mut NameContext,
    env: &IfcapEnv,
    pc_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    expr: &IfcapExpr
) -> Result<ExprOutputContext,InferenceError> {
    use IfcapExpr::*;
    match expr {
        Var(var) => {
            if let Some(var_type) = env.get(var) {
                Result::Ok(ExprOutputContext {
                    expr_type: var_type.clone(),
                    constraints: IVector::new(),
                })

            } else {
                Result::Err(UnknownBindingError(*var))
            }
        }

        Lit(_) => {
            Result::Ok(ExprOutputContext {
                expr_type: TypeBool { sec_label: name_ctx.fresh_label() } ,
                constraints: IVector::new()
            })
        }

        IfcapExpr::Op(e1, e2) => {
            let op1_out = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, e1)?;
            let op2_out = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, e2)?;

            let mut constraints = IVector::new();
            constraints.append(op1_out.constraints);
            constraints.append(op2_out.constraints);

            // output type is boolean, label must be join of operand labels
            let out_type: IfcapType = TypeBool { sec_label: name_ctx.fresh_label() };
            constraints.append(ivector![
                TypeConstraint::label_join_eq(
                    op1_out.expr_type.label(),
                    op2_out.expr_type.label(),
                    out_type.label()
                ),

                // operands have to be booleans
                TypeConstraint::Unify(
                    TypeBool { sec_label: name_ctx.fresh_label() },
                    op1_out.expr_type
                ),
                TypeConstraint::Unify(
                    TypeBool { sec_label: name_ctx.fresh_label() },
                    op2_out.expr_type
                )
            ]);

            Result::Ok(ExprOutputContext {
                expr_type: out_type,
                constraints: constraints
            })
        }

        // TODO: add security label on newref expr
        IfcapExpr::NewRef(init) => {
            let init_out = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, init)?;
            let mut constraints = IVector::new();
            constraints.append(init_out.constraints);

            let ref_security = name_ctx.fresh_label();
            let ref_resource = name_ctx.fresh_label();
            let ref_val_type = name_ctx.fresh_tyvar_with_label(init_out.expr_type.label());

            constraints.append(ivector![
                // well-formedness constraints for reference types
                TypeConstraint::label_nonempty(ref_resource),
                TypeConstraint::label_flowsto(ref_val_type.label(), ref_security),

                // security context constraints
                TypeConstraint::label_join_eq(pc_label, progress_label, ref_security)
            ]);

            Result::Ok(ExprOutputContext {
                expr_type: IfcapType::TypeRef {
                    sec_label: ref_security,
                    res_label: ref_resource,
                    val_type: Box::new(ref_val_type)
                },
                constraints: constraints
            })
        }

        IfcapExpr::NewChan =>  {
            let val_type = name_ctx.fresh_tyvar();
            let chan_security = name_ctx.fresh_label();
            let send_resource = name_ctx.fresh_label();
            let recv_resource = name_ctx.fresh_label();

            let mut constraints = IVector::new();

            constraints.append(ivector![
                // well-formedness of channel type
                TypeConstraint::label_flowsto(val_type.label(), chan_security),
                TypeConstraint::label_nonempty(send_resource),
                TypeConstraint::label_nonempty(recv_resource),

                // security context constraints 
                TypeConstraint::label_join_eq(pc_label, progress_label, chan_security)
            ]);

            Result::Ok(ExprOutputContext {
                expr_type: IfcapType::TypeChan {
                    sec_label: chan_security,
                    send_res_label: send_resource,
                    recv_res_label: recv_resource,
                    send_trans_label: name_ctx.fresh_label(),
                    recv_trans_label: name_ctx.fresh_label(),
                    val_type: Box::new(val_type)
                },
                constraints: constraints
            })
        }

        IfcapExpr::Deref(ref_expr) => {
            let ref_ctx = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, ref_expr)?;
            let val_type = name_ctx.fresh_tyvar();
            let out_type = name_ctx.fresh_tyvar();
            let ref_security = name_ctx.fresh_label();
            let ref_resource = name_ctx.fresh_label();
            let val_type2 = val_type.clone();

            let mut constraints = IVector::new();
            constraints.append(ref_ctx.constraints);
            constraints.append(ivector![
                // thread must have shared access to reference resource
                TypeConstraint::label_overlaps(cap_label, ref_resource),

                // ref label lower bounds output label
                TypeConstraint::label_flowsto(ref_security, out_type.label()),

                // val label lower bounds output label
                TypeConstraint::Subtype(val_type, out_type)
            ]);

            Result::Ok(ExprOutputContext {
                expr_type: IfcapType::TypeRef {
                    sec_label: ref_security,
                    res_label: ref_resource,
                    val_type: Box::new(val_type2)
                },
                constraints: constraints
            })
        }
    }
}

/// output context for statement constraints
struct StmtOutputContext { 
    sched_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    constraints: IVector<TypeConstraint>
}

/// infer type for expression; takes type environment and input context, returns output context
fn infer_type_stmt(
    name_ctx: &mut NameContext,
    env: &IfcapEnv,
    sched_label: LabelVar,
    pc_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    stmt: &IfcapStmt
) -> Result<StmtOutputContext,InferenceError> {
    match stmt {
        IfcapStmt::Let { var, expr, stmt } => {
            let expr_out = infer_type_expr(name_ctx, &env, pc_label, progress_label, cap_label, expr)?;

            let mut stmt_env = env.clone();
            stmt_env.insert(*var, expr_out.expr_type);

            let stmt_out =
                infer_type_stmt(
                    name_ctx, &stmt_env,
                    sched_label, pc_label, progress_label, cap_label,
                    stmt)?;

            Result::Ok(StmtOutputContext {
                sched_label: stmt_out.sched_label,
                progress_label: stmt_out.progress_label,
                cap_label: stmt_out.cap_label,
                constraints: stmt_out.constraints
            })
        },

        IfcapStmt::Block { stmts } => {
            let mut cur_sched_label = sched_label;
            let mut cur_progress_label = sched_label;
            let mut cur_cap_label = sched_label;
            let mut constraints = IVector::new();

            for stmt in stmts.iter() {
                let stmt_out =
                    infer_type_stmt(
                        name_ctx, env,
                        cur_sched_label, pc_label, cur_progress_label, cur_cap_label,
                        stmt)?;
                cur_sched_label = stmt_out.sched_label;
                cur_progress_label = stmt_out.progress_label;
                cur_cap_label = stmt_out.cap_label;
                constraints.append(stmt_out.constraints);
            }

            Result::Ok(StmtOutputContext {
                sched_label: cur_sched_label,
                progress_label: cur_progress_label,
                cap_label: cur_cap_label,
                constraints: constraints
            })
        },

        IfcapStmt::If { guard, then_branch, else_branch } => {
            let guard_out =
                infer_type_expr(
                    name_ctx, &env,
                    pc_label, progress_label, cap_label,
                    guard)?;
            let guard_label = guard_out.expr_type.label();
            let branch_pc = name_ctx.fresh_label();
            let then_out =
                infer_type_stmt(
                    name_ctx, &env,
                    sched_label, branch_pc, progress_label, cap_label,
                    then_branch)?;
            let else_out =
                infer_type_stmt(
                    name_ctx, &env,
                    sched_label, branch_pc, progress_label, cap_label,
                    else_branch)?;

            let mut constraints = IVector::new();
            constraints.append(guard_out.constraints);
            constraints.append(then_out.constraints);
            constraints.append(else_out.constraints);

            constraints.append(ivector![
                // guard must be a boolean
                TypeConstraint::Unify(
                    guard_out.expr_type,
                    IfcapType::TypeBool { sec_label: guard_label }
                ),

                // guard label must flow to pc label of branches
                TypeConstraint::label_join_eq(pc_label, guard_label, branch_pc),

                // output contexts at branches must match
                TypeConstraint::label_eq(then_out.sched_label, else_out.sched_label),
                TypeConstraint::label_eq(then_out.progress_label, else_out.progress_label),
                TypeConstraint::label_eq(then_out.cap_label, else_out.cap_label),

                // scheduler label must upper bound branch pc
                TypeConstraint::label_flowsto(branch_pc, sched_label),

                // thread must have shared access to global scheduler resource
                TypeConstraint::label_flowsto(cap_label, name_ctx.sched_resource)
            ]);

            Result::Ok(StmtOutputContext {
                sched_label: else_out.sched_label,
                progress_label: else_out.progress_label,
                cap_label: else_out.cap_label,
                constraints: constraints
            })
        },

        IfcapStmt::While { guard, body } => {
            let guard_out =
                infer_type_expr(
                    name_ctx, &env,
                    pc_label, progress_label, cap_label,
                    guard)?;
            let guard_label = guard_out.expr_type.label();
            let body_pc = name_ctx.fresh_label();
            let body_out =
                infer_type_stmt(
                    name_ctx, &env,
                    sched_label, body_pc, progress_label, cap_label,
                    body)?;

            let mut constraints = IVector::new();
            constraints.append(guard_out.constraints);
            constraints.append(body_out.constraints);

            constraints.append(ivector![
                // guard must be a boolean
                TypeConstraint::Unify(
                    guard_out.expr_type,
                    IfcapType::TypeBool { sec_label: guard_label }
                ),

                // guard label must flow to pc label of branches
                TypeConstraint::label_join_eq(pc_label, guard_label, body_pc),

                // input and output contexts of body must match
                TypeConstraint::label_eq(sched_label, body_out.sched_label),
                TypeConstraint::label_eq(progress_label, body_out.progress_label),
                TypeConstraint::label_eq(cap_label, body_out.cap_label),

                // scheduler label must upper bound branch pc
                TypeConstraint::label_flowsto(body_pc, sched_label),

                // thread must have shared access to global scheduler resource
                TypeConstraint::label_flowsto(cap_label, name_ctx.sched_resource)
            ]);

            Result::Ok(StmtOutputContext {
                sched_label: sched_label,
                progress_label: sched_label,
                cap_label: sched_label,
                constraints: constraints
            })
        },

        IfcapStmt::Spawn { stmt } => {
            let spawn_cap_label = name_ctx.fresh_label();
            let cont_cap_label = name_ctx.fresh_label();

            let spawn_out =
                infer_type_stmt(
                    name_ctx, env,
                    sched_label, pc_label, progress_label, spawn_cap_label,
                    stmt)?;

            let mut constraints = IVector::new();
            constraints.append(spawn_out.constraints);

            constraints.append(ivector![
                // make sure continuation and spawned capabilities are disjoint
                TypeConstraint::label_meet_eq(
                    spawn_cap_label, cont_cap_label, cap_label
                ),
                TypeConstraint::label_disjoint(spawn_cap_label, cont_cap_label)
            ]);

            Result::Ok(StmtOutputContext {
                sched_label: sched_label,
                progress_label: progress_label,
                cap_label: cont_cap_label,
                constraints: constraints
            })
        },

        IfcapStmt::Send { value, chan } => {
            let value_out =
                infer_type_expr(
                    name_ctx, env,
                    pc_label, progress_label, cap_label,
                    value)?;

            let chan_out =
                infer_type_expr(
                    name_ctx, env,
                    pc_label, progress_label, cap_label,
                    chan)?;

            let chan_send_res = name_ctx.fresh_label();
            let chan_recv_res = name_ctx.fresh_label();
            let chan_send_trans = name_ctx.fresh_label();
            let chan_recv_trans = name_ctx.fresh_label();
            let chan_val_type = name_ctx.fresh_tyvar();
            let chan_val_type2 = chan_val_type.clone();
            let chan_type = IfcapType::TypeChan {
                sec_label: chan_out.expr_type.label(),
                send_res_label: chan_send_res,
                recv_res_label: chan_recv_res,
                send_trans_label: chan_send_trans,
                recv_trans_label: chan_recv_trans,
                val_type: Box::new(chan_val_type)
            };

            let cap2_label = name_ctx.fresh_label();
            let cap3_label = name_ctx.fresh_label();

            let progress2_label = name_ctx.fresh_label();

            let mut constraints = IVector::new();
            constraints.append(value_out.constraints);
            constraints.append(chan_out.constraints);
            constraints.append(ivector![
                // capability check
                TypeConstraint::label_flowsto(cap_label, chan_send_res),

                // capability transfer
                TypeConstraint::label_meet_eq(chan_send_trans, cap2_label, cap_label),
                TypeConstraint::label_disjoint(chan_send_trans, cap2_label),
                TypeConstraint::label_meet_eq(chan_recv_trans, cap2_label, cap3_label),

                // progress leak
                TypeConstraint::label_join_flowsto(pc_label, progress_label, chan_type.label()),
                TypeConstraint::label_flowsto(chan_type.label(), progress2_label),

                // types must match
                TypeConstraint::Unify(chan_out.expr_type, chan_type),
                TypeConstraint::Subtype(value_out.expr_type, chan_val_type2),
            ]);

            Result::Ok(StmtOutputContext {
                sched_label: sched_label,
                progress_label: progress2_label,
                cap_label: cap3_label,
                constraints: constraints
            })
        },

        IfcapStmt::Recv { chan, var, stmt } => {
            let chan_out =
                infer_type_expr(
                    name_ctx, env,
                    pc_label, progress_label, cap_label,
                    chan)?;

            let mut body_env = env.clone();
            body_env.insert(*var, chan_out.expr_type.clone());

            let progress2_label = name_ctx.fresh_label();
            let cap2_label = name_ctx.fresh_label();
            let cap3_label = name_ctx.fresh_label();

            let body_out =
                infer_type_stmt(
                    name_ctx, &body_env,
                    sched_label, pc_label, progress2_label, cap3_label,
                    stmt)?;

            let chan_send_res = name_ctx.fresh_label();
            let chan_recv_res = name_ctx.fresh_label();
            let chan_send_trans = name_ctx.fresh_label();
            let chan_recv_trans = name_ctx.fresh_label();
            let chan_val_type = name_ctx.fresh_tyvar();
            let chan_type = IfcapType::TypeChan {
                sec_label: chan_out.expr_type.label(),
                send_res_label: chan_send_res,
                recv_res_label: chan_recv_res,
                send_trans_label: chan_send_trans,
                recv_trans_label: chan_recv_trans,
                val_type: Box::new(chan_val_type)
            };

            let mut constraints = IVector::new();
            constraints.append(chan_out.constraints);
            constraints.append(body_out.constraints);
            constraints.append(ivector![
                // chan has to have a channel type
                TypeConstraint::Unify(chan_out.expr_type, chan_type.clone()),

                // progress leak
                TypeConstraint::label_join_flowsto(pc_label, progress_label, chan_type.label()),
                TypeConstraint::label_flowsto(chan_type.label(), progress2_label),

                // capability check
                TypeConstraint::label_flowsto(cap_label, chan_recv_res),

                // capability transfer
                TypeConstraint::label_meet_eq(chan_recv_trans, cap2_label, cap_label),
                TypeConstraint::label_disjoint(chan_recv_trans, cap2_label),
                TypeConstraint::label_meet_eq(chan_send_trans, cap2_label, cap3_label),
            ]);

            Result::Ok(StmtOutputContext {
                sched_label: body_out.sched_label,
                progress_label: body_out.progress_label,
                cap_label: body_out.cap_label,
                constraints: constraints
            })
        },
    }
}

/// generate type constraints from program statement
pub fn gen_constraints(stmt: &IfcapStmt) -> Result<IVector<TypeConstraint>,InferenceError> {
    let mut name_ctx = NameContext::new();
    let env: HashMap<Ident, IfcapType> = HashMap::new();
    let sched_label = name_ctx.fresh_label();
    let pc_label = name_ctx.fresh_label();
    let progress_label = name_ctx.fresh_label();
    let cap_label = name_ctx.fresh_label();
    let stmt_out =
        infer_type_stmt(
            &mut name_ctx, &env,
            sched_label, pc_label, progress_label, cap_label,
            stmt
        )?;
    let mut constraints = stmt_out.constraints;
    constraints.push_back(
        TypeConstraint::label_nonempty(name_ctx.sched_resource)
    );
    Result::Ok(constraints)
}
