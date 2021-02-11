// IFCAP
// a secure, concurrent language

use im::HashMap;
use im::vector::Vector as IVector;

/* language */
#[derive(PartialEq,Eq,Clone,Hash)]
struct Ident(String);

enum IfcapExpr {
    Lit(bool),
    Op(Box<IfcapExpr>, Box<IfcapExpr>),
    NewRef(Box<IfcapExpr>),
    NewChan,
    Deref(Box<IfcapExpr>)
}

enum IfcapStmt {
    Let { var: Ident, expr: IfcapExpr, stmt: Box<IfcapStmt> },

    Block { stmts: Vec<IfcapStmt> },

    If {
        guard: IfcapExpr,
        then_branch: Box<IfcapStmt>,
        else_branch: Box<IfcapStmt>
    },

    While {
        guard: IfcapExpr,
        body: Box<IfcapStmt>
    },

    Spawn { stmt: Box<IfcapStmt> },

    Send { value: IfcapExpr, chan: IfcapExpr },

    Recv { chan: IfcapExpr, var: Ident, body: Box<IfcapStmt> },

    Join {
        chan1: IfcapExpr, chan2: IfcapExpr,
        var1: Ident, var2: Ident,
        body: Box<IfcapStmt>
    },

    Select {
        chan1: IfcapExpr, var1: Ident, body1: Box<IfcapStmt>,
        chan2: IfcapExpr, var2: Ident, body2: Box<IfcapStmt>
    }
}

/* type system */

// security/capability label with identifier
#[derive(Copy, Clone)]
struct LabelVar(i32);

#[derive(Clone)]
enum IfcapType {
    TypeBool { sec_label: LabelVar },
    TypeRef { sec_label: LabelVar, res_label: LabelVar, val_type: Box<IfcapType> },
    TypeChan {
        sec_label: LabelVar,
        send_res_label: LabelVar, recv_res_label: LabelVar,
        send_trans_label: LabelVar, recv_trans_label: LabelVar,
        val_type: Box<IfcapType>
    },
    TypeVar { id: i32, sec_label: LabelVar },
}

impl IfcapType {
    fn label(&self) -> LabelVar { 
        match self {
            IfcapType::TypeBool { sec_label } => *sec_label,
            IfcapType::TypeRef { sec_label, .. } => *sec_label,
            IfcapType::TypeChan { sec_label, .. }=> *sec_label,
            IfcapType::TypeVar { sec_label, .. }=> *sec_label
        }
    }
}

type IfcapEnv = HashMap<Ident, IfcapType>;

#[derive(Clone)]
enum LatticeExpr { // lattice expression
    Top,
    Bottom,
    Var(LabelVar),
    Join(Box<LatticeExpr>,Box<LatticeExpr>),
    Meet(Box<LatticeExpr>, Box<LatticeExpr>)
}

impl LatticeExpr {
    fn join(e1: LatticeExpr, e2: LatticeExpr) -> LatticeExpr {
        LatticeExpr::Join(Box::new(e1), Box::new(e2))
    }

    fn meet(e1: LatticeExpr, e2: LatticeExpr) -> LatticeExpr {
        LatticeExpr::Meet(Box::new(e1), Box::new(e2))
    }
}

#[derive(Clone)]
enum LatticeEq { // lattice equations
    FlowsTo(LatticeExpr, LatticeExpr),
    Neq(LatticeExpr, LatticeExpr),
    Eq(LatticeExpr, LatticeExpr)
}

#[derive(Clone)]
enum TypeConstraint { // type inference constraint
    Unify(IfcapType, IfcapType),
    Subtype(IfcapType, IfcapType),
    Lattice(LatticeEq)
}

impl TypeConstraint {
    fn label_flowsto(label1: LabelVar, label2: LabelVar) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::FlowsTo(
                LatticeExpr::Var(label1),
                LatticeExpr::Var(label2)
            )
        )
    }

    // label1 join label2 = label3
    fn label_join_eq(
        label1: LabelVar, label2: LabelVar, label3: LabelVar
    ) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::Eq(
                LatticeExpr::join(
                    LatticeExpr::Var(label1),
                    LatticeExpr::Var(label2)
                ),
                LatticeExpr::Var(label3)
            )
        )
    }

    // label1 meet label2 = label3
    fn label_meet_eq(
        label1: LabelVar, label2: LabelVar, label3: LabelVar
    ) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::Eq(
                LatticeExpr::meet(
                    LatticeExpr::Var(label1),
                    LatticeExpr::Var(label2)
                ),
                LatticeExpr::Var(label3)
            )
        )
    }

    fn label_eq(label1: LabelVar, label2: LabelVar) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::Eq(
                LatticeExpr::Var(label1),
                LatticeExpr::Var(label2)
            )
        )
    }

    fn label_disjoint(label1: LabelVar, label2: LabelVar) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::Eq(
                LatticeExpr::Top,
                LatticeExpr::join(
                    LatticeExpr::Var(label1),
                    LatticeExpr::Var(label2)
                )
            )
        )
    }

    fn label_overlaps(label1: LabelVar, label2: LabelVar) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::Neq(
                LatticeExpr::Top,
                LatticeExpr::join(
                    LatticeExpr::Var(label1),
                    LatticeExpr::Var(label2)
                )
            )
        )
    }

    fn label_nonempty(label: LabelVar) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::Neq(
                LatticeExpr::Top,
                LatticeExpr::Var(label)
            )
        )
    }
}

// solve lattice by converting to effectively propositional formulas

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


struct ExprOutputContext {
    expr_type: IfcapType,
    constraints: IVector<TypeConstraint>
}

// infer type for expression
fn infer_type_expr(
    name_ctx: &mut NameContext,
    env: &IfcapEnv,
    pc_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    expr: &IfcapExpr
) -> ExprOutputContext {
    match expr {
        IfcapExpr::Lit(_) => {
            ExprOutputContext {
                expr_type: IfcapType::TypeBool { sec_label: name_ctx.fresh_label() } ,
                constraints: IVector::new()
            }
        }

        IfcapExpr::Op(e1, e2) => {
            let op1_out = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, e1);
            let op2_out = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, e2);

            let constraints = IVector::new();
            constraints.append(op1_out.constraints);
            constraints.append(op2_out.constraints);

            // output type is boolean, label must be join of operand labels
            let out_type: IfcapType = IfcapType::TypeBool { sec_label: name_ctx.fresh_label() };
            constraints.push_back(
                TypeConstraint::label_join_eq(
                    op1_out.expr_type.label(),
                    op2_out.expr_type.label(),
                    out_type.label()
                )
            );

            // operands have to be booleans
            constraints.push_back(
                TypeConstraint::Unify(
                    IfcapType::TypeBool { sec_label: name_ctx.fresh_label() },
                    op1_out.expr_type
                )
            );
            constraints.push_back(
                TypeConstraint::Unify(
                    IfcapType::TypeBool { sec_label: name_ctx.fresh_label() },
                    op2_out.expr_type
                )
            );

            ExprOutputContext {
                expr_type: out_type,
                constraints: constraints
            }
        }

        // TODO: add security label on newref expr
        IfcapExpr::NewRef(init) => {
            let init_out = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, init);
            let constraints = IVector::new();
            constraints.append(init_out.constraints);

            let ref_security = name_ctx.fresh_label();
            let ref_resource = name_ctx.fresh_label();
            let ref_val_type = name_ctx.fresh_tyvar_with_label(init_out.expr_type.label());

            // well-formedness constraints for reference types
            constraints.push_back(
                TypeConstraint::label_nonempty(ref_resource)
            );

            constraints.push_back(
                TypeConstraint::label_flowsto(ref_val_type.label(), ref_security)
            );

            // flows-to constraints for security 
            constraints.push_back(
                TypeConstraint::label_join_eq(pc_label, progress_label, ref_security)
            );

            ExprOutputContext {
                expr_type: IfcapType::TypeRef {
                    sec_label: ref_security,
                    res_label: ref_resource,
                    val_type: Box::new(ref_val_type)
                },
                constraints: constraints
            }
        }

        IfcapExpr::NewChan =>  {
            let val_type = name_ctx.fresh_tyvar();
            let chan_security = name_ctx.fresh_label();
            let send_resource = name_ctx.fresh_label();
            let recv_resource = name_ctx.fresh_label();

            let constraints = IVector::new();

            // well-formedness of channel type
            constraints.push_back(
                TypeConstraint::label_flowsto(val_type.label(), chan_security)
            );

            constraints.push_back(
                TypeConstraint::label_nonempty(send_resource)
            );

            constraints.push_back(
                TypeConstraint::label_nonempty(recv_resource)
            );

            // security context constraints 
            constraints.push_back(
                TypeConstraint::label_join_eq(pc_label, progress_label, chan_security)
            );

            ExprOutputContext {
                expr_type: IfcapType::TypeChan {
                    sec_label: chan_security,
                    send_res_label: send_resource,
                    recv_res_label: recv_resource,
                    send_trans_label: name_ctx.fresh_label(),
                    recv_trans_label: name_ctx.fresh_label(),
                    val_type: Box::new(val_type)
                },
                constraints: constraints
            }
        }

        IfcapExpr::Deref(ref_expr) => {
            let ref_ctx = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, ref_expr);
            let val_type = name_ctx.fresh_tyvar();
            let out_type = name_ctx.fresh_tyvar();
            let ref_security = name_ctx.fresh_label();
            let ref_resource = name_ctx.fresh_label();

            let constraints = IVector::new();
            constraints.append(ref_ctx.constraints);

            constraints.push_back(
                TypeConstraint::label_overlaps(cap_label, ref_resource)
            );

            constraints.push_back(
                TypeConstraint::label_flowsto(ref_security, out_type.label())
            );

            let val_type2 = val_type.clone();
            constraints.push_back(
                TypeConstraint::Subtype(val_type, out_type)
            );

            ExprOutputContext {
                expr_type: IfcapType::TypeRef {
                    sec_label: ref_security,
                    res_label: ref_resource,
                    val_type: Box::new(val_type2)
                },
                constraints: constraints
            }
        }
    }
}


struct StmtOutputContext { 
    sched_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    constraints: IVector<TypeConstraint>
}

fn infer_type_stmt(
    name_ctx: &mut NameContext,
    env: &IfcapEnv,
    sched_label: LabelVar,
    pc_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    stmt: &IfcapStmt
) -> StmtOutputContext {
    match stmt {
        IfcapStmt::Let { var, expr, stmt } => {
            let expr_out = infer_type_expr(name_ctx, &env, pc_label, progress_label, cap_label, expr);

            let stmt_env = env.clone();
            stmt_env.insert(*var, expr_out.expr_type);

            let stmt_out = infer_type_stmt(name_ctx, &stmt_env, sched_label, pc_label, progress_label, cap_label, stmt);

            StmtOutputContext {
                sched_label: stmt_out.sched_label,
                progress_label: stmt_out.progress_label,
                cap_label: stmt_out.cap_label,
                constraints: stmt_out.constraints
            }
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
                        stmt);
                cur_sched_label = stmt_out.sched_label;
                cur_progress_label = stmt_out.progress_label;
                cur_cap_label = stmt_out.cap_label;
                constraints.append(stmt_out.constraints);
            }

            StmtOutputContext {
                sched_label: cur_sched_label,
                progress_label: cur_progress_label,
                cap_label: cur_cap_label,
                constraints: constraints
            }
        },

        IfcapStmt::If { guard, then_branch, else_branch } => {
            let guard_out = infer_type_expr(name_ctx, &env, pc_label, progress_label, cap_label, guard);
            let branch_pc = name_ctx.fresh_label();
            let then_out =
                infer_type_stmt(
                    name_ctx, &env,
                    sched_label, branch_pc, progress_label, cap_label,
                    then_branch);
            let else_out =
                infer_type_stmt(
                    name_ctx, &env,
                    sched_label, branch_pc, progress_label, cap_label,
                    else_branch);

            let constraints = IVector::new();
            constraints.append(guard_out.constraints);
            constraints.append(then_out.constraints);
            constraints.append(else_out.constraints);

            // guard label must flow to pc label of branches
            constraints.push_back(
                TypeConstraint::label_join_eq(
                    pc_label, guard_out.expr_type.label(),
                    branch_pc
                )
            );

            // output contexts at branches must match
            constraints.push_back(
                TypeConstraint::label_eq(then_out.sched_label, else_out.sched_label)
            );
            constraints.push_back(
                TypeConstraint::label_eq(then_out.progress_label, else_out.progress_label)
            );
            constraints.push_back(
                TypeConstraint::label_eq(then_out.cap_label, else_out.cap_label)
            );

            // scheduler label must upper bound branch pc
            constraints.push_back(
                TypeConstraint::label_flowsto(branch_pc, sched_label)
            );

            // thread must have shared access to global scheduler resource
            constraints.push_back(
                TypeConstraint::label_flowsto(cap_label, name_ctx.sched_resource)
            );

            StmtOutputContext {
                sched_label: else_out.sched_label,
                progress_label: else_out.progress_label,
                cap_label: else_out.cap_label,
                constraints: constraints
            }
        },

        IfcapStmt::While { guard, body } => {
            let guard_out = infer_type_expr(name_ctx, &env, pc_label, progress_label, cap_label, guard);
            let body_pc = name_ctx.fresh_label();
            let body_out =
                infer_type_stmt(
                    name_ctx, &env,
                    sched_label, body_pc, progress_label, cap_label,
                    body);

            let constraints = IVector::new();
            constraints.append(guard_out.constraints);
            constraints.append(body_out.constraints);

            // guard label must flow to pc label of branches
            constraints.push_back(
                TypeConstraint::label_join_eq(
                    pc_label, guard_out.expr_type.label(), body_pc
                )
            );

            // input and output contexts of body must match
            constraints.push_back(
                TypeConstraint::label_eq(sched_label, body_out.sched_label)
            );
            constraints.push_back(
                TypeConstraint::label_eq(progress_label, body_out.progress_label)
            );
            constraints.push_back(
                TypeConstraint::label_eq(cap_label, body_out.cap_label)
            );

            // scheduler label must upper bound branch pc
            constraints.push_back(
                TypeConstraint::label_flowsto(body_pc, sched_label)
            );

            // thread must have shared access to global scheduler resource
            constraints.push_back(
                TypeConstraint::label_flowsto(cap_label, name_ctx.sched_resource)
            );

            StmtOutputContext {
                sched_label: sched_label,
                progress_label: sched_label,
                cap_label: sched_label,
                constraints: constraints
            }
        },

        IfcapStmt::Spawn { stmt } => {
            let spawn_cap_label = name_ctx.fresh_label();
            let cont_cap_label = name_ctx.fresh_label();

            let spawn_out =
                infer_type_stmt(
                    name_ctx, env,
                    sched_label, pc_label, progress_label, spawn_cap_label,
                    stmt);

            let constraints = IVector::new();
            constraints.append(spawn_out.constraints);

            // make sure continuation and spawned capabilities are disjoint
            constraints.push_back(
                TypeConstraint::label_meet_eq(
                    spawn_cap_label, cont_cap_label, cap_label
                )
            );

            constraints.push_back(
                TypeConstraint::label_disjoint(spawn_cap_label, cont_cap_label)
            );

            StmtOutputContext {
                sched_label: sched_label,
                progress_label: progress_label,
                cap_label: cont_cap_label,
                constraints: constraints
            }
        },

        IfcapStmt::Send { value, chan } => { },

        IfcapStmt::Recv { chan, var, body } => { },

        IfcapStmt::Join { chan1, chan2, var1, var2, body } => { },

        IfcapStmt::Select { chan1, var1, body1, chan2, var2, body2 } => { },
    }
}

fn main() {
    println!("Hello, world!");
}
