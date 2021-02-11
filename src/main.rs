// IFCAP
// a secure, concurrent language

use im::HashMap;
use im::catlist::CatList;

/* language */
struct Ident(String);

enum IfcapExpr {
    Lit(bool),
    Op(Box<IfcapExpr>, Box<IfcapExpr>),
    NewRef(Box<IfcapExpr>),
    NewChan,
    Deref(Box<IfcapExpr>)
}

enum IfcapStmt {
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

    Spawn { fork: Box<IfcapStmt> },

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
            IfcapType::TypeVar { id, sec_label }=> *sec_label
        }
    }
}

enum LatticeExpr { // lattice expression
    Top,
    Bottom,
    Var(LabelVar),
    Join(Box<LatticeExpr>,Box<LatticeExpr>),
    Meet(Box<LatticeExpr>, Box<LatticeExpr>)
}

enum LatticeEq { // lattice equations
    FlowsTo(LatticeExpr, LatticeExpr),
    Neq(LatticeExpr, LatticeExpr),
    Eq(LatticeExpr, LatticeExpr)
}

enum TypeConstraint { // type inference constraint
    Unify(IfcapType, IfcapType),
    Subtype(IfcapType, IfcapType),
    Lattice(LatticeEq)
}

// solve lattice by converting to effectively propositional formulas

struct NameContext {
    next_label_id: i32,
    next_tyvar_id: i32
}

impl NameContext {
    fn new() -> NameContext {
        NameContext { next_label_id: 0, next_tyvar_id: 0 }
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
    constraints: CatList<TypeConstraint>
}

struct StmtOutputContext { 
    sched_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    constraints: CatList<TypeConstraint>
}

// infer type for expression
fn infer_type_expr(
    name_ctx: &mut NameContext,
    env: &HashMap<&str, IfcapType>,
    pc_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    expr: &IfcapExpr
) -> ExprOutputContext {
    match expr {
        IfcapExpr::Lit(_) => {
            ExprOutputContext {
                expr_type: IfcapType::TypeBool { sec_label: name_ctx.fresh_label() } ,
                constraints: CatList::new()
            }
        }

        IfcapExpr::Op(e1, e2) => {
            let constraints = CatList::new();
            let op_ctx1 = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, e1);
            let op_ctx2 = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, e2);

            constraints.append(op_ctx1.constraints);
            constraints.append(op_ctx2.constraints);

            // output type is boolean, label must be join of operand labels
            let out_type: IfcapType = IfcapType::TypeBool { sec_label: name_ctx.fresh_label() };
            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::FlowsTo(
                        LatticeExpr::Join(
                            Box::new(LatticeExpr::Var(op_ctx1.expr_type.label())),
                            Box::new(LatticeExpr::Var(op_ctx2.expr_type.label()))
                        ),
                        LatticeExpr::Var(out_type.label())
                    )
                )
            );

            // operands have to be booleans
            constraints.push_back(
                TypeConstraint::Unify(
                    IfcapType::TypeBool { sec_label: name_ctx.fresh_label() },
                    op_ctx1.expr_type
                )
            );
            constraints.push_back(
                TypeConstraint::Unify(
                    IfcapType::TypeBool { sec_label: name_ctx.fresh_label() },
                    op_ctx2.expr_type
                )
            );

            ExprOutputContext {
                expr_type: out_type,
                constraints: constraints
            }
        }

        // TODO: add security label on newref expr
        IfcapExpr::NewRef(init) => {
            let init_ctx = infer_type_expr(name_ctx, env, pc_label, progress_label, cap_label, init);
            let constraints = CatList::new().append(init_ctx.constraints);

            let ref_security = name_ctx.fresh_label();
            let ref_resource = name_ctx.fresh_label();
            let ref_val_type = name_ctx.fresh_tyvar_with_label(init_ctx.expr_type.label());

            // well-formedness constraints for reference types
            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::Neq(
                        LatticeExpr::Top,
                        LatticeExpr::Var(ref_resource)
                    )
                )
            );

            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::FlowsTo(
                        LatticeExpr::Var(ref_val_type.label()),
                        LatticeExpr::Var(ref_security)
                    )
                )
            );

            // flows-to constraints for security 
            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::FlowsTo(
                        LatticeExpr::Join(
                            Box::new(LatticeExpr::Var(pc_label)),
                            Box::new(LatticeExpr::Var(progress_label))
                        ),
                        LatticeExpr::Var(ref_security)
                    )
                )
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

            let constraints = CatList::new();

            // well-formedness of channel type
            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::FlowsTo(
                        LatticeExpr::Var(val_type.label()),
                        LatticeExpr::Var(chan_security)
                    )
                )
            );

            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::Neq(
                        LatticeExpr::Top,
                        LatticeExpr::Var(send_resource)
                    )
                )
            );

            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::Neq(
                        LatticeExpr::Top,
                        LatticeExpr::Var(recv_resource)
                    )
                )
            );

            // security context constraints 
            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::FlowsTo(
                        LatticeExpr::Join(
                            Box::new(LatticeExpr::Var(pc_label)),
                            Box::new(LatticeExpr::Var(progress_label))
                        ),
                        LatticeExpr::Var(chan_security)
                    )
                )
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
            let constraints = CatList::new().append(ref_ctx.constraints);
            let val_type = name_ctx.fresh_tyvar();
            let out_type = name_ctx.fresh_tyvar();
            let ref_security = name_ctx.fresh_label();
            let ref_resource = name_ctx.fresh_label();

            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::Neq(
                        LatticeExpr::Top,
                        LatticeExpr::Join(
                            Box::new(LatticeExpr::Var(cap_label)),
                            Box::new(LatticeExpr::Var(ref_resource))
                        )
                    )
                )
            );

            constraints.push_back(
                TypeConstraint::Lattice(
                    LatticeEq::FlowsTo(
                        LatticeExpr::Var(ref_security),
                        LatticeExpr::Var(out_type.label()),
                    )
                )
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
                constraints: CatList::new()
            }
        }
    }
}

/*
fn infer_type_stmt(
    name_ctx: &mut NameContext,
    env: &HashMap<&str, IfcapType>,
    sched_label: LabelVar,
    pc_label: LabelVar,
    progress_label: LabelVar,
    cap_label: LabelVar,
    stmt: IfcapStmt
) -> StmtOutputContext;
*/

fn main() {
    println!("Hello, world!");
}
