// types.res
// type system and type inference

pub mod constr_gen;
pub mod constr_solve;

use im::HashMap;
use crate::lang::Ident;

// security/capability label with identifier
#[derive(Copy, Clone)]
pub struct LabelVar(i32);
pub type TypeVarId = i32;

#[derive(Clone)]
pub enum IfcapType {
    TypeBool { sec_label: LabelVar },
    TypeRef { sec_label: LabelVar, res_label: LabelVar, val_type: Box<IfcapType> },
    TypeChan {
        sec_label: LabelVar,
        send_res_label: LabelVar, recv_res_label: LabelVar,
        send_trans_label: LabelVar, recv_trans_label: LabelVar,
        val_type: Box<IfcapType>
    },
    TypeVar { id: TypeVarId, sec_label: LabelVar },
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

// type constraints

#[derive(Clone)]
pub enum LatticeExpr { // lattice expression
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
pub enum LatticeEq { // lattice equations
    FlowsTo(LatticeExpr, LatticeExpr),
    Neq(LatticeExpr, LatticeExpr),
    Eq(LatticeExpr, LatticeExpr)
}

#[derive(Clone)]
pub enum TypeConstraint { // type inference constraint
    Unify(IfcapType, IfcapType),
    Subtype(IfcapType, IfcapType),
    Lattice(LatticeEq)
}

impl TypeConstraint {
    fn label_flowsto_expr(expr1: LatticeExpr, expr2: LatticeExpr) -> TypeConstraint {
        TypeConstraint::Lattice(LatticeEq::FlowsTo(expr1, expr2))
    }

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

    // label1 join label2 flowsto label3
    fn label_join_flowsto(
        label1: LabelVar, label2: LabelVar, label3: LabelVar
    ) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::FlowsTo(
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

// type inference error

pub enum InferenceError {
    UnknownBindingError(Ident),
    UnificationError(IfcapType,IfcapType),
    InfiniteTypeError(TypeVarId,IfcapType),
}