// types.res
// type system and type inference

pub mod constr_gen;
pub mod constr_solve;
pub mod lattice_solve;

use std::fmt;
use std::fmt::Display;
use std::error::Error;

use im::HashMap;
use crate::lang::Ident;

// security/capability label with identifier
#[derive(Copy, Clone, Debug)]
pub struct LabelVar(i32);

pub type TypeVarId = i32;

impl Display for LabelVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

#[derive(Clone,Debug)]
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
        use IfcapType::*;
        match self {
            TypeBool { sec_label } => *sec_label,
            TypeRef { sec_label, .. } => *sec_label,
            TypeChan { sec_label, .. }=> *sec_label,
            TypeVar { sec_label, .. }=> *sec_label
        }
    }
}

impl Display for IfcapType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use IfcapType::*;
        match self {
            TypeBool { sec_label } => write!(f, "bool_{}", sec_label),

            TypeRef { sec_label, res_label, val_type } =>
                write!(f, "ref_{}^{} {}", sec_label, res_label, val_type),

            TypeChan {
                sec_label,
                send_res_label, recv_res_label,
                send_trans_label, recv_trans_label,
                val_type
            } =>
                write!(f, "chan_{} ({},{}) ({},{}) {}",
                    sec_label,
                    send_res_label, recv_res_label,
                    send_trans_label, recv_trans_label,
                    val_type),

            TypeVar { id, sec_label }=> write!(f, "ty{}_{}", id, sec_label)
        }
    }
}

type IfcapEnv = HashMap<Ident, IfcapType>;

// type constraints

#[derive(Clone,Debug)]
pub enum LatticeExpr { // lattice expression
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

impl Display for LatticeExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LatticeExpr::*;
        match self {
            Var(v) => write!(f, "{}", v),

            Join(l1,l2) => write!(f, "{} ⊔ {}", l1, l2),

            Meet(l1,l2) => write!(f, "{} ⊓ {}", l1, l2),
        }
    }
}

#[derive(Clone,Debug)]
pub enum LatticeEq { // lattice equations
    FlowsTo(LatticeExpr, LatticeExpr),
    Eq(LatticeExpr, LatticeExpr),
    EqTop(LatticeExpr),
    NeqTop(LatticeExpr),
}

impl Display for LatticeEq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LatticeEq::*;
        match self {
            FlowsTo(l1, l2) => write!(f, "{} ⊑ {}", l1, l2),

            Eq(l1, l2) => write!(f, "{} = {}", l1, l2),

            EqTop(l) => write!(f, "{} = T", l),

            NeqTop(l) => write!(f, "{} != ⊤", l),
        }
    }
}

#[derive(Clone,Debug)]
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
            LatticeEq::EqTop(
                LatticeExpr::join(
                    LatticeExpr::Var(label1),
                    LatticeExpr::Var(label2)
                )
            )
        )
    }

    fn label_overlaps(label1: LabelVar, label2: LabelVar) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::NeqTop(
                LatticeExpr::join(
                    LatticeExpr::Var(label1),
                    LatticeExpr::Var(label2)
                )
            )
        )
    }

    fn label_nonempty(label: LabelVar) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::NeqTop(LatticeExpr::Var(label))
        )
    }

    fn label_empty(label: LabelVar) -> TypeConstraint {
        TypeConstraint::Lattice(
            LatticeEq::EqTop(LatticeExpr::Var(label))
        )
    }
}

impl Display for TypeConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TypeConstraint::*;
        match self {
            Unify(ty1, ty2) => write!(f, "{} = {}", ty1, ty2),

            Subtype(ty1, ty2) => write!(f, "{} <: {}", ty1, ty2),

            Lattice(lat_eq) => write!(f, "{}", lat_eq)
        }
    }
}

// type inference error

#[derive(Debug)]
pub enum InferenceError {
    UnknownBindingError(Ident),
    UnificationError(IfcapType,IfcapType),
    InfiniteTypeError(TypeVarId,IfcapType),
}

impl Display for InferenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use InferenceError::*;
        match self {
            UnknownBindingError(id) => write!(f, "unknown binding: {}", id.0),

            UnificationError(ty1,ty2) => write!(f, "cannot unify types {} and {}", ty1, ty2),

            InfiniteTypeError(id,ty) => write!(f, "ty{} is infinite, equals {}", id, ty),
        }
    }
}

impl Error for InferenceError {}
