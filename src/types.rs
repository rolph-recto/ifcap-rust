// types.res
// type system and type inference

mod constr_gen;
mod constr_solve;

use im::HashMap;
use crate::lang::Ident;

// security/capability label with identifier
#[derive(Copy, Clone)]
struct LabelVar(i32);
type TypeVarId = i32;

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
