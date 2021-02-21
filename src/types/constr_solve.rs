// constr_solve.rs
// solve typing constraints

use im::HashMap;
use im::vector::Vector as IVector;
use super::IfcapType;
use super::IfcapType::*;
use super::TypeVarId;
use super::TypeConstraint;
use super::TypeConstraint::*;

// substitution of type variables with types
type Subst = HashMap<TypeVarId, IfcapType>;

// fn apply(subst: &Subst, ty: &IfcapType) -> IfcapType;

fn substitute(ty: &IfcapType, sub: &Subst) -> IfcapType {
    match ty {
        TypeVar { id, ..} => {
            if sub.contains_key(id) {
                sub[id].clone()

            } else {
                ty.clone()
            }
        }

        TypeBool { .. } => ty.clone(),

        TypeRef { sec_label, res_label, val_type } => {
            let val_type_sub = substitute(val_type, sub);
            TypeRef {
                sec_label: *sec_label,
                res_label: *res_label,
                val_type: Box::new(val_type_sub)
            }
        }

        TypeChan { sec_label, send_res_label, recv_res_label,
            send_trans_label, recv_trans_label, val_type } =>
        {
            let val_type_sub = substitute(val_type, sub);
            TypeChan {
                sec_label: *sec_label,
                send_res_label: *send_res_label, recv_res_label: *recv_res_label,
                send_trans_label: *send_trans_label, recv_trans_label: *recv_trans_label,
                val_type: Box::new(val_type_sub)
            }
        }
    }
}

fn compose_subst(sub1: &Subst, sub2: &Subst) -> Subst {
    let mut sub2_composed = Subst::new();
    for (k, v) in sub2.iter() {
        sub2_composed.insert(*k, substitute(v, sub1));
    }

    sub1.clone().union(sub2_composed)
}

fn occurs_check(id: TypeVarId, ty: &IfcapType) -> bool {
    match ty {
        TypeVar { id: var_id, .. } => id == *var_id,

        TypeBool { .. } => false,

        TypeRef { val_type, .. } => occurs_check(id, val_type),

        TypeChan { val_type, .. } => occurs_check(id, val_type)
    }
}

fn unify_var(id: TypeVarId, ty: &IfcapType) -> Option<Subst> {
    match ty {
        TypeVar { .. } => { Option::from(Subst::new()) }

        _ => {
            if !occurs_check(id, ty) {
                let mut subst = Subst::new();
                subst.insert(id, ty.clone());
                Option::from(subst)

            } else {
                Option::None
            }
        }
    }
}

fn unify(ty1: &IfcapType, ty2: &IfcapType) -> Option<Subst> {
    match (ty1, ty2) {
        (TypeVar { .. }, TypeVar { .. }) => {
            Option::from(Subst::new())
        }

        (TypeVar { id: id1, .. }, _) => {
            unify_var(*id1, ty2)
        }

        (_, TypeVar { id: id2, .. },) => {
            unify_var(*id2, ty1)
        }

        (TypeBool { .. }, TypeBool { .. }) => {
            Option::from(Subst::new())
        }

        (TypeRef { val_type: val_type1, .. }, TypeRef { val_type: val_type2, .. }) => {
            unify(val_type1, val_type2)
        }

        (TypeChan { val_type: val_type1, .. }, TypeChan { val_type: val_type2, .. }) => {
            unify(val_type1, val_type2)
        }

        _ => {
            Option::None
        }
    }
}

fn solve_unification_constraints(constraints: &IVector<TypeConstraint>) -> Option<Subst> {
    let mut cur_subst = Subst::new();
    for constraint in constraints.iter() {
        let unify_res = match constraint {
            Unify(ty1, ty2) => unify(ty1, ty2),
            Subtype(ty1, ty2) => unify(ty1, ty2),
            _ => Option::from(Subst::new())
        };

        if let Some(subst) = unify_res {
            cur_subst = compose_subst(&cur_subst, &subst);

        } else { return unify_res }
    }

    Option::from(cur_subst)
}