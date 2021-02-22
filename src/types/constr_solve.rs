//! solve typing constraints

use im::HashMap;
use im::vector::Vector as IVector;
use super::IfcapType;
use super::IfcapType::*;
use super::TypeVarId;
use super::TypeConstraint;
use super::TypeConstraint::*;
use super::InferenceError;
use super::InferenceError::*;

/// substitution of type variables with types
pub type Subst = HashMap<TypeVarId, IfcapType>;

/// apply substitution `sub` to type `ty`
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

/// compose substitutions `sub1` and `sub2` together
fn compose_subst(sub1: &Subst, sub2: &Subst) -> Subst {
    let mut sub2_composed = Subst::new();
    for (k, v) in sub2.iter() {
        sub2_composed.insert(*k, substitute(v, sub1));
    }

    sub1.clone().union(sub2_composed)
}

/// perform occurs check for type variable `id` in type `ty`
fn occurs_check(id: TypeVarId, ty: &IfcapType) -> bool {
    match ty {
        TypeVar { id: var_id, .. } => id == *var_id,

        TypeBool { .. } => false,

        TypeRef { val_type, .. } => occurs_check(id, val_type),

        TypeChan { val_type, .. } => occurs_check(id, val_type)
    }
}

/// unify variable `id` with type `ty`
fn unify_var(id: TypeVarId, ty: &IfcapType) -> Result<Subst,InferenceError> {
    match ty {
        TypeVar { .. } => { Result::Ok(Subst::new()) }

        _ => {
            if !occurs_check(id, ty) {
                let mut subst = Subst::new();
                subst.insert(id, ty.clone());
                Result::Ok(subst)

            } else { // occurs check fail; there is an infinite term
                Result::Err(InfiniteTypeError(id, ty.clone()))
            }
        }
    }
}

/// unify types `ty1` and `ty2`
fn unify(ty1: &IfcapType, ty2: &IfcapType) -> Result<Subst,InferenceError> {
    match (ty1, ty2) {
        (TypeVar { .. }, TypeVar { .. }) => {
            Result::Ok(Subst::new())
        }

        (TypeVar { id: id1, .. }, _) => {
            unify_var(*id1, ty2)
        }

        (_, TypeVar { id: id2, .. },) => {
            unify_var(*id2, ty1)
        }

        (TypeBool { .. }, TypeBool { .. }) => {
            Result::Ok(Subst::new())
        }

        (TypeRef { val_type: val_type1, .. }, TypeRef { val_type: val_type2, .. }) => {
            unify(val_type1, val_type2)
        }

        (TypeChan { val_type: val_type1, .. }, TypeChan { val_type: val_type2, .. }) => {
            unify(val_type1, val_type2)
        }

        _ => { // unification failed
            Result::Err(UnificationError(ty1.clone(),ty2.clone()))
        }
    }
}

// solve all unification constraints by composing unifications in sequence
pub fn solve_unification_constraints(
    constraints: &IVector<TypeConstraint>
) -> Result<Subst,InferenceError> {
    let mut cur_subst = Subst::new();
    for constraint in constraints.iter() {
        let unify_res = match constraint {
            Unify(ty1, ty2) => unify(ty1, ty2),
            Subtype(ty1, ty2) => unify(ty1, ty2),
            _ => Result::Ok(Subst::new())
        }?;

        cur_subst = compose_subst(&cur_subst, &unify_res);
    }

    Result::Ok(cur_subst)
}