//! solve typing constraints

use im::HashMap;
use im::vector::Vector as IVector;
use im::vector as ivector;
use super::IfcapType;
use super::IfcapType::*;
use super::TypeVarId;
use super::TypeConstraint;
use super::TypeConstraint::*;
use super::InferenceError;
use super::InferenceError::*;
use super::LatticeExpr;
use super::LatticeEq;

/// substitution of type variables with types
pub type Subst = HashMap<TypeVarId, IfcapType>;

/// apply substitution `sub` to `self
trait Substitutable {
    fn substitute(&self, sub: &Subst) -> Self;
}

impl Substitutable for IfcapType {
    fn substitute(&self, sub: &Subst) -> IfcapType {
        match self {
            TypeVar { id, ..} => {
                if sub.contains_key(id) {
                    sub[id].clone()

                } else {
                    self.clone()
                }
            }

            TypeBool { .. } => self.clone(),

            TypeRef { sec_label, res_label, val_type } => {
                let val_type_sub = val_type.substitute(sub);
                TypeRef {
                    sec_label: *sec_label,
                    res_label: *res_label,
                    val_type: Box::new(val_type_sub)
                }
            }

            TypeChan { sec_label, send_res_label, recv_res_label,
                send_trans_label, recv_trans_label, val_type } =>
            {
                let val_type_sub = val_type.substitute(sub);
                TypeChan {
                    sec_label: *sec_label,
                    send_res_label: *send_res_label, recv_res_label: *recv_res_label,
                    send_trans_label: *send_trans_label, recv_trans_label: *recv_trans_label,
                    val_type: Box::new(val_type_sub)
                }
            }
        }
    }
}

impl Substitutable for TypeConstraint {
    fn substitute(&self, sub: &Subst) -> TypeConstraint {
        match self {
            Unify(ty1,ty2)=> Unify(ty1.substitute(sub), ty2.substitute(sub)),
            Subtype(ty1,ty2)=> Subtype(ty1.substitute(sub), ty2.substitute(sub)),
            _ => self.clone()
        }
    }
}

/// compose substitutions `sub1` and `sub2` together
fn compose_subst(sub1: &Subst, sub2: &Subst) -> Subst {
    let mut sub2_composed = Subst::new();
    for (k, v) in sub2.iter() {
        sub2_composed.insert(*k, v.substitute(sub1));
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

/// generate lattice constraints from unification constraints
fn unify_induce_lattice_eqs(ty1: &IfcapType, ty2: &IfcapType) -> IVector<LatticeEq> {
    match (ty1, ty2) {
        (TypeBool { sec_label: sec1 }, TypeBool { sec_label: sec2 }) =>
            ivector!(
                LatticeEq::Eq(LatticeExpr::Var(*sec1), LatticeExpr::Var(*sec2))
            ),

        (TypeRef { sec_label: sec1, res_label: res1, val_type: val1 },
        TypeRef { sec_label: sec2, res_label: res2, val_type: val2 }) => {
            let mut eqs = IVector::new();
            eqs.append(unify_induce_lattice_eqs(val1, val2));
            eqs.append(ivector![
                LatticeEq::Eq(LatticeExpr::Var(*sec1), LatticeExpr::Var(*sec2)),
                LatticeEq::Eq(LatticeExpr::Var(*res1), LatticeExpr::Var(*res2)),
            ]);

            eqs
        }

        (TypeChan { sec_label: sec1, send_res_label: send_res1, recv_res_label: recv_res1,
                    send_trans_label: send_trans1, recv_trans_label: recv_trans1, val_type: val1 },
        TypeChan { sec_label: sec2, send_res_label: send_res2, recv_res_label: recv_res2,
                    send_trans_label: send_trans2, recv_trans_label: recv_trans2, val_type: val2 }) => {
            let mut eqs = IVector::new();
            eqs.append(unify_induce_lattice_eqs(val1, val2));
            eqs.append(ivector![
                LatticeEq::Eq(LatticeExpr::Var(*sec1), LatticeExpr::Var(*sec2)),
                LatticeEq::Eq(LatticeExpr::Var(*send_res1), LatticeExpr::Var(*send_res2)),
                LatticeEq::Eq(LatticeExpr::Var(*recv_res1), LatticeExpr::Var(*recv_res2)),
                LatticeEq::Eq(LatticeExpr::Var(*send_trans1), LatticeExpr::Var(*send_trans2)),
                LatticeEq::Eq(LatticeExpr::Var(*recv_trans1), LatticeExpr::Var(*recv_trans2)),
            ]);

            eqs
        }

        _ => IVector::new()
    }
}

/// generate lattice constraints from subtyping constraints
fn subtype_induce_lattice_eqs(ty1: &IfcapType, ty2: &IfcapType) -> IVector<LatticeEq> {
    match (ty1, ty2) {
        (TypeBool { sec_label: sec1 }, TypeBool { sec_label: sec2 }) =>
            ivector!(
                LatticeEq::Eq(LatticeExpr::Var(*sec1), LatticeExpr::Var(*sec2))
            ),

        (TypeRef { sec_label: sec1, res_label: res1, val_type: val1 },
        TypeRef { sec_label: sec2, res_label: res2, val_type: val2 }) => {
            let mut eqs = IVector::new();
            eqs.append(unify_induce_lattice_eqs(val1, val2));
            eqs.append(ivector![
                LatticeEq::FlowsTo(LatticeExpr::Var(*sec1), LatticeExpr::Var(*sec2)),
                LatticeEq::Eq(LatticeExpr::Var(*res1), LatticeExpr::Var(*res2)),
            ]);

            eqs
        }

        (TypeChan { sec_label: sec1, send_res_label: send_res1, recv_res_label: recv_res1,
                    send_trans_label: send_trans1, recv_trans_label: recv_trans1, val_type: val1 },
        TypeChan { sec_label: sec2, send_res_label: send_res2, recv_res_label: recv_res2,
                    send_trans_label: send_trans2, recv_trans_label: recv_trans2, val_type: val2 }) => {
            let mut eqs = IVector::new();
            eqs.append(subtype_induce_lattice_eqs(val1, val2));
            eqs.append(ivector![
                LatticeEq::FlowsTo(LatticeExpr::Var(*sec1), LatticeExpr::Var(*sec2)),
                LatticeEq::Eq(LatticeExpr::Var(*send_res1), LatticeExpr::Var(*send_res2)),
                LatticeEq::Eq(LatticeExpr::Var(*recv_res1), LatticeExpr::Var(*recv_res2)),
                LatticeEq::Eq(LatticeExpr::Var(*send_trans1), LatticeExpr::Var(*send_trans2)),
                LatticeEq::Eq(LatticeExpr::Var(*recv_trans1), LatticeExpr::Var(*recv_trans2)),
            ]);

            eqs
        }

        _ => IVector::new()
    }
}


// TODO: finish
fn solve_lattice_constraints(constraints: IVector<LatticeEq>) -> Result<(),InferenceError> {
    let mut translator = super::lattice_solve::TranslationContext::new();
    let predicates = translator.lattice_encoding_to_predicates(constraints);
    let propositions = translator.propositionalize(predicates);

    for proposition in propositions.iter() {
        println!("{}", proposition)
    }

    Ok(())
}

pub fn infer_type(program: &crate::lang::IfcapStmt) -> Result<(),InferenceError> {
    let mut constraints = super::constr_gen::gen_constraints(program)?;
    let mut unifier;
    
    loop {
        unifier = solve_unification_constraints(&constraints)?;
        if unifier.len() == 0 { break; }

        constraints =
            constraints.iter()
            .map(|constr| { constr.substitute(&unifier) })
            .collect::<IVector<TypeConstraint>>();
    }

    let lattice_eqs =
        constraints.iter()
        .flat_map(|constr| {
            match constr {
                TypeConstraint::Unify(ty1, ty2) => unify_induce_lattice_eqs(ty1, ty2),
                TypeConstraint::Subtype(ty1, ty2) => subtype_induce_lattice_eqs(ty1, ty2),
                TypeConstraint::Lattice(eq) => ivector!(eq.clone()),
            }
        })
        .collect::<IVector<LatticeEq>>();

    solve_lattice_constraints(lattice_eqs)
}