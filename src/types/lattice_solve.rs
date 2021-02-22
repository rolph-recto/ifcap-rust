//! solve lattice constraints

use std::collections::HashMap;
use im::HashSet as IHashSet;
use im::Vector as IVector;

use super::LatticeExpr;
use super::LatticeEq;

pub type TermConstId = i32;
pub type PredicateId = i32;
pub type PropositionId = i32;

#[derive(PartialEq,Eq,Clone)]
pub enum Term {
    Var,
    Const(TermConstId)
}

#[derive(PartialEq,Eq,Clone)]
pub enum Predicate {
    AtomicPredicate(PredicateId, Term),
    And(Box<Predicate>, Box<Predicate>),
    Or(Box<Predicate>, Box<Predicate>),
    Implies(Box<Predicate>, Box<Predicate>),
    Not(Box<Predicate>)
}

impl Predicate {
    fn atom(id: PredicateId, t: Term) -> Predicate {
        Predicate::AtomicPredicate(id, t)
    }

    fn and(p1: Predicate, p2: Predicate) -> Predicate {
        Predicate::And(Box::new(p1), Box::new(p2))
    }

    fn or(p1: Predicate, p2: Predicate) -> Predicate {
        Predicate::Or(Box::new(p1), Box::new(p2))
    }
    

    fn implies(p1: Predicate, p2: Predicate) -> Predicate {
        Predicate::Implies(Box::new(p1), Box::new(p2))
    }

    fn not(p: Predicate) -> Predicate {
        Predicate::Not(Box::new(p))
    }

    fn constants(&self) -> IHashSet<TermConstId> {
        use Predicate::*;
        match self {
            AtomicPredicate(_, term) => {
                match term {
                    Term::Const(id) => IHashSet::new().update(*id),
                    _ => IHashSet::new()
                }
            },

            And(p1, p2) => p1.constants().union(p2.constants()),

            Or(p1, p2) => p1.constants().union(p2.constants()),

            Implies(p1, p2) => p1.constants().union(p2.constants()),

            Not(p) => p.constants()
        }
    }
}

#[derive(PartialEq,Eq,Clone)]
pub enum Proposition {
    AtomicProposition(PropositionId),
    And(Box<Proposition>, Box<Proposition>),
    Or(Box<Proposition>, Box<Proposition>),
    Implies(Box<Proposition>, Box<Proposition>),
    Not(Box<Proposition>),
}

impl Proposition {
    fn atom(id: PropositionId) -> Proposition {
        Proposition::AtomicProposition(id)
    }

    fn and(p1: Proposition, p2: Proposition) -> Proposition {
        Proposition::And(Box::new(p1), Box::new(p2))
    }

    fn or(p1: Proposition, p2: Proposition) -> Proposition {
        Proposition::Or(Box::new(p1), Box::new(p2))
    }

    fn implies(p1: Proposition, p2: Proposition) -> Proposition {
        Proposition::Implies(Box::new(p1), Box::new(p2))
    }

    fn not(p: Proposition) -> Proposition {
        Proposition::Not(Box::new(p))
    }
}

impl std::fmt::Display for Proposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Proposition::*;
        match self {
            AtomicProposition(id) => write!(f, "P{}", id),
            And(prop1, prop2) => write!(f, "({} && {})", prop1, prop2),
            Or(prop1, prop2) => write!(f, "({} || {})", prop1, prop2),
            Implies(prop1, prop2) => write!(f, "({} => {})", prop1, prop2),
            Not(prop) => write!(f, "(!{})", prop),
        }
    }
}

pub struct TranslationContext {
    cur_term_const: i32,
    cur_proposition_id: i32,
    predicate_proposition_map: HashMap<(PredicateId,TermConstId), PropositionId>
}

impl TranslationContext {
    pub fn new() -> Self {
        TranslationContext {
            cur_term_const: 1,
            cur_proposition_id: 1,
            predicate_proposition_map: HashMap::new()
        }
    }

    fn next_term_const(&mut self) -> TermConstId {
        let id = self.cur_term_const;
        self.cur_term_const += 1;
        id
    }

    fn next_proposition_id(&mut self) -> PropositionId {
        let id = self.cur_proposition_id;
        self.cur_proposition_id += 1;
        id
    }

    fn lattice_expr_to_predicate(&mut self, lat_expr: &LatticeExpr, term: &Term) -> Predicate {
        match lat_expr {
            LatticeExpr::Var(v) => Predicate::atom(v.0, term.clone()),
            LatticeExpr::Join(l1,l2) => {
                let p1 = self.lattice_expr_to_predicate(l1, term);
                let p2 = self.lattice_expr_to_predicate(l2, term);
                Predicate::or(p1, p2)
            },
            LatticeExpr::Meet(l1,l2) => {
                let p1 = self.lattice_expr_to_predicate(l1, term);
                let p2 = self.lattice_expr_to_predicate(l2, term);
                Predicate::and(p1, p2)
            }
        }
    }

    /// convert lattice constraint to formula in the effectively propositional fragment of FOL
    pub fn lattice_encoding_to_predicates(&mut self, lat_eqs: IVector<LatticeEq>) -> IVector<Predicate> {
        lat_eqs.iter()
        .map(|lat_eq| {
            match lat_eq {
                LatticeEq::FlowsTo(l1, l2) => {
                    let p1 = self.lattice_expr_to_predicate(l1, &Term::Var);
                    let p2 = self.lattice_expr_to_predicate(l2, &Term::Var);
                    Predicate::implies(p1, p2)
                },

                LatticeEq::Eq(l1, l2) => {
                    let p1 = self.lattice_expr_to_predicate(l1, &Term::Var);
                    let p2 = self.lattice_expr_to_predicate(l2, &Term::Var);
                    Predicate::and(
                        Predicate::implies(p1.clone(), p2.clone()),
                        Predicate::implies(p2.clone(), p1.clone()),
                    )
                }

                LatticeEq::EqTop(l) => {
                    let p = self.lattice_expr_to_predicate(l, &Term::Var);
                    Predicate::not(p)
                }

                LatticeEq::NeqTop(l) => {
                    let const_id = self.next_term_const();
                    let p = self.lattice_expr_to_predicate(l, &Term::Const(const_id));
                    Predicate::not(p)
                }
            }
        })
        .collect::<IVector<Predicate>>()
    }

    fn atomic_predicate_to_proposition(
        &mut self,
        atomic_predicate: PredicateId,
        ground_term: TermConstId
    ) -> PropositionId {
        let key = (atomic_predicate, ground_term);
        match self.predicate_proposition_map.get(&key) {
            Some(prop) => *prop,
            None => {
                let id = self.next_proposition_id();
                self.predicate_proposition_map.insert(key, id);
                id
            }
        }
    }

    fn predicate_to_proposition(
        &mut self,
        predicate: &Predicate,
        ground_term: TermConstId
    ) -> Proposition {
        use Predicate::*;
        match predicate {
            AtomicPredicate(pred_id, _) => {
                let prop_id = self.atomic_predicate_to_proposition(*pred_id, ground_term);
                Proposition::AtomicProposition(prop_id)
            },

            And(pred1, pred2) => {
                let prop1 = self.predicate_to_proposition(pred1, ground_term);
                let prop2 = self.predicate_to_proposition(pred2, ground_term);
                Proposition::and(prop1, prop2)
            },

            Or(pred1, pred2) => {
                let prop1 = self.predicate_to_proposition(pred1, ground_term);
                let prop2 = self.predicate_to_proposition(pred2, ground_term);
                Proposition::or(prop1, prop2)
            },

            Implies(pred1, pred2) => {
                let prop1 = self.predicate_to_proposition(pred1, ground_term);
                let prop2 = self.predicate_to_proposition(pred2, ground_term);
                Proposition::implies(prop1, prop2)
            },

            Not(pred) => {
                let prop = self.predicate_to_proposition(pred, ground_term);
                Proposition::not(prop)
            },
        }
    }

    /// convert predicate logic formula into propositional logic formula
    pub fn propositionalize(&mut self, predicates: IVector<Predicate>) -> IVector<Proposition> {
        // collect ground terms (Herbrand universe)
        let ground_terms =
            predicates.iter()
            .fold(IHashSet::new(), |acc, pred| { acc.union(pred.constants()) });

        let mut propositions = IVector::new();
        for predicate in predicates.iter() {
            let consts = predicate.constants();

            // if the predicate is universally quantified, instantiate
            // term vars with all ground terms
            if consts.len() == 0 {
                for const_id in ground_terms.iter() {
                    propositions.push_back(self.predicate_to_proposition(predicate, *const_id));
                }

            // if predicate is existentially quantified, it has already been skolemized
            // so don't instantiate with other ground terms
            } else if consts.len() == 1 {
                let const_id = *consts.iter().last().unwrap();
                propositions.push_back(self.predicate_to_proposition(predicate, const_id));

            } else {
                panic!("Predicate has {} constants, can only have one!", consts.len())
            }
        }

        propositions
    }
}
