//! solve lattice constraints

use std::collections::HashMap;
use im::HashMap as IHashMap;
use im::HashSet as IHashSet;
use im::Vector as IVector;
use im::vector as ivector;

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

#[derive(PartialEq,Eq,Copy,Clone,Hash)]
pub enum CNFLiteral {
    PosAtom(PropositionId),
    NegAtom(PropositionId)
}

pub type CNFProposition = IVector<IVector<CNFLiteral>>;

pub type Model = IHashMap<PropositionId, bool>;

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
                        Predicate::implies(p2, p1),
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
    pub fn propositionalize(&mut self, predicates: &IVector<Predicate>) -> IVector<Proposition> {
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

    /// convert proposition to CNF
    pub fn to_cnf(&mut self, prop: &Proposition) -> CNFProposition {
        use Proposition::*;
        use CNFLiteral::*;

        match prop {
            // is prop is atomic, it is already in CNF
            AtomicProposition(atom_id) => ivector![ivector![PosAtom(*atom_id)]],

            And(p1, p2) => {
                let mut cnf: CNFProposition = IVector::new();
                let cnf1 = self.to_cnf(p1);
                let cnf2 = self.to_cnf(p2);
                cnf.append(cnf1);
                cnf.append(cnf2);
                cnf
            }

            Or(p1, p2) => {
                let mut cnf: CNFProposition = IVector::new();
                let cnf1 = self.to_cnf(p1);
                let cnf2 = self.to_cnf(p2);

                for pp1 in cnf1.iter() {
                    for pp2 in cnf2.iter() {
                        let mut clause: IVector<CNFLiteral> = IVector::new();

                        for lit1 in pp1.iter() {
                            clause.push_back(*lit1);
                        }

                        for lit2 in pp2.iter() {
                            clause.push_back(*lit2);
                        }

                        cnf.push_back(clause);
                    }
                }

                cnf
            }

            Implies(p1, p2) => self.to_cnf(&Or(Box::new(Not(p1.clone())), p2.clone())),

            Not(p) => {
                // TODO: figure out why this has to be so complicated
                match &**p {
                    // if subproposition is atomic, prop is already in CNF
                    AtomicProposition(atom_id) =>
                        ivector![ivector![NegAtom(*atom_id)]],

                    // continue converting subproposition into CNF
                    And(pp1, pp2) =>
                        self.to_cnf(&Or(Box::new(Not(pp1.clone())), Box::new(Not(pp2.clone())))),

                    Or(pp1, pp2) =>
                        self.to_cnf(&And(Box::new(Not(pp1.clone())), Box::new(Not(pp2.clone())))),

                    Implies(pp1, pp2) =>
                        self.to_cnf(&And(Box::new(Not(pp1.clone())), pp2.clone())),

                    Not(p) =>
                        self.to_cnf(&p.clone())
                }
            }
        }
    }

    /// partition clause into positive and negative literals
    fn partition_clause(
        &mut self,
        clause: &IVector<CNFLiteral>
    ) -> (IHashSet<PropositionId>, IHashSet<PropositionId>) {
        let mut posset: IHashSet<PropositionId> = IHashSet::new();
        let mut negset: IHashSet<PropositionId> = IHashSet::new();

        for lit in clause.iter() {
            match lit {
                CNFLiteral::PosAtom(atom) => {
                    posset.insert(*atom);
                },

                CNFLiteral::NegAtom(atom) => {
                    negset.insert(*atom);
                }
            }
        }

        (posset, negset)
    }

    /// remove clauses that are always true regardless of the model
    fn remove_tautological_clauses(
        &mut self,
        cnf: &CNFProposition
    ) -> CNFProposition {
        let mut new_cnf: CNFProposition = IVector::new();

        for clause in cnf.iter() {
            let (posset, negset) = self.partition_clause(clause);
            if posset.union(negset).len() == 0 {
                new_cnf.push_back(clause.clone());
            }
        }

        new_cnf
    }

    /// remove unit clauses and extend model
    fn extract_unit_clauses(
        &mut self,
        cnf: &CNFProposition
    ) -> (CNFProposition, IHashSet<CNFLiteral>) {
        let mut new_cnf: CNFProposition = IVector::new();
        let mut unit_clauses: IHashSet<CNFLiteral> = IHashSet::new();

        for clause in cnf.iter() {
            if clause.len() == 1 {
                unit_clauses.insert(*clause.head().unwrap());

            } else {
                new_cnf.push_back(clause.clone())
            }
        }

        (new_cnf, unit_clauses)
    }

    /// DPLL algorithm: backtrack and apply resolution rule + extra optimizations
    fn resolve(&mut self, cnf: &CNFProposition, model: Model) -> Option<Model> {
        // check for empty clauses (these are always unsatisfiable)
        if cnf.iter().any(|clause| { clause.len() == 0 }) {
            Option::None

        } else {
            // unit propagation
            let (mut new_cnf, unit_clauses) = self.extract_unit_clauses(cnf);

            // - extend model to add data from unit clauses
            let mut contradictory_unit = false;
            for unit_clause in unit_clauses.iter() {
                let (atom, unit_val) = match unit_clause {
                    CNFLiteral::PosAtom(atom) => (*atom, true),
                    CNFLiteral::NegAtom(atom) => (*atom, false)
                };

                match model.get(&atom) {
                    Option::None => {
                        model.insert(atom, unit_val);
                    },

                    Option::Some(&model_val) => {
                        // unit clause is inconsistent with model. proposition is unsat
                        if model_val != unit_val {
                            contradictory_unit = true
                        }
                    }
                }
            }

            if contradictory_unit {
                Option::None

            } else {
                // pure literal elimination

            }
        }
    }

    /// check satisfiability using DPLL
    fn solve_sat(&mut self, cnf: &CNFProposition) -> Option<Model> {
        // preprocessing phase

        // remove for tautological clauses
        let mut new_cnf = self.remove_tautological_clauses(cnf);

        // repeatedly apply resolution to build model
        self.resolve(&new_cnf, IHashMap::new())
    }
}
