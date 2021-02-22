//! IFCAP
//! a secure, concurrent language
#![allow(dead_code)]

mod types;
mod lang;

use im::vector as ivector;
use lang::*;
use types::constr_solve::Subst;
use types::InferenceError;

fn prog1() -> IfcapStmt {
    stmts(ivector![
        letvar("x", newref(lit(true)), stmts(ivector![
        send(lit(true), var("x"))
        ]))
    ])
}

fn prog2() -> IfcapStmt {
    stmts(ivector![
        letvar("x", newchan(), stmts(ivector![
        assign(var("x"), lit(true))
        ]))
    ])
}

fn infer_type(program: &IfcapStmt) -> Result<Subst,InferenceError> {
    let constraints = types::constr_gen::gen_constraints(program)?;
    types::constr_solve::solve_unification_constraints(&constraints)
}

fn main() {
    let solution = infer_type(&prog2());

    match solution {
        Result::Ok(_) => {
            println!("Solution found for unfication constraints!")
        }
        
        Result::Err(_) => {
            println!("No solution for unification constraints")
        }
    }
}
