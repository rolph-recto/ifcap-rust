//! language definition

use im::Vector as IVector;

#[derive(PartialEq,Eq,Clone,Copy,Hash)]
pub struct Ident(&'static str);

#[derive(PartialEq,Eq,Clone,Copy)]
pub enum SecurityLevel { Public, Secret }

#[derive(PartialEq,Eq,Clone)]
pub enum IfcapExpr {
    Var(Ident),
    Lit(bool),
    Op(Box<IfcapExpr>, Box<IfcapExpr>),
    NewRef(Box<IfcapExpr>, SecurityLevel),
    NewChan,
    Deref(Box<IfcapExpr>)
}

#[derive(PartialEq,Eq,Clone)]
pub enum IfcapStmt {
    Let { var: Ident, expr: IfcapExpr, stmt: Box<IfcapStmt> },

    Assign { lhs: IfcapExpr, rhs: IfcapExpr },

    Block { stmts: IVector<IfcapStmt> },

    If {
        guard: IfcapExpr,
        then_branch: Box<IfcapStmt>,
        else_branch: Box<IfcapStmt>
    },

    While {
        guard: IfcapExpr,
        body: Box<IfcapStmt>
    },

    Spawn { stmt: Box<IfcapStmt> },

    Send { value: IfcapExpr, chan: IfcapExpr },

    Recv { chan: IfcapExpr, var: Ident, stmt: Box<IfcapStmt> },

    /*
    Join {
        chan1: IfcapExpr, chan2: IfcapExpr,
        var1: Ident, var2: Ident,
        body: Box<IfcapStmt>
    },

    Select {
        chan1: IfcapExpr, var1: Ident, body1: Box<IfcapStmt>,
        chan2: IfcapExpr, var2: Ident, body2: Box<IfcapStmt>
    }
    */
}

// smart constructors

use IfcapExpr::*;
use IfcapStmt::*;

pub fn var(var: &'static str) -> IfcapExpr { Var(Ident(var)) }

pub fn lit(b: bool) -> IfcapExpr { Lit(b) }

pub fn op(expr1: IfcapExpr, expr2: IfcapExpr) -> IfcapExpr {
    Op(Box::new(expr1), Box::new(expr2))
}

pub fn newref(expr: IfcapExpr, sec_level: SecurityLevel) -> IfcapExpr {
    NewRef(Box::new(expr), sec_level)
}

pub fn newchan() -> IfcapExpr { NewChan }

pub fn deref(ref_expr: IfcapExpr) -> IfcapExpr { 
    Deref(Box::new(ref_expr))
}

pub fn letvar(var: &'static str, expr: IfcapExpr, cont: IfcapStmt) -> IfcapStmt {
    Let { var: Ident(var), expr, stmt: Box::new(cont) }
}

pub fn assign(lhs: IfcapExpr, rhs: IfcapExpr) -> IfcapStmt {
    Assign { lhs, rhs }
}

pub fn cond(guard: IfcapExpr, then_branch: IfcapStmt, else_branch: IfcapStmt) -> IfcapStmt {
    If {
        guard,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch)
    }
}

pub fn while_loop(guard: IfcapExpr, body: IfcapStmt) -> IfcapStmt {
    While { guard, body: Box::new(body), }
}

pub fn spawn(stmt: IfcapStmt) -> IfcapStmt {
    Spawn { stmt: Box::new(stmt) }
}

pub fn send(value: IfcapExpr, chan:IfcapExpr) -> IfcapStmt {
    Send { value, chan }
}

pub fn recv(chan:IfcapExpr, var: &'static str, cont: IfcapStmt) -> IfcapStmt {
    Recv { chan, var: Ident(var), stmt: Box::new(cont) }
}

pub fn stmts(v: IVector<IfcapStmt>) -> IfcapStmt {
    Block { stmts: v }
}
