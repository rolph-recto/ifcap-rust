//! language definition

use im::Vector as IVector;

#[derive(PartialEq,Eq,Clone,Copy,Hash)]
pub struct Ident(&'static str);

#[derive(PartialEq,Eq,Clone)]
pub enum IfcapExpr {
    Var(Ident),
    Lit(bool),
    Op(Box<IfcapExpr>, Box<IfcapExpr>),
    NewRef(Box<IfcapExpr>),
    NewChan,
    Deref(Box<IfcapExpr>)
}

#[derive(PartialEq,Eq,Clone)]
pub enum IfcapStmt {
    Let { var: Ident, expr: IfcapExpr, stmt: Box<IfcapStmt> },

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

pub fn expr_var(var: &'static str) -> IfcapExpr { Var(Ident(var)) }

pub fn expr_lit(b: bool) -> IfcapExpr { Lit(b) }

pub fn expr_op(expr1: IfcapExpr, expr2: IfcapExpr) -> IfcapExpr {
    Op(Box::new(expr1), Box::new(expr2))
}

pub fn expr_newref(expr: IfcapExpr) -> IfcapExpr {
    NewRef(Box::new(expr))
}

pub fn expr_newchan() -> IfcapExpr { NewChan }

pub fn expr_deref(ref_expr: IfcapExpr) -> IfcapExpr { 
    Deref(Box::new(ref_expr))
}

pub fn stmt_let(var: &'static str, expr: IfcapExpr, cont: IfcapStmt) -> IfcapStmt {
    Let { var: Ident(var), expr, stmt: Box::new(cont) }
}

pub fn stmt_if(guard: IfcapExpr, then_branch: IfcapStmt, else_branch: IfcapStmt) -> IfcapStmt {
    If {
        guard,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch)
    }
}

pub fn stmt_while(guard: IfcapExpr, body: IfcapStmt) -> IfcapStmt {
    While { guard, body: Box::new(body), }
}

pub fn stmt_spawn(stmt: IfcapStmt) -> IfcapStmt {
    Spawn { stmt: Box::new(stmt) }
}

pub fn stmt_send(value: IfcapExpr, chan:IfcapExpr) -> IfcapStmt {
    Send { value, chan }
}

pub fn stmt_recv(chan:IfcapExpr, var: &'static str, cont: IfcapStmt) -> IfcapStmt {
    Recv { chan, var: Ident(var), stmt: Box::new(cont) }
}

pub fn stmts(v: IVector<IfcapStmt>) -> IfcapStmt {
    Block { stmts: v }
}