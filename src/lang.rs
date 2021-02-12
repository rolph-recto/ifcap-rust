// lang.rs
// language definition
#[derive(PartialEq,Eq,Clone,Copy,Hash)]
pub struct Ident(&'static str);

pub enum IfcapExpr {
    Lit(bool),
    Op(Box<IfcapExpr>, Box<IfcapExpr>),
    NewRef(Box<IfcapExpr>),
    NewChan,
    Deref(Box<IfcapExpr>)
}

pub enum IfcapStmt {
    Let { var: Ident, expr: IfcapExpr, stmt: Box<IfcapStmt> },

    Block { stmts: Vec<IfcapStmt> },

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

    Recv { chan: IfcapExpr, var: Ident, body: Box<IfcapStmt> },

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