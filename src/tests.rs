
#[cfg(test)]
mod tests {
    use matches::assert_matches;
    use im::vector as ivector;
    use crate::lang::*;
    use crate::lang::SecurityLevel::*;
    use crate::types::IfcapType::*;
    use crate::types::InferenceError::*;
    use crate::types::constr_solve::*;

    #[test]
    fn prog1() {
        let prog = stmts(ivector![
            letvar("x", newref(lit(true), Public), stmts(ivector![
            send(lit(true), var("x"))
            ]))
        ]);

        let res = infer_type(&prog);
        assert_matches!(res.unwrap_err(), UnificationError(_, _))
    }

    #[test]
    fn prog2() {
        let prog = stmts(ivector![
            letvar("x", newchan(), stmts(ivector![
            assign(var("x"), lit(true))
            ]))
        ]);

        let res = infer_type(&prog);
        assert_matches!(res.unwrap_err(), UnificationError(_, _))
    }

    #[test]
    fn prog3() {
        let prog = stmts(ivector![
            letvar("x", newchan(), stmts(ivector![
            assign(var("y"), lit(true))
            ]))
        ]);

        let res = infer_type(&prog);
        assert_matches!(res.unwrap_err(), UnknownBindingError(_));
    }

    #[test]
    fn prog4() {
        let prog = stmts(ivector![
            letvar("x", newref(lit(false), Public), stmts(ivector![
            assign(var("x"), lit(true))
            ]))
        ]);

        let res = infer_type(&prog);
        assert_matches!(res, Result::Ok(_));
    }
}