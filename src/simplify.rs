use crate::*;

#[derive(Debug)]
enum Case {
    None,
    Nat(u64),
    Div(u64, u64),
}

impl Case {
    fn normalize(expr: Expr) -> Expr {
        Case::to_expr(Case::from_expr(&expr)).unwrap()
    }

    fn to_expr((sa, a): (bool, Case)) -> Option<Expr> {
        match a {
            Case::None => None,
            Case::Nat(n) => Some(nat(n)),
            Case::Div(1, a) => Some(recip(nat(a))),
            Case::Div(a, 1) => Some(nat(a)),
            Case::Div(a0, a1) => Some(div(nat(a0), nat(a1))),
        }.map(|n| if !sa {neg(n)} else {n})
    }

    fn from_expr(expr: &Expr) -> (bool, Case) {
        use Expr::*;
        match expr {
            Nat(n) => (true, Case::Nat(*n)),
            Neg(a) => {
                match &**a {
                    Nat(a) => (false, Case::Nat(*a)),
                    Recip(a) => {
                        if let Nat(a) = &**a {(false, Case::Div(1, *a))}
                        else {(false, Case::None)}
                    }
                    Mul(ab) => {
                        match (&ab.0, &ab.1) {
                            (Nat(a), Recip(b)) => {
                                if let Nat(b) = &**b {(false, Case::Div(*a, *b))}
                                else {(false, Case::None)}
                            }
                            _ => (false, Case::None),
                        }
                    }
                    _ => (false, Case::None),
                }
            }
            Recip(a) => {
                match &**a {
                    Nat(a) => (true, Case::Div(1, *a)),
                    _ => (true, Case::None),
                }
            }
            Mul(ab) => {
                if let (Nat(a), Recip(b)) = (&ab.0, &ab.1) {
                    if let Nat(b) = &**b {
                        if a == b && *b != 0 {(true, Case::Nat(1))}
                        else {
                            let mut a = *a;
                            let mut b = *b;
                            let a = &mut a;
                            let b = &mut b;
                            let mut f = |p: u64| if *a % p == 0 && *b % p == 0 {
                                *a /= p;
                                *b /= p;
                            };
                            f(2); f(3); f(5); f(7); f(11); f(13); f(17);
                            (true, Case::Div(*a, *b))
                        }
                    } else {
                        (true, Case::None)
                    }
                } else {(true, Case::None)}
            }
            _ => (true, Case::None),
        }
    }

    fn add_nat(a: (bool, u64), b: (bool, u64)) -> Expr {
        match (a, b) {
            ((true, a), (true, b)) => nat(a + b),
            ((false, b), (true, a)) | ((true, a), (false, b)) =>
                if a >= b {nat(a - b)} else {neg(nat(b - a))},
            ((false, a), (false, b)) => neg(nat(a + b)),
        }
    }

    fn add_div(a: (bool, u64, u64), b: (bool, u64, u64)) -> Expr {
        match (a, b) {
            ((true, a0, a1), (true, b0, b1)) =>
                if a1 == b1 {div(nat(a0 + b0), nat(a1))}
                else {nat(a0 * b1 + a1 * b0) / nat(a1 * b1)}.simplify(),
            ((false, b0, b1), (true, a0, a1)) | ((true, a0, a1), (false, b0, b1)) =>
                if a1 == b1 {
                    if a0 >= b0 {div(nat(a0 - b0), nat(a1))}
                    else {neg(div(nat(b0 - a0), nat(a1)))}.simplify()
                }
                else {
                    let d1 = a0 * b1;
                    let d2 = a1 * b0;
                    if d1 >= d2 {nat(d1 - d2) / nat(a1 * b1)}
                    else {neg(nat(d2 - d1) / nat(a1 * b1))}.simplify()
                },
            ((false, a0, a1), (false, b0, b1)) =>
                neg(nat(a0) / nat(a1) + nat(b0) / nat(b1)).simplify(),
        }
    }

    fn mul_nat(a: (bool, u64), b: (bool, u64)) -> Expr {
        match (a, b) {
            ((true, a), (true, b)) | ((false, a), (false, b)) => nat(a * b),
            ((false, a), (true, b)) | ((true, a), (false, b)) => neg(nat(a * b)),
        }
    }

    fn mul_div(a: (bool, u64, u64), b: (bool, u64, u64)) -> Expr {
        match (a, b) {
            ((true, a0, a1), (true, b0, b1)) | ((false, a0, a1), (false, b0, b1)) =>
                div(nat(a0 * b0), nat(a1 * b1)),
            ((false, a0, a1), (true, b0, b1)) | ((true, a0, a1), (false, b0, b1)) =>
                neg(div(nat(a0 * b0), nat(a1 * b1)))
        }
    }
}

pub fn run(expr: Expr) -> Expr {
    use Expr::*;

    match expr {
        X | Y | Tau | E | Nat(_) | Var(_) => expr,
        Neg(a) => {
            let a = a.simplify();
            if let Some(a) = a.get_neg() {
                return a.clone().simplify();
            }
            if let Some(a) = a.get_nat() {
                if a == 0 {return nat(0)};
            }
            Neg(Box::new(a))
        }
        Abs(a) => Abs(Box::new(a.simplify())),
        Recip(a) => {
            let a = a.simplify();
            if let Some((a, b)) = a.get_div() {
                return div(b.clone(), a.clone()).simplify();
            }
            if let Some(a) = a.get_neg() {
                return neg(recip(a.clone())).simplify();
            }
            if let Some(a) = a.get_recip() {
                return a.clone().simplify();
            }
            Recip(Box::new(a))
        }
        Sqrt(a) => Sqrt(Box::new(a.simplify())),
        Step(a) => {
            let a = a.simplify();
            if a.get_nat().is_some() {
                return nat(1);
            }
            if let Some(a) = a.get_neg() {
                if let Some(a) = a.get_nat() {
                    return if a == 0 {nat(1)} else {nat(0)};
                }
            }
            Step(Box::new(a))
        }
        Sin(a) => {
            let a = a.simplify();
            if let Tau = a {return nat(0)};
            if let Some((a, b)) = a.get_add() {
                if let Tau = a {return Sin(Box::new(b.clone()))};
                if let Tau = b {return Sin(Box::new(a.clone()))};
            }
            Sin(Box::new(a))
        }
        Exp(a) => {
            let a = a.simplify();
            if let Some(a) = a.get_nat() {
                if a == 0 {return nat(1)};
                if a == 1 {return E};
            }
            Exp(Box::new(a))
        }
        Ln(a) => Ln(Box::new(a.simplify())),
        Add(ab) => {
            let a = ab.0.simplify();
            let b = ab.1.simplify();
            match (Case::from_expr(&a), Case::from_expr(&b)) {
                ((_, Case::Nat(0)), _) => return b,
                (_, (_, Case::Nat(0))) => return a,
                ((_, Case::None), _) | (_, (_, Case::None)) => {}
                ((sa, Case::Nat(a)), (sb, Case::Nat(b))) =>
                    return Case::normalize(Case::add_nat((sa, a), (sb, b))),
                ((sa, Case::Div(a0, a1)), (sb, Case::Div(b0, b1))) =>
                    return Case::normalize(Case::add_div((sa, a0, a1), (sb, b0, b1))),
                ((sa, Case::Nat(a)), (sb, Case::Div(b0, b1))) =>
                    return Case::normalize(Case::add_div((sa, a * b1, b1), (sb, b0, b1))),
                ((sa, Case::Div(a0, a1)), (sb, Case::Nat(b))) =>
                    return Case::normalize(Case::add_div((sa, a0, a1), (sb, a1 * b, a1))),
            }

            match (a.get_neg(), b.get_neg()) {
                (Some(a), Some(b)) => return neg(add(a.clone(), b.clone())).simplify(),
                (Some(a), None) => return sub(b, a.clone()).simplify(),
                (None, Some(_)) => {}
                (None, None) => {}
            }

            Add(Box::new((a, b)))
        }
        Mul(ab) => {
            let a = ab.0.simplify();
            let b = ab.1.simplify();
            match (Case::from_expr(&a), Case::from_expr(&b)) {
                ((_, Case::Nat(0)), _) => return nat(0),
                (_, (_, Case::Nat(0))) => return nat(0),
                ((_, Case::Nat(1)), _) => return b,
                (_, (_, Case::Nat(1))) => return a,
                ((_, Case::None), _) | (_, (_, Case::None)) => {}
                ((sa, Case::Nat(a)), (sb, Case::Nat(b))) =>
                    return Case::normalize(Case::mul_nat((sa, a), (sb, b))),
                ((sa, Case::Div(a0, a1)), (sb, Case::Div(b0, b1))) =>
                    return Case::normalize(Case::mul_div((sa, a0, a1), (sb, b0, b1))),
                ((sa, Case::Nat(a)), (sb, Case::Div(b0, b1))) |
                ((sb, Case::Div(b0, b1)), (sa, Case::Nat(a))) =>
                    return Case::normalize(Case::mul_div((sa, a, 1), (sb, b0, b1))),
            }

            match (a.get_neg(), b.get_neg()) {
                (Some(a), Some(b)) => return mul(a.clone(), b.clone()).simplify(),
                (Some(a), None) => return neg(mul(a.clone(), b)).simplify(),
                (None, Some(b)) => return neg(mul(a, b.clone())).simplify(),
                (None, None) => {}
            }
            match (a.get_recip(), b.get_recip()) {
                (Some(a), Some(b)) => return recip(mul(a.clone(), b.clone())).simplify(),
                (Some(a), None) => return div(b, a.clone()).simplify(),
                (None, Some(_)) => {}
                (None, None) => {}
            }
            match (a.get_div(), b.get_div()) {
                (Some((a0, a1)), Some((b0, b1))) =>
                    return ((a0.clone() * b0.clone()) / (a1.clone() * b1.clone())).simplify(),
                (Some((a0, a1)), None) => return (a0.clone() * b) / a1.clone(),
                (None, Some((b0, b1))) => return (a * b0.clone()) / b1.clone(),
                (None, None) => {}
            }

            Mul(Box::new((a, b)))
        }
        Max(ab) => {
            let a = ab.0.simplify();
            let b = ab.1.simplify();
            if let (Some(a), Some(b)) = (a.get_nat(), b.get_nat()) {
                return Nat(if a >= b {a} else {b});
            }
            Max(Box::new((a, b)))
        }
        Min(ab) => {
            let a = ab.0.simplify();
            let b = ab.1.simplify();
            if let (Some(a), Some(b)) = (a.get_nat(), b.get_nat()) {
                return Nat(if a <= b {a} else {b});
            }
            Min(Box::new((a, b)))
        }
        Let(_) => expr,
        Decor(ab) => Decor(Box::new((ab.0.simplify(), ab.1.clone()))),
        App(abc) => App(Box::new((abc.0, abc.1.simplify(), abc.2.simplify()))),
    }
}
