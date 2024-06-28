#![doc = include_str!("../README.md")]
#![deny(missing_docs)]

use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

use serde::{Serialize, Deserialize};

use cache::Cache;
use token::Token;
use image::{RgbImage, Rgb};

pub mod cache;
pub mod compressor;
pub mod constant;
pub mod grid;
pub mod partial_eval;
pub mod partial_red;
pub mod semantics;
pub mod sd;
pub mod textures;
pub mod token;
pub mod wasm;

/// A parameteric point in 2 dimensions.
pub type Point2 = [Expr; 2];
/// A parametric point in 3 dimensions.
pub type Point3 = [Expr; 3];
/// A parametric point in 4 dimensions.
pub type Point4 = [Expr; 4];

/// A parametric color in 2 dimensions.
pub type Color = [Expr; 3];

/// Stores variables that are reused in expression.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Context {
    /// Variables and their expressions.
    pub vars: Vec<(String, Expr)>,
}

impl Context {
    /// Creates new empty context.
    pub fn new() -> Context {
        Context {
            vars: vec![]
        }
    }
}

/// Used to decorate an expression with extra information.
pub type Decor = (Expr, Vec<Token>);

/// Stores context and external functions.
///
/// The context is some custom data type that one needs for external functions.
#[derive(Clone)]
pub struct Runtime<T = ()> {
    /// Context.
    pub ctx: std::sync::Arc<T>,
    /// External functions.
    pub functions: Vec<fn(&T, u32, f64, f64) -> f64>,
}

impl Runtime {
    /// Creates new runtime with empty context.
    pub fn new() -> Runtime {
        Runtime {
            ctx: std::sync::Arc::new(()),
            functions: vec![],
        }
    }
}

impl<T> Runtime<T> {
    /// Creates runtime from parts.
    pub fn from_parts(ctx: T, functions: Vec<fn(&T, u32, f64, f64) -> f64>) -> Runtime<T> {
        Runtime {
            ctx: std::sync::Arc::new(ctx),
            functions,
        }
    }
}

/// Stores expression of two variables (X and Y).
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    /// X.
    X,
    /// Y.
    Y,
    /// Tau.
    Tau,
    /// Euler's constant.
    E,
    /// Variable.
    Var(String),
    /// Natural number.
    Nat(u64),
    /// Negative.
    Neg(Box<Expr>),
    /// Absolute function.
    Abs(Box<Expr>),
    /// Reciprocal (unary division).
    Recip(Box<Expr>),
    /// Square root.
    Sqrt(Box<Expr>),
    /// Step function.
    Step(Box<Expr>),
    /// Sine function.
    Sin(Box<Expr>),
    /// Natural exponent.
    Exp(Box<Expr>),
    /// Natural logarithm.
    Ln(Box<Expr>),
    /// Addition.
    Add(Box<(Expr, Expr)>),
    /// Multiplication.
    Mul(Box<(Expr, Expr)>),
    /// Maximum.
    Max(Box<(Expr, Expr)>),
    /// Minimum.
    Min(Box<(Expr, Expr)>),
    /// Let-expression.
    Let(Box<(Context, Expr)>),
    /// Decorate expression with additional information.
    ///
    /// This is used in semantical analysis.
    Decor(Box<Decor>),
    /// Call some external function.
    App(Box<(u32, Expr, Expr)>),
}

impl Div<u64> for Expr {
    type Output = Expr;
    fn div(self, other: u64) -> Expr {div(self, nat(other))}
}

impl Div<Expr> for Expr {
    type Output = Expr;
    fn div(self, other: Expr) -> Expr {div(self, other)}
}

impl Mul<u64> for Expr {
    type Output = Expr;
    fn mul(self, other: u64) -> Expr {mul(self, nat(other))}
}

impl Mul<Expr> for Expr {
    type Output = Expr;
    fn mul(self, other: Expr) -> Expr {mul(self, other)}
}

impl Add<u64> for Expr {
    type Output = Expr;
    fn add(self, other: u64) -> Expr {add(self, nat(other))}
}

impl Add<Expr> for Expr {
    type Output = Expr;
    fn add(self, other: Expr) -> Expr {add(self, other)}
}

impl Sub<u64> for Expr {
    type Output = Expr;
    fn sub(self, other: u64) -> Expr {sub(self, nat(other))}
}

impl Sub<Expr> for Expr {
    type Output = Expr;
    fn sub(self, other: Expr) -> Expr {sub(self, other)}
}

impl Neg for Expr {
    type Output = Expr;
    fn neg(self) -> Expr {neg(self)}
}

impl fmt::Display for Expr {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use Expr::*;

        match self {
            X => write!(w, "x")?,
            Y => write!(w, "y")?,
            Tau => write!(w, "τ")?,
            E => write!(w, "𝐞")?,
            Var(name) => write!(w, "{}", name)?,
            Nat(n) => write!(w, "{}", n)?,
            Neg(a) => {
                if a.needs_parens() {
                    write!(w, "-({})", a)?;
                } else {
                    write!(w, "-{}", a)?;
                }
            }
            Abs(a) => write!(w, "abs({})", a)?,
            Recip(a) => {
                if a.needs_parens() {
                    write!(w, "1/({})", a)?;
                } else {
                    write!(w, "1/{}", a)?;
                }
            }
            Sqrt(a) => write!(w, "sqrt({})", a)?,
            Step(a) => write!(w, "step({})", a)?,
            Sin(a) => write!(w, "sin({})", a)?,
            Exp(a) => write!(w, "𝐞^({})", a)?,
            Ln(a) => write!(w, "ln({})", a)?,
            Add(ab) => {
                if let Some(b) = ab.1.get_neg() {
                    if ab.0.needs_parens() &&
                       !ab.0.get_recip().is_some() &&
                       !ab.0.get_div().is_some() &&
                       !ab.0.get_sub().is_some() &&
                       !ab.0.get_square().is_some() &&
                       !ab.0.get_mul().is_some()
                    {
                        write!(w, "({})", ab.0)?;
                    } else {
                        write!(w, "{}", ab.0)?;
                    }
                    write!(w, "-")?;
                    if b.needs_parens() &&
                       !b.get_recip().is_some() &&
                       !b.get_div().is_some() &&
                       !b.get_square().is_some()
                    {
                        write!(w, "({})", b)?;
                    } else {
                        write!(w, "{}", b)?;
                    }
                } else {
                    if ab.0.needs_parens() &&
                       !ab.0.get_recip().is_some() &&
                       !ab.0.get_div().is_some() &&
                       !ab.0.get_sub().is_some() &&
                       !ab.0.get_square().is_some()
                    {
                        write!(w, "({})", ab.0)?;
                    } else {
                        write!(w, "{}", ab.0)?;
                    }
                    write!(w, "+")?;
                    if ab.1.needs_parens() &&
                       !ab.1.get_recip().is_some() &&
                       !ab.1.get_div().is_some() &&
                       !ab.1.get_square().is_some()
                    {
                        write!(w, "({})", ab.1)?;
                    } else {
                        write!(w, "{}", ab.1)?;
                    }
                }
            }
            Mul(ab) => {
                if let Some(b) = ab.1.get_recip() {
                    if ab.0.needs_parens() {
                        write!(w, "({})", ab.0)?;
                    } else {
                        write!(w, "{}", ab.0)?;
                    }
                    write!(w, "/")?;
                    if b.needs_parens() {
                        write!(w, "({})", b)?;
                    } else {
                        write!(w, "{}", b)?;
                    }
                } else {
                    if let Some(a) = self.get_square() {
                        if a.needs_parens() {
                            write!(w, "({})", a)?;
                        } else {
                            write!(w, "{}", a)?;
                        }
                        write!(w, "^2")?;
                    } else {
                        if ab.0.needs_parens() {
                            write!(w, "({})", ab.0)?;
                        } else {
                            write!(w, "{}", ab.0)?;
                        }
                        write!(w, "*")?;
                        if ab.1.needs_parens() {
                            write!(w, "({})", ab.1)?;
                        } else {
                            write!(w, "{}", ab.1)?;
                        }
                    }
                }
            }
            Max(ab) => write!(w, "max({},{})", ab.0, ab.1)?,
            Min(ab) => write!(w, "min({},{})", ab.0, ab.1)?,
            Let(ab) => {
                let ctx = &ab.0;
                write!(w, "{}\nwhere\n", ab.1)?;
                for var in &ctx.vars {
                    write!(w, "  {} = {}\n", var.0, var.1)?;
                }
            }
            Decor(ab) => {
                if ab.0.needs_parens() {
                    write!(w, "({}) : ", ab.0)?;
                } else {
                    write!(w, "{} : ", ab.0)?;
                }
                let mut tabs = 0;
                let mut last_start = false;
                for token in &ab.1 {
                    use Token::*;

                    match token {
                        TokenExpr(a) => write!(w, "{}", a)?,
                        StartParens => {
                            write!(w, "(")?;
                        }
                        EndParens => {
                            write!(w, ")")?
                        }
                        StartSquareBracket => {
                            write!(w, "[")?;
                        }
                        EndSquareBracket => {
                            write!(w, "]")?;
                        }
                        StartCurlyBracket => {
                            write!(w, "{{")?;
                        }
                        EndCurlyBracket => {
                            write!(w, "}}")?;
                        }
                        Space => write!(w, " ")?,
                        Comma => write!(w, ",")?,
                        NewLine => {
                            if last_start {
                                tabs += 1;
                            }
                            write!(w, "\n")?;
                        }
                        Tabs => {
                            for _ in 0..tabs {
                                write!(w, "  ")?;
                            }
                        }
                        TabsPrev => {
                            tabs -= 1;
                            for _ in 0..tabs {
                                write!(w, "  ")?;
                            }
                        }
                    }
                    last_start = token.is_start_bracket();
                }
            }
            App(abc) => write!(w, "app({},{},{})", abc.0, abc.1, abc.2)?,
        }
        Ok(())
    }
}

impl Expr {
    /// Returns true if expression has a given variable decoration.
    pub fn has_decor_var(&self, var: &str) -> bool {
        if let Expr::Decor(ab) = self {
            let dec = &ab.1;
            if dec.len() != 1 {return false};

            if let Token::TokenExpr(v) = &dec[0] {
                if let Expr::Var(v) = v {
                    if &**v == var {return true}
                }
            }
        }
        false
    }

    /// Gets the inner expression of decoration.
    pub fn decor_inner(&self) -> Option<&Expr> {
        match self {
            Expr::Decor(ab) => Some(&ab.0),
            _ => None
        }
    }

    /// Returns true if it needs parenthesis.
    pub fn needs_parens(&self) -> bool {
        use Expr::*;

        match self {
            X | Y | Tau | E | Var(_) |
            Nat(_) | Abs(_) | Sin(_) | Step(_) | Sqrt(_) |
            Exp(_) | Ln(_) |
            Min(_) | Max(_) => false,
            _ => true,
        }
    }

    /// Get natural number.
    pub fn get_nat(&self) -> Option<u64> {
        match self {
            Expr::Nat(n) => Some(*n),
            _ => None,
        }
    }

    /// Get negative argument.
    pub fn get_neg(&self) -> Option<&Expr> {
        match self {
            Expr::Neg(a) => Some(a),
            _ => None,
        }
    }

    /// Get subtraction arguments.
    pub fn get_sub(&self) -> Option<(&Expr, &Expr)> {
        match self {
            Expr::Add(ab) => {
                if let Some(b) = ab.1.get_neg() {
                    Some((&ab.0, b))
                } else {None}
            }
            _ => None,
        }
    }

    /// Get reciprocal argument (unary division).
    pub fn get_recip(&self) -> Option<&Expr> {
        match self {
            Expr::Recip(a) => Some(a),
            _ => None,
        }
    }

    /// Get addition arguments.
    pub fn get_add(&self) -> Option<(&Expr, &Expr)> {
        match self {
            Expr::Add(ab) => Some((&ab.0, &ab.1)),
            _ => None,
        }
    }

    /// Get multiplication arguments.
    pub fn get_mul(&self) -> Option<(&Expr, &Expr)> {
        match self {
            Expr::Mul(ab) => Some((&ab.0, &ab.1)),
            _ => None,
        }
    }

    /// Get division arguments.
    pub fn get_div(&self) -> Option<(&Expr, &Expr)> {
        match self {
            Expr::Mul(ab) => {
                if let Some(b) = ab.1.get_recip() {
                    Some((&ab.0, b))
                } else {None}
            }
            _ => None,
        }
    }

    /// Get square argument.
    pub fn get_square(&self) -> Option<&Expr> {
        match self {
            Expr::Mul(ab) => {
                if ab.0 == ab.1 {
                    Some(&ab.0)
                } else {None}
            }
            _ => None,
        }
    }

    /// Returns true if one.
    pub fn is_one(&self) -> bool {
        match self {
            Expr::Nat(1) => true,
            _ => false,
        }
    }

    /// Returns true if zero.
    pub fn is_zero(&self) -> bool {
        match self {
            Expr::Nat(0) => true,
            _ => false,
        }
    }

    /// Rewrite expression.
    pub fn rewrite(self, ctx: &Context) -> Expr {
        use Expr::*;

        for var in &ctx.vars {
            if var.1 == self {return Var(var.0.clone())}
        }

        match self {
            X | Y | Tau | E | Nat(_) | Var(_) => self,
            Neg(a) => Neg(Box::new(a.rewrite(ctx))),
            Abs(a) => Abs(Box::new(a.rewrite(ctx))),
            Recip(a) => Recip(Box::new(a.rewrite(ctx))),
            Sqrt(a) => Sqrt(Box::new(a.rewrite(ctx))),
            Step(a) => Step(Box::new(a.rewrite(ctx))),
            Sin(a) => Sin(Box::new(a.rewrite(ctx))),
            Exp(a) => Exp(Box::new(a.rewrite(ctx))),
            Ln(a) => Ln(Box::new(a.rewrite(ctx))),
            Add(ab) => Add(Box::new((ab.0.rewrite(ctx), ab.1.rewrite(ctx)))),
            Mul(ab) => Mul(Box::new((ab.0.rewrite(ctx), ab.1.rewrite(ctx)))),
            Max(ab) => Max(Box::new((ab.0.rewrite(ctx), ab.1.rewrite(ctx)))),
            Min(ab) => Min(Box::new((ab.0.rewrite(ctx), ab.1.rewrite(ctx)))),
            Let(_) => self,
            Decor(ab) => Decor(Box::new((ab.0.rewrite(ctx), ab.1.clone()))),
            App(abc) => App(Box::new((abc.0, abc.1.rewrite(ctx), abc.2.rewrite(ctx)))),
        }
    }

    /// Simplify expression.
    pub fn simplify(self) -> Expr {
        use Expr::*;

        match self {
            X | Y | Tau | E | Nat(_) | Var(_) => self,
            Neg(a) => {
                if let Some(a) = a.get_neg() {
                    return a.clone().simplify();
                }
                if let Some(a) = a.get_nat() {
                    if a == 0 {return nat(0)};
                }
                Neg(Box::new(a.simplify()))
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
                if let Some(b) = b.get_neg() {
                    if &a == b {return Nat(0)}
                    if b.is_zero() {return a}
                    if let (Some(a), Some(b)) = (a.get_nat(), b.get_nat()) {
                        if a >= b {
                            return Nat(a - b);
                        } else {
                            return neg(Nat(b - a));
                        }
                    }
                    if let (Some((a0, a1)), Some((b0, b1))) = (a.get_div(), b.get_div()) {
                        if a1 == b1 {
                            return div(sub(a0.clone(), b0.clone()), a1.clone()).simplify();
                        } else {
                            return div(sub(mul(a0.clone(), b1.clone()), mul(a1.clone(), b0.clone())),
                                mul(a1.clone(), b1.clone())).simplify();
                        }
                    }
                    if let (Some((a0, a1)), Some(b)) = (a.get_div(), b.get_recip()) {
                        if a1 == b {
                            return div(sub(a0.clone(), nat(1)), a1.clone()).simplify();
                        } else {
                            return div(sub(mul(a0.clone(), b.clone()), a1.clone()),
                                mul(a1.clone(), b.clone())).simplify();
                        }
                    }
                    if let (Some(a), Some((b0, b1))) = (a.get_recip(), b.get_div()) {
                        if a == b1 {
                            return div(sub(nat(1), b0.clone()), b1.clone()).simplify();
                        } else {
                            return div(sub(b1.clone(), mul(a.clone(), b0.clone())),
                                mul(a.clone(), b1.clone())).simplify();
                        }
                    }
                    if let (Some(a), Some(b)) = (a.get_recip(), b.get_recip()) {
                        return div(sub(b.clone(), a.clone()), mul(a.clone(), b.clone())).simplify();
                    }
                    if let (true, Some((b0, b1))) = (a.is_one(), b.get_div()) {
                        return div(sub(b1.clone(), b0.clone()), b1.clone()).simplify();
                    }
                    if let (Some((a0, a1)), true) = (a.get_div(), b.is_one()) {
                        return div(sub(a0.clone(), a1.clone()), a1.clone()).simplify();
                    }
                }
                if let (Some(a), Some(b)) = (a.get_nat(), b.get_nat()) {
                    return Nat(a + b);
                }
                if let (Some(a), Some(b)) = (a.get_recip(), b.get_recip()) {
                    return div(add(a.clone(), b.clone()), mul(a.clone(), b.clone())).simplify()
                }
                if let (true, Some(b)) = (a.is_one(), b.get_neg()) {
                    if let Some(b) = b.get_recip() {
                        return div(sub(b.clone(), nat(1)), b.clone()).simplify();
                    }
                }
                if let (Some(a), Some((b0, b1))) = (a.get_recip(), b.get_div()) {
                    if a == b1 {
                        return div(add(nat(1), b0.clone()), a.clone()).simplify();
                    } else {
                        return div(
                            add(b1.clone(), mul(a.clone(), b0.clone())),
                            mul(a.clone(), b1.clone())).simplify();
                    }
                }
                if let (Some((a0, a1)), Some(b)) = (a.get_div(), b.get_recip()) {
                    if a1 == b {
                        return div(add(a0.clone(), nat(1)), b.clone()).simplify();
                    } else {
                        return div(add(mul(a0.clone(), b.clone()), a1.clone()),
                            mul(a1.clone(), b.clone())).simplify();
                    }
                }
                if let (Some(a), None) = (a.get_neg(), b.get_neg()) {
                    return sub(b, a.clone()).simplify();
                }
                if a.is_zero() {return b}
                if b.is_zero() {return a}
                Add(Box::new((a, b)))
            }
            Mul(ab) => {
                let a = ab.0.simplify();
                let b = ab.1.simplify();
                if a.is_zero() || b.is_zero() {return Nat(0)};
                if let (Some(a), Some(b)) = (a.get_recip(), b.get_recip()) {
                    return Recip(Box::new(Mul(Box::new((a.clone(), b.clone()))))).simplify();
                }
                if let Some(b) = b.get_recip() {
                    if a == *b {return Nat(1)};
                    if let (Some(a), Some(b)) = (a.get_nat(), b.get_nat()) {
                        if a % b == 0 {return nat(a / b)};
                        if a % 2 == 0 && b % 2 == 0 {
                            return div(nat(a / 2), nat(b / 2)).simplify();
                        }
                        if a % 3 == 0 && b % 3 == 0 {
                            return div(nat(a / 3), nat(b / 3)).simplify();
                        }
                        if a % 5 == 0 && b % 5 == 0 {
                            return div(nat(a / 5), nat(b / 5)).simplify();
                        }
                        if a % 7 == 0 && b % 7 == 0 {
                            return div(nat(a / 7), nat(b / 7)).simplify();
                        }
                        if a % 11 == 0 && b % 11 == 0 {
                            return div(nat(a / 11), nat(b / 11)).simplify();
                        }
                        if a % 13 == 0 && b % 13 == 0 {
                            return div(nat(a / 13), nat(b / 13)).simplify();
                        }
                    }
                }
                if let (Some(a), Some(b)) = (a.get_nat(), b.get_nat()) {
                    return Nat(a * b);
                }
                if let (Some((a0, a1)), Some(b)) = (a.get_div(), b.get_recip()) {
                    return div(a0.clone(), mul(a1.clone(), b.clone())).simplify();
                }
                if let (Some(a), Some((b0, b1))) = (a.get_recip(), b.get_div()) {
                    return div(b0.clone(), mul(a.clone(), b1.clone())).simplify();
                }
                if let (Some((a0, a1)), Some((b0, b1))) = (a.get_div(), b.get_div()) {
                    return div(mul(a0.clone(), b0.clone()), mul(a1.clone(), b1.clone())).simplify()
                }
                if let (Some(a), Some((b0, b1))) = (a.get_nat(), b.get_div()) {
                    return div(mul(nat(a), b0.clone()), b1.clone()).simplify()
                }
                if let (Some(a), Some(b)) = (a.get_neg(), b.get_neg()) {
                    return mul(a.clone(), b.clone()).simplify();
                }
                if let Some(a) = a.get_neg() {
                    return neg(mul(a.clone(), b)).simplify();
                }
                if let Some(b) = b.get_neg() {
                    return neg(mul(a, b.clone())).simplify();
                }
                if let Some((a0, a1)) = a.get_div() {
                    return div(mul(a0.clone(), b), a1.clone()).simplify();
                }
                else if a.is_one() {b}
                else if b.is_one() {a}
                else {Mul(Box::new((a, b)))}
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
            Let(_) => self,
            Decor(ab) => Decor(Box::new((ab.0.simplify(), ab.1.clone()))),
            App(abc) => App(Box::new((abc.0, abc.1.simplify(), abc.2.simplify()))),
        }
    }

    /// Evaluate X with Y set to zero.
    pub fn eval(&self, v: f64) -> f64 {
        let rt = Runtime::new();
        self.eval2(&rt, [v, 0.0], &Context::new(), &mut Cache::new())
    }

    /// Evaluate in 2D.
    pub fn eval2<T>(&self, rt: &Runtime<T>, v: [f64; 2], ctx: &Context, cache: &mut Cache) -> f64 {
        use Expr::*;

        match self {
            X => v[0],
            Y => v[1],
            Tau => 6.283185307179586,
            E => 2.718281828459045,
            Var(name) => cache.val(rt, v, name, ctx).0,
            Nat(n) => *n as f64,
            Neg(a) => -a.eval2(rt, v, ctx, cache),
            Abs(a) => a.eval2(rt, v, ctx, cache).abs(),
            Recip(a) => a.eval2(rt, v, ctx, cache).recip(),
            Sqrt(a) => a.eval2(rt, v, ctx, cache).sqrt(),
            Step(a) => {
                let v = a.eval2(rt, v, ctx, cache);
                if v >= 0.0 {1.0} else {0.0}
            }
            Sin(a) => a.eval2(rt, v, ctx, cache).sin(),
            Exp(a) => a.eval2(rt, v, ctx, cache).exp(),
            Ln(a) => a.eval2(rt, v, ctx, cache).ln(),
            Add(ab) => ab.0.eval2(rt, v, ctx, cache) + ab.1.eval2(rt, v, ctx, cache),
            Mul(ab) => ab.0.eval2(rt, v, ctx, cache) * ab.1.eval2(rt, v, ctx, cache),
            Max(ab) => ab.0.eval2(rt, v, ctx, cache).max(ab.1.eval2(rt, v, ctx, cache)),
            Min(ab) => ab.0.eval2(rt, v, ctx, cache).min(ab.1.eval2(rt, v, ctx, cache)),
            Let(ab) => {
                let ctx = &ab.0;
                ab.1.eval2(rt, v, ctx, cache)
            }
            Decor(ab) => ab.0.eval2(rt, v, ctx, cache),
            App(abc) => {
                let f = rt.functions[abc.0 as usize];
                f(&rt.ctx, abc.0, abc.1.eval2(rt, v, ctx, cache), abc.2.eval2(rt, v, ctx, cache))
            }
        }
    }

    /// Gets X dependence.
    ///
    /// This is used to improve caching when using interpreter.
    pub fn dep_x<T>(&self, rt: &Runtime<T>, v: [f64; 2], ctx: &Context, cache: &mut Cache) -> bool {
        use Expr::*;

        match self {
            X => true,
            Y | Tau | E | Nat(_) => false,
            Var(name) => cache.val(rt, v, name, ctx).1,
            Neg(a) | Abs(a) | Recip(a) | Sqrt(a) |
            Step(a) | Sin(a) | Exp(a) | Ln(a) => a.dep_x(rt, v, ctx, cache),
            Add(ab) | Mul(ab) | Max(ab) | Min(ab) => {
                let a_dep_x = ab.0.dep_x(rt, v, ctx, cache);
                let b_dep_x = ab.1.dep_x(rt, v, ctx, cache);
                a_dep_x || b_dep_x
            }
            Let(ab) => {
                let ctx = &ab.0;
                ab.1.dep_x(rt, v, ctx, cache)
            }
            Decor(ab) => ab.0.dep_x(rt, v, ctx, cache),
            App(abc) => {
                let a_dep_x = abc.1.dep_x(rt, v, ctx, cache);
                let b_dep_x = abc.2.dep_x(rt, v, ctx, cache);
                a_dep_x || b_dep_x
            }
        }
    }

    /// Substitute X and Y with 2D point.
    pub fn subst2(&self, p: &Point2) -> Expr {
        use Expr::*;

        match self {
            X => p[0].clone(),
            Y => p[1].clone(),
            Tau | E => self.clone(),
            Var(_) => self.clone(),
            Nat(n) => Nat(*n),
            Neg(a) => Neg(Box::new(a.subst2(p))),
            Abs(a) => Abs(Box::new(a.subst2(p))),
            Recip(a) => Recip(Box::new(a.subst2(p))),
            Sqrt(a) => Sqrt(Box::new(a.subst2(p))),
            Step(a) => Step(Box::new(a.subst2(p))),
            Sin(a) => Sin(Box::new(a.subst2(p))),
            Exp(a) => Exp(Box::new(a.subst2(p))),
            Ln(a) => Ln(Box::new(a.subst2(p))),
            Add(ab) => Add(Box::new((ab.0.subst2(p), ab.1.subst2(p)))),
            Mul(ab) => Mul(Box::new((ab.0.subst2(p), ab.1.subst2(p)))),
            Max(ab) => Max(Box::new((ab.0.subst2(p), ab.1.subst2(p)))),
            Min(ab) => Min(Box::new((ab.0.subst2(p), ab.1.subst2(p)))),
            Let(_) => self.clone(),
            Decor(ab) => Decor(Box::new((ab.0.subst2(p), ab.1.clone()))),
            App(abc) => App(Box::new((abc.0, abc.1.subst2(p), abc.2.subst2(p)))),
        }
    }

    /// Translate in 2D.
    pub fn translate(&self, off: Point2) -> Expr {
        self.subst2(&p2_sub([x(), y()], off))
    }

    /// Scale in 2D.
    pub fn scale(&self, s: Point2) -> Expr {
        self.subst2(&p2_div([x(), y()], s))
    }

    /// Scale at 2D coordinate.
    pub fn scale_at(&self, off: Point2, s: Point2) -> Expr {
        self.translate(p2_neg(off.clone())).scale(s).translate(off)
    }

    /// Rotate radians.
    pub fn rotate(&self, rad: Expr) -> Expr {
        let sin = sin(rad.clone());
        let cos = cos(rad);
        let r1 = [cos.clone(), neg(sin.clone())];
        let r2 = [sin, cos];
        let id = [x(), y()];
        self.subst2(&[p2_dot(r1, id.clone()), p2_dot(r2, id)])
    }

    /// Rotate radians at 2D coordinate.
    pub fn rotate_at(&self, off: Point2, rad: Expr) -> Expr {
        self.translate(p2_neg(off.clone())).rotate(rad).translate(off)
    }
}

/// Call some external function.
pub fn app(id: u32, a: Expr, b: Expr) -> Expr {Expr::App(Box::new((id, a, b)))}
/// X.
pub fn x() -> Expr {Expr::X}
/// Y.
pub fn y() -> Expr {Expr::Y}
/// Variable.
pub fn var(v: &str) -> Expr {Expr::Var(v.into())}
/// Tau.
pub fn tau() -> Expr {Expr::Tau}
/// Pi.
pub fn pi() -> Expr {div(tau(), nat(2))}
/// 45 degrees in radians.
pub fn rad_45() -> Expr {div(tau(), nat(8))}
/// 90 degrees in radians.
pub fn rad_90() -> Expr {div(tau(), nat(4))}
/// Euler's constant.
pub fn e() -> Expr {Expr::E}
/// Natural number.
pub fn nat(a: u64) -> Expr {Expr::Nat(a)}
/// Half unit.
pub fn half() -> Expr {div(nat(1), nat(2))}
/// Negative.
pub fn neg(a: Expr) -> Expr {Expr::Neg(Box::new(a))}
/// Absolute value.
pub fn abs(a: Expr) -> Expr {Expr::Abs(Box::new(a))}
/// Reciprocal (univary division).
pub fn recip(a: Expr) -> Expr {Expr::Recip(Box::new(a))}
/// Square root.
pub fn sqrt(a: Expr) -> Expr {Expr::Sqrt(Box::new(a))}
/// Step at zero.
pub fn step(a: Expr) -> Expr {Expr::Step(Box::new(a))}
/// Step at `x`.
pub fn step_at(a: Expr, x: Expr) -> Expr {step(sub(x, a))}
/// Step after zero.
pub fn step_pos(a: Expr) -> Expr {set_inv(step(neg(a)))}
/// Step after `x`.
pub fn step_pos_at(a: Expr, x: Expr) -> Expr {step_pos(sub(x, a))}
/// If `cond` is greater or equal to zero, then return `a`, otherwise `b`.
pub fn pos(cond: Expr, a: Expr, b: Expr) -> Expr {
    lerp(b, a, step_pos(cond))
}
/// Range with exclusive end.
pub fn range(a: Expr, b: Expr, x: Expr) -> Expr {
    mul(step_at(a, x.clone()), set_inv(step_at(b, x)))
}
/// Range with inclusive end.
pub fn range_incl(a: Expr, b: Expr, x: Expr) -> Expr {
    mul(step_at(a, x.clone()), set_inv(step_pos_at(b, x)))
}
/// Clamp value.
pub fn clamp(a: Expr, b: Expr, x: Expr) -> Expr {
    pos(sub(x.clone(), a.clone()), pos(sub(x.clone(), b.clone()), b, x), a)
}
/// Clamp value to unit range.
pub fn clamp_unit(x: Expr) -> Expr {clamp(nat(0), nat(1), x)}
/// Clamp value to u8 range.
pub fn clamp_u8(x: Expr) -> Expr {clamp(nat(0), nat(255), x)}
/// Greater or equal.
pub fn ge(a: Expr, b: Expr) -> Expr {step(sub(a, b))}
/// Greater than.
pub fn gt(a: Expr, b: Expr) -> Expr {step_pos(sub(a, b))}
/// Less or equal.
pub fn le(a: Expr, b: Expr) -> Expr {set_inv(gt(a, b))}
/// Less than.
pub fn lt(a: Expr, b: Expr) -> Expr {set_inv(ge(a, b))}
/// Equal.
pub fn eq(a: Expr, b: Expr) -> Expr {set_and(ge(a.clone(), b.clone()), le(a, b))}
/// Invert set.
pub fn set_inv(a: Expr) -> Expr {sub(nat(1), a)}
/// AND of two sets.
pub fn set_and(a: Expr, b: Expr) -> Expr {min(a, b)}
/// OR of two sets.
pub fn set_or(a: Expr, b: Expr) -> Expr {max(a, b)}
/// XOR of two sets.
pub fn set_xor(a: Expr, b: Expr) -> Expr {
    set_or(set_and(a.clone(), set_inv(b.clone())),
        set_and(b, set_inv(a)))
}
/// Sine.
pub fn sin(a: Expr) -> Expr {Expr::Sin(Box::new(a))}
/// Cosine.
pub fn cos(a: Expr) -> Expr {sin(add(a, rad_90()))}
/// Natural exponent.
pub fn exp(a: Expr) -> Expr {Expr::Exp(Box::new(a))}
/// Natural logarithm.
pub fn ln(a: Expr) -> Expr {Expr::Ln(Box::new(a))}
/// Maximum.
pub fn max(a: Expr, b: Expr) -> Expr {Expr::Max(Box::new((a, b)))}
/// Minimum.
pub fn min(a: Expr, b: Expr) -> Expr {Expr::Min(Box::new((a, b)))}
/// Addition.
pub fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new((a, b)))
}
/// Subtraction.
pub fn sub(a: Expr, b: Expr) -> Expr {
    add(a, neg(b))
}
/// Multiplication.
pub fn mul(a: Expr, b: Expr) -> Expr {
    Expr::Mul(Box::new((a, b)))
}
/// Division.
pub fn div(a: Expr, b: Expr) -> Expr {
    mul(a, recip(b))
}
/// Square `a^2`.
pub fn square(a: Expr) -> Expr {mul(a.clone(), a)}
/// Linear interpolation.
pub fn lerp(a: Expr, b: Expr, t: Expr) -> Expr {
    add(a.clone(), mul(sub(b, a), t))
}
/// Convert from unit interval to radians.
pub fn unit_to_rad(a: Expr) -> Expr {
    mul(a, tau())
}
/// Convert from radians to unit interval.
pub fn rad_to_unit(a: Expr) -> Expr {
    div(a, tau())
}
/// Let-expression.
pub fn let_(ctx: Context, a: Expr) -> Expr {
    Expr::Let(Box::new((ctx, a)))
}
/// Chess pattern.
pub fn chess(n: u64) -> Expr {
    let sx = step(sin(mul(mul(div(nat(n), nat(2)), tau()), x())));
    let sy = step(sin(mul(mul(div(nat(n), nat(2)), tau()), y())));
    set_xor(sx, sy)
}
/// Limit set to unit square.
pub fn set_unit_square(f: Expr) -> Expr {
    set_and(set_and(
        range(nat(0), nat(1), x()),
        range(nat(0), nat(1), y())
    ), f)
}

/// If `cond` is greater or equal to zero, then `a` is returned, otherwise `b`.
pub fn p2_pos(cond: Expr, a: Point2, b: Point2) -> Point2 {
    p2_lerp(b, a, step_pos(cond))
}
/// Component-wise absolute of 2D vector.
pub fn p2_abs(a: Point2) -> Point2 {
    let [a0, a1] = a;
    [abs(a0), abs(a1)]
}
/// Negative 2D vector.
pub fn p2_neg(a: Point2) -> Point2 {
    let [a0, a1] = a;
    [neg(a0), neg(a1)]
}
/// Addition of 2D vectors.
pub fn p2_add(a: Point2, b: Point2) -> Point2 {
    let [a0, a1] = a;
    let [b0, b1] = b;
    [add(a0, b0), add(a1, b1)]
}
/// Subtraction of 2D vectors.
pub fn p2_sub(a: Point2, b: Point2) -> Point2 {
    let [a0, a1] = a;
    let [b0, b1] = b;
    [sub(a0, b0), sub(a1, b1)]
}
/// Component-wise multiplication of 2D vectors.
pub fn p2_mul(a: Point2, b: Point2) -> Point2 {
    let [a0, a1] = a;
    let [b0, b1] = b;
    [mul(a0, b0), mul(a1, b1)]
}
/// Component-wise division of 2D vector.
pub fn p2_div(a: Point2, b: Point2) -> Point2 {
    let [a0, a1] = a;
    let [b0, b1] = b;
    [div(a0, b0), div(a1, b1)]
}
/// Maximum of 2D vector components.
pub fn p2_max(a: Point2, b: Point2) -> Point2 {
    let [a0, a1] = a;
    let [b0, b1] = b;
    [max(a0, b0), max(a1, b1)]
}
/// Scale 2D vector.
pub fn p2_scale(a: Point2, b: Expr) -> Point2 {
    p2_mul(a, [b.clone(), b])
}
/// Circle in 2D.
pub fn p2_circle(ang_offset: Expr) -> Point2 {
    [cos(ang_offset.clone()), sin(ang_offset)]
}
/// Spiral in 2D.
pub fn p2_spiral(ang_offset: Expr) -> Point2 {
    p2_scale(p2_circle(ang_offset.clone()), rad_to_unit(ang_offset))
}
/// Dot product of 2D vectors.
pub fn p2_dot(a: Point2, b: Point2) -> Expr {
    let [a0, a1] = a;
    let [b0, b1] = b;
    add(mul(a0, b0), mul(a1, b1))
}
/// Length of 2D vector.
pub fn p2_len(a: Point2) -> Expr {
    sqrt(p2_dot(a.clone(), a))
}
/// Linear interpolation in 2D.
pub fn p2_lerp(a: Point2, b: Point2, t: Expr) -> Point2 {
    let [a0, a1] = a;
    let [b0, b1] = b;
    [lerp(a0, b0, t.clone()), lerp(a1, b1, t)]
}
/// Quadratic Bezier spline in 2D.
pub fn p2_qbez(a: Point2, b: Point2, c: Point2, t: Expr) -> Point2 {
    let l1 = p2_lerp(a, b.clone(), t.clone());
    let l2 = p2_lerp(b, c, t.clone());
    p2_lerp(l1, l2, t)
}
/// Cubic Bezier spline in 2D.
pub fn p2_cbez(a: Point2, b: Point2, c: Point2, d: Point2, t: Expr) -> Point2 {
    let l1 = p2_qbez(a, b.clone(), c.clone(), t.clone());
    let l2 = p2_qbez(b, c, d, t.clone());
    p2_lerp(l1, l2, t)
}
/// Substitutes with offset.
pub fn p2_subst(p: Point2, off: Point2) -> Point2 {
    let [a0, a1] = p;
    [a0.subst2(&off), a1.subst2(&off)]
}

/// Gets triangles of quad.
pub fn quad_to_tri(quad: [Point2; 4], uv: [Point2; 4]) -> [([Point2; 3], [Point2; 3]); 2] {
    let [q0, q1, q2, q3] = quad;
    let [uv0, uv1, uv2, uv3] = uv;
    [
        ([q0, q1.clone(), q2.clone()], [uv0, uv1.clone(), uv2.clone()]),
        ([q1, q2, q3], [uv1, uv2, uv3])
    ]
}

/// Gets position within quad using UV coordinates.
pub fn quad_pos(quad: [Point2; 4], uv: Point2) -> Point2 {
    let [q0, q1, q2, q3] = quad;
    let [uv0, uv1] = uv;
    p2_lerp(
        p2_lerp(q0, q1, uv0.clone()),
        p2_lerp(q2, q3, uv0),
        uv1
    )
}

/// Gets expression for inside triangle.
pub fn inside_triangle(triangle: [Point2; 3], pos: Point2) -> Expr {
    let [b0, b1, b2] = to_barycentric(triangle, pos);
    set_and(set_and(
        range(nat(0), nat(1), b0),
        range(nat(0), nat(1), b1)
    ), range(nat(0), nat(1), b2))
}

/// Gets UV coordinates in triangle.
pub fn to_uv(triangle: [Point2; 3], uv: [Point2; 3], pos: Point2) -> Point2 {
    let [b0, b1, b2] = to_barycentric(triangle, pos);
    let [uv0, uv1, uv2] = uv;
    p2_add(p2_add(p2_scale(uv0, b0),
        p2_scale(uv1, b1)),
        p2_scale(uv2, b2))
}

/// Transforms from cartesian coordinates to barycentric.
pub fn to_barycentric(triangle: [Point2; 3], pos: Point2) -> Point3 {
    let x = pos[0].clone();
    let y = pos[1].clone();
    let x1 = triangle[0][0].clone();
    let y1 = triangle[0][1].clone();
    let x2 = triangle[1][0].clone();
    let y2 = triangle[1][1].clone();
    let x3 = triangle[2][0].clone();
    let y3 = triangle[2][1].clone();
    let lambda1 = div(add(mul(sub(y2.clone(), y3.clone()), sub(x.clone(), x3.clone())), mul(sub(x3.clone(), x2.clone()), sub(y.clone(), y3.clone()))),
        add(mul(sub(y2.clone(), y3.clone()), sub(x1.clone(), x3.clone())), mul(sub(x3.clone(), x2.clone()), sub(y1.clone(), y3.clone()))));
    let lambda2 = div(add(mul(sub(y3.clone(), y1.clone()), sub(x, x3.clone())), mul(sub(x1.clone(), x3.clone()), sub(y, y3.clone()))),
        add(mul(sub(y2, y3.clone()), sub(x1, x3.clone())), mul(sub(x3, x2), sub(y1, y3))));
    let lambda3 = sub(sub(nat(1), lambda1.clone()), lambda2.clone());
    [lambda1, lambda2, lambda3]
}

/// Transforms from barycentric coordinates to cartesian.
pub fn from_barycentric(triangle: [Point2; 3], lambda: Point3) -> Point2 {
    let x1 = triangle[0][0].clone();
    let y1 = triangle[0][1].clone();
    let x2 = triangle[1][0].clone();
    let y2 = triangle[1][1].clone();
    let x3 = triangle[2][0].clone();
    let y3 = triangle[2][1].clone();
    [
        add(add(mul(lambda[0].clone(), x1), mul(lambda[1].clone(), x2)), mul(lambda[2].clone(), x3)),
        add(add(mul(lambda[0].clone(), y1), mul(lambda[1].clone(), y2)), mul(lambda[2].clone(), y3),)
    ]
}

/// Gets 4D point with same components.
pub fn p4_same(x: Expr) -> Point4 {
    [x.clone(), x.clone(), x.clone(), x.clone()]
}
/// Gets x and y component of 4D point.
pub fn p4_xy(p: Point4) -> Point2 {
    [p[0].clone(), p[1].clone()]
}
/// Gets z and w component of 4D point.
pub fn p4_zw(p: Point4) -> Point2 {
    [p[2].clone(), p[3].clone()]
}

/// Render to image using single thread.
pub fn gen_to_image<T, F>(rt: &Runtime<T>, color: Color, img: &mut RgbImage, report: F)
    where T: 'static + Clone,
          F: Fn(&mut RgbImage, f64)
{
    let (w, h) = img.dimensions();
    let ctx = Context::new();
    let ref mut cache = Cache::new();
    for y in 0..h {
        cache.clear();
        report(img, y as f64 / h as f64);
        for x in 0..w {
            let pixel = img.get_pixel_mut(x, y);
            cache.clear_dep_x();
            let p = [x as f64, y as f64];
            let r = color[0].eval2(rt, p, &ctx, cache) as u8;
            let g = color[1].eval2(rt, p, &ctx, cache) as u8;
            let b = color[2].eval2(rt, p, &ctx, cache) as u8;
            *pixel = Rgb([r, g, b]);
        }
    }
}

/// Render using single thread.
pub fn gen<T>(rt: &Runtime<T>, color: Color, file: &str, size: [u32; 2])
    where T: 'static + Clone
{
    let mut img = RgbImage::new(size[0], size[1]);
    gen_to_image(rt, color, &mut img, |_img, progress| {
        eprintln!("{:.2} %", 100.0 * progress);
    });
    img.save(file).unwrap();
}

/// Render to image using Rayon and interpreter.
pub fn par_gen_to_image<T, F>(rt: &Runtime<T>, color: Color, img: &mut RgbImage, report: F)
    where T: 'static + Send + Sync + Clone,
          F: 'static + Fn(&mut RgbImage, f64) + Send,
{
    use rayon::iter::ParallelIterator;
    use rayon::iter::IntoParallelIterator;
    use std::sync::mpsc::channel;
    use std::sync::Mutex;
    use std::ops::DerefMut;

    let (w, h) = img.dimensions();
    let ctx = Context::new();
    let (sender, receiver) = channel::<(u32, Vec<Rgb::<u8>>)>();
    // Get the address of the image in a mutex,
    // knowing that the thread will be joined before returning.
    let img_mutex = Mutex::new(img as *mut RgbImage as usize);
    let join = std::thread::spawn(move || {
        let mut img_guard = img_mutex.lock().unwrap();
        let img = unsafe {&mut *(*img_guard.deref_mut() as *mut RgbImage)};
        let mut row_count = h;
        'outer: loop {
            std::thread::sleep(std::time::Duration::from_millis(500));
            let mut got_any = false;
            while let Ok((y, row)) = receiver.try_recv() {
                got_any = true;
                for (x, pixel) in row.into_iter().enumerate() {
                    img.put_pixel(x as u32, y, pixel);
                }
                row_count -= 1;
                if row_count == 0 {break 'outer};
            }
            if got_any {
                report(img, (h - row_count) as f64 / h as f64);
            };
        }
        drop(img_guard);
    });

    (0..h).into_par_iter().for_each(|y| {
        let ref mut cache = Cache::new();
        let mut res = vec![Rgb([0; 3]); w as usize];
        for (x, pixel) in res.iter_mut().enumerate() {
            cache.clear_dep_x();
            let p = [x as f64, y as f64];
            let r = color[0].eval2(rt, p, &ctx, cache) as u8;
            let g = color[1].eval2(rt, p, &ctx, cache) as u8;
            let b = color[2].eval2(rt, p, &ctx, cache) as u8;
            *pixel = Rgb([r, g, b]);
        }
        sender.send((y, res)).unwrap();
    });
    join.join().unwrap();
}

/// Render using Rayon and interpreter.
pub fn par_gen<T>(rt: &Runtime<T>, color: Color, file: &str, size: [u32; 2])
    where T: 'static + Send + Sync + Clone,
{
    let file2 = file.to_string();
    let mut img = RgbImage::new(size[0], size[1]);
    par_gen_to_image(rt, color, &mut img, move |img, progress| {
        use std::io::Write;
        eprintln!("{:.2} %", 100.0 * progress);
        let _ = std::io::stderr().flush();
        img.save(&file2).unwrap();
    });
    img.save(&file).unwrap();
}

/// Render using WASM parallel generation.
pub fn wasm_par_gen_to_image<T, F>(
    cpus: u8,
    rt: &Runtime<T>,
    color: Color,
    img: &mut RgbImage,
    report: F
)
    where T: 'static + Clone + Send + Sync,
          F: 'static + Fn(&mut RgbImage, f64) + Send,
{
    use std::sync::{Arc, Mutex};
    use std::sync::mpsc::channel;
    use std::ops::DerefMut;

    let (w, h) = img.dimensions();
    let (sender, receiver) = channel::<(u32, Vec<Rgb::<u8>>)>();
    // Get the address of the image in a mutex,
    // knowing that the thread will be joined before returning.
    let img_mutex = Mutex::new(img as *mut RgbImage as usize);
    let join = std::thread::spawn(move || {
        let mut img_guard = img_mutex.lock().unwrap();
        let img = unsafe {&mut *(*img_guard.deref_mut() as *mut RgbImage)};
        let mut row_count = h;
        'outer: loop {
            std::thread::sleep(std::time::Duration::from_millis(500));
            let mut got_any = false;
            while let Ok((y, row)) = receiver.try_recv() {
                got_any = true;
                for (x, pixel) in row.into_iter().enumerate() {
                    img.put_pixel(x as u32, y, pixel);
                }
                row_count -= 1;
                if row_count == 0 {break 'outer};
            }
            if got_any {
                report(img, (h - row_count) as f64 / h as f64);
            };
        }
        drop(img_guard);
    });

    let y_iter: Arc<Mutex<u32>> = Arc::new(0.into());
    let mut threads = vec![];
    for _ in 0..cpus {
        use wasm::Wasm;

        let sender = sender.clone();
        let y_iter = y_iter.clone();
        let color = color.clone();
        let rt = rt.clone();
        threads.push(std::thread::spawn(move || {
            let mut rt = rt;
            let rt_guard = current::CurrentGuard::new(&mut rt);

            let mut cr = Wasm::from_expr::<T>(&color[0]).unwrap();
            let mut cg = Wasm::from_expr::<T>(&color[1]).unwrap();
            let mut cb = Wasm::from_expr::<T>(&color[2]).unwrap();

            loop {
                let mut y_write = y_iter.lock().unwrap();
                let y = *y_write;
                if *y_write >= h {break}
                *y_write += 1;
                drop(y_write);

                let ref mut cache = Cache::new();
                let mut res = vec![Rgb([0; 3]); w as usize];
                for (x, pixel) in res.iter_mut().enumerate() {
                    cache.clear_dep_x();
                    let p = [x as f64, y as f64];
                    let r = cr.main.call(&mut cr.store, p[0], p[1]).unwrap() as u8;
                    let g = cg.main.call(&mut cg.store, p[0], p[1]).unwrap() as u8;
                    let b = cb.main.call(&mut cb.store, p[0], p[1]).unwrap() as u8;
                    *pixel = Rgb([r, g, b]);
                }
                sender.send((y, res)).unwrap();
            }

            drop(rt_guard);
        }))
    }
    drop(sender);

    for th in threads.into_iter() {th.join().unwrap()};
    join.join().unwrap();
}

/// Render using WASM parallel generation.
pub fn wasm_par_gen<T>(cpus: u8, rt: &Runtime<T>, color: Color, file: &str, size: [u32; 2])
    where T: 'static + Clone + Send + Sync,
{
    let file2 = file.to_string();
    let mut img = RgbImage::new(size[0], size[1]);
    wasm_par_gen_to_image(cpus, rt, color, &mut img, move |img, progress| {
        use std::io::Write;
        eprintln!("{:.2} %", 100.0 * progress);
        let _ = std::io::stderr().flush();
        img.save(&file2).unwrap();
    });
    img.save(&file).unwrap();
}

/// Save to file.
pub fn save(file: &str, data: ([u32; 2], Color)) -> anyhow::Result<()> {
    use std::fs::File;
    use std::io::Write;

    let mut file = File::create(file)?;
    let encoded: Vec<u8> = bincode::serialize(&data)?;
    file.write_all(&encoded)?;
    Ok(())
}

/// Open file.
pub fn open(file: &str) -> anyhow::Result<([u32; 2], Color)> {
    use std::fs::File;
    use std::io::Read;

    let mut file = File::open(file)?;
    let mut decoded: Vec<u8> = vec![];
    file.read_to_end(&mut decoded)?;
    Ok(bincode::deserialize(&decoded)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let a = mul(x(), x());
        assert_eq!(a.eval(2.0), 4.0);

        let a = neg(nat(1));
        assert_eq!(a.eval(0.0), -1.0);

        let a = div(nat(1), nat(2));
        assert_eq!(a.eval(0.0), 0.5);

        let a = pi();
        assert_eq!(a.eval(0.0), 3.141592653589793);

        let a = lerp(neg(nat(1)), nat(1), x());
        assert_eq!(a.eval(0.0), -1.0);
        assert_eq!(a.eval(1.0), 1.0);

        let a = cos(x());
        assert_eq!(a.eval(0.0), 1.0);

        let a = step(x());
        assert_eq!(a.eval(-1.0), 0.0);
        assert_eq!(a.eval(0.0), 1.0);
        assert_eq!(a.eval(1.0), 1.0);

        let a = step_at(nat(2), x());
        assert_eq!(a.eval(1.0), 0.0);
        assert_eq!(a.eval(2.0), 1.0);

        let a = range(nat(1), nat(2), x());
        assert_eq!(a.eval(0.5), 0.0);
        assert_eq!(a.eval(1.5), 1.0);
        assert_eq!(a.eval(2.5), 0.0);

        let a = p2_len([x(), x()]);
        assert_eq!(a.eval(0.0), 0.0);
        assert_eq!(a.eval(1.0), 2.0_f64.sqrt());

        let a = clamp(nat(1), nat(5), x());
        assert_eq!(a.eval(0.0), 1.0);
        assert_eq!(a.eval(1.0), 1.0);
        assert_eq!(a.eval(5.0), 5.0);
        assert_eq!(a.eval(6.0), 5.0);
    }

    #[test]
    fn test_simplify() {
        // Subtraction.
        let a = sub(div(nat(2), nat(5)), recip(nat(3)));
        assert_eq!(a.simplify(), recip(nat(15)));

        let a = sub(recip(nat(3)), div(nat(2), nat(5)));
        assert_eq!(a.simplify(), neg(recip(nat(15))));

        let a = sub(div(nat(2), nat(5)), div(nat(1), nat(5)));
        assert_eq!(a.simplify(), recip(nat(5)));

        let a = sub(div(nat(3), nat(5)), div(nat(1), nat(5)));
        assert_eq!(a.simplify(), div(nat(2), nat(5)));

        let a = sub(div(nat(3), nat(5)), div(nat(1), nat(2)));
        assert_eq!(a.simplify(), recip(nat(10)));

        let a = sub(div(nat(4), nat(5)), div(nat(1), nat(2)));
        assert_eq!(a.simplify(), div(nat(3), nat(10)));

        // Addition.
        let a = add(div(nat(2), nat(5)), recip(nat(3)));
        assert_eq!(a.simplify(), div(nat(11), nat(15)));

        let a = add(recip(nat(3)), div(nat(2), nat(5)));
        assert_eq!(a.simplify(), div(nat(11), nat(15)));

        let a = add(div(nat(2), nat(5)), div(nat(1), nat(5)));
        assert_eq!(a.simplify(), div(nat(3), nat(5)));

        let a = add(div(nat(3), nat(5)), div(nat(1), nat(5)));
        assert_eq!(a.simplify(), div(nat(4), nat(5)));

        let a = add(div(nat(3), nat(5)), div(nat(1), nat(2)));
        assert_eq!(a.simplify(), div(nat(11), nat(10)));

        let a = add(div(nat(4), nat(5)), div(nat(1), nat(2)));
        assert_eq!(a.simplify(), div(nat(13), nat(10)));

        // Multiplication.
        let a = mul(div(nat(2), nat(5)), recip(nat(3)));
        assert_eq!(a.simplify(), div(nat(2), nat(15)));

        let a = mul(recip(nat(3)), div(nat(2), nat(5)));
        assert_eq!(a.simplify(), div(nat(2), nat(15)));

        let a = mul(div(nat(2), nat(5)), div(nat(1), nat(5)));
        assert_eq!(a.simplify(), div(nat(2), nat(25)));

        let a = mul(div(nat(3), nat(5)), div(nat(1), nat(5)));
        assert_eq!(a.simplify(), div(nat(3), nat(25)));

        let a = mul(div(nat(3), nat(5)), div(nat(1), nat(2)));
        assert_eq!(a.simplify(), div(nat(3), nat(10)));

        let a = mul(div(nat(4), nat(5)), div(nat(1), nat(2)));
        assert_eq!(a.simplify(), div(nat(2), nat(5)));

        // Division.
        let a = div(div(nat(2), nat(5)), recip(nat(3)));
        assert_eq!(a.simplify(), div(nat(6), nat(5)));

        let a = div(recip(nat(3)), div(nat(2), nat(5)));
        assert_eq!(a.simplify(), div(nat(5), nat(6)));

        let a = div(div(nat(2), nat(5)), div(nat(1), nat(5)));
        assert_eq!(a.simplify(), nat(2));

        let a = div(div(nat(3), nat(5)), div(nat(1), nat(5)));
        assert_eq!(a.simplify(), nat(3));

        let a = div(div(nat(3), nat(5)), div(nat(1), nat(2)));
        assert_eq!(a.simplify(), div(nat(6), nat(5)));

        let a = div(div(nat(4), nat(5)), div(nat(1), nat(2)));
        assert_eq!(a.simplify(), div(nat(8), nat(5)));

        let a = div(div(nat(2), nat(3)), nat(5));
        assert_eq!(a.simplify(), div(nat(2), nat(15)));

        // Recip.
        let a = recip(div(nat(1), nat(3)));
        assert_eq!(a.simplify(), nat(3));
    }
}
