//! Wasm generation.

use wasmer::{Store, Module, Instance, imports, Imports, TypedFunction};
use crate::semantics::{BinOp, UnOp};
use crate::{Context, Expr};

/// Get imported functions.
pub fn imports(store: &mut Store) -> wasmer::Imports {
    use wasmer::Function;
    fn abs(v: f64) -> f64 {v.abs()}
    fn sin(v: f64) -> f64 {v.sin()}
    fn exp(v: f64) -> f64 {v.exp()}
    fn ln(v: f64) -> f64 {v.ln()}
    fn recip(v: f64) -> f64 {v.recip()}
    fn step(v: f64) -> f64 {if v >= 0.0 {1.0} else {0.0}}
    fn id(v: f64) -> f64 {v}
    imports! {
        "env" => {
            "abs" => Function::new_typed(store, abs),
            "sin" => Function::new_typed(store, sin),
            "exp" => Function::new_typed(store, exp),
            "ln" => Function::new_typed(store, ln),
            "recip" => Function::new_typed(store, recip),
            "step" => Function::new_typed(store, step),
            "id" => Function::new_typed(store, id),
        },
    }
}

/// Generate unary operator.
pub fn gen_unop(unop: UnOp) -> String {
    use UnOp::*;
    match unop {
        Abs => format!("call $abs"),
        Neg => format!("f64.neg"),
        Sqrt => format!("f64.sqrt"),
        Recip => format!("call $recip"),
        Step => format!("call $step"),
        Sin => format!("call $sin"),
        Exp => format!("call $exp"),
        Ln => format!("call $ln"),
        Id => format!("call $id"),
    }
}

/// Generate binary operator.
pub fn gen_binop(binop: BinOp) -> String {
    use BinOp::*;
    match binop {
        Add => format!("f64.add"),
        Mul => format!("f64.mul"),
        Max => format!("f64.max"),
        Min => format!("f64.min"),
    }
}

/// Generates WAT code for imported functions.
pub fn functions() -> String {
    r#"
    (func $recip (import "env" "recip") (param f64) (result f64))
    (func $step (import "env" "step") (param f64) (result f64))
    (func $ln (import "env" "ln") (param f64) (result f64))
    (func $exp (import "env" "exp") (param f64) (result f64))
    (func $abs (import "env" "abs") (param f64) (result f64))
    (func $sin (import "env" "sin") (param f64) (result f64))
    "#.into()
}

/// Generate WAT code from variables in context.
pub fn gen_vars(ctx: &Context) -> String {
    let mut res: String = String::new();
    for var in &ctx.vars {
        res.push_str(&gen_expr(&var.1));
        res.push_str("\nset_local $");
        res.push_str(&var.0);
        res.push_str("\n");
    }
    res
}

/// Generates WAT code from expression.
pub fn gen_expr(e: &Expr) -> String {
    use Expr::*;
    match e {
        X => "\nget_local $x".into(),
        Y => "\nget_local $y".into(),
        Tau => "f64.const 6.283185307179586".into(),
        E => "f64.const 2.718281828459045".into(),
        Nat(n) => format!("f64.const {}", n),
        Var(name) => format!("local.get ${}", name),
        Neg(a) => format!("{}\n{}", gen_expr(a), gen_unop(UnOp::Neg)),
        Recip(a) => format!("{}\n{}", gen_expr(a), gen_unop(UnOp::Recip)),
        Exp(a) => format!("{}\n{}", gen_expr(a), gen_unop(UnOp::Exp)),
        Ln(a) => format!("{}\n{}", gen_expr(a), gen_unop(UnOp::Ln)),
        Sin(a) => format!("{}\n{}", gen_expr(a), gen_unop(UnOp::Sin)),
        Abs(a) => format!("{}\n{}", gen_expr(a), gen_unop(UnOp::Abs)),
        Sqrt(a) => format!("{}\n{}", gen_expr(a), gen_unop(UnOp::Sqrt)),
        Step(a) => format!("{}\n{}", gen_expr(a), gen_unop(UnOp::Step)),
        Add(ab) => format!("{}\n{}\n{}", gen_expr(&ab.0), gen_expr(&ab.1), gen_binop(BinOp::Add)),
        Mul(ab) => format!("{}\n{}\n{}", gen_expr(&ab.0), gen_expr(&ab.1), gen_binop(BinOp::Mul)),
        Max(ab) => format!("{}\n{}\n{}", gen_expr(&ab.0), gen_expr(&ab.1), gen_binop(BinOp::Max)),
        Min(ab) => format!("{}\n{}\n{}", gen_expr(&ab.0), gen_expr(&ab.1), gen_binop(BinOp::Min)),
        Let(ab) => {
            let mut s = String::new();
            for var in &ab.0.vars {
                s.push_str("(local $");
                s.push_str(&var.0);
                s.push_str(" f64) ");
            }
            format!("{}\n{}\n{}", s, gen_vars(&ab.0), gen_expr(&ab.1))
        }
        Decor(ab) => gen_expr(&ab.0),
    }
}

/// Generated WASM.
pub struct Wasm {
    /// WASM store.
    pub store: Store,
    /// WASM module.
    pub module: Module,
    /// Imported functions.
    pub imports: Imports,
    /// The WASM instance.
    pub instance: Instance,
    /// The render function.
    pub main: TypedFunction<(f64, f64), f64>,
}

impl Wasm {
    /// Generates JIT from expression.
    pub fn from_expr(e: &Expr) -> anyhow::Result<Wasm> {
        let module_wat = format!(r#"
        (module
        {}
        (type $t0 (func (param f64) (param f64) (result f64)))
        (func $main (export "main") (type $t0) (param $x f64) (param $y f64) (result f64)
            {}
        ))
        "#, functions(), gen_expr(e));

        let mut store = Store::default();
        let module = Module::new(&store, &module_wat)?;
        let imports = imports(&mut store);
        let instance = Instance::new(&mut store, &module, &imports)?;

        let f: TypedFunction<(f64, f64), f64> = instance.exports
            .get_typed_function(&store, "main").unwrap();

        Ok(Wasm {
            store,
            module,
            imports,
            instance,
            main: f,
        })
    }
}
