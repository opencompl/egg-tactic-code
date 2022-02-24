use egg::{rewrite as rw, *};
use ordered_float::NotNan;

pub type EGraph = egg::EGraph<Group, ConstantFold>;
pub type Rewrite = egg::Rewrite<Group, ConstantFold>;

pub type Constant = NotNan<f64>;

define_language! {
    pub enum Group {
        "*" = Mul([Id; 2]),
        "^-1" = Inv([Id; 1]),
        "1" = Constant(Constant),
        Symbol(Symbol),
    }
}

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator
pub struct MathCostFn;
impl egg::CostFunction<Group> for MathCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Group, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            Math::Inv => 2,
            _ => 1,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

fn is_const_or_distinct_var(v: &str, w: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let v = v.parse().unwrap();
    let w = w.parse().unwrap();
    move |egraph, _, subst| {
        egraph.find(subst[v]) != egraph.find(subst[w])
            && (egraph[subst[v]].data.is_some()
                || egraph[subst[v]]
                    .nodes
                    .iter()
                    .any(|n| matches!(n, Math::Symbol(..))))
    }
}

fn is_const(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| egraph[subst[var]].data.is_some()
}

fn is_sym(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        egraph[subst[var]]
            .nodes
            .iter()
            .any(|n| matches!(n, Math::Symbol(..)))
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(n) = &egraph[subst[var]].data {
            *(n.0) != 0.0
        } else {
            true
        }
    }
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> { vec![
    rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
    rw!("one-mul";  "(* 1 ?a)" => "?a"),
    //rw!("mul-one";  "(* ?a 1)" => "?a"),
    rw!("inv-left";  "(* (^-1 ?a) ?a)" => "1"),
    //rw!("inv-right";  "(* ?a (^-1 ?a))" => "1"),
]}

egg::test_fn! {
    math_associate_adds, [
        rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    ],
    runner = Runner::default()
        .with_iter_limit(7)
        .with_scheduler(SimpleScheduler),
    "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))"
    =>
    "(+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))"
    @check |r: Runner<Math, ()>| assert_eq!(r.egraph.number_of_classes(), 127)
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    math_fail, rules(),
    "(+ x y)" => "(/ x y)"
}

egg::test_fn! {math_simplify_add, rules(), "(+ x (+ x (+ x x)))" => "(* 4 x)" }
egg::test_fn! {math_powers, rules(), "(* (pow 2 x) (pow 2 y))" => "(pow 2 (+ x y))"}

egg::test_fn! {
    math_simplify_const, rules(),
    "(+ 1 (- a (* (- 2 1) a)))" => "1"
}

egg::test_fn! {
    math_simplify_root, rules(),
    runner = Runner::default().with_node_limit(75_000),
    r#"
    (/ 1
       (- (/ (+ 1 (sqrt five))
             2)
          (/ (- 1 (sqrt five))
             2)))"#
    =>
    "(/ 1 (sqrt five))"
}

egg::test_fn! {
    math_simplify_factor, rules(),
    "(* (+ x 3) (+ x 1))"
    =>
    "(+ (+ (* x x) (* 4 x)) 3)"
}

egg::test_fn! {math_diff_same,      rules(), "(d x x)" => "1"}
egg::test_fn! {math_diff_different, rules(), "(d x y)" => "0"}
egg::test_fn! {math_diff_simple1,   rules(), "(d x (+ 1 (* 2 x)))" => "2"}
egg::test_fn! {math_diff_simple2,   rules(), "(d x (+ 1 (* y x)))" => "y"}
egg::test_fn! {math_diff_ln,        rules(), "(d x (ln x))" => "(/ 1 x)"}

egg::test_fn! {
    diff_power_simple, rules(),
    "(d x (pow x 3))" => "(* 3 (pow x 2))"
}

egg::test_fn! {
    diff_power_harder, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(10))
        .with_iter_limit(60)
        .with_node_limit(100_000)
        .with_explanations_enabled()
        // HACK this needs to "see" the end expression
        .with_expr(&"(* x (- (* 3 x) 14))".parse().unwrap()),
    "(d x (- (pow x 3) (* 7 (pow x 2))))"
    =>
    "(* x (- (* 3 x) 14))"
}

egg::test_fn! {
    integ_one, rules(), "(i 1 x)" => "x"
}

egg::test_fn! {
    integ_sin, rules(), "(i (cos x) x)" => "(sin x)"
}

egg::test_fn! {
    integ_x, rules(), "(i (pow x 1) x)" => "(/ (pow x 2) 2)"
}

egg::test_fn! {
    integ_part1, rules(), "(i (* x (cos x)) x)" => "(+ (* x (sin x)) (cos x))"
}

egg::test_fn! {
    integ_part2, rules(),
    "(i (* (cos x) x) x)" => "(+ (* x (sin x)) (cos x))"
}

egg::test_fn! {
    integ_part3, rules(), "(i (ln x) x)" => "(- (* x (ln x)) x)"
}

#[test]
fn assoc_mul_saturates() {
    let expr: RecExpr<Math> = "(* x 1)".parse().unwrap();

    let runner: Runner<Math, ConstantFold> = Runner::default()
        .with_iter_limit(3)
        .with_expr(&expr)
        .run(&rules());

    assert!(matches!(runner.stop_reason, Some(StopReason::Saturated)));
}

#[test]
fn math_ematching_bench() {
    let exprs = &[
        "(i (ln x) x)",
        "(i (+ x (cos x)) x)",
        "(i (* (cos x) x) x)",
        "(d x (+ 1 (* 2 x)))",
        "(d x (- (pow x 3) (* 7 (pow x 2))))",
        "(+ (* y (+ x y)) (- (+ x 2) (+ x x)))",
        "(/ 1 (- (/ (+ 1 (sqrt five)) 2) (/ (- 1 (sqrt five)) 2)))",
    ];

    egg::test::bench_egraph("math", rules(), exprs);
}


fn main() {
    println!("Hello, world!");
}
