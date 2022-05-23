use egg::{rewrite as rw, *};

// #[derive(Debug)]
// pub struct MatchAST<L> {
//     target: L

// }
// impl<L: Language> CostFunction<L> for MatchAST<L> {
//     type Cost = usize;
//     fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
//     where
//         C: FnMut(Id) -> Self::Cost,
//     {
//         if (enode.eq(&self.target)) { return 1; } else { return 100; }
//     }
// }

struct SillyCostFn;
impl CostFunction<SymbolLang> for SillyCostFn {
    type Cost = f64;
    fn cost<C>(&mut self, enode: &SymbolLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        let op_cost = match enode.op.as_str() {
            "ANSWER" => 1.0,
            _ => 100.0
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

#[derive(Debug)]
pub struct AstSizeFive;
impl<L: Language> CostFunction<L> for AstSizeFive {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> <egg::AstSize as CostFunction<L>>::Cost,
    {
        let tot_size = enode.fold(1, |sum, id| sum + costs(id));
        println!("tot_size: {}",tot_size);
        if tot_size == 5 {1} else {100}
    }
}

fn mainGroupCheck() {

  let rules: &[Rewrite<SymbolLang, ()>] = &[
      rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
      rw!("assoc-mul'"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
      rw!("one-mul";  "(* 1 ?a)" => "?a"),
      rw!("one-mul'";  "?a" => "(* 1 ?a)"),
      rw!("inv-left";  "(* (^-1 ?a) ?a)" => "1"),
      rw!("inv-left'";  "1" => "(* (^-1 a) a)"),
      rw!("inv-left''";  "1" => "(* (^-1 b) b)"),
      rw!("mul-one";  "(* ?a 1)" => "?a"),
      rw!("mul-one'";  "?a" => "(* ?a 1)" ),
      rw!("inv-right";  "(* ?a (^-1 ?a))" => "1"),
      rw!("inv-right'";  "1" => "(* a (^-1 a))"),
      rw!("inv-right''";  "1" => "(* b (^-1 b))"),
      //rw!("anwser''";  "(* (^-1 b)(^-1 a))" => "ANSWER"),

  ];

    // We can make our own Language later to work with other types.
    //(a * b) * (1⁻¹⁻¹ * b⁻¹ * ((a⁻¹ * a⁻¹⁻¹⁻¹) * a))
    //let start = "(* (* a b)(* (^-1 (^-1 1))  (* (^-1 b) (* (* (^-1 a) (^-1 (^-1 (^-1 a)))) a))))".parse().unwrap();

    // a * 1  -- won't work without
    //let start = "(* a 1)".parse().unwrap();

    // a⁻¹⁻¹ = a
    let start = "(^-1 (^-1 a))".parse().unwrap();

    //  a⁻¹ * (a * b) = b
    //let start = "(* (^-1  a) (* a b))".parse().unwrap();

    //  a * (a⁻¹ * b) = b
    //let start = "(* a (* (^-1  a) b))".parse().unwrap();

    //(a * b)⁻¹ = b⁻¹ * a⁻¹
    // let start = "(^-1 (* a b))".parse().unwrap();
    //let start = "(* 1 (* 1 1))".parse().unwrap();
    //let start = "(* (^-1 b) (^-1 a))".parse().unwrap();

    //(1 : G)⁻¹ = 1
    //let start = "(^-1 1)".parse().unwrap();

    // That's it! We can run equality saturation now.
    let mut runner = Runner::default()
        //.with_node_limit(105)
        // .with_explanations_enabled()
        .with_expr(&start)
        .run(rules);

    // Dump
    // runner.egraph.dot().to_pdf("target/group.pdf").unwrap();
    //runner.egraph.dot().to_pdf("target/group2.pdf").unwrap();
    //println!("Debug: {:?} \n \n", runner.egraph.dump());

    // Extractors can take a user-defined cost function,
    // we'll use the egg-provided AstSize for now
    let mut extractor = Extractor::new(&runner.egraph, AstSize);


    // We want to extract the best expression represented in the
    // same e-class as our initial expression, not from the whole e-graph.
    // Luckily the runner stores the eclass Id where we put the initial expression.
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);


    println!("Best expr : {:?} -- cost: {}",best_expr, best_cost);
    // println!("{}", runner.explain_equivalence(&start, &best_expr).get_flat_string());
    // we found the best thing, which is just "a" in this case
}

fn main() {
    mainGroupCheck();
}
