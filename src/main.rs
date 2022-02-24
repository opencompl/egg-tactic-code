use egg::{rewrite as rw, *};


fn main() {

  let rules: &[Rewrite<SymbolLang, ()>] = &[
      rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
      rw!("assoc-mul'"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
      rw!("one-mul";  "(* 1 ?a)" => "?a"),
      rw!("one-mul'";  "?a" => "(* 1 ?a)"),
      rw!("inv-left";  "(* (^-1 ?a) ?a)" => "1"),
      rw!("inv-left'";  "1" => "(* (^-1 a) a)"),
      rw!("mul-one";  "(* ?a 1)" => "?a"),
      rw!("inv-right";  "(* ?a (^-1 ?a))" => "1"),
      rw!("inv-right'";  "1" => "(* a (^-1 a))"),

  ];

    // We can make our own Language later to work with other types.
    //(a * b) * (1⁻¹⁻¹ * b⁻¹ * ((a⁻¹ * a⁻¹⁻¹⁻¹) * a))
    let start = "(* (* a b)(* (^-1 (^-1 1))  (* (^-1 b) (* (* (^-1 a) (^-1 (^-1 (^-1 a)))) a))))".parse().unwrap();

    //let start = "(^-1 (^-1 a))".parse().unwrap();
    // That's it! We can run equality saturation now.
    let mut runner = Runner::default().with_expr(&start)
        //.with_node_limit(15)
        .run(rules);

    // Dump
    //runner.egraph.dot().to_pdf("target/group.pdf").unwrap();
    //runner.egraph.dot().to_pdf("target/group2.pdf").unwrap();
    //println!("Debug: {:?} \n \n", runner.egraph.dump());

    // Extractors can take a user-defined cost function,
    // we'll use the egg-provided AstSize for now
    let extractor = Extractor::new(&runner.egraph, AstSize);


    // We want to extract the best expression represented in the
    // same e-class as our initial expression, not from the whole e-graph.
    // Luckily the runner stores the eclass Id where we put the initial expression.
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    // we found the best thing, which is just "a" in this case
    println!("Best expr : {:?} -- cost: {}",best_expr, best_cost);
}
