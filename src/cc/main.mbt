
fn eval(term: String) -> Term raise {
  let ctx = Context::new()
  let term_ast = parse(term)
  let _ = ctx.infer(parse(term))
  normalise(term_ast)
}

fn main {
  println(try? eval("let f = let A = * in fun f: A -> A -> Bool => fun x: A => f x x in let A = Bool -> Bool -> Bool in f (fun x: * => fun y: * => true) (A -> A)"))
}
