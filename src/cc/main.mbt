
fn eval(term: String) -> Term raise {
  let ctx = Context::new()
  let term_ast = ctx.parse(term)
  let _ = ctx.infer(term_ast)
  ctx.normalise(term_ast)
}

fn main {
  println(try? eval("let f = let A = Type in fun f: A -> A -> Bool => fun x: A => f x x in let A = Bool -> Bool -> Bool in f (fun x: Type => fun y: Type => true) (A -> A)"))
}
