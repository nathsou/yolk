
fn main {
  let ctx = Context::new()
  println(try? (ctx.infer(parse_term("let id: forall A: *, A -> A = fun A: * => fun x: A => x in id Bool true"))))
}
