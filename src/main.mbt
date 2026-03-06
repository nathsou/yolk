fn main {
  let expr = try! parse("fun a: A => fun b: B => fun c: C => c")
  let ctx = TypeContext::new()
  let ty = try? ctx.infer(expr)
  println("\{expr}: \{ty}")
}
