fn main {
  let expr = try! parse("(fun x: Bool => x)")
  let ctx = TypeContext::new()
  let ty = try? ctx.infer(expr)
  println(ty)
}
