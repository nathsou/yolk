
fn main {
  let ctx = Context::new()
  let ty = try? ctx.infer(Lam("A", Star, Lam("x", BoundVar(0), BoundVar(0))))
  println(ty)
}
