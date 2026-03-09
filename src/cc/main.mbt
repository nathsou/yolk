
fn main {
  // let ctx = Context::new()
  println(try? ((parse("fun A: * => fun B: * => A -> B"))))
}
