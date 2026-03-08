fn main {
  try! proove("(A, B) -> (B, A)", "fun p => (p.1, p.0)")
}
