
// Core AST used by the kernel
pub enum Term {
  Star
  Box
  Bool
  Const(Const)
  BoundVar(DeBruijnIndex)
  FreeVar(String, FreeVarId)
  LocalVar(String, FreeVarId)
  App(Term, Term)
  Lam(String, Term, Term)
  Pi(String, Term, Term)
  Ann(Term, Term)
} derive(Show)

pub type DeBruijnIndex = UInt
pub type FreeVarId = UInt

pub fn Term::is_sort(self: Term) -> Bool {
  self is (Star | Box)
}

pub impl Eq for Term with equal(self: Term, other: Term) -> Bool {
  match (self, other) {
    (Box, Box) => true
    (Star, Star) => true
    (Bool, Bool) => true
    (Const(c1), Const(c2)) => c1 == c2
    (BoundVar(i), BoundVar(j)) => i == j
    (FreeVar(x, i), FreeVar(y, j)) => i == j && x == y
    (LocalVar(x, i), LocalVar(y, j)) => i == j && x == y
    (App(f, x), App(g, y)) => x == y && f == g
    (Lam(_, t1, body1), Lam(_, t2, body2)) => t1 == t2 && body1 == body2
    (Pi(_, a1, b1), Pi(_, a2, b2)) => a1 == a2 && b1 == b2
    (Ann(lhs1, ty1), (Ann(lhs2, ty2))) => ty1 == ty2 && lhs1 == lhs2
    _ => false
  }
}
