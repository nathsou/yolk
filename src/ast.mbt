pub enum Type {
  Arrow(Type, Type)
  Atom(String) // only introduced as lambda arguments to prove implications
  Bool
} derive(Show, Eq)

type DeBruijnIndex = UInt

pub enum Expr {
  Var(DeBruijnIndex)
  Abs(ty~ : Type?, body~ : Expr)
  App(Expr, Expr)
  Ann(Expr, Type)
  Const(Const)
} derive(Show, Eq)

pub enum Const {
  Bool(Bool)
} derive(Show, Eq)
