
pub enum Term {
  Star
  Box
  Bool
  Const(Const)
  // locally nameless representation: bound variables are represented by their de Bruijn index, free variables have a name
  BoundVar(DeBruijnIndex)
  FreeVar(String, FreeVarId)
  App(Term, Term)
  Lam(String, Term, Term)
  Pi(String?, Term, Term)
  Let(String, Term, Term)
  Ann(Term, Term)
}

pub enum Const {
  Bool(Bool)
} derive(Eq)

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
    (FreeVar(_, x), FreeVar(_, y)) => x == y
    (App(f, x), App(g, y)) => x == y && f == g
    (Lam(_, t1, body1), Lam(_, t2, body2)) => t1 == t2 && body1 == body2
    (Pi(_, a1, b1), Pi(_, a2, b2)) => a1 == a2 && b1 == b2
    (Let(_, t1, body1), Let(_, t2, body2)) => t1 == t2 && body1 == body2
    (Ann(lhs1, ty1), (Ann(lhs2, ty2))) => ty1 == ty2 && lhs1 == lhs2
    _ => false
  }
}

pub impl Show for Const with output(self: Const, logger: &Logger) {
  let str = match self {
    Bool(true) => "true"
    Bool(false) => "false"
  }

  logger.write_string(str)
}

fn Term::parens(self: Term, wrap~: Bool, bindings~: Array[String], depth~: Int, logger: &Logger) -> Unit {
  if wrap { logger.write_char('(') }
  self.fmt(bindings~, depth~, logger)
  if wrap { logger.write_char(')') }
}

fn Term::fmt(self: Term, bindings~: Array[String], depth~: Int, logger: &Logger) -> Unit {
  match self {
    Bool => logger.write_string("Bool")
    Star => logger.write_char('*')
    Box => logger.write_char('□')
    BoundVar(idx) => {
      let eff_idx = bindings.length() - 1 - idx.reinterpret_as_int()
      if eff_idx < 0 {
        logger.write_string("<invalid bound variable index: \{idx}>")
      } else {
        logger.write_string(bindings[eff_idx])
      }
    }
    FreeVar(name, _) => logger.write_string(name)
    Const(c) => c.output(logger)
    App(lhs, rhs) => {
      let lhs_needs_parens = lhs is Lam(_)
      let rhs_needs_parens = rhs is (Lam(_) | App(_))
      lhs.parens(wrap=lhs_needs_parens, bindings~, depth~, logger)
      logger.write_char(' ')
      rhs.parens(wrap=rhs_needs_parens, bindings~, depth~, logger)
    }
    Lam(x, ty, body) => {
      bindings.push(x)
      defer { let _ = bindings.unsafe_pop() }
      logger.write_string("fun ")
      logger.write_string(x)
      logger.write_string(": ")
      ty.fmt(bindings~, depth~, logger)
      logger.write_string(" => ")
      body.fmt(bindings~, depth=depth + 1, logger)
    }
    Pi(Some(x), a, b) => {
      logger.write_string("forall ")
      logger.write_string(x)
      logger.write_string(": ")
      a.fmt(bindings~, depth~, logger)
      logger.write_string(", ")
      bindings.push(x)
      defer { let _ = bindings.unsafe_pop() }
      b.fmt(bindings~, depth = depth + 1, logger)
    }
    Pi(None, a, b) => {
      a.parens(wrap=a is Pi(_), bindings~, depth~, logger)
      logger.write_string(" -> ")
      b.fmt(bindings~, depth = depth + 1, logger)
    }
    Let(x, val, body) => {
      logger.write_string("let ")
      logger.write_string(x)
      logger.write_string(" = ")
      val.fmt(bindings~, depth~, logger)
      logger.write_string(" in ")
      bindings.push(x)
      defer { let _ = bindings.unsafe_pop() }
      body.fmt(bindings~, depth = depth + 1, logger)
    }
    Ann(e, ty) => {
      logger.write_char('(')
      let lhs_needs_parens = e is (App(_) | Lam(_) | Pi(_))
      e.parens(wrap=lhs_needs_parens, bindings~, depth~, logger)
      logger.write_string(": ")
      ty.fmt(bindings~, depth~, logger)
      logger.write_char(')')
    }
  }
}

pub impl Show for Term with output(self: Term, logger: &Logger) {
  self.fmt(bindings=[], depth=0, logger)
}

test "show term" {
  fn parse(input: String) -> Term raise {
    Parser::new(Lexer::new(input).tokenise()).parse()
  }

  fn assert_show_expr(expr: String) raise {
    assert_eq("\{parse(expr)}", expr)
  }

  {
    let e = Lam("a", FreeVar("A", 0), Lam("b", FreeVar("B", 1), Lam("c", FreeVar("C", 2), BoundVar(0))))
    assert_eq("\{e}", "fun a: A => fun b: B => fun c: C => c")
  }

  assert_show_expr("Bool")
  assert_show_expr("*")
  assert_show_expr("□")
  assert_show_expr("Bool -> Bool")
  assert_show_expr("* -> Bool")
  assert_show_expr("(x: Bool)")
  assert_show_expr("(*: □)")
  assert_show_expr("((Bool: *): □)")
  assert_show_expr("A -> B -> A")
  // `->` is right-associative
  assert_eq(parse("A -> (B -> C)"), parse("A -> B -> C"))
  assert_show_expr("(A -> B) -> A")
  assert_show_expr("forall A: *, A -> A")
  assert_show_expr("forall A: *, Bool")
  assert_show_expr("forall A: *, forall b: Bool, P A b")
  assert_show_expr("true")
  assert_show_expr("false")
  assert_show_expr("fun x: Bool => x")
  assert_show_expr("fun x: Bool => (x: Bool)")
  assert_show_expr("fun x0: A => fun y0: B => fun z0: C => fun x1: D => fun y1: E => fun z2: F => y0")
  assert_show_expr("fun a: A => fun b: B => fun c: C => c")
  assert_show_expr("((fun x: A => x): A -> A)")
  assert_show_expr("(((fun x: A => x): A -> A): *)")
  assert_show_expr("f (g x)")
  assert_show_expr("x y z")
  assert_show_expr("let id = fun x: A => x in id")

  // application is left-associative
  assert_eq(parse("(x y) z"), parse("x y z"))
}
