
// Surface-level syntax
pub enum Expr {
  Star
  Box
  Bool
  Const(Const)
  Var(String)
  App(Expr, Expr)
  Fun(String, Expr, Expr)
  Pi(String?, Expr, Expr)
  Ann(Expr, Expr)
  Let(name~: String, ty~: Expr, val~: Expr, rhs~: Expr)
} derive (Eq)

pub enum Const {
  Bool(Bool)
} derive(Eq)

pub impl Show for Const with output(self: Const, logger: &Logger) {
  let str = match self {
    Bool(true) => "true"
    Bool(false) => "false"
  }

  logger.write_string(str)
}

fn Expr::parens(self: Expr, wrap~: Bool, bindings~: Array[String], depth~: Int, logger: &Logger) -> Unit {
  if wrap { logger.write_char('(') }
  self.fmt(bindings~, depth~, logger)
  if wrap { logger.write_char(')') }
}

fn Expr::fmt(self: Expr, bindings~: Array[String], depth~: Int, logger: &Logger) -> Unit {
  match self {
    Bool => logger.write_string("Bool")
    Star => logger.write_char('*')
    Box => logger.write_char('□')
    Var(name) => logger.write_string(name)
    Const(c) => c.output(logger)
    App(lhs, rhs) => {
      let lhs_needs_parens = lhs is Fun(_)
      let rhs_needs_parens = rhs is (Fun(_) | App(_))
      lhs.parens(wrap=lhs_needs_parens, bindings~, depth~, logger)
      logger.write_char(' ')
      rhs.parens(wrap=rhs_needs_parens, bindings~, depth~, logger)
    }
    Fun(x, ty, body) => {
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
    Ann(e, ty) => {
      logger.write_char('(')
      let lhs_needs_parens = e is (App(_) | Fun(_) | Pi(_))
      e.parens(wrap=lhs_needs_parens, bindings~, depth~, logger)
      logger.write_string(": ")
      ty.fmt(bindings~, depth~, logger)
      logger.write_char(')')
    }
    Let(name~, ty~, val~, rhs~) => {
      logger.write_string("let ")
      logger.write_string(name)
      logger.write_string(": ")
      ty.fmt(bindings~, depth~, logger)
      logger.write_char(' ')
      logger.write_string(" = ")
      val.fmt(bindings~, depth~, logger)
      logger.write_string(" in ")
      rhs.fmt(bindings~, depth~, logger)
    }
  }
}

pub impl Show for Expr with output(self: Expr, logger: &Logger) {
  self.fmt(bindings=[], depth=0, logger)
}

test "show expr" {
  fn assert_show_expr(expr: String) raise {
    assert_eq("\{parse(expr)}", expr)
  }

  {
    let e: Expr = Fun("a", Var("A"), Fun("b", Var("B"), Fun("c", Var("C"), Var("c"))))
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
  // application is left-associative
  assert_eq(parse("(x y) z"), parse("x y z"))
}
