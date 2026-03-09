pub enum Type {
  Arrow(Type, Type)
  Atom(String) // only introduced as lambda arguments to prove implications
  Tuple(Array[Type])
  Bool
} derive(Eq)

type DeBruijnIndex = Int

pub enum Expr {
  BoundVar(DeBruijnIndex)
  FreeVar(String)
  Abs(String, Type?, Expr)
  App(Expr, Expr)
  Ann(Expr, Type)
  Tuple(Array[Expr])
  Proj(Expr, UInt)
  Const(Const)
}

pub enum Const {
  Bool(Bool)
} derive(Eq)

pub impl Eq for Expr with equal(self: Expr, other: Expr) -> Bool {
  match (self, other) {
    (BoundVar(i1), BoundVar(i2)) => i1 == i2
    (FreeVar(x1), FreeVar(x2)) => x1 == x2
    (Abs(_, ann1, body1), Abs(_, ann2, body2)) => ann1 == ann2 && body1 == body2
    (App(lhs1, rhs1), App(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
    (Ann(e1, t1), Ann(e2, t2)) => t1 == t2 && e1 == e2
    (Const(c1), Const(c2)) => c1 == c2
    (Tuple(xs), Tuple(ys)) => xs == ys
    (Proj(t1, idx1), Proj(t2, idx2)) => idx1 == idx2 && t1 == t2
    _ => false
  }
}

pub impl Show for Type with output(self: Type, logger: &Logger) {
  match self {
    Bool => logger.write_string("Bool")
    Atom(a) => logger.write_string(a)
    Arrow(t0, t1) => {
      logger.write_object(t0)
      logger.write_string(" -> ")
      logger.write_object(t1)
    }
    Tuple(tys) => {
      logger.write_iter(tys.iter(), prefix="(", suffix=")", sep=", ")
    }
  }
}

pub impl Show for Const with output(self: Const, logger: &Logger) {
  let str = match self {
    Bool(true) => "true"
    Bool(false) => "false"
  }

  logger.write_string(str)
}

fn Expr::fmt(self: Expr, bindings~: Array[String], depth~: Int, logger: &Logger) -> Unit {
  match self {
    BoundVar(idx) => {
      let eff_idx = bindings.length() - 1 - idx
      if eff_idx < 0 {
        abort("invalid bound var index")
      } else {
        logger.write_string(bindings[eff_idx])
      }
    }
    FreeVar(x) => logger.write_string(x)
    Const(c) => c.output(logger)
    App(lhs, rhs) => {
      let needs_parens = lhs is Abs(_)
      if needs_parens { logger.write_char('(') }
      lhs.fmt(bindings~, depth~, logger)
      if needs_parens { logger.write_char(')') }
      logger.write_char(' ')
      rhs.fmt(bindings~, depth~, logger)
    }
    Abs(x, ann, body) => {
      bindings.push(x)
      defer { let _ = bindings.unsafe_pop() }
      logger.write_string("fun ")
      logger.write_string(x)
      if ann is Some(ty) { logger.write_string(": \{ty}") }
      logger.write_string(" => ")
      body.fmt(bindings~, depth=depth + 1, logger)
    }
    Ann(e, ty) => {
      logger.write_char('(')
      e.fmt(bindings~, depth~, logger)
      logger.write_string(": ")
      logger.write_object(ty)
      logger.write_char(')')
    }
    Tuple(elems) => {
      logger.write_iter(elems.iter(), prefix="(", suffix=")", sep=", ")
    }
    Proj(lhs, index) => {
      lhs.fmt(bindings~, depth~, logger)
      logger.write_char('.')
      logger.write_object(index)
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
    let e = Abs("a", Some(Atom("A")), Abs("b", Some(Atom("B")), Abs("c", Some(Atom("C")), BoundVar(0))))
    assert_eq("\{e}", "fun a: A => fun b: B => fun c: C => c")
  }

  assert_show_expr("true")
  assert_show_expr("false")
  assert_show_expr("(x: Bool)")
  assert_show_expr("fun x => x")
  assert_show_expr("fun x: Bool => x")
  assert_show_expr("fun x: Bool => (x: Bool)")
  assert_show_expr("(true, false)")
  assert_show_expr("(true, false, fun x => x)")
  assert_show_expr("(true, false, fun x => x).2 (false, true)")
  assert_show_expr("(fun x => x, (fun y => y, false)).1.0")
  assert_show_expr("(true, true, true, true, true, true, true, true, true, true, true, true).11")
  assert_show_expr("fun x0 => fun y0 => fun z0 => fun x1 => fun y1 => fun z2 => y0")
  assert_show_expr("fun a: A => fun b: B => fun c: C => c")
  assert_show_expr("fun x => fun y => fun z => x")
  assert_show_expr("fun x => fun y => fun z => y")
  assert_show_expr("fun x => fun y => fun z => z")
  assert_show_expr("(fun x => fun y => y) true")
  assert_show_expr("(fun x => fun y => fun z => x) true false")
  assert_show_expr("(fun x => x: A -> A)")
  assert_show_expr("f g x")
}
