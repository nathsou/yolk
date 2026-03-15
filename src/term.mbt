
pub enum Term {
  Sort(UniverseLevel) // 0 = Prop, 1 = Type 0, 2 = Type 1, ...
  Bool
  Const(Name)
  // locally nameless representation: bound variables are represented by their de Bruijn index, free variables have a name
  BoundVar(DeBruijnIndex)
  FreeVar(String, FreeVarId)
  App(Term, Term)
  Lam(String, Term, Term)
  Pi(String?, Term, Term)
  // in a dependently-typed language, let-bindings are not just syntactic sugar for (\x. body) val
  Let(String, Term, Term)
  Ann(Term, Term)
}

pub type DeBruijnIndex = UInt
pub type FreeVarId = UInt

pub type UniverseLevel = UInt

pub fn Term::alpha_eq(self: Term, other: Term) -> Bool {
  match (self, other) {
    (Sort(u1), Sort(u2)) => u1 == u2
    (Bool, Bool) => true
    (Const(r1), Const(r2)) => r1 == r2
    (BoundVar(i), BoundVar(j)) => i == j
    (FreeVar(_, id1), FreeVar(_, id2)) => id1 == id2
    (App(f, x), App(g, y)) => x.alpha_eq(y) && f.alpha_eq(g)
    (Lam(_, t1, body1), Lam(_, t2, body2)) => t1.alpha_eq(t2) && body1.alpha_eq(body2)
    (Pi(_, a1, b1), Pi(_, a2, b2)) => a1.alpha_eq(a2) && b1.alpha_eq(b2)
    (Let(_, t1, body1), Let(_, t2, body2)) => t1.alpha_eq(t2) && body1.alpha_eq(body2)
    (Ann(lhs1, ty1), (Ann(lhs2, ty2))) => ty1.alpha_eq(ty2) && lhs1.alpha_eq(lhs2)
    _ => false
  }
}

fn Term::has_loose_bvar(self: Term, depth: DeBruijnIndex) -> Bool {
  match self {
    BoundVar(i) => i == depth
    App(f, arg) => f.has_loose_bvar(depth) || arg.has_loose_bvar(depth)
    Lam(_, ty, body) => ty.has_loose_bvar(depth) || body.has_loose_bvar(depth + 1)
    Pi(x, a, b) => {
      let b_depth = if x is None { depth } else { depth + 1 }
      a.has_loose_bvar(depth) || b.has_loose_bvar(b_depth)
    }
    Let(_, val, body) => val.has_loose_bvar(depth) || body.has_loose_bvar(depth + 1)
    Ann(lhs, rhs) => lhs.has_loose_bvar(depth) || rhs.has_loose_bvar(depth)
    Sort(_) | Bool | Const(_) | FreeVar(_) => false
  }
}

fn Term::occurs_free(self: Term, var_id: FreeVarId) -> Bool {
  match self {
    FreeVar(_, id) => id == var_id
    App(f, arg) => f.occurs_free(var_id) || arg.occurs_free(var_id)
    Lam(_, ty, body) => ty.occurs_free(var_id) || body.occurs_free(var_id)
    Pi(_, a, b) => a.occurs_free(var_id) || b.occurs_free(var_id)
    Let(_, val, body) => val.occurs_free(var_id) || body.occurs_free(var_id)
    Ann(lhs, rhs) => lhs.occurs_free(var_id) || rhs.occurs_free(var_id)
    Sort(_) | Bool | Const(_) | BoundVar(_) => false
  }
}

fn Term::occurs_in(self: Term, term: Term) -> Bool {
  if self.alpha_eq(term) {
    true
  } else {
    match term {
      App(f, arg) => self.occurs_in(f) || self.occurs_in(arg) 
      Lam(_, ty, body) => self.occurs_in(ty) || self.occurs_in(body)
      Pi(_, a, b) => self.occurs_in(a) || self.occurs_in(b)
      Let(_, val, body) => self.occurs_in(val) || self.occurs_in(body)
      Ann(lhs, rhs) => self.occurs_in(lhs) || self.occurs_in(rhs)
      Sort(_) | Bool | Const(_) | BoundVar(_) | FreeVar(_) => false
    }
  }
}

test "occurs_in" {
  assert_true(Term::Const(Leaf("X")).occurs_in(Const(Leaf("X"))))
  assert_false(Term::Const(Leaf("X")).occurs_in(Const(Leaf("Y"))))
  assert_true(FreeVar("x", 0).occurs_in(App(Const(Leaf("F")), FreeVar("x", 0))))
  assert_true(FreeVar("x", 0).occurs_in(App(App(Const(Leaf("F")), FreeVar("x", 0)), Const(Leaf("Y")))))
  assert_true(FreeVar("x", 0).occurs_in(Pi(None, FreeVar("x", 0), FreeVar("x", 0))))
}

fn Term::collect_app_args(self: Term) -> (Term, Array[Term]) {
  let mut func = self
  let args: Array[Term] = []

  while func is App(f, arg) {
    args.push(arg)
    func = f
  }

  (func, args.rev())
}

pub fn Term::collect_pi_types(self: Term) -> Array[Term] {
  let mut ty = self
  let types: Array[Term] = []

  while ty is Pi(_, arg_ty, rest) {
    types.push(arg_ty)
    ty = rest
  }

  let sorted = types.rev()
  sorted.push(ty)
  sorted
}

fn Term::parens(self: Term, wrap~: Bool, bindings~: Array[String], depth~: Int, logger: &Logger) -> Unit {
  if wrap { logger.write_char('(') }
  self.fmt(bindings~, depth~, logger)
  if wrap { logger.write_char(')') }
}

fn Term::fmt(self: Term, bindings~: Array[String], depth~: Int, logger: &Logger) -> Unit {
  match self {
    Bool => logger.write_string("Bool")
    Sort(u) => logger.write_string(show_sort(u))
    BoundVar(idx) => {
      let eff_idx = bindings.length() - 1 - idx.reinterpret_as_int()
      if eff_idx < 0 {
        logger.write_string("<invalid bound variable index: \{idx}>")
      } else {
        logger.write_string(bindings[eff_idx])
      }
    }
    FreeVar(name, _) => logger.write_string(name)
    Const(name) => logger.write_object(name)
    App(lhs, rhs) => {
      let lhs_needs_parens = lhs is Lam(_)
      let rhs_needs_parens = rhs is (Lam(_) | App(_))
      lhs.parens(wrap=lhs_needs_parens, bindings~, depth~, logger)
      logger.write_char(' ')
      rhs.parens(wrap=rhs_needs_parens, bindings~, depth~, logger)
    }
    Lam(x, ty, body) => {
      logger.write_string("fun ")
      logger.write_string(x)
      logger.write_string(": ")
      ty.fmt(bindings~, depth~, logger)
      logger.write_string(" => ")
      bindings.push(x)
      defer { let _ = bindings.unsafe_pop() }
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
      b.parens(wrap=b is Pi(Some(_), _, _), bindings~, depth = depth + 1, logger)
    }
    Let(x, val, body) => {
      logger.write_string("let ")
      logger.write_string(x)
      logger.write_string(" := ")
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
    let sterm = Parser::new(Lexer::new(input).tokenise()).parse_term()
    let elab = Elaborator::new()
    elab.elaborate_term(sterm)
  }

  fn assert_show_expr(expr: String) raise {
    let parsed = parse(expr)
    assert_eq("\{parsed}", expr, msg="Expected '\{parsed}' to show as '\{expr}'")
  }

  {
    let e = Lam("a", FreeVar("A", 0), Lam("b", FreeVar("B", 1), Lam("c", FreeVar("C", 2), BoundVar(0))))
    assert_eq("\{e}", "fun a: A => fun b: B => fun c: C => c")
  }

  assert_show_expr("Bool")
  assert_show_expr("Prop")
  assert_show_expr("Type")
  assert_show_expr("Type 1")
  assert_show_expr("Type 27")
  assert_show_expr("Bool -> Bool")
  assert_show_expr("Type -> Bool")
  assert_show_expr("fun x: Bool => (x: Bool)")
  assert_show_expr("(Type: Type 1)")
  assert_show_expr("((Bool: Type 1): Type 2)")
  assert_show_expr("fun A: Type => fun B: Type => A -> B -> A")
  // `->` is right-associative
  assert_true(parse("fun A: Type => A -> (A -> A)").alpha_eq(parse("fun A: Type => A -> A -> A")))
  assert_show_expr("forall A: Prop, A -> A")
  assert_show_expr("forall A: Type 78, Bool")
  assert_show_expr("forall A: Type, forall P: A -> Bool -> Prop, forall b: Bool, P A b")
  assert_show_expr("true")
  assert_show_expr("false")
  assert_show_expr("fun x: Bool => x")
  assert_show_expr("fun x: Bool => (x: Bool)")
  assert_show_expr("fun A: Type => fun B: Type => fun C: Type => fun a: A => fun b: B => fun c: C => c")
  assert_show_expr("fun A: Type => ((fun x: A => x): A -> A)")
  assert_show_expr("fun A: Type => (((fun x: A => x): A -> A): Prop)")
  assert_show_expr("fun A: Type => fun f: A -> A => fun g: A -> A => fun x: A => f (g x)")
  assert_show_expr("let id := fun A: Type => fun x: A => x in id")
  assert_true(parse("Sort 0").alpha_eq(parse("Prop")))
  assert_true(parse("Sort 1").alpha_eq(parse("Type")))
  assert_true(parse("Sort 2").alpha_eq(parse("Type 1")))
  assert_true(parse("Sort 3").alpha_eq(parse("Type 2")))
  assert_true(parse("Type 0").alpha_eq(parse("Type")))
  assert_true(parse("Type 1").alpha_eq(parse("Type 1")))
}
