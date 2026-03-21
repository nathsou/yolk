
pub enum Term {
  Sort(Level) // 0 = Prop, 1 = Type 0, 2 = Type 1, ...
  Const(Name, Array[Level])
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

// https://lmf.cnrs.fr/downloads/Perso/long.pdf
pub enum Level {
  Zero
  Succ(Level)
  Max(Level, Level)
  IMax(Level, Level)
  Param(UniverseVar)
}

pub type UniverseVar = String

pub fn Level::from(n: UInt) -> Level {
  let mut lvl = Zero

  for _ in 0..<(n.reinterpret_as_int()) {
    lvl = Succ(lvl)
  }

  lvl
}

pub fn Level::as_nat(self: Level) -> Option[UInt] {
  let mut count: UInt = 0
  let mut current = self

  while current is Succ(inner) {
    count += 1
    current = inner
  }

  if current is Zero {
    Some(count)
  } else {
    None
  }
}

pub fn Level::subst(self: Level, param: String, lvl: Level) -> Level {
  match self {
    Zero => Zero
    Succ(l) => Succ(l.subst(param, lvl))
    Max(l1, l2) => Max(l1.subst(param, lvl), l2.subst(param, lvl))
    IMax(l1, l2) => IMax(l1.subst(param, lvl), l2.subst(param, lvl))
    Param(p) => if p == param { lvl } else { self }
  }
}

pub fn Level::subst_many(self: Level, subst: (Array[String], Array[Level])) -> Level {
  match self {
    Zero => Zero
    Succ(l) => Succ(l.subst_many(subst))
    Max(l1, l2) => Max(l1.subst_many(subst), l2.subst_many(subst))
    IMax(l1, l2) => IMax(l1.subst_many(subst), l2.subst_many(subst))
    Param(p) => {
      for i in 0..<subst.0.length() {
        if subst.0[i] == p {
          return subst.1[i]
        }
      }

      self
    }
  }
}

pub fn Level::free_vars(self: Level) -> Set[String] {
  let fvs: Set[String] = @set.new()

  fn aux (lvl: Level) -> Unit {
    match lvl {
      Zero => ()
      Succ(l) => aux(l)
      Max(l1, l2) | IMax(l1, l2) => { aux(l1); aux(l2) }
      Param(u) => { fvs.add(u) }
    }
  }

  aux(self)
  fvs
}

pub fn Level::simplify(u: Level) -> Level {
  match u {
    Zero | Param(_) => u
    Succ(l) => Succ(l.simplify())
    Max(l1, l2) => {
      match (l1.simplify(), l2.simplify()) {
        (Zero, l) | (l, Zero) => l
        (Succ(sl1), Succ(sl2)) => Succ(Max(sl1, sl2).simplify())
        (sl1, sl2) => Max(sl1, sl2)
      }
    }
    IMax(l1, l2) => {
      // Simplify the second argument first — IMax is determined by whether l2 is zero
      match l2.simplify() {
        Zero => Zero // IMax(_, 0) = 0
        Succ(_) as sl2 => Level::Max(l1, sl2).simplify() // IMax(a, b+1) = Max(a, b+1)
        sl2 => IMax(l1.simplify(), sl2) // can't reduce further (e.g. Param)
      }
    }
  }
}

// TODO: implement https://lmf.cnrs.fr/downloads/Perso/long.pdf
// u <= v + n, see https://github.com/digama0/lean-type-theory section 2.2
pub fn Level::leq(u: Level, v: Level, n: Int) -> Bool {
  match (u, v) {
    (Zero, _) if n >= 0 => true
    (l1, l2) if n >= 0 && l1.structural_eq(l2) => true
    (IMax(_, Zero), l) => Zero.leq(l, n)
    (IMax(l1, Succ(l2)), l) => Max(l1, Succ(l2)).leq(l, n)
    (IMax(l1, IMax(l2, l3)), l) => Max(IMax(l1, l2), IMax(l2, l3)).leq(l, n)
    (l, IMax(l1, IMax(l2, l3))) => l.leq(Max(IMax(l1, l3), IMax(l2, l3)), n)
    (IMax(l1, Max(l2, l3)), l) => Max(IMax(l1, l2), IMax(l1, l3)).leq(l, n)
    (l, IMax(l1, Max(l2, l3))) => l.leq(Max(IMax(l1, l2), IMax(l1, l3)), n)
    (Succ(l1), l2) => l1.leq(l2, n - 1)
    (l1, Succ(l2)) => l1.leq(l2, n + 1)
    (Max(l1, l2), l) => l1.leq(l, n) && l2.leq(l, n)
    (l, Max(l1, l2)) => l.leq(l1, n) || l.leq(l2, n)
    (l1, l2) => {
      // if for all free variable v in l1 and l2,
      // substituting them with Zero and Succ(v) preserves the leq relation, then l1 <= l2
      let fvs = l1.free_vars().union(l2.free_vars())

      if fvs.is_empty() {
        // No free variables — all structural cases above were exhausted
        return false
      }

      for fv in fvs {
        if !(l1.subst(fv, Zero).leq(l2.subst(fv, Zero), n)) {
          return false
        }

        if !(l1.subst(fv, Succ(Param(fv))).leq(l2.subst(fv, Succ(Param(fv))), n)) {
          return false
        }
      }

      true
    }
  }
}

/// Structural equality (no normalization, no leq). Used inside leq to avoid circular calls.
fn Level::structural_eq(self: Level, other: Level) -> Bool {
  match (self, other) {
    (Zero, Zero) => true
    (Succ(a), Succ(b)) => a.structural_eq(b)
    (Max(a1, b1), Max(a2, b2)) | (IMax(a1, b1), IMax(a2, b2)) =>
      a1.structural_eq(a2) && b1.structural_eq(b2)
    (Param(p1), Param(p2)) => p1 == p2
    _ => false
  }
}

pub impl Eq for Level with equal(self: Level, other: Level) -> Bool {
  let s1 = self.simplify()
  let s2 = other.simplify()
  s1.leq(s2, 0) && s2.leq(s1, 0)
}

pub impl Show for Level with output(self: Level, logger: &Logger) -> Unit {
  match self.simplify() {
    Zero => logger.write_char('0')
    Succ(l) => {
      let mut count = 1
      let mut current = l

      while current is Succ(inner) {
        count += 1
        current = inner
      }

      if current is Zero {
        logger.write_object(count)
      } else {
        logger.write_char('(')
        logger.write_object(current)
        logger.write_string(" + ")
        logger.write_object(count)
        logger.write_char(')')
      }
    }
    Max(l1, l2) | IMax(l1, l2) => {
      logger.write_string(if self is Max(_) { "(max " } else { "(imax " })
      logger.write_object(l1)
      logger.write_char(' ')
      logger.write_object(l2)
      logger.write_char(')')
    }
    Param(name) => logger.write_string(name)
  }
}

pub fn Term::is_alpha_eq(self: Term, other: Term) -> Bool {
  match (self, other) {
    (Sort(l1), Sort(l2)) => l1 == l2
    (Const(r1, levels1), Const(r2, levels2)) => r1 == r2 && levels1 == levels2
    (BoundVar(i), BoundVar(j)) => i == j
    (FreeVar(_, id1), FreeVar(_, id2)) => id1 == id2
    (App(f, x), App(g, y)) => x.is_alpha_eq(y) && f.is_alpha_eq(g)
    (Lam(_, t1, body1), Lam(_, t2, body2)) => t1.is_alpha_eq(t2) && body1.is_alpha_eq(body2)
    (Pi(_, a1, b1), Pi(_, a2, b2)) => a1.is_alpha_eq(a2) && b1.is_alpha_eq(b2)
    (Let(_, t1, body1), Let(_, t2, body2)) => t1.is_alpha_eq(t2) && body1.is_alpha_eq(body2)
    (Ann(lhs1, ty1), (Ann(lhs2, ty2))) => ty1.is_alpha_eq(ty2) && lhs1.is_alpha_eq(lhs2)
    _ => false
  }
}

pub fn Term::subst_levels(self: Term, subst: (Array[String], Array[Level])) -> Term raise TypeCheckError {
  if subst.0.length() != subst.1.length() {
    raise TypeError(self, "Universe instantiation mismatch: expected \{subst.0.length()} levels, got \{subst.1.length()}")
  }

  fn aux(term: Term) -> Term {
    match term {
      Let(x, val, body) => Let(x, aux(val), aux(body))
      Lam(x, ty, body) => Lam(x, aux(ty), aux(body))
      Pi(x, a, b) => Pi(x, aux(a), aux(b))
      App(f, arg) => App(aux(f), aux(arg))
      Ann(e, ty) => Ann(aux(e), aux(ty))
      Const(name, levels) => Const(name, levels.map(l => l.subst_many(subst)))
      Sort(l) => Sort(l.subst_many(subst))
      FreeVar(_, _) | BoundVar(_) => term
    }
  }

  aux(self)
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
    Sort(_) | Const(_) | FreeVar(_) => false
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
    Sort(_) | Const(_) | BoundVar(_) => false
  }
}

// Replace syntactic occurrences of `target` in `body` with `BoundVar(idx)`,
// adjusting idx when going under binders.
fn abstract_term(body: Term, target: Term, idx: DeBruijnIndex) -> Term {
  if body.is_alpha_eq(target) {
    return BoundVar(idx)
  }
  
  match body {
    Lam(x, ty, b) => Lam(x, abstract_term(ty, target, idx), abstract_term(b, target, idx + 1))
    Pi(x, a, b) => Pi(x, abstract_term(a, target, idx), abstract_term(b, target, if x is Some(_) { idx + 1 } else { idx }))
    App(f, arg) => App(abstract_term(f, target, idx), abstract_term(arg, target, idx))
    Let(x, val, b) => Let(x, abstract_term(val, target, idx), abstract_term(b, target, idx + 1))
    Ann(l, r) => Ann(abstract_term(l, target, idx), abstract_term(r, target, idx))
    _ => body
  }
}

fn const_occurs_in(c: Name, term: Term) -> Bool {
  match term {
    Const(name, _) => name == c
    App(f, arg) => const_occurs_in(c, f) || const_occurs_in(c, arg)
    Lam(_, ty, body) => const_occurs_in(c, ty) || const_occurs_in(c, body)
    Pi(_, a, b) => const_occurs_in(c, a) || const_occurs_in(c, b)
    Let(_, val, body) => const_occurs_in(c, val) || const_occurs_in(c, body)
    Ann(lhs, rhs) => const_occurs_in(c, lhs) || const_occurs_in(c, rhs)
    Sort(_) | FreeVar(_) | BoundVar(_) => false
  }
}

test "const_occurs_in" {
  assert_true(const_occurs_in(Leaf("X"), Const(Leaf("X"), [])))
  assert_false(const_occurs_in(Leaf("X"), Const(Leaf("Y"), [])))
  assert_false(const_occurs_in(Leaf("X"), App(FreeVar("X", 0), Const(Leaf("Y"), []))))
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

pub fn Level::show_sort(self: Level, logger: &Logger) -> Unit {
  match self.as_nat() {
    Some(0) => logger.write_string("Prop")
    Some(1) => logger.write_string("Type")
    Some(n) => logger.write_string("Type \{n - 1}")
    None => {
      logger.write_string("Sort ")
      logger.write_object(self)
    }
  }
}

fn Term::parens(self: Term, wrap~: Bool, bindings~: Array[String], depth~: Int, logger: &Logger) -> Unit {
  if wrap { logger.write_char('(') }
  self.fmt(bindings~, depth~, logger)
  if wrap { logger.write_char(')') }
}

fn Term::fmt(
  self: Term,
  bindings~: Array[String],
  depth~: Int,
  logger: &Logger,
  show_var_ids~: Bool = false,
) -> Unit {
  match self {
    Sort(l) => l.show_sort(logger)
    BoundVar(idx) => {
      let eff_idx = bindings.length() - 1 - idx.reinterpret_as_int()
      if eff_idx < 0 {
        logger.write_string("<invalid bound variable index: \{idx}>")
      } else {
        let name = bindings[eff_idx]
        logger.write_string(if show_var_ids { "bv_\{name}#\{idx}" } else { name })
      }
    }
    FreeVar(name, id) => logger.write_string(if show_var_ids { "fv_\{name}#\{id}" } else { name })
    Const(Path(Leaf("Nat"), "zero"), _) => logger.write_char('0')
    Const(name, []) => logger.write_object(name)
    Const(name, levels) => {
      logger.write_object(name)
      logger.write_iter(levels.iter(), sep=", ", prefix=".{", suffix="}")
    }
    App(Const(Path(Leaf("Nat"), "succ"), _), arg) => {
      let mut count = 1
      let mut current_arg = arg

      while current_arg is App(Const(Path(Leaf("Nat"), "succ"), _), next_arg) {
        count += 1
        current_arg = next_arg
      }

      if current_arg is Const(Path(Leaf("Nat"), "zero"), _) {
        logger.write_object(count)
      } else {
        // not a numeral, show as current_arg + count
        current_arg.parens(wrap=!(current_arg is (FreeVar(_) | BoundVar(_) | Const(_))) , bindings~, depth~, logger)
        logger.write_string(" + ")
        logger.write_object(count)
      }
    }
    App(App(Const(Path(Leaf("Nat"), "add"), _), a), b) => {
      a.parens(wrap=!(a is (FreeVar(_) | BoundVar(_) | Const(_))), bindings~, depth~, logger)
      logger.write_string(" + ")
      b.parens(wrap=!(b is (FreeVar(_) | BoundVar(_) | Const(_))), bindings~, depth~, logger)
    }
    App(App(Const(Path(Leaf("Nat"), "mul"), _), a), b) => {
      a.parens(wrap=!(a is (FreeVar(_) | BoundVar(_) | Const(_))), bindings~, depth~, logger)
      logger.write_string(" * ")
      b.parens(wrap=!(b is (FreeVar(_) | BoundVar(_) | Const(_))), bindings~, depth~, logger)
    }
    App(App(App(Const(Leaf("Eq"), _), _ty), a), b) => {
      a.parens(wrap=!(a is (FreeVar(_) | BoundVar(_) | Const(_))), bindings~, depth~, logger)
      logger.write_string(" = ")
      b.parens(wrap=!(b is (FreeVar(_) | BoundVar(_) | Const(_))), bindings~, depth~, logger)
    }
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
  // `->` is right-associative
  assert_true(parse("fun A: Type => A -> (A -> A)").is_alpha_eq(parse("fun A: Type => A -> A -> A")))
  assert_show_expr("forall A: Prop, A -> A")
  assert_show_expr("forall A: Type 17, Bool")
  assert_show_expr("true")
  assert_show_expr("false")
  assert_true(parse("Sort 0").is_alpha_eq(parse("Prop")))
  assert_true(parse("Sort 1").is_alpha_eq(parse("Type")))
  assert_true(parse("Sort 2").is_alpha_eq(parse("Type 1")))
  assert_true(parse("Sort 3").is_alpha_eq(parse("Type 2")))
  assert_true(parse("Type 0").is_alpha_eq(parse("Type")))
  assert_true(parse("Type 1").is_alpha_eq(parse("Type 1")))
}

test "Level::from and as_nat" {
  assert_eq(Level::from(0), Zero)
  assert_eq(Level::from(1), Succ(Zero))
  assert_eq(Level::from(3), Succ(Succ(Succ(Zero))))
  assert_eq(Level::from(0).as_nat(), Some(0))
  assert_eq(Level::from(1).as_nat(), Some(1))
  assert_eq(Level::from(5).as_nat(), Some(5))
  assert_eq(Param("u").as_nat(), None)
  assert_eq(Max(Zero, Succ(Zero)).as_nat(), None)
}

test "Level::simplify" {
  assert_eq(Zero.simplify(), Zero)
  assert_eq(Succ(Succ(Zero)).simplify(), Succ(Succ(Zero)))
  assert_eq(Param("u").simplify(), Param("u"))
  // Max identities
  assert_eq(Max(Zero, Succ(Zero)).simplify(), Succ(Zero))
  assert_eq(Max(Succ(Zero), Zero).simplify(), Succ(Zero))
  assert_eq(Max(Succ(Zero), Succ(Zero)).simplify(), Succ(Zero))
  assert_eq(Max(Succ(Zero), Succ(Succ(Zero))).simplify(), Succ(Succ(Zero)))
  assert_eq(Max(Succ(Succ(Zero)), Succ(Zero)).simplify(), Succ(Succ(Zero)))
  // IMax: second arg is zero → zero (impredicativity)
  assert_eq(IMax(Succ(Zero), Zero).simplify(), Zero)
  assert_eq(IMax(Succ(Succ(Zero)), Zero).simplify(), Zero)
  // IMax: second arg is non-zero → Max
  assert_eq(IMax(Zero, Succ(Zero)).simplify(), Succ(Zero))
  assert_eq(IMax(Succ(Succ(Zero)), Succ(Zero)).simplify(), Succ(Succ(Zero)))
  assert_eq(IMax(Succ(Zero), Succ(Succ(Zero))).simplify(), Succ(Succ(Zero)))
  // Nested IMax simplification
  assert_eq(IMax(Succ(Succ(Zero)), IMax(Succ(Zero), Succ(Zero))).simplify(), Succ(Succ(Zero)))
  // IMax with Param stays
  assert_eq(IMax(Succ(Zero), Param("u")).simplify(), IMax(Succ(Zero), Param("u")))
}

test "Level::leq" {
  // concrete level ordering
  assert_true(Zero.leq(Zero, 0))
  assert_true(Zero.leq(Succ(Zero), 0))
  assert_true(Zero.leq(Succ(Succ(Zero)), 0))
  assert_false(Succ(Zero).leq(Zero, 0))
  assert_false(Succ(Succ(Zero)).leq(Succ(Zero), 0))
  assert_true(Succ(Zero).leq(Succ(Zero), 0))
  assert_true(Succ(Zero).leq(Succ(Succ(Zero)), 0))
  // with offset
  assert_true(Succ(Zero).leq(Zero, 1))
  assert_false(Succ(Zero).leq(Zero, 0))
  assert_false(Succ(Succ(Zero)).leq(Zero, 1))
  assert_true(Succ(Succ(Zero)).leq(Zero, 2))
  // Max
  assert_true(Max(Succ(Zero), Succ(Succ(Zero))).leq(Succ(Succ(Zero)), 0))
  assert_false(Max(Succ(Zero), Succ(Succ(Zero))).leq(Succ(Zero), 0))
  // Param
  assert_true(Param("u").leq(Param("u"), 0))
  assert_true(Param("u").leq(Succ(Param("u")), 0))
  assert_true(Zero.leq(Param("u"), 0))
}

test "Level equality" {
  // same concrete levels
  assert_eq(Level::from(0), Level::from(0))
  assert_eq(Level::from(3), Level::from(3))
  // different concrete levels
  assert_not_eq(Level::from(0), Level::from(1))
  assert_not_eq(Level::from(2), Level::from(5))
  // Max normalises
  assert_eq(Max(Zero, Succ(Zero)), Succ(Zero))
  assert_eq(Max(Succ(Zero), Succ(Succ(Zero))), Succ(Succ(Zero)))
  // IMax normalises
  assert_eq(IMax(Succ(Zero), Zero), Zero)
  assert_eq(IMax(Succ(Zero), Succ(Zero)), Succ(Zero))
  // Param equality
  assert_eq(Param("u"), Param("u"))
  assert_not_eq(Param("u"), Param("v"))
}

test "Level::subst" {
  assert_eq(Param("u").subst("u", Succ(Zero)), Succ(Zero))
  assert_eq(Param("u").subst("v", Succ(Zero)), Param("u"))
  assert_eq(Zero.subst("u", Succ(Zero)), Zero)
  assert_eq(Max(Param("u"), Param("v")).subst("u", Zero), Max(Zero, Param("v")))
  assert_eq(IMax(Param("u"), Param("u")).subst("u", Succ(Zero)), IMax(Succ(Zero), Succ(Zero)))
}

test "Level::free_vars" {
  assert_eq(Zero.free_vars().length(), 0)
  assert_eq(Succ(Zero).free_vars().length(), 0)
  assert_eq(Param("u").free_vars().length(), 1)
  assert_true(Param("u").free_vars().contains("u"))
  let fvs = Max(Param("u"), IMax(Param("v"), Param("w"))).free_vars()
  assert_eq(fvs.length(), 3)
  assert_true(fvs.contains("u"))
  assert_true(fvs.contains("v"))
  assert_true(fvs.contains("w"))
}

test "Level::Show" {
  assert_eq(Zero.to_string(), "0")
  assert_eq(Succ(Zero).to_string(), "1")
  assert_eq(Succ(Succ(Zero)).to_string(), "2")
  assert_eq(Succ(Succ(Succ(Zero))).to_string(), "3")
  assert_eq(Param("u").to_string(), "u")
  assert_eq(Max(Param("u"), Param("v")).to_string(), "(max u v)")
  assert_eq(IMax(Param("u"), Param("v")).to_string(), "(imax u v)")
  assert_eq(Succ(Param("u")).to_string(), "(u + 1)")
  assert_eq(IMax(Max(Succ(Zero), Param("u")), Succ(Succ(Succ(Param("v"))))).to_string(), "(imax (max 1 u) (v + 3))")
}
