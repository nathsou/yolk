
struct Context {
  locals: Map[String, Term] // free variables
}

pub fn Context::new() -> Context {
  { locals: {} }
}

fn normalise(term: Term) -> Term {
  match term {
    App(lhs, rhs) => {
      let lhs_norm = normalise(lhs)
      let rhs_norm = normalise(rhs)

      match lhs_norm {
        Lam(_, _, body) => normalise(instantiate(body, 0, rhs_norm))
        _ => App(lhs_norm, rhs_norm)
      }
    }
    Lam(x, ty, body) => Lam(x, normalise(ty), normalise(body))
    Pi(x, a, b) => Pi(x, normalise(a), normalise(b))
    Star | Box | Bool | Atom(_) | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

fn Context::fresh_name(self: Context, hint: String) -> String {
  let mut name = hint
  let mut i = 0

  while self.locals.contains(name) {
    name = "\{name}@\{i}"
    i += 1
  }

  name
}

fn open(term: Term, idx: DeBruijnIndex, name: String) -> Term {
  instantiate(term, idx, FreeVar(name))
}

fn instantiate(term: Term, idx: DeBruijnIndex, s: Term) -> Term {
  match term {
    BoundVar(i) if i == idx => s
    Lam(x, ty, body) => Lam(x, instantiate(ty, idx, s), instantiate(body, idx + 1, s))
    Pi(x, a, b) => Pi(x, instantiate(a, idx, s), instantiate(b, idx + 1, s))
    App(f, arg) => App(instantiate(f, idx, s), instantiate(arg, idx, s))
    Star | Box | Bool | Atom(_) | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

fn close(term: Term, name: String, idx: DeBruijnIndex) -> Term {
  match term {
    FreeVar(x) if x == name => BoundVar(idx)
    Lam(x, ty, body) => Lam(x, close(ty, name, idx), close(body, name, idx + 1))
    Pi(x, a, b) => Pi(x, close(a, name, idx), close(b, name, idx + 1))
    App(f, arg) => App(close(f, name, idx), close(arg, name, idx))
    Star | Box | Bool | Atom(_) | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

pub suberror TypeCheckError {
  TypeError(Term, String)
}

pub impl Show for TypeCheckError with output(self: TypeCheckError, logger) -> Unit {
  match self {
    TypeError(term, message) => {
      logger.write_string("Type error when checking '\{term}': \{message}")
    }
  }
}

fn Context::lookup_free_var(self: Context, name: String) -> Term? {
  self.locals.get(name)
}

pub fn Context::infer(self: Context, term: Term) -> Term raise TypeCheckError {
  match term {
    Bool | Atom(_) => Star
    Star => Box
    Box => raise TypeError(term, "Box has no type")
    Const(c) => match c { Bool(_) => Bool }
    BoundVar(_) => raise TypeError(term, "BoundVar")
    FreeVar(x) => {
      if self.lookup_free_var(x) is Some(t) {
        if !self.infer(t).is_sort() {
          raise TypeError(term, "Invalid type '\{t}' for variable '\{x}'")
        }

        t
      } else {
        raise TypeError(term, "Unbound variable '\{x}'")
      }
    }
    App(lhs, rhs) => {
      match normalise(self.infer(lhs)) {
        Pi(_, t0, t1) => {
          self.check(rhs, t0)
          instantiate(t1, 0, rhs)
        }
        lhs_ty => raise TypeError(term, "Expected LHS of application '\{term}' to be a Pi term, got '\{lhs_ty}'")
      }
    }
    Lam(x, arg_ty, body) => {
      let s1 = self.infer(arg_ty)
      if !s1.is_sort() {
        raise TypeError(term, "Invalid lambda argument type, expected * or box, got '\{s1}'")
      }

      let fresh_x = self.fresh_name(x)
      self.locals[fresh_x] = arg_ty
      defer self.locals.remove(fresh_x)
      let body_ty = self.infer(open(body, 0, fresh_x))

      Pi(x, arg_ty, close(body_ty, fresh_x, 0))
    }
    Pi(x, arg_ty, body_ty) => {
      let s1 = self.infer(arg_ty)
      if !s1.is_sort() {
        raise TypeError(term, "Invalid Pi argument type, expected * or box, got '\{s1}'")
      }

      let fresh_x = self.fresh_name(x)
      self.locals[fresh_x] = arg_ty
      defer self.locals.remove(fresh_x)
      let s2 = self.infer(open(body_ty, 0, fresh_x))
      if !s2.is_sort() {
        raise TypeError(term, "Invalid Pi body type, expected * or box, got '\{s2}'")
      }

      s2
    }
  }
}

pub fn Context::check(self: Context, term: Term, ty: Term) -> Unit raise TypeCheckError {
  match term {
    _ => {
      let inferred_ty_norm = normalise(self.infer(term))
      let ty_norm = normalise(ty)
      if inferred_ty_norm != ty_norm {
        raise TypeError(term, "Expected \{ty_norm}, got \{inferred_ty_norm}")
      }
    }
  }
}

test "normalisation" {
  fn assert_nf(term: Term, nf: Term) -> Unit raise {
    assert_eq(normalise(term), nf, msg="unexpected normal form")
  }

  assert_nf(Star, Star)
  assert_nf(Box, Box)
  assert_nf(FreeVar("x"), FreeVar("x"))
  assert_nf(Lam("x", Bool, BoundVar(0)), Lam("x", Bool, BoundVar(0)))
  assert_nf(App(Lam("x", Bool, BoundVar(0)), Const(Bool(true))), Const(Bool(true)))
  assert_nf(App(Lam("α", Star, Pi("x", BoundVar(0), BoundVar(1))), Atom("A")), Pi("x", Atom("A"), Atom("A")))
}

test "type checking" {
  fn assert_type(term: Term, ty: Term) -> Unit raise {
    let ctx = Context::new()
    ctx.check(term, ty)
  }

  fn assert_type_err(term: Term) -> Unit raise {
    let ctx = Context::new()
    
    try ({ let _ = ctx.infer(term) }) catch {
      _ => ()
    } noraise {
      _ => fail("Expected type error for '\{term}', but typing succeeded") 
    }
  }

  assert_type(Bool, Star)
  assert_type(Star, Box)
  assert_type(Pi("x", Bool, Bool), Star)
  assert_type(Pi("x", Star, Bool), Star)
  assert_type(Pi("x", Bool, Star), Box)
  assert_type(Pi("x", Star, Star), Box)
  assert_type(Lam("x", Bool, BoundVar(0)), Pi("x", Bool, Bool))
  assert_type(Lam("x", Bool, BoundVar(0)), Pi("y", Bool, Bool))
  assert_type(Lam("x", Star, Pi("x", BoundVar(0), Bool)), Pi("x", Star, Star))
  assert_type(App(Lam("x", Bool, BoundVar(0)), Const(Bool(true))), Bool)
  assert_type(App(Lam("a", Star, Pi("x", BoundVar(0), Bool)), Atom("A")), Star)

  assert_type_err(Box)
  assert_type_err(App(Lam("x", Bool, BoundVar(1)), Const(Bool(true))))
  assert_type_err(App(Lam("x", Bool, BoundVar(0)), Atom("A")))
  assert_type_err(Lam("a", Box, Pi("x", BoundVar(0), Bool)))
  assert_type_err(Lam("x", Bool, Pi("x", BoundVar(0), BoundVar(1))))

  // church encodings
  {
    let bool_ty = Pi("A", Star, Pi("t", BoundVar(0), Pi("f", BoundVar(1), BoundVar(2))))
    let c_true = Lam("A", Star, Lam("t", BoundVar(0), Lam("f", BoundVar(1), BoundVar(1))))
    let c_false = Lam("A", Star, Lam("t", BoundVar(0), Lam("f", BoundVar(1), BoundVar(0))))
    assert_type(bool_ty, Star)
    assert_type(c_true, bool_ty)
    assert_type(c_false, bool_ty)
  }

  // church naturals 
  {
    let nat_ty = Pi("A", Star, Pi("succ", Pi("_", BoundVar(0), BoundVar(1)), Pi("zero", BoundVar(1), BoundVar(2))))
    let c_zero = Lam("A", Star, Lam("s", Pi("_", BoundVar(0), BoundVar(1)), Lam("z", BoundVar(1), BoundVar(0))))
    assert_type(nat_ty, Star)
    assert_type(c_zero, nat_ty)
  }

  {
    // K-Combinator
    let k_comb = Lam("A", Star, Lam("B", Star, Lam("x", BoundVar(1), Lam("y", BoundVar(1), BoundVar(1)))))
    let k_type = Pi("A", Star, Pi("B", Star, Pi("x", BoundVar(1), Pi("y", BoundVar(1), BoundVar(3)))))
    assert_type(k_comb, k_type)
  }

  {
    let id_ty = Lam("A", Star, BoundVar(0))
    assert_type(id_ty, Pi("A", Star, Star))
    assert_type(App(id_ty, Bool), Star)

    let type_alias = App(id_ty, Bool)
    let f = Lam("x", type_alias, BoundVar(0))
    assert_type(f, Pi("x", type_alias, type_alias))
    assert_type(App(f, Const(Bool(true))), Bool)
  }

  {
    // (\lambda f:(Bool -> Star). \lambda b:Bool. f b)
    let dep_apply = Lam("f", Pi("_", Bool, Star), Lam("b", Bool, App(BoundVar(1), BoundVar(0))))
    let dep_apply_ty = Pi("f", Pi("_", Bool, Star), Pi("b", Bool, Star))
    assert_type(dep_apply, dep_apply_ty)
  }


  // applying to a non-function
  assert_type_err(App(Const(Bool(true)), Const(Bool(true))))

  // un-typable self-application
  assert_type_err(Lam("x", Star, App(BoundVar(0), BoundVar(0))))
  
  // applying incorrect type to dependent function
  // (\lambda x:Bool. x) Star
  assert_type_err(App(Lam("x", Bool, BoundVar(0)), Star))
  
  // trying to declare types at the box level
  assert_type_err(Lam("x", Box, BoundVar(0)))
}
