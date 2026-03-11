
struct Context {
  mut next_free_var_id: UInt 
  locals: Map[FreeVarId, Term] // free variables
}

pub fn Context::new() -> Context {
  { next_free_var_id: 0, locals: {} }
}

/// Parses a term from a string, updating the context's next_free_var_id to account for any free variables introduced by the term
pub fn Context::parse(self: Context, input: String) -> Term raise {
  let tokens = Lexer::new(input).tokenise()
  let parser = Parser::new(tokens)
  let term = parser.parse_term()
  self.next_free_var_id += parser.free_vars.length().reinterpret_as_uint()
  term
}

fn Context::fresh_var_id(self: Context) -> FreeVarId {
  let id = self.next_free_var_id
  self.next_free_var_id += 1
  id
}

fn Context::declare_fresh(self: Context, ty: Term) -> FreeVarId {
  let var_id = self.fresh_var_id()
  self.locals[var_id] = ty
  var_id
}

fn Context::lookup_local_var(self: Context, var_id: FreeVarId) -> Term? {
  self.locals.get(var_id)
}

fn Context::normalise(self: Context, term: Term) -> Term {
  match term {
    App(lhs, rhs) => {
      let lhs_norm = self.normalise(lhs)
      let rhs_norm = self.normalise(rhs)

      match lhs_norm {
        Lam(_, _, body) => self.normalise(instantiate(body, 0, rhs_norm))
        _ => App(lhs_norm, rhs_norm)
      }
    }
    Lam(x, ty, body) => {
      // 1. Generate a fresh FreeVar
      let fresh_x = self.declare_fresh(ty)
      defer self.locals.remove(fresh_x)
      
      // 2. Open the binder, replacing BoundVar(0) with the FreeVar
      let opened = open(body, 0, x, fresh_x)
      
      // 3. Normalise the locally closed body
      let norm_body = self.normalise(opened)
      
      // 4. Close the FreeVar back into BoundVar(0)
      Lam(x, self.normalise(ty), close(norm_body, fresh_x, 0))
    }
    Pi(x, a, b) => {
      let a_norm = self.normalise(a)
      let b_norm = if x is Some(name) {
        let fresh_x = self.declare_fresh(a)
        defer self.locals.remove(fresh_x)
        
        let opened = open(b, 0, name, fresh_x)
        close(self.normalise(opened), fresh_x, 0)
      } else {
        self.normalise(b)
      }
      
      Pi(x, a_norm, b_norm)
    }
    Let(_, val, body) => self.normalise(instantiate(body, 0, val))
    Ann(lhs, _) => self.normalise(lhs)
    Star | Box | Bool | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

fn instantiate(term: Term, idx: DeBruijnIndex, s: Term) -> Term {
  match term {
    BoundVar(i) if i == idx => s
    Lam(x, ty, body) => Lam(x, instantiate(ty, idx, s), instantiate(body, idx + 1, s))
    Pi(x, a, b) => Pi(x, instantiate(a, idx, s), instantiate(b, if x is Some(_) { idx + 1 } else { idx }, s))
    App(f, arg) => App(instantiate(f, idx, s), instantiate(arg, idx, s))
    Let(x, val, body) => Let(x, instantiate(val, idx, s), instantiate(body, idx + 1, s))
    Ann(lhs, rhs) => Ann(instantiate(lhs, idx, s), instantiate(rhs, idx, s))
    Star | Box | Bool | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

fn open(term: Term, idx: DeBruijnIndex, name: String, var_id: FreeVarId) -> Term {
  instantiate(term, idx, FreeVar(name, var_id))
}

fn close(term: Term, var_id: FreeVarId, idx: DeBruijnIndex) -> Term {
  match term {
    FreeVar(_, v_id) if v_id == var_id => BoundVar(idx)
    Lam(x, ty, body) => Lam(x, close(ty, var_id, idx), close(body, var_id, idx + 1))
    Pi(x, a, b) => Pi(x, close(a, var_id, idx), close(b, var_id, if x is Some(_) { idx + 1 } else { idx }))
    App(f, arg) => App(close(f, var_id, idx), close(arg, var_id, idx))
    Let(x, val, body) => Let(x, close(val, var_id, idx), close(body, var_id, idx + 1))
    Ann(lhs, rhs) => Ann(close(lhs, var_id, idx), close(rhs, var_id, idx))
    Star | Box | Bool | Const(_) | BoundVar(_) | FreeVar(_) => term
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

pub fn Context::infer(self: Context, term: Term) -> Term raise TypeCheckError {
  match term {
    Bool => Star
    Star => Box
    Box => raise TypeError(term, "□ has no type")
    Const(c) => match c { Bool(_) => Bool }
    BoundVar(_) => raise TypeError(term, "BoundVar")
    FreeVar(name, var_id) => {
      if self.lookup_local_var(var_id) is Some(t) {
        t
      } else {
        raise TypeError(term, "Unbound variable '\{name}'")
      }
    }
    App(lhs, rhs) => {
      match self.normalise(self.infer(lhs)) {
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
        raise TypeError(term, "Invalid lambda argument type, expected * or □, got '\{s1}'")
      }

      let fresh_x = self.declare_fresh(arg_ty)
      defer self.locals.remove(fresh_x)
      let body_ty = self.infer(open(body, 0, x, fresh_x))

      Pi(Some(x), arg_ty, close(body_ty, fresh_x, 0))
    }
    Pi(x, arg_ty, body_ty) => {
      let s1 = self.infer(arg_ty)
      if !s1.is_sort() {
        raise TypeError(term, "Invalid Pi argument type, expected * or □, got '\{s1}'")
      }

      let s2 = if x is Some(name) {
        let fresh_x = self.declare_fresh(arg_ty)
        defer self.locals.remove(fresh_x)
        close(self.infer(open(body_ty, 0, name, fresh_x)), fresh_x, 0)
      } else {
        self.infer(body_ty)
      }

      if !s2.is_sort() {
        raise TypeError(term, "Invalid Pi body type, expected * or □, got '\{s2}'")
      }

      s2
    }
    Let(_, val, body) => {
      // check that val is well-typed
      let _ = self.infer(val)
      self.infer(instantiate(body, 0, val))
    }
    Ann(lhs, ty) => {
      let s = self.infer(ty)
      if !s.is_sort() {
        raise TypeError(term, "Invalid annotation type: \{ty}")
      }

      self.check(lhs, ty)
      ty
    }
  }
}

pub fn Context::check(self: Context, term: Term, ty: Term) -> Unit raise TypeCheckError {
  match term {
    _ => {
      let inferred_ty_norm = self.normalise(self.infer(term))
      let ty_norm = self.normalise(ty)
      if inferred_ty_norm != ty_norm {
        raise TypeError(term, "Expected type '\{ty_norm}', got '\{inferred_ty_norm}'")
      }
    }
  }
}

test "normalisation" {
  fn assert_nf(term: String, nf: String) -> Unit raise {
    let ctx = Context::new()
    assert_eq(ctx.normalise(ctx.parse(term)), ctx.parse(nf), msg="unexpected normal form for '\{term}' and '\{nf}'")
  }

  assert_nf("*", "*")
  assert_nf("□", "□")
  assert_nf("x", "x")
  assert_nf("fun x: Bool => x", "fun x: Bool => x")
  assert_nf("(fun x: Bool => x) true", "true")
  assert_nf("(fun T: * => forall x: T, T) A", "A -> A")
}

test "type checking" {
  fn assert_type(term: String, ty: String) -> Unit raise {
    let ctx = Context::new()
    ctx.check(ctx.parse(term), ctx.parse(ty))
  }

  fn assert_type_err(term: String) -> Unit raise {
    let ctx = Context::new()
    
    try ({ let _ = ctx.infer(ctx.parse(term)) }) catch {
      _ => ()
    } noraise {
      _ => fail("Expected type error for '\{term}', but typing succeeded") 
    }
  }

  assert_type("Bool", "*")
  assert_type("*", "□")
  assert_type("(Bool: *)", "*")
  assert_type("(true: Bool)", "Bool")
  assert_type("Bool -> Bool", "*")
  assert_type("((Bool -> Bool): *)", "*")
  assert_type("* -> Bool", "*")
  assert_type("Bool -> *", "□")
  assert_type("* -> *", "□")
  assert_type("fun x: Bool => x", "Bool -> Bool")
  assert_type("fun x: * => forall x: x, Bool", "* -> *")
  assert_type("(fun x: Bool => x) true", "Bool")
  assert_type("(fun A: * => A -> Bool) Bool", "*")
  assert_type("fun A: * => fun B: * => A -> B", "forall A: *, forall B: *, *")
  assert_type("let x = true in fun y: * => x", "forall A: *, Bool")
  assert_type("let T = Bool -> Bool in fun f: T => fun x: Bool => f x", "(Bool -> Bool) -> Bool -> Bool")

  assert_type_err("□")
  assert_type_err("(fun x: Bool => y) true")
  assert_type_err("(fun x: Bool => x) y")
  assert_type_err("fun A: □ => A -> Bool")
  assert_type_err("fun x: Bool => x -> y")
  assert_type_err("((fun A: * => A): Bool)")
  assert_type_err("((Bool -> Bool): □)")

  // church encodings
  {
    let bool_ty = "forall A: *, forall t: A, forall f: A, A"
    assert_type(bool_ty, "*")
    assert_type("fun A: * => fun t: A => fun f: A => t", bool_ty)
    assert_type("fun A: * => fun t: A => fun f: A => f", bool_ty)
  }

  // church naturals 
  {
    let nat_ty = "forall A: *, forall succ: A -> A, forall zero: A, A"
    let c_zero = "fun A: * => fun succ: A -> A => fun z: A => z"
    assert_type(nat_ty, "*")
    assert_type(c_zero, nat_ty)
  }

  {
    // K-Combinator
    let k_comb = "fun A: * => fun B: * => fun x: A => fun y: B => x"
    let k_type = "forall A: *, forall B: *, forall x: A, forall y: B, A"
    assert_type(k_comb, k_type)
  }

  {
    let id_ty = "fun A: * => A"
    assert_type(id_ty, "* -> *")
    assert_type("(\{id_ty}) Bool", "*")

    let type_alias = "((\{id_ty}) Bool)"
    let f = "fun x: \{type_alias} => x"
    assert_type(f, "\{type_alias} -> \{type_alias}")
    assert_type("(\{f}) true", "Bool")
  }

  {
    let dep_apply = "fun f: Bool -> * => fun b: Bool => f b"
    let dep_apply_ty = "forall f: Bool -> *, Bool -> *"
    assert_type(dep_apply, dep_apply_ty)
  }

  // applying to a non-function
  assert_type_err("true true")

  // un-typable self-application
  assert_type_err("fun x: * => x x")
  
  // applying incorrect type to dependent function
  assert_type_err("(fun x: Bool => x) *")
  
  // trying to declare types at the box level
  assert_type_err("fun x: □ => x")
}
