
struct GlobalEnv {
  decls: Map[Name, Decl[Term]]
}

fn GlobalEnv::default() -> GlobalEnv raise {
  let env: GlobalEnv = { decls: {} }
  
  env.add(Leaf("Bool"), Inductive(
    params=[],
    arity=Sort(1),
    constructors=[
      ("true", Const(Leaf("Bool"))),
      ("false", Const(Leaf("Bool"))),
    ],
    ty=Sort(1),
  ))

  env.add(Leaf("true"), Constructor(
    inductive_name=Leaf("Bool"),
    ty=Const(Leaf("Bool")),
  ))

  env.add(Leaf("false"), Constructor(
    inductive_name=Leaf("Bool"),
    ty=Const(Leaf("Bool")),
  ))
  
  env.add(Leaf("Nat"), Inductive(
    params=[],
    arity=Sort(1),
    constructors=[
      ("zero", Const(Leaf("Nat"))),
      ("succ", Pi(None, Const(Leaf("Nat")), Const(Leaf("Nat")))),
    ],
    ty=Sort(1),
  ))

  env.add(Path(Leaf("Nat"), "zero"), Constructor(
    inductive_name=Leaf("Nat"),
    ty=Const(Leaf("Nat")),
  ))

  env.add(Path(Leaf("Nat"), "succ"), Constructor(
    inductive_name=Leaf("Nat"),
    ty=Pi(None, Const(Leaf("Nat")), Const(Leaf("Nat"))),
  ))

  env
}

fn GlobalEnv::add(self: GlobalEnv, name: Name, decl: Decl[Term]) -> Unit raise TypeCheckError {
  if self.decls.contains(name) {
    raise DuplicateDeclaration(name)
  }

  self.decls[name] = decl
}

struct Context {
  mut next_free_var_id: FreeVarId 
  free_vars: Map[FreeVarId, Term]
  env: GlobalEnv
}

pub fn Context::new() -> Context raise {
  {
    env: GlobalEnv::default(),
    next_free_var_id: 0,
    free_vars: {},
  }
}

pub fn Context::add_decl(self: Context, name: Name, decl: Decl[Term]) -> Unit raise TypeCheckError {
  self.check_decl(name, decl)
  self.env.add(name, decl)
}

fn Context::check_decl(self: Context, name: Name, decl: Decl[Term]) -> Unit raise TypeCheckError {
  let ensure_sort = (decl_name: String, ty: Term) => {
    match self.whnf(self.infer(ty)) {
      Sort(u)  => u
      t => {
        raise TypeError(ty, "Invalid type for '\{decl_name}' '\{name}': expected a sort, got '\{t}'")
      }
    }
  }

  // check that all the top-level declarations are well-typed
  match decl {
    Axiom(ty) => { let _ = ensure_sort("axiom", ty) }
    Definition(ty, body) => {
      let _ = ensure_sort("definition", ty)
      self.check(body, ty)
    }
    Inductive(ty~, ..) => {
      let _ = ensure_sort("inductive type", ty)
    }
    // https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#well-formed-inductives  
    // https://ammkrn.github.io/type_checking_in_lean4/declarations/inductive.html#constructor
    Constructor(inductive_name~, ty~) => {
      if self.env.decls.get(inductive_name) is Some(Inductive(params~, arity~, ..)) {
        let _ = ensure_sort("constructor", ty)
        let arity_tys = arity.collect_pi_types()
        let ind_level = match arity_tys.last() {
          Some(Sort(u)) => u
          last => raise TypeError(ty, "Invalid constructor type for '\{name}': expected resulting type to be a sort, got '\{last}'")
        }

        // 1. The constructor's type/telescope has to share the same parameters as the type of the inductive being declared.
        let mut rem_ty = ty
        let free_vars_to_remove: Array[FreeVarId] = []
        defer {
          for var_id in free_vars_to_remove {
            self.free_vars.remove(var_id)
          }
        }
        
        for param in params {
          let (_, param_ty) = param

          match rem_ty {
            Pi(x, a, b) => {
              if !self.is_definitionally_equal(a, param_ty) {
                raise TypeError(ty, "Constructor '\{name}' parameter type '\{a}' does not match inductive type '\{inductive_name}' parameter type '\{param_ty}'")
              }
              
              rem_ty = if x is Some(_) {
                let fresh_x = self.declare_fresh(param_ty)
                free_vars_to_remove.push(fresh_x)
                open(b, 0, fresh_x)
              } else {
                b
              }
            }
            _ => raise TypeError(ty, "Constructor '\{name}' has too few parameters compared to inductive type '\{inductive_name}'")
          }
        }

        let mut arg_idx = 0
        // 2. For the non-parameter elements of the constructor type's telescope, the binder type must actually be a type (must infer as Sort _).
        // 3. For any non-parameter element of the constructor type's telescope, the element's inferred sort must be less than or equal to the inductive type's sort
        // or the inductive type being declared has to be a Prop.
        // 4. No argument to the constructor may contain a non strictly-positive occurrence of the type being declared
        while rem_ty is Pi(x, arg_ty, rest) {
          let s = self.infer(arg_ty)
          if self.whnf(s) is Sort(u) {
            if ind_level > 0 && u > ind_level {
              raise TypeError(ty, "Invalid universe level in constructor '\{name}': Parameter has type '\{arg_ty}' at universe level '\{u}' which is not less than or equal to the inductive type's resulting universe level '\{ind_level}'")
            }

            if !self.is_strictly_positive(arg_ty, inductive_name) {
              raise TypeError(ty, "Constructor '\{name}' has a non strictly-positive occurrence of the inductive type being declared in argument #\{arg_idx + 1}")
            }

            rem_ty = if x is Some(_) {
              let fresh_x = self.declare_fresh(arg_ty)
              free_vars_to_remove.push(fresh_x)
              open(rest, 0, fresh_x)
            } else {
              rest
            }
          } else {
            raise TypeError(ty, "Constructor '\{name}' has non-type parameter '\{arg_ty}'")
          }

          arg_idx += 1
        }

        // 5. The end of the constructor's telescope must be a valid application of arguments to the type being declared.
        let is_valid = match rem_ty {
          Const(ref_name) if ref_name == inductive_name => true
          App(_) => {
            // rem_ty should be of the form `I p1...pm, i1 ..in` (I applied to the parameters and indices)
            let (head, args) = rem_ty.collect_app_args()
            let mut is_valid = true

            if head is Const(ref_name) && ref_name == inductive_name {
              if args.length() < params.length() {
                is_valid = false
              } else {
                // check parameters
                for param, arg in params.zip_to_iter2(args) {
                  let arg_ty = self.infer(arg)
                  if !self.is_definitionally_equal(param.1, arg_ty) {
                    is_valid = false
                    break
                  }
                }

                if is_valid {
                  // check indices
                  let indices = arity_tys[:arity_tys.length() - 1] // all but the resulting sort
                  if indices.length() != args.length() - params.length() {
                    is_valid = false
                  } else {
                    let mut i = params.length()

                    for index in indices {
                      let index_ty = self.infer(args[i])
                      if !self.is_definitionally_equal(index, index_ty) {
                        is_valid = false
                        break
                      }

                      i += 1
                    }
                  }
                }
              }
            } else {
              is_valid = false
            }
            
            is_valid
          }
          _ => false
        }

        if !is_valid {
          raise TypeError(ty, "Constructor '\{name}' has invalid resulting type '\{rem_ty}', expected an application of the inductive type being declared to its parameters")
        }
      } else {
        raise TypeError(ty, "Constructor '\{name}' refers to unknown inductive type '\{inductive_name}'")
      }
    }
  }
}

fn Context::is_strictly_positive(self: Context, ty: Term, inductive_type_name: Name) -> Bool raise TypeCheckError {
  let ind = Const(inductive_type_name)

  // non-recursive case
  if !ind.occurs_in(ty) {
    return true
  }

  match ty {
    Const(_) => true // `I`: simple case
    App(_) => { // `I t1, ..., tn` simple case, where I does not occur in ti for any i
      let (_head, args) = ty.collect_app_args()
      return !args.iter().any(arg => ind.occurs_in(arg))
    }
    Pi(_, a, b) => { // functional case
      !ind.occurs_in(a) && self.is_strictly_positive(b, inductive_type_name)
    }
    _ => true
  }
}

test "is_strictly_positive" {
  let ctx = Context::new()
  let ind = Leaf("Ind")
  let bool = Const(Leaf("Bool"))
  assert_true(ctx.is_strictly_positive(Pi(None, bool, bool), ind))
  assert_true(ctx.is_strictly_positive(Pi(None, bool, Const(ind)), ind))
  assert_false(ctx.is_strictly_positive(Pi(None, Const(ind), Const(ind)), ind))
}

fn Context::fresh_var_id(self: Context) -> FreeVarId raise TypeCheckError {
  let id = self.next_free_var_id
  if id == @uint.max_value {
    raise FreeVarIdOverflow
  }

  self.next_free_var_id += 1
  id
}

fn Context::declare_fresh(self: Context, ty: Term) -> FreeVarId raise TypeCheckError {
  let var_id = self.fresh_var_id()
  self.free_vars[var_id] = ty
  var_id
}

fn Context::lookup_free_var(self: Context, var_id: FreeVarId) -> Term? {
  self.free_vars.get(var_id)
}

fn Context::normalise(self: Context, term: Term) -> Term raise TypeCheckError {
  match term {
    Const(name) => {
      if self.env.decls.get(name) is Some(decl) {
        match decl {
          Axiom(_) => term
          // delta reduction: unfold definitions
          Definition(_, body) => self.normalise(body)
          Inductive(_) => term
          Constructor(_) => term
        }
      } else {
        Const(name)
      }
    }
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
      defer self.free_vars.remove(fresh_x)

      // 2. Open the binder, replacing BoundVar(0) with the FreeVar
      let opened = open(body, 0, fresh_x)

      // 3. Normalise the locally closed body
      let norm_body = self.normalise(opened)

      // 4. Close the FreeVar back into BoundVar(0)
      let closed = close(norm_body, fresh_x, 0)

      // 5. eta-conversion: (fun x => f x) <=> f, when x is not free in f
      if closed is App(f, BoundVar(0)) && !f.has_loose_bvar(0) {
        return f
      }

      Lam(x, self.normalise(ty), closed)
    }
    Pi(x, a, b) => {
      let a_norm = self.normalise(a)
      let b_norm = if x is Some(_) {
        let fresh_x = self.declare_fresh(a)
        defer self.free_vars.remove(fresh_x)

        let opened = open(b, 0, fresh_x)
        close(self.normalise(opened), fresh_x, 0)
      } else {
        self.normalise(b)
      }

      Pi(x, a_norm, b_norm)
    }
    Let(_, val, body) => self.normalise(instantiate(body, 0, self.normalise(val)))
    Ann(lhs, _) => self.normalise(lhs)
    Sort(_) | BoundVar(_) | FreeVar(_) => term
  }
}

// Weak Head Normal Form: only reduce the head of the term, and do not recurse under binders
pub fn Context::whnf(self: Context, term: Term) -> Term {
  match term {
    App(f, arg) => {
      // Only evaluate the function part to see if it's a Lam
      let f_whnf = self.whnf(f)
      match f_whnf {
        Lam(_, _, body) => self.whnf(instantiate(body, 0, arg))
        _ => App(f_whnf, arg)
      }
    }
    Let(_, val, body) => {
      // zeta reduction
      self.whnf(instantiate(body, 0, val))
    }
    Const(name) => {
      if self.env.decls.get(name) is Some(decl) {
        match decl {
          Axiom(_) => term
          // delta reduction
          Definition(_, body) => self.whnf(body)
          Inductive(_) => term
          Constructor(_) => term
        }
      } else {
        Const(name)
      }
    }
    Ann(lhs, _) => self.whnf(lhs)
    Lam(_) | Pi(_) | Sort(_) | BoundVar(_) | FreeVar(_) => term
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
    Sort(_) | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

fn open(term: Term, idx: DeBruijnIndex, var_id: FreeVarId) -> Term {
  instantiate(term, idx, FreeVar(var_id))
}

fn close(term: Term, var_id: FreeVarId, idx: DeBruijnIndex) -> Term {
  match term {
    FreeVar(v_id) if v_id == var_id => BoundVar(idx)
    Lam(x, ty, body) => Lam(x, close(ty, var_id, idx), close(body, var_id, idx + 1))
    Pi(x, a, b) => Pi(x, close(a, var_id, idx), close(b, var_id, if x is Some(_) { idx + 1 } else { idx }))
    App(f, arg) => App(close(f, var_id, idx), close(arg, var_id, idx))
    Let(x, val, body) => Let(x, close(val, var_id, idx), close(body, var_id, idx + 1))
    Ann(lhs, rhs) => Ann(close(lhs, var_id, idx), close(rhs, var_id, idx))
    Sort(_) | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

pub suberror TypeCheckError {
  TypeError(Term, String)
  DuplicateDeclaration(Name)
  FreeVarIdOverflow
}

pub impl Show for TypeCheckError with output(self: TypeCheckError, logger) -> Unit {
  match self {
    TypeError(term, message) => {
      logger.write_string("Type error when checking '\{term}': \{message}")
    }
    DuplicateDeclaration(name) => {
      logger.write_string("Duplicate declaration: '\{name}' is already declared")
    }
    FreeVarIdOverflow => {
      logger.write_string("Ran out of free variable IDs")
    }
  }
}

pub fn Context::infer(self: Context, term: Term) -> Term raise TypeCheckError {
  match term {
    Sort(u) => Sort(u + 1) // Prop : Type 0, Type u : Type (u + 1)
    Const(name) => {
      if self.env.decls.get(name) is Some(decl) {
        match decl {
          Axiom(ty) => ty
          // we already checked that the environment is well-formed
          Definition(ty, _) => ty
          Inductive(ty~, ..) => ty
          Constructor(ty~, ..) => ty
        }
      } else {
        raise TypeError(term, "Unbound reference '\{name}'")
      }
    }
    BoundVar(_) => raise TypeError(term, "BoundVar")
    FreeVar(var_id) => {
      if self.lookup_free_var(var_id) is Some(t) {
        t
      } else {
        raise TypeError(term, "Unbound variable '\{term}'")
      }
    }
    App(lhs, rhs) => {
      match self.whnf(self.infer(lhs)) {
        Pi(_, t0, t1) => {
          self.check(rhs, t0)
          instantiate(t1, 0, rhs)
        }
        lhs_ty => raise TypeError(term, "Expected LHS of application '\{term}' to be a Pi term, got '\{lhs_ty}'")
      }
    }
    Lam(x, arg_ty, body) => {
      let s1 = self.infer(arg_ty)
      if !(self.whnf(s1) is Sort(_)) {
        raise TypeError(term, "Invalid lambda argument type, got '\{s1}'")
      }

      let fresh_x = self.declare_fresh(arg_ty)
      defer self.free_vars.remove(fresh_x)
      let body_ty = self.infer(open(body, 0, fresh_x))
      let x = if body_ty.occurs_free(fresh_x) { Some(x) } else { None }

      Pi(x, arg_ty, close(body_ty, fresh_x, 0))
    }
    Pi(x, arg_ty, body_ty) => {
      let s1 = self.infer(arg_ty)
      let u1 = if self.whnf(s1) is Sort(u) {
        u
      } else {
        raise TypeError(term, "Invalid Pi argument type, got '\{s1}'")
      }

      let s2 = if x is Some(_) {
        let fresh_x = self.declare_fresh(arg_ty)
        defer self.free_vars.remove(fresh_x)
        close(self.infer(open(body_ty, 0, fresh_x)), fresh_x, 0)
      } else {
        self.infer(body_ty)
      }

      let u2 = if self.whnf(s2) is Sort(u) {
        u
      } else {
        raise TypeError(term, "Invalid Pi body type, got '\{s2}'")
      }

      Sort(if u2 == 0 {
        0 // Impredicativity: If the body is a Prop, the Pi is a Prop
      } else {
        u1.max(u2)
      })
    }
    Let(_, val, body) => {
      // check that val is well-typed
      let _ = self.infer(val)
      self.infer(instantiate(body, 0, val))
    }
    Ann(lhs, ty) => {
      let s = self.infer(ty)
      if !(self.whnf(s) is Sort(_)) {
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
      if !self.is_definitionally_equal(inferred_ty_norm, ty_norm) {
        raise TypeError(term, "Expected type '\{ty_norm}', got '\{inferred_ty_norm}'")
      }
    }
  }
}

// TODO: this is currently very naive and normalises both terms fully before comparing them, which is very inefficient.
// see https://rocq-prover.org/doc/V8.19.0/refman/language/core/conversion.html for how to do this more efficiently by interleaving reduction and comparison
// and only reducing as much as needed to determine definitional equality
pub fn Context::is_definitionally_equal(self: Context, term: Term, expected: Term) -> Bool raise TypeCheckError {
  let t1_norm = self.normalise(term)
  let t2_norm = self.normalise(expected)

  if t1_norm.alpha_eq(t2_norm) {
    true
  } else {
    match (t1_norm, t2_norm) {
    // universes are cumulative: Type u <= Type v if u <= v
      (Sort(u1), Sort(u2)) => u1 <= u2
      (Pi(_, a1, b1), Pi(_, a2, b2)) => {
        // Domains must be exactly equal, codomains can be cumulative
        a1.alpha_eq(a2) && self.is_definitionally_equal(b1, b2)
      }
      _ => false
    }
  }
}

fn elab_term(term: String) -> (Context, Term) raise {
  let s_term = Parser::new(Lexer::new(term).tokenise()).parse_term()
  let elab = Elaborator::new()
  let term_elab = elab.elaborate_term(s_term)
  (Context::new(), term_elab)
}

test "normalisation" {
  fn assert_nf(term: String, nf: String) -> Unit raise {
    let (ctx, term_elab) = elab_term(term)
    let (_, nf_elab) = elab_term(nf)
    if !ctx.normalise(term_elab).alpha_eq(nf_elab) {
      fail("Expected normal form of '\{term}' to be '\{nf}', got '\{ctx.normalise(term_elab)}'")
    }
  }

  assert_nf("Type", "Type")
  assert_nf("Type 1", "Type 1")
  assert_nf("fun x: Bool => x", "fun x: Bool => x")
  assert_nf("(fun x: Bool => x) true", "true")
  assert_nf("(fun A: Type => ((fun T: Type => forall x: T, T) A)) Bool", "Bool -> Bool")

  // eta-conversion
  assert_nf("fun f: Bool -> Bool => fun x: Bool => f x", "fun f: Bool -> Bool => f")
  assert_nf("fun f: Bool -> Bool -> Bool => fun x: Bool => f x x", "fun f: Bool -> Bool -> Bool => fun x: Bool => f x x")
  assert_nf("fun f: Bool -> Bool => fun x: Bool => f (f x)", "fun f: Bool -> Bool => fun x: Bool => f (f x)")
  assert_nf("fun x: Bool -> Bool => x x", "fun x: Bool -> Bool => x x")

  // let expressions
  assert_nf("let x := true in x", "true")
  assert_nf("let f := fun x: Bool => x in f true", "true")
  assert_nf("let id := fun A: Type => fun x: A => x in id Bool true", "true")
  assert_nf("let const := fun A: Type => fun B: Type => fun x: A => fun y: B => x in const Bool Bool true false", "true")

  // beta reduction
  assert_nf("(fun p: Bool -> Bool => p true) (fun x: Bool => x)", "true")

  // complex applications
  assert_nf("(fun A: Type => fun x: A => x) Bool true", "true")
  assert_nf("(fun f: Bool -> Bool => fun x: Bool => f (f x)) (fun x: Bool => x) true", "true")
}

test "type checking" {
  fn assert_type(term: String, ty: String) -> Unit raise {
    let (ctx, term_elab) = elab_term(term)
    let (_, ty_elab) = elab_term(ty)
    ctx.check(term_elab, ty_elab)
  }

  fn assert_type_err(term: String) -> Unit raise {
    let (ctx, term_elab) = elab_term(term)
    let res = try? ctx.infer(term_elab)

    if res is Ok(ty) {
      fail("Expected type error for '\{term}', but got type '\{ty}'")
    }
  }

  assert_type("Prop", "Type")
  assert_type("Prop", "Type 1") // universe cumulativity
  assert_type("Bool", "Type")
  assert_type("Bool", "Type 1998")
  assert_type("Type", "Type 1")
  assert_type("Type 0", "Type 1")
  assert_type("(Bool: Type)", "Type")
  assert_type("(true: Bool)", "Bool")
  assert_type("Bool -> Bool", "Type")
  assert_type("((Bool -> Bool): Type)", "Type")
  assert_type("((Bool -> Bool): Type 1)", "Type 1")
  assert_type("Type -> Bool", "Type 1")
  assert_type("Bool -> Type", "Type 1")
  assert_type("Type -> Type", "Type 1")
  assert_type("Type 1 -> Type", "Type 2")
  assert_type("Type 2 -> Type 5", "Type 6")
  assert_type("Type 5 -> Type 4", "Type 6")
  assert_type("fun x: Bool => x", "Bool -> Bool")
  assert_type("fun x: Type => forall x: x, Bool", "Type -> Type")
  assert_type("(fun x: Bool => x) true", "Bool")
  assert_type("(fun A: Type => A -> Bool) Bool", "Type")
  assert_type("fun A: Type => fun B: Type => A -> B", "forall A: Type, forall B: Type, Type")
  assert_type("let x := true in fun y: Type => x", "forall A: Type, Bool")
  assert_type("let T := Bool -> Bool in fun f: T => fun x: Bool => f x", "(Bool -> Bool) -> Bool -> Bool")
  assert_type("fun A: Type 1 => A -> Bool", "forall A: Type 1, Type 1")
  assert_type("fun x: Type 1 => x", "forall x: Type 1, Type 1")

  assert_type_err("((fun A: Type => A): Bool)")
  assert_type_err("(Type 7 : Type 5)")
  assert_type_err("(Type 7 : Prop)")

  // church encodings
  {
    let bool_ty = "forall A: Type, A -> A -> A"
    assert_type(bool_ty, "Type 1")
    assert_type("fun A: Type => fun t: A => fun f: A => t", bool_ty)
    assert_type("fun A: Type => fun t: A => fun f: A => f", bool_ty)
  }

  // church naturals
  {
    let nat_ty = "forall A: Type, (A -> A) -> A -> A"
    let c_zero = "fun A: Type => fun succ: A -> A => fun z: A => z"
    assert_type(nat_ty, "Type 1")
    assert_type(c_zero, nat_ty)
  }

  {
    // K-Combinator
    let k_comb = "fun A: Type => fun B: Type => fun x: A => fun y: B => x"
    let k_type = "forall A: Type, forall B: Type, A -> B -> A"
    assert_type(k_comb, k_type)
  }

  {
    let id_ty = "fun A: Type => A"
    assert_type(id_ty, "Type -> Type")
    assert_type("(\{id_ty}) Bool", "Type")

    let type_alias = "((\{id_ty}) Bool)"
    let f = "fun x: \{type_alias} => x"
    assert_type(f, "\{type_alias} -> \{type_alias}")
    assert_type("(\{f}) true", "Bool")
  }

  {
    let dep_apply = "fun f: Bool -> Type => fun b: Bool => f b"
    let dep_apply_ty = "forall f: Bool -> Type, Bool -> Type"
    assert_type(dep_apply, dep_apply_ty)
  }

  // applying to a non-function
  assert_type_err("true true")

  // un-typable self-application
  assert_type_err("fun x: Type => x x")

  // applying incorrect type to dependent function
  assert_type_err("(fun x: Bool => x) Prop")

  // let bindings
  assert_type("let id := fun x: Bool => x in id", "Bool -> Bool")
  assert_type("let T := Bool in (true: T)", "Bool")
  assert_type("let T := Type in let U := T in (Bool: U)", "Type")

  // dependent pair and logical operations
  assert_type("forall A: Type, forall B: A -> Type, Type", "Type 1")
  assert_type("fun A: Type => fun B: Type => forall C: Type, (A -> B -> C) -> C", "forall A: Type, forall B: Type, Type 1")

  // function abstraction validation
  assert_type_err("fun x: true => x")
  assert_type("fun A: Type => fun P: A -> Type => fun a: A => P a", "forall A: Type, (A -> Type) -> A -> Type")

  // universe applications
  assert_type("(fun A: Type => fun x: A => x) Bool", "Bool -> Bool")
  assert_type("(fun A: Type 1 => fun x: A => x) Bool", "Bool -> Bool")

  // logical operations (Church encoding)
  {
    // Conjunction (and)
    let and_ty = "fun A: Prop => fun B: Prop => forall C: Prop, (A -> B -> C) -> C"
    assert_type(and_ty, "forall A: Prop, forall B: Prop, Prop")

    // Pair constructor for and: fun A, B, a, b, C, f => f a b
    let pair = "fun A: Prop => fun B: Prop => fun a: A => fun b: B => fun C: Type => fun f: A -> B -> C => f a b"
    let pair_ty = "forall A: Prop, forall B: Prop, A -> B -> (forall C: Type, (A -> B -> C) -> C)"
    assert_type(pair, pair_ty)

    // Disjunction (or)
    let or_ty = "fun A: Prop => fun B: Prop => forall C: Prop, (A -> C) -> (B -> C) -> C"
    assert_type(or_ty, "forall A: Prop, forall B: Prop, Prop")

    // Left constructor for or: fun A, B, a, C, l, r => l a
    let left = "fun A: Prop => fun B: Prop => fun a: A => fun C: Prop => fun l: A -> C => fun r: B -> C => l a"
    let left_ty = "forall A: Prop, forall B: Prop, A -> (forall C: Prop, (A -> C) -> ((B -> C) -> C))"
    assert_type(left, left_ty)

    // Right constructor for or: fun A, B, b, C, l, r => r b
    let right = "fun A: Prop => fun B: Prop => fun b: B => fun C: Prop => fun l: A -> C => fun r: B -> C => r b"
    let right_ty = "forall A: Prop, forall B: Prop, B -> (forall C: Prop, (A -> C) -> ((B -> C) -> C))"
    assert_type(right, right_ty)

    // False is the type that takes any type and returns it
    let false_ty = "forall X: Prop, X"
    assert_type(false_ty, "Prop")

    // Negation (not) is A -> False
    let not_ty = "fun A: Prop => A -> (\{false_ty})"
    assert_type(not_ty, "forall A: Prop, Prop")

    // Law of Non-contradiction: not (A and (not A))
    let ncontra = "fun A: Prop => fun p: (forall C: Prop, (A -> (A -> (\{false_ty})) -> C) -> C) => p (\{false_ty}) (fun a: A => fun na: A -> (\{false_ty}) => na a)"
    let ncontra_ty = "forall A: Prop, (forall C: Prop, (A -> (A -> (\{false_ty})) -> C) -> C) -> (\{false_ty})"
    assert_type(ncontra, ncontra_ty)
  }
}
