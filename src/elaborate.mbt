
pub struct Elaborator {
  bound_vars: Array[String]
  open_vars: Array[(Int, FreeVarId)] // (index into bound_vars, fvar_id)
  mut inductive_type_being_defined: Name?
  ctx: Context
}

pub suberror ElaborationError {
  Message(String)
}

pub impl Show for ElaborationError with output(self: ElaborationError, logger: &Logger) {
  match self {
    Message(msg) => logger.write_string(msg)
  }
}

pub fn Elaborator::new() -> Elaborator {
  Elaborator::from(Context::new())
}

pub fn Elaborator::from(ctx: Context) -> Elaborator {
  {
    bound_vars: [],
    open_vars: [],
    inductive_type_being_defined: None,
    ctx,
  }
}

pub fn Elaborator::elaborate(self: Elaborator, program: Program[STerm]) -> Unit raise {
  for top_level in program.0 {
    match top_level {
      Declaration(name, decl) => self.elaborate_decl(name, decl)
      Command(name, args) => self.run_command(name, args)
    }
  }
}

pub fn Elaborator::run_command(self: Elaborator, name: String, args: Array[STerm]) -> Unit raise {
  let args_elab = args.map(arg => self.elaborate_term(arg))
  if args_elab.length() != 1 {
    raise ElaborationError::Message("'\{name}' command expects exactly one argument")
  }

  match name {
    "eval" | "check" | "valid" => {
      let ty = self.ctx.infer(args_elab[0])

      match name {
        "check" => { println(ty) }
        "valid" => ()
        "eval" => {
          let nf = self.ctx.normalise(args_elab[0])
          println(nf)
        }
        _ => ()
      }
    }
    "invalid" => {
      try self.ctx.infer(args_elab[0]) catch {
        _ => ()
      } noraise {
        ty => raise ElaborationError::Message("Expected term '\{args[0]}' to be invalid, but it is well-typed with type '\{ty}'")
      }
    }
    _ => raise ElaborationError::Message("Invalid command: '\{name}'")
  }
}

pub fn Elaborator::elaborate_decl(self: Elaborator, name: Name, decl: Decl[STerm]) -> Unit raise {
  match decl {
    Axiom(ty) => {
      let ty_elab = self.elaborate_term(ty)
      self.ctx.add_decl(name, Axiom(ty_elab))
    }
    Definition(ty, body) => {
      let ty_elab = self.elaborate_term(ty)
      let body_elab = self.elaborate_term_check(body, ty_elab)
      self.ctx.add_decl(name, Definition(ty_elab, body_elab))
    }
    Inductive({ params, constructors, ty }) => {
      self.inductive_type_being_defined = Some(name)
      let original_bound_vars_len = self.bound_vars.length()
      defer {
        self.inductive_type_being_defined = None
        self.bound_vars.truncate(original_bound_vars_len)
      }

      let params_elab: Array[(String, Term)] = []
      
      for param in params {
        self.bound_vars.push(param.0)
        params_elab.push((param.0, self.elaborate_term(param.1)))
      }

      let constructors_elab = constructors.map(ctor => (ctor.0, self.elaborate_term(ctor.1)))
      let ty_elab = self.elaborate_term(ty)
      let ind_elab: InductiveDecl[Term] = { params: params_elab, constructors: constructors_elab, ty: ty_elab }
      self.ctx.add_decl(name, Inductive(ind_elab))

      for ctor in constructors {
        let mut ctor_ty = ctor.1
        
        for arg in params.rev_iter() {
          ctor_ty = Pi(Some(arg.0), Some(arg.1), ctor_ty)
        }

        let ctor_ty_elab = self.elaborate_term(ctor_ty)
        self.ctx.add_decl(Path(name, ctor.0), Constructor(ind=ind_elab, ty=ctor_ty_elab))
      }

      self.ctx.generate_recursor(name, ind_elab)
    }
    Constructor(_) => raise ElaborationError::Message("Constructors must be declared as part of an inductive type")
    Recursor(..) => raise ElaborationError::Message("Recursors are auto-generated and cannot be declared manually")
  }
}

pub fn Elaborator::elaborate_term(self: Elaborator, term: STerm) -> Term raise {
  match term {
    Sort(u) => Sort(u)
    Var(name) => {
      for i = self.bound_vars.length() - 1; i >= 0; i = i - 1 {
        if name == Leaf(self.bound_vars[i]) {
          // Check if this bound var is currently open as a FreeVar
          for entry in self.open_vars.rev_iter() {
            if entry.0 == i {
              return FreeVar(self.bound_vars[i], entry.1)
            }
          }

          return BoundVar((self.bound_vars.length() - 1 - i).reinterpret_as_uint())
        }
      }

      if self.ctx.env.decls.contains(name) || (self.inductive_type_being_defined is Some(ind) && name == ind) {
        Const(name)
      } else {
        raise ElaborationError::Message("Undefined variable: '\{name}'")
      }
    }
    App(Fun(x, None, fun_body), arg) => {
      let arg_elab = self.elaborate_term(arg)
      let arg_ty = try self.ctx.infer(arg_elab) catch {
        _ => raise ElaborationError::Message("Cannot infer the type of argument '\{x}', add a type annotation to the lambda: 'fun (\{x} : <type>) = ...'")
      }

      self.bound_vars.push(x)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let body_elab = self.elaborate_term(fun_body)
      App(Lam(x, arg_ty, body_elab), arg_elab)
    }
    App(lhs, rhs) => {
      let lhs_elab = self.elaborate_term(lhs)
      let rhs_elab = try self.ctx.infer(lhs_elab) catch {
        _ => self.elaborate_term(rhs)
      } noraise {
        lhs_ty => match self.ctx.whnf(lhs_ty) {
          Pi(_, domain, _) => self.elaborate_term_check(rhs, domain)
          _ => self.elaborate_term(rhs)
        }
      }
      Term::App(lhs_elab, rhs_elab)
    }
    Fun(x, None, _) => raise ElaborationError::Message("'fun \{x}' requires a type annotation here; unannotated lambdas are only allowed where the type is known from context")
    Fun(x, Some(ty_s), body) => {
      let ty_elab = self.elaborate_term(ty_s)
      self.bound_vars.push(x)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let body_elab = self.elaborate_term(body)
      Lam(x, ty_elab, body_elab)
    }
    Pi(Some(x), None, _) => raise ElaborationError::Message("'forall \{x}' requires a type annotation here; unannotated forall is only allowed where the type is known from context")
    Pi(x, Some(a), b) => {
      let a_elab = self.elaborate_term(a)
      match x {
        Some(x) => {
          self.bound_vars.push(x)
          defer { let _ = self.bound_vars.unsafe_pop() }
          let b_elab = self.elaborate_term(b)
          Pi(Some(x), a_elab, b_elab)
        }
        None => {
          let b_elab = self.elaborate_term(b)
          Pi(None, a_elab, b_elab)
        }
      }
    }
    Pi(None, None, _) => raise ElaborationError::Message("Arrow type requires a domain type annotation")
    Let(x, val, body) => {
      let val_elab = self.elaborate_term(val)
      self.bound_vars.push(x)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let body_elab = self.elaborate_term(body)
      Let(x, val_elab, body_elab)
    }
    Ann(e, ty) => {
      let ty_elab = self.elaborate_term(ty)
      let e_elab = self.elaborate_term_check(e, ty_elab)
      Ann(e_elab, ty_elab)
    }
    Match(scrutinee~, motive~, cases~) => {
      self.elaborate_match(scrutinee, motive, cases, None)
    }
  }
}

pub fn Elaborator::elaborate_term_check(self: Elaborator, sterm: STerm, expected_ty: Term) -> Term raise {
  match sterm {
    Fun(x, None, body) => {
      match self.ctx.whnf(expected_ty) {
        Pi(_, domain, codomain) => {
          let fresh = self.ctx.declare_fresh(domain)
          defer self.ctx.free_vars.remove(fresh)
          let opened_codomain = instantiate(codomain, 0, FreeVar(x, fresh))
          self.bound_vars.push(x)
          let bv_idx = self.bound_vars.length() - 1
          self.open_vars.push((bv_idx, fresh))
          defer {
            let _ = self.bound_vars.unsafe_pop()
            let _ = self.open_vars.unsafe_pop()
          }
          let body_elab = self.elaborate_term_check(body, opened_codomain)
          Lam(x, domain, close(body_elab, fresh, 0))
        }
        other => raise ElaborationError::Message("Expected a function type for 'fun \{x} =>', got '\{other}'")
      }
    }
    Fun(x, Some(ty_s), body) => {
      match self.ctx.whnf(expected_ty) {
        Pi(_, _domain, codomain) => {
          let ty_elab = self.elaborate_term(ty_s)
          let fresh = self.ctx.declare_fresh(ty_elab)
          defer self.ctx.free_vars.remove(fresh)
          let opened_codomain = instantiate(codomain, 0, FreeVar(x, fresh))
          self.bound_vars.push(x)
          let bv_idx = self.bound_vars.length() - 1
          self.open_vars.push((bv_idx, fresh))
          defer {
            let _ = self.bound_vars.unsafe_pop()
            let _ = self.open_vars.unsafe_pop()
          }
          let body_elab = self.elaborate_term_check(body, opened_codomain)
          Lam(x, ty_elab, close(body_elab, fresh, 0))
        }
        _ => self.elaborate_term(sterm)
      }
    }
    Pi(Some(x), None, body) => {
      match self.ctx.whnf(expected_ty) {
        Pi(Some(_), domain, codomain) => {
          let fresh = self.ctx.declare_fresh(domain)
          defer self.ctx.free_vars.remove(fresh)
          let opened_codomain = instantiate(codomain, 0, FreeVar(x, fresh))
          self.bound_vars.push(x)
          defer { let _ = self.bound_vars.unsafe_pop() }
          let body_elab = self.elaborate_term_check(body, opened_codomain)
          Pi(Some(x), domain, close(body_elab, fresh, 0))
        }
        other => raise ElaborationError::Message("Expected a named Pi type for 'forall \{x},', got '\{other}'")
      }
    }
    Match(scrutinee~, motive~, cases~) => {
      self.elaborate_match(scrutinee, motive, cases, Some(expected_ty))
    }
    _ => self.elaborate_term(sterm)
  }
}

// Count the number of leading Pi binders in a Term.
fn count_pi_binders(ty: Term) -> Int {
  match ty {
    Pi(_, _, b) => 1 + count_pi_binders(b)
    _ => 0
  }
}

// Count the number of leading Fun binders in an STerm.
fn count_fun_binders(sterm: STerm) -> Int {
  match sterm {
    Fun(_, _, body) => 1 + count_fun_binders(body)
    _ => 0
  }
}

// Build a dependent motive by abstracting `terms` from `ret_ty`
// `terms` contains index terms followed by the scrutinee, matching the Pi binders of motive_ty.
// e.g. for Nat with scrutinee n and ret_ty = Eq Nat (Nat.add 0 n) n:
//   build_dependent_motive(Nat -> Prop, ret_ty, [n]) = fun x => Eq Nat (Nat.add 0 x) x
fn build_dependent_motive(motive_ty: Term, ret_ty: Term, terms: Array[Term]) -> Term {
  // Collect binder names and types from motive_ty (without opening, to preserve BoundVar structure)
  let binders: Array[(String, Term)] = []
  let mut remaining = motive_ty
  for _ in terms {
    match remaining {
      Pi(x, a, b) => {
        let name = match x { Some(x) => x; None => "_" }
        binders.push((name, a))
        remaining = b
      }
      _ => break
    }
  }

  // Build the body by abstracting each term
  // terms[i] corresponds to binder[i]. In the innermost body (under all binders),
  // binder[0] is BoundVar(n-1), binder[1] is BoundVar(n-2), ..., binder[n-1] is BoundVar(0).
  let n = terms.length()
  let mut body = ret_ty
  for i in 0..<n {
    body = abstract_term(body, terms[i], (n - 1 - i).reinterpret_as_uint())
  }

  // Wrap with Lam binders from innermost to outermost
  for i = binders.length() - 1; i >= 0; i = i - 1 {
    let (name, ty) = binders[i]
    body = Lam(name, ty, body)
  }

  body
}

fn Elaborator::elaborate_match(
  self: Elaborator,
  scrutinee: STerm,
  motive: STerm?,
  cases: Array[MatchCase],
  expected_ty: Term?,
) -> Term raise {
  let scrutinee_elab = self.elaborate_term(scrutinee)
  let scrutinee_ty = self.ctx.infer(scrutinee_elab)
  let scrutinee_ty_whnf = self.ctx.whnf(scrutinee_ty)
  let (scrutinee_ty_head, scrutinee_ty_params) = scrutinee_ty_whnf.collect_app_args()
  let scrutinee_ty_name = match scrutinee_ty_head {
    Const(name) => name.root()
    other => raise ElaborationError::Message("Expected scrutinee of 'match' to have an inductive type, got '\{other}'")
  }

  let ind = match self.ctx.env.decls.get(Leaf(scrutinee_ty_name)) {
    Some(Inductive(ind)) => ind
    _ => raise ElaborationError::Message("Expected scrutinee of 'match' to have an inductive type, got '\{scrutinee_ty}'")
  }

  if ind.constructors.length() != cases.length() {
    raise ElaborationError::Message("Number of match cases (\{cases.length()}) does not match number of constructors for type '\{scrutinee_ty_name}' (\{ind.constructors.length()})")
  }

  let rec_name = Name::Path(Leaf(scrutinee_ty_name), "rec")
  let (rec_ty, num_minors) = match self.ctx.env.decls.get(rec_name) {
    Some(Recursor(ty~, num_minors~, ..)) => (ty, num_minors)
    _ => raise ElaborationError::Message("No recursor found for inductive type '\{scrutinee_ty_name}'")
  }

  // Walk the recursor type applying params to reach the motive binder.
  let mut partial_ty = rec_ty
  for param in scrutinee_ty_params {
    match partial_ty {
      Pi(Some(_), _, body) => { partial_ty = instantiate(body, 0, param) }
      Pi(None, _, body) => { partial_ty = body }
      _ => raise ElaborationError::Message("Recursor type has fewer params than expected")
    }
  }

  // The next Pi binder is the motive's type
  let motive_ty = match partial_ty {
    Pi(Some(_), motive_ty, _) | Pi(None, motive_ty, _) => motive_ty
    _ => raise ElaborationError::Message("Recursor type missing motive Pi binder")
  }

  // Elaborate the motive
  // - If omitted, build a dependent motive that abstracts the scrutinee (and indices) from expected_ty.
  // - If provided as a non-function, wrap it in anonymous lambdas to match motive_ty's arity.
  let motive_elab: Term = match motive {
    None => match expected_ty {
      None => raise ElaborationError::Message("Match expression requires a return type annotation (use 'return <type>') when the expected type is not known from context")
      Some(ret_ty) => {
        let num_ind_params = ind.params.length()
        let terms_to_abstract: Array[Term] = []

        for i in num_ind_params..<scrutinee_ty_params.length() {
          terms_to_abstract.push(scrutinee_ty_params[i])
        }

        terms_to_abstract.push(scrutinee_elab)
        build_dependent_motive(motive_ty, ret_ty, terms_to_abstract)
      }
    }
    Some(m) => {
      let n_pi = count_pi_binders(motive_ty)
      let n_fun = count_fun_binders(m)
      let wrapped: STerm = if n_fun < n_pi {
        let mut result = m
        for _ in 0..<(n_pi - n_fun) {
          result = Fun("_", None, result)
        }
        result
      } else {
        m
      }
      self.elaborate_term_check(wrapped, motive_ty)
    }
  }

  // Apply the motive.
  match partial_ty {
    Pi(Some(_), _, body) => { partial_ty = instantiate(body, 0, motive_elab) }
    Pi(None, _, body) => { partial_ty = body }
    _ => raise ElaborationError::Message("Recursor type missing motive Pi binder")
  }

  // Extract one minor premise type per constructor from the leading Pi binders.
  let minor_tys: Array[Term] = []
  for _ in 0..<num_minors {
    match partial_ty {
      Pi(Some(_), minor_ty, rest) => {
        minor_tys.push(minor_ty)
        partial_ty = instantiate(rest, 0, Sort(0)) // dummy: minors don't depend on each other
      }
      Pi(None, minor_ty, rest) => {
        minor_tys.push(minor_ty)
        partial_ty = rest
      }
      _ => raise ElaborationError::Message("Recursor type missing minor Pi binder")
    }
  }

  let minor_ty_by_ctor: Map[String, Term] = Map::from_array(
    ind.constructors.mapi((i, ctor) => (ctor.0, minor_tys[i]))
  )

  let minor_premises_by_ctor: Map[String, Term] = Map::from_array(cases.map(case => {
    let fun = case.args.rev_fold(init=case.body, (acc, arg) => Fun(arg, None, acc))
    let minor_ty = match minor_ty_by_ctor.get(case.ctor) {
      Some(ty) => ty
      None => raise ElaborationError::Message("Unknown constructor '\{case.ctor}' for type '\{scrutinee_ty_name}'")
    }
    (case.ctor, self.elaborate_term_check(fun, minor_ty))
  }))

  let ordered_handlers: Array[Term] = ind.constructors.map(ctor => {
    match minor_premises_by_ctor.get(ctor.0) {
      Some(handler) => handler
      None => raise ElaborationError::Message("No handler provided for constructor '\{ctor.0}' in 'match' expression")
    }
  })

  let mut rec_app: Term = Const(rec_name)
  for param in scrutinee_ty_params {
    rec_app = App(rec_app, param)
  }
  
  let rec_motive_partial_app = Term::App(rec_app, motive_elab)
  let rec_motive_full_app = ordered_handlers.fold(init=rec_motive_partial_app, (acc, minor) => App(acc, minor))
  App(rec_motive_full_app, scrutinee_elab)
}
