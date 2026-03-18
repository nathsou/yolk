
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
    _ => self.elaborate_term(sterm)
  }
}
