
pub struct Elaborator {
  bound_vars: Array[String]
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
      let body_elab = self.elaborate_term(body)
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
          ctor_ty = Pi(Some(arg.0), arg.1, ctor_ty)
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
          return BoundVar((self.bound_vars.length() - 1 - i).reinterpret_as_uint())
        }
      }

      if self.ctx.env.decls.contains(name) || (self.inductive_type_being_defined is Some(ind) && name == ind) {
        Const(name)
      } else {
        raise ElaborationError::Message("Undefined variable: '\{name}'")
      }
    }
    App(lhs, rhs) => {
      let lhs_elab = self.elaborate_term(lhs)
      let rhs_elab = self.elaborate_term(rhs)
      App(lhs_elab, rhs_elab)
    }
    Fun(x, ty, body) => {
      let ty_elab = self.elaborate_term(ty)
      self.bound_vars.push(x)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let body_elab = self.elaborate_term(body)
      Lam(x, ty_elab, body_elab)
    }
    Pi(x, a, b) => {
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
    Let(x, val, body) => {
      let val_elab = self.elaborate_term(val)
      self.bound_vars.push(x)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let body_elab = self.elaborate_term(body)
      Let(x, val_elab, body_elab)
    }
    Ann(e, ty) => {
      let e_elab = self.elaborate_term(e)
      let ty_elab = self.elaborate_term(ty)
      Ann(e_elab, ty_elab)
    }
  }
}
