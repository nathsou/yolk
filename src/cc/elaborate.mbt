
pub struct Elaborator {
  bound_vars: Array[String]
  free_vars: Map[String, FreeVarId]
  env: GlobalEnv
}

pub suberror ElaborationError {
  Message(String)
}

pub struct GlobalEnv {
  decls: Map[Name, Decl[Term]]
}

pub fn GlobalEnv::add(self: GlobalEnv, name: Name, decl: Decl[Term]) -> Unit raise ElaborationError {
  if self.decls.contains(name) {
    raise Message("Duplicate declaration: \{name}")
  }

  self.decls[name] = decl
}

pub fn Elaborator::new() -> Elaborator {
  { bound_vars: [], free_vars: {}, env: { decls: {} } }
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

  match name {
    "eval" | "check" => {
      if args_elab.length() != 1 {
        raise ElaborationError::Message("'\{name}' command expects exactly one argument")
      }

      let ctx = Context::from(self)
      let ty = ctx.infer(args_elab[0])

      if name == "check" {
        println(ty)
      } else {
        let nf = ctx.normalise(args_elab[0])
        println(nf)
      }
    }
    _ => raise ElaborationError::Message("Invalid command: '\{name}'")
  }
}

pub fn Elaborator::elaborate_decl(self: Elaborator, name: Name, decl: Decl[STerm]) -> Unit raise ElaborationError {
  match decl {
    Axiom(ty) => {
      let ty_elab = self.elaborate_term(ty)
      self.env.add(name, Axiom(ty_elab))
    }
    Definition(ty, body) => {
      let ty_elab = self.elaborate_term(ty)
      let body_elab = self.elaborate_term(body)
      self.env.add(name, Definition(ty_elab, body_elab))
    }
    Inductive(_) => ()
  }
}

pub fn Elaborator::elaborate_term(self: Elaborator, term: STerm) -> Term raise ElaborationError {
  match term {
    Sort(u) => Sort(u)
    Bool => Bool
    Const(c) => Const(c)
    Var(v) => {
      for i = self.bound_vars.length() - 1; i >= 0; i = i - 1 {
        if self.bound_vars[i] == v {
          return BoundVar((self.bound_vars.length() - 1 - i).reinterpret_as_uint())
        }
      }

      if self.env.decls.contains(Leaf(v)) {
        Ref(Leaf(v))
      } else {
        let var_id: FreeVarId = if self.free_vars.get(v) is Some(var_id) {
          var_id
        } else {
          let var_id = self.free_vars.length().reinterpret_as_uint()
          self.free_vars[v] = var_id
          var_id
        }

        FreeVar(v, var_id)
      }
    }
    Ref(name) => {
      if self.env.decls.contains(name) {
        Ref(name)
      } else {
        raise ElaborationError::Message("Undefined reference: \{name}")
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
