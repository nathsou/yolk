pub suberror ElaboratorError {}

pub struct Elaborator {
  bound_vars: Array[String]
  free_vars: Map[String, FreeVarId]
  mut next_var_id: FreeVarId
}

pub fn Elaborator::new() -> Elaborator {
  { bound_vars: [], free_vars: {}, next_var_id: 0 }
}

pub fn Elaborator::elaborate(self: Elaborator, expr: Expr) -> Term raise ElaboratorError {
  match expr {
    Bool => Bool
    Star => Star
    Box => Box
    Const(c) => Const(c)
    Var(x) => {
      for i = self.bound_vars.length() - 1; i >= 0; i = i - 1 {
        if self.bound_vars[i] == x {
          return BoundVar((self.bound_vars.length() - 1 - i).reinterpret_as_uint())
        }
      }

      let var_id: FreeVarId = if self.free_vars.get(x) is Some(var_id) {
        var_id
      } else {
        let var_id = self.next_var_id
        self.next_var_id += 1
        self.free_vars[x] = var_id
        var_id
      }

      FreeVar(x, var_id)
    }
    App(lhs, rhs) => App(self.elaborate(lhs), self.elaborate(rhs))
    Fun(x, ty, body) => {
      let core_ty = self.elaborate(ty)
      self.bound_vars.push(x)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let core_body = self.elaborate(body)

      Lam(x, core_ty, core_body)
    }
    Pi(x, a, b) => {
      let core_a = self.elaborate(a)
      let name = x.unwrap_or("_")
      self.bound_vars.push(name)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let core_b = self.elaborate(b)
      Pi(name, core_a, core_b)
    }
    Ann(e, ty) => Ann(self.elaborate(e), self.elaborate(ty))
    Let(name~, ty~, val~, rhs~) => {
      let core_ty = self.elaborate(ty)
      let val = self.elaborate(val)

      self.bound_vars.push(name)
      defer { let _ = self.bound_vars.unsafe_pop() }
      App(Lam(name, core_ty, self.elaborate(rhs)), val)
    }
  }
}
