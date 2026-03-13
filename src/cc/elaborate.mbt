
pub struct Elaborator {
  bound_vars: Array[String]
  free_vars: Map[String, FreeVarId]
}

pub fn Elaborator::new() -> Elaborator {
  { bound_vars: Array::new(), free_vars: Map::new() }
}

pub fn Elaborator::elaborate(self: Elaborator, term: STerm) -> Term raise {
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

      let var_id: FreeVarId = if self.free_vars.get(v) is Some(var_id) {
        var_id
      } else {
        let var_id = self.free_vars.length().reinterpret_as_uint()
        self.free_vars[v] = var_id
        var_id
      }

      FreeVar(v, var_id)
    }
    App(lhs, rhs) => {
      let lhs_elab = self.elaborate(lhs)
      let rhs_elab = self.elaborate(rhs)
      App(lhs_elab, rhs_elab)
    }
    Fun(x, ty, body) => {
      let ty_elab = self.elaborate(ty)
      self.bound_vars.push(x)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let body_elab = self.elaborate(body)
      Lam(x, ty_elab, body_elab)
    }
    Pi(x, a, b) => {
      let a_elab = self.elaborate(a)

      match x {
        Some(x) => {
          self.bound_vars.push(x)
          defer { let _ = self.bound_vars.unsafe_pop() }
          let b_elab = self.elaborate(b)
          Pi(Some(x), a_elab, b_elab)
        }
        None => {
          let b_elab = self.elaborate(b)
          Pi(None, a_elab, b_elab)
        }
      }
    }
    Let(x, val, body) => {
      let val_elab = self.elaborate(val)
      self.bound_vars.push(x)
      defer { let _ = self.bound_vars.unsafe_pop() }
      let body_elab = self.elaborate(body)
      Let(x, val_elab, body_elab)
    }
    Ann(e, ty) => {
      let e_elab = self.elaborate(e)
      let ty_elab = self.elaborate(ty)
      Ann(e_elab, ty_elab)
    }
  }
}
