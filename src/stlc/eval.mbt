
pub fn eval(expr: Expr) -> Expr raise TypeCheckError {
  // only normalise expr if it type checks
  let ctx = TypeContext::new()
  let _ = ctx.infer(expr)
  normalise(expr)
}

fn normalise(expr: Expr) -> Expr {
  match expr {
    App(lhs, rhs) => {
      let norm_lhs = normalise(lhs)
      let norm_rhs = normalise(rhs)
      
      match norm_lhs {
        Abs(_, _, body) => normalise(instantiate(body, 0, norm_rhs))
        _ => App(norm_lhs, norm_rhs)
      }
    }
    Ann(e, _) => normalise(e)
    Tuple(elems) => Tuple(elems.map(normalise))
    Proj(lhs, idx) => match normalise(lhs) {
      Tuple(elems) => elems[idx.reinterpret_as_int()]
      _ => expr // not possible after type checking
    }
    Abs(_) | BoundVar(_) | FreeVar(_) | Const(_) => expr
  }
}

fn instantiate(expr: Expr, idx: DeBruijnIndex, s: Expr) -> Expr {
  match expr {
    BoundVar(n) if n == idx => s
    Abs(x, ty, body) => Abs(x, ty, instantiate(body, idx + 1, s))
    App(lhs, rhs) => App(instantiate(lhs, idx, s), instantiate(rhs, idx, s))
    Ann(e, ty) => Ann(instantiate(e, idx, s), ty)
    Tuple(elems) => Tuple(elems.map(e => instantiate(e, idx, s)))
    Proj(lhs, i) => Proj(instantiate(lhs, idx, s), i)
    BoundVar(_) | FreeVar(_) | Const(_) => expr
  }
}

test "eval" {
  fn assert_nf(expr: String, expected_normal_form: String) raise {
    assert_eq(eval(parse(expr)), parse(expected_normal_form))
  }

  assert_nf("true", "true")
  assert_nf("false", "false")
  assert_nf("(true: Bool)", "true")
  assert_nf("(true, false)", "(true, false)")
  assert_nf("(true, false).0", "true")
  assert_nf("(true, false).1", "false")
  assert_nf("(true, fun x: Bool => x).1 true", "true")
  assert_nf("fun x: A => x", "fun y: A => y")
  assert_nf("(fun x: Bool => x) true", "true")
  assert_nf("(fun x: Bool => fun y: Bool => x) true false", "true")
  assert_nf("(fun x: Bool => fun y: Bool => y) true false", "false")
  assert_nf("(fun x: Bool => fun y: (Bool, Bool) => (x, y)) true (false, false)", "(true, (false, false))")
  assert_nf("(fun x: Bool => fun y: (Bool, Bool) => (y, x, y)) true (false, false)", "((false, false), true, (false, false))")
  assert_nf("(true, (fun x: (Bool, Bool) => (x, x)) (true, false))", "(true, ((true, false), (true, false)))")
}
