
pub fn eval(expr: Expr) -> Expr {
  let mut res = expr

  while step(res) is next && next != res {
    res = next
  }

  res
}

fn step(expr: Expr) -> Expr {
  match expr {
    App(Abs(_, body), arg) => shift(subst(body, 0, shift(arg, 0, 1)), 0, -1)
    App(lhs, rhs) => App(eval(lhs), eval(rhs))
    Abs(ty, body) => Abs(ty, eval(body))
    Ann(e, _) => eval(e)
    Var(_) | Const(_) => expr
  }
}

fn subst(expr: Expr, idx: DeBruijnIndex, s: Expr) -> Expr {
  match expr {
    Var(n) if n == idx => s
    Var(_) | Const(_) => expr
    Abs(ty, body) => Abs(ty, subst(body, idx + 1, shift(s, 0, 1)))
    App(lhs, rhs) => App(subst(lhs, idx, s), subst(rhs, idx, s))
    Ann(e, ty) => Ann(subst(e, idx, s), ty)
  }
}

fn shift(expr: Expr, depth: Int, amount: Int) -> Expr {
  match expr {
    Abs(ty, body) => Abs(ty, shift(body, depth + 1, amount))
    App(f, arg) => App(shift(f, depth, amount), shift(arg, depth, amount))
    Ann(e, ty) => Ann(shift(e, depth, amount), ty)
    Var(n) if n >= depth => Var(n + amount) // free variable
    Var(_) | Const(_) => expr
  }
}

test "eval" {
  fn assert_eval(input: String, res: String) raise {
    assert_eq(eval(parse(input)), parse(res))
  }

  assert_eval("true", "true")
  assert_eval("false", "false")
  assert_eval("(true: Bool)", "true")
  assert_eval("fun x => x", "fun y => y")
  assert_eval("(fun x => x) true", "true")
  assert_eval("(fun x => fun y => x) true false", "true")
  assert_eval("(fun x => fun y => y) true false", "false")
}
