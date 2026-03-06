
pub fn eval(expr: Expr) -> Expr {
  let mut res = expr

  while step(res) is next && next != res {
    res = next
  }

  res
}

fn step(expr: Expr) -> Expr {
  match expr {
    App(Abs(_, _, body), arg) => shift(subst(body, 0, shift(arg, 0, 1)), 0, -1)
    App(lhs, rhs) => App(eval(lhs), eval(rhs))
    Abs(x, ty, body) => Abs(x, ty, eval(body))
    Ann(e, _) => eval(e)
    Tuple(elems) => Tuple(elems.map(eval))
    Var(_) | Const(_) => expr
  }
}

fn subst(expr: Expr, idx: DeBruijnIndex, s: Expr) -> Expr {
  match expr {
    Var(n) if n == idx => s
    Var(_) | Const(_) => expr
    Abs(x, ty, body) => Abs(x, ty, subst(body, idx + 1, shift(s, 0, 1)))
    App(lhs, rhs) => App(subst(lhs, idx, s), subst(rhs, idx, s))
    Ann(e, ty) => Ann(subst(e, idx, s), ty)
    Tuple(elems) => Tuple(elems.map(e => subst(e, idx, s)))
  }
}

fn shift(expr: Expr, depth: Int, amount: Int) -> Expr {
  match expr {
    Abs(x, ty, body) => Abs(x, ty, shift(body, depth + 1, amount))
    App(f, arg) => App(shift(f, depth, amount), shift(arg, depth, amount))
    Ann(e, ty) => Ann(shift(e, depth, amount), ty)
    Tuple(elems) => Tuple(elems.map(e => shift(e, depth, amount)))
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
  assert_eval("(true, false)", "(true, false)")
  assert_eval("fun x => x", "fun y => y")
  assert_eval("(fun x => x) true", "true")
  assert_eval("(fun x => fun y => x) true false", "true")
  assert_eval("(fun x => fun y => y) true false", "false")
  assert_eval("(fun x => fun y => (x, y)) true (false, false)", "(true, (false, false))")
  assert_eval("(fun x => fun y => (y, x, y)) true (false, false)", "((false, false), true, (false, false))")
  assert_eval("(true, (fun x => (x, x)) (true, false))", "(true, ((true, false), (true, false)))")
}
