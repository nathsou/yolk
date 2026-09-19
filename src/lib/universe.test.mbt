// An independent numeric semantics for the universe comparison tests.
///|
fn eval_level(level : Level, u : Int, v : Int) -> Int {
  match level {
    Zero => 0
    Param("u") => u
    Param(_) => v
    Succ(a) => eval_level(a, u, v) + 1
    Max(a, b) => {
      let x = eval_level(a, u, v)
      let y = eval_level(b, u, v)
      if x > y {
        x
      } else {
        y
      }
    }
    IMax(a, b) => {
      let y = eval_level(b, u, v)
      if y == 0 {
        0
      } else {
        let x = eval_level(a, u, v)
        if x > y {
          x
        } else {
          y
        }
      }
    }
  }
}

///|
test "universe comparison agrees with numeric semantics" {
  let base : Array[Level] = [Zero, Succ(Zero), Param("u"), Param("v")]
  let levels = base.copy()
  for a in base {
    levels.push(Succ(a))
    for b in base {
      levels.push(Max(a, b))
      levels.push(IMax(a, b))
    }
  }
  levels.push(IMax(Level::from(2), IMax(Zero, Succ(Zero))))
  levels.push(IMax(Param("u"), IMax(Param("v"), Param("u"))))
  levels.push(IMax(Param("u"), Max(Param("u"), Param("v"))))
  levels.push(Max(IMax(Param("u"), Param("v")), IMax(Param("v"), Param("u"))))
  levels.push(IMax(Max(Param("u"), Param("v")), Param("u")))

  for a in levels {
    for b in levels {
      for offset in -2..<3 {
        let actual = a.leq(b, offset)
        let mut bounded = true
        for u in 0..<7 {
          for v in 0..<7 {
            if eval_level(a, u, v) > eval_level(b, u, v) + offset {
              bounded = false
            }
          }
        }
        // The bounded oracle is regression coverage, not a proof of the solver.
        assert_true(
          actual == bounded,
          msg="Incorrect comparison: \{a} <= \{b} + \{offset}",
        )
        assert_true(actual == a.simplify().leq(b.simplify(), offset))
      }
      assert_true((a == b) == (b == a))
    }
  }
}

///|
test "universe identities for arbitrary parameters" {
  let u = Level::Param("u")
  let v = Level::Param("v")
  let w = Level::Param("w")
  assert_eq(IMax(Zero, u), u)
  assert_eq(IMax(u, u), u)
  assert_eq(IMax(u, IMax(v, w)), Max(IMax(u, w), IMax(v, w)))
  assert_eq(IMax(u, Max(v, w)), Max(IMax(u, v), IMax(u, w)))
  assert_eq(Max(u, Max(v, w)), Max(Max(u, v), w))
  assert_eq(Max(u, v), Max(v, u))
  assert_eq(Succ(Max(u, v)), Max(Succ(u), Succ(v)))
  assert_false(IMax(Level::from(2), IMax(Zero, Succ(Zero))).leq(Succ(Zero), 0))
}
