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

// Numeric semantics over three parameters, for the randomized comparison test.
///|
fn eval_level3(level : Level, u : Int, v : Int, w : Int) -> Int {
  match level {
    Zero => 0
    Param("u") => u
    Param("v") => v
    Param(_) => w
    Succ(a) => eval_level3(a, u, v, w) + 1
    Max(a, b) => {
      let x = eval_level3(a, u, v, w)
      let y = eval_level3(b, u, v, w)
      if x > y {
        x
      } else {
        y
      }
    }
    IMax(a, b) => {
      let y = eval_level3(b, u, v, w)
      if y == 0 {
        0
      } else {
        let x = eval_level3(a, u, v, w)
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
fn random_level(state : Ref[UInt], depth : Int) -> Level {
  // Deterministic linear congruential generator, so failures are reproducible.
  state.val = state.val * 1664525 + 1013904223
  let pick = (state.val >> 16).reinterpret_as_int() % 8
  if depth == 0 {
    return match pick % 4 {
      0 => Zero
      1 => Param("u")
      2 => Param("v")
      _ => Param("w")
    }
  }
  match pick {
    0 => Zero
    1 => Param("u")
    2 => Param("v")
    3 => Param("w")
    4 => Succ(random_level(state, depth - 1))
    5 => Max(random_level(state, depth - 1), random_level(state, depth - 1))
    _ => IMax(random_level(state, depth - 1), random_level(state, depth - 1))
  }
}

///|
test "universe comparison agrees with numeric semantics on random levels" {
  let state : Ref[UInt] = { val: 42 }
  let levels : Array[Level] = []
  for _ in 0..<120 {
    levels.push(random_level(state, 4))
  }
  // Offsets and nesting depth are small, so any counterexample has a witness
  // with every parameter below this bound.
  let bound = 7
  for a in levels {
    for b in levels {
      for offset in -1..<2 {
        let mut bounded = true
        for u in 0..<bound {
          for v in 0..<bound {
            for w in 0..<bound {
              if eval_level3(a, u, v, w) > eval_level3(b, u, v, w) + offset {
                bounded = false
              }
            }
          }
        }
        assert_true(
          a.leq(b, offset) == bounded,
          msg="Incorrect comparison: \{a} <= \{b} + \{offset}",
        )
      }
    }
  }
}

///|
test "universe comparison is not exponential in max-only parameters" {
  // Only parameters deciding an imax are split into cases; 32 parameters (the
  // parser's limit) in plain maxima would otherwise take 2^32 cases.
  let mut forward = Level::Param("u0")
  let mut backward = Level::Param("u31")
  for i in 1..<32 {
    forward = Max(forward, Param("u\{i}"))
    backward = Max(backward, Param("u\{31 - i}"))
  }
  assert_eq(forward, backward)
  assert_false(Succ(forward).leq(backward, 0))
  assert_true(Succ(forward).leq(backward, 1))
}
