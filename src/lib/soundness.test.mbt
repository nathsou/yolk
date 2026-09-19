// Parse independently so a syntax error cannot masquerade as a kernel rejection.
///|
fn assert_kernel_rejects(source : String) -> Unit raise {
  let program = Parser::new(Lexer::new(source).tokenise()).parse()
  let elab = Elaborator::new()
  try elab.elaborate(program) catch {
    TypeCheckError::TypeError(_, _) => ()
    err => fail("Expected a kernel type error, got \{err}")
  } noraise {
    _ => fail("Kernel accepted invalid program:\n\{source}")
  }
}

///|
fn assert_program_output(
  source : String,
  expected : Array[String],
) -> Unit raise {
  let program = Parser::new(Lexer::new(source).tokenise()).parse()
  let output : Array[String] = []
  Elaborator::new().elaborate(program, on_command_output=s => output.push(s))
  assert_eq(output, expected)
}

///|
test "reject axiom-free binder contradiction" {
  assert_kernel_rejects(
    (
      #|def identity (A B : Prop) : A -> A := fun x => x
      #|def cast : forall A : Prop, forall B : Prop, forall x : A, B := identity
      #|theorem contradiction : False := cast True False True.intro
    ),
  )
  assert_ok(
    (
      #|def identity (A : Prop) : A -> A := fun x => x
      #|def named (A : Prop) : forall x : A, A := identity A
      #|def arrow (A : Prop) : A -> A := named A
    ),
  )
  let (_, arrow) = elab_term("forall A : Prop, forall B : Prop, A -> A")
  let (ctx, named) = elab_term(
    "forall A : Prop, forall B : Prop, forall x : A, B",
  )
  assert_false(arrow.is_alpha_eq(named))
  assert_false(ctx.is_def_eq(arrow, named))
  assert_false(ctx.is_def_eq(named, arrow))
}

///|
test "reject hidden negative occurrences and the diagonal contradiction" {
  assert_kernel_rejects(
    (
      #|inductive Bad : Prop
      #|  | intro : ((Bad -> False) : Prop) -> Bad
      #|def out (x : Bad) : Bad -> False :=
      #|  Bad.rec (fun _ => Bad -> False) (fun f => f) x
      #|def diagonal (x : Bad) : False := out x x
      #|theorem contradiction : False := diagonal (Bad.intro diagonal)
    ),
  )
  for
    field in [
      "(let T := Bad in T -> False)", "((fun (_ : Unit) => Bad -> False) Unit.unit)",
      "((fun T : Prop => T -> False) Bad)", "(True -> ((Bad -> False) : Prop))",
    ] {
    assert_kernel_rejects("inductive Bad : Prop | intro : \{field} -> Bad")
  }
  assert_kernel_rejects(
    (
      #|inductive Flip (A B : Type) : Type
      #|  | mk : Flip B A -> Flip A B
    ),
  )
  assert_kernel_rejects(
    (
      #|inductive Nested : Type
      #|  | mk : List.{0} Nested -> Nested
    ),
  )
  assert_ok(
    (
      #|def Id (A : Type) : Type := A
      #|inductive Positive : Type
      #|  | leaf : Positive
      #|  | node : Id Positive -> Positive
    ),
  )
}

///|
test "reject polymorphic Prop discrimination" {
  assert_kernel_rejects(
    (
      #|inductive Two.{u} : Sort u
      #|  | a : Two.{u}
      #|  | b : Two.{u}
      #|def distinguish (p : Two.{0}) : Bool :=
      #|  Two.rec.{0, 1} (fun _ => Bool) true false p
      #|theorem collapse (p q : Two.{0}) : Eq Bool (distinguish p) (distinguish q) :=
      #|  Eq.refl Bool (distinguish p)
      #|def IsTrue (b : Bool) : Prop := Bool.rec.{1} (fun _ => Prop) True False b
      #|theorem contradiction : False :=
      #|  Eq.rec Bool true (fun b _ => IsTrue b) True.intro false (collapse Two.a.{0} Two.b.{0})
    ),
  )
  assert_kernel_rejects(
    (
      #|inductive Two : Prop | a : Two | b : Two
      #|def distinguish (p : Two) : Bool := Two.rec (fun _ => Bool) true false p
    ),
  )
  assert_ok(
    (
      #|inductive Small.{u} : Sort (imax u 0) | mk : Small.{u}
      #|inductive Data.{u} : Type u | mk : Data.{u}
      #|def dataToBool (d : Data.{0}) : Bool := Data.rec.{0, 1} (fun _ => Bool) true d
      #|def smallProof (p : Small.{1}) : True := Small.rec.{1} (fun _ => True) True.intro p
    ),
  )
}

///|
test "universe bounds and constructor instances" {
  assert_kernel_rejects(
    (
      #|inductive TooSmall : Type
      #|  | mk : (forall A : Type, True -> Bool) -> TooSmall
    ),
  )
  assert_ok(
    (
      #|inductive BigEnough : Type 1
      #|  | mk : (forall A : Type, True -> Bool) -> BigEnough
      #|def f.{u} (A : Sort u) : Sort (imax 0 u) := A
    ),
  )
  assert_kernel_rejects("inductive Wrong.{u} : Type u | mk : Wrong.{0}")
  assert_kernel_rejects(
    "inductive Wrong.{u} : Type u | mk : Wrong.{0} -> Wrong.{u}",
  )
  assert_ok("inductive Good.{u} : Type u | mk : Good.{max u u}")
}

///|
test "global declarations are well scoped and have valid arities" {
  for
    program in [
      "inductive Broken : true -> Type", "inductive Broken (x : true) : Type", "inductive Broken : forall A : Type, (true : A) -> Type",
      "def identity (A : Sort u) : Sort u := A", "axiom unknown : Sort u", "inductive Unknown : Type u",
      "def hidden : Nat := (fun (A : Type u) => 0) Nat", "inductive Unknown : Type | mk : (Type u -> Nat) -> Unknown",
    ] {
    assert_kernel_rejects(program)
  }
  let ctx = Context::new()
  let fvar = ctx.declare_fresh(Sort(Zero))
  defer ctx.free_vars.remove(fvar)
  try ctx.add_decl(Leaf("escaped"), [], Axiom(FreeVar("P", fvar))) catch {
    TypeError(_, _) => ()
    err => fail("Unexpected error: \{err}")
  } noraise {
    _ => fail("Accepted a free variable in a global declaration")
  }
}

///|
test "failed inductive declarations leave the environment unchanged" {
  let elab = Elaborator::new()
  let before = elab.ctx.env.decls.length()
  let program = Parser::new(
    Lexer::new(
      (
        #|inductive Broken : Type
        #|  | good : Broken
        #|  | bad : (Broken -> False) -> Broken
      ),
    ).tokenise(),
  ).parse()
  try elab.elaborate(program) catch {
    _ => ()
  } noraise {
    _ => fail("Expected failure")
  }
  assert_eq(elab.ctx.env.decls.length(), before)
  assert_false(elab.ctx.env.decls.contains(Leaf("Broken")))
  assert_false(elab.ctx.env.decls.contains(Path(Leaf("Broken"), "good")))
  elab.elaborate(
    Parser::new(
      Lexer::new("inductive Broken : Type | good : Broken").tokenise(),
    ).parse(),
  )

  // The generated recursor can fail after all constructor checks have passed.
  let before = elab.ctx.env.decls.length()
  try
    elab.elaborate(
      Parser::new(
        Lexer::new("inductive Collision : Type | rec : Collision").tokenise(),
      ).parse(),
    )
  catch {
    _ => ()
  } noraise {
    _ => fail("Expected recursor name collision")
  }
  assert_eq(elab.ctx.env.decls.length(), before)
  assert_false(elab.ctx.env.decls.contains(Leaf("Collision")))
}

///|
test "multiple and dependent index telescopes" {
  assert_program_output(
    (
      #|inductive Mixed : Nat -> Bool -> Type | mk : Mixed 0 true
      #|def mixed (m : Mixed 0 true) : Nat := Mixed.rec.{1} (fun _ _ _ => Nat) 7 0 true m
      #|#eval mixed Mixed.mk
      #|inductive Dep : forall A : Type, A -> Type | mk : Dep Nat 0
      #|def dep : Nat := Dep.rec.{1} (fun _ _ _ => Nat) 8 Nat 0 Dep.mk
      #|#eval dep
    ),
    ["7", "8"],
  )
  assert_kernel_rejects(
    "inductive Mixed : Nat -> Bool -> Type | mk : Mixed true 0",
  )
  assert_kernel_rejects(
    "inductive Dep : forall A : Type, A -> Type | mk : Dep Nat true",
  )
}

///|
test "functional recursive fields support computation and induction" {
  assert_program_output(
    (
      #|inductive Tree : Type
      #|  | leaf : Tree
      #|  | node : (Bool -> Tree) -> Tree
      #|def count (t : Tree) : Nat :=
      #|  Tree.rec.{1} (fun _ => Nat) 1 (fun children ih => 1 + ih true + ih false) t
      #|def all (t : Tree) : True :=
      #|  Tree.rec.{0} (fun _ => True) True.intro (fun children ih => ih true) t
      #|#eval count (Tree.node (fun _ : Bool => Tree.node (fun _ : Bool => Tree.leaf)))
      #|#eval all (Tree.node (fun _ : Bool => Tree.leaf))
      #|inductive Indexed : Nat -> Type
      #|  | leaf : forall n : Nat, Indexed n
      #|  | node : (forall n : Nat, Eq Nat n n -> Indexed n) -> Indexed 0
      #|def depth (n : Nat) (t : Indexed n) : Nat :=
      #|  Indexed.rec.{1} (fun _ _ => Nat) (fun n => 0) (fun children ih => Nat.succ (ih 3 (Eq.refl Nat 3))) n t
      #|#eval depth 0 (Indexed.node (fun n : Nat => fun h : Eq Nat n n => Indexed.leaf n))
    ),
    ["7", "True.intro", "1"],
  )
}

///|
test "polymorphic indexed recursion substitutes universes in reduction" {
  assert_program_output(
    (
      #|inductive Indexed.{u} (A : Type u) : List.{u} A -> Type u
      #|  | leaf : Indexed.{u} A (List.nil.{u} A)
      #|  | node : forall a : A, Indexed.{u} A (List.nil.{u} A) -> Indexed.{u} A (List.cons.{u} A a (List.nil.{u} A))
      #|def count.{u} (A : Type u) (xs : List.{u} A) (t : Indexed.{u} A xs) : Nat :=
      #|  Indexed.rec.{u, 1} A (fun _ _ => Nat) 0 (fun a child ih => Nat.succ ih) xs t
      #|#eval count.{0} Bool (List.cons.{0} Bool true (List.nil.{0} Bool)) (Indexed.node.{0} Bool true (Indexed.leaf.{0} Bool))
    ),
    ["1"],
  )
}

///|
test "generated recursor signatures are themselves well typed" {
  let ctx = elab_program(
    (
      #|inductive W (L : Type) (A : L -> Type) : Type
      #|  | node : forall l : L, (A l -> W L A) -> W L A
      #|inductive Dep : forall A : Type, A -> Type | mk : Dep Nat 0
    ),
  )
  for _, entry in ctx.env.decls {
    if entry.decl is Recursor(ty~, ..) {
      ty.check_scope(entry.uvs)
      assert_true(ctx.whnf(ctx.infer(ty)) is Sort(_))
    }
  }
  let fake : InductiveDecl[Term] = {
    params: [],
    constructors: [],
    ty: Sort(Zero),
  }
  try
    ctx.add_decl(
      Leaf("forged"),
      [],
      Constructor(ind=fake, ty=Const(Leaf("False"), [])),
    )
  catch {
    TypeError(_, _) => ()
    err => fail("Unexpected error: \{err}")
  } noraise {
    _ => fail("Accepted a standalone constructor")
  }
}

///|
test "let annotations remain kernel checked" {
  assert_kernel_rejects("#check let x : False := true in x")
  assert_kernel_rejects("def bad : Bool := let x : False := true in x")
  assert_kernel_rejects("#check let x : true := true in x")
  assert_program_output(
    (
      #|def identity (A : Type) (a : A) : A := let x : A := a in x
      #|#eval identity Bool true
      #|#eval let f : Bool -> Bool := fun x => x in f false
    ),
    ["true", "false"],
  )
}

///|
test "inductive arities may reduce to dependent products" {
  assert_program_output(
    #|def Arity : Type 1 := Nat -> Type
    #|inductive Reduced : Arity | mk : Reduced 0
    #|#eval Reduced.rec.{1} (fun _ _ => Nat) 9 0 Reduced.mk
    , ["9"],
  )
}

///|
test "matches preserve qualified inductive names" {
  assert_program_output(
    (
      #|inductive NS.T : Type
      #|  | mk : NS.T
      #|def NS.value (x : NS.T) : Nat := match x | mk => 7
      #|#eval NS.value NS.T.mk
      #|inductive NS.Tree : Type
      #|  | leaf : NS.Tree
      #|  | node : NS.Tree -> NS.Tree
      #|def NS.depth (tree : NS.Tree) : Nat :=
      #|  match tree
      #|    | leaf => 0
      #|    | node _ depth => Nat.succ depth
      #|#eval NS.depth (NS.Tree.node (NS.Tree.node NS.Tree.leaf))
    ),
    ["7", "2"],
  )
}
