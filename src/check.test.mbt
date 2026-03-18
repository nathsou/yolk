
test "is_strictly_positive" {
  let ctx = Context::new()
  let ind = Leaf("Ind")
  let bool = Const(Leaf("Bool"))
  assert_true(ctx.is_strictly_positive(Pi(None, bool, bool), ind))
  assert_true(ctx.is_strictly_positive(Pi(None, bool, Const(ind)), ind))
  assert_false(ctx.is_strictly_positive(Pi(None, Const(ind), Const(ind)), ind))
}

fn elab_term(term: String, ctx~: Context? = None) -> (Context, Term) raise {
  let s_term = Parser::new(Lexer::new(term).tokenise()).parse_term()
  let elab = match ctx {
    Some(ctx) => Elaborator::from(ctx)
    None => Elaborator::new()
  }
  let term_elab = elab.elaborate_term(s_term)
  (elab.ctx, term_elab)
}

fn assert_nf(term: String, nf: String) -> Unit raise {
  let (ctx, term_elab) = elab_term(term)
  let (_, nf_elab) = elab_term(nf, ctx=Some(ctx))
  if !ctx.normalise(term_elab).is_alpha_eq(nf_elab) {
    fail("Expected normal form of '\{term}' to be '\{nf}', got '\{ctx.normalise(term_elab)}'")
  }
}

test "normalisation" {
  assert_nf("Type", "Type")
  assert_nf("Type 1", "Type 1")
  assert_nf("fun x: Bool => x", "fun x: Bool => x")
  assert_nf("(fun x: Bool => x) true", "true")
  assert_nf("(fun A: Type => ((fun T: Type => forall x: T, T) A)) Bool", "Bool -> Bool")

  // eta-conversion (regression tests: nested fun still works)
  assert_nf("fun f: Bool -> Bool => fun x: Bool => f x", "fun f: Bool -> Bool => f")
  assert_nf("fun f: Bool -> Bool -> Bool => fun x: Bool => f x x", "fun f: Bool -> Bool -> Bool => fun x: Bool => f x x")
  assert_nf("fun f: Bool -> Bool => fun x: Bool => f (f x)", "fun f: Bool -> Bool => fun x: Bool => f (f x)")
  assert_nf("fun x: Bool -> Bool => x x", "fun x: Bool -> Bool => x x")

  // let expressions
  assert_nf("let x := true in x", "true")
  assert_nf("let f := fun x: Bool => x in f true", "true")
  assert_nf("let id := fun (A: Type) (x: A) => x in id Bool true", "true")
  assert_nf("let const := fun (A: Type) (B: Type) (x: A) (y: B) => x in const Bool Bool true false", "true")

  // beta reduction
  assert_nf("(fun p: Bool -> Bool => p true) (fun x: Bool => x)", "true")

  // complex applications
  assert_nf("(fun (A: Type) (x: A) => x) Bool true", "true")
  assert_nf("(fun (f: Bool -> Bool) (x: Bool) => f (f x)) (fun x: Bool => x) true", "true")
}

test "type checking" {
  fn assert_type(term: String, ty: String) -> Unit raise {
    let (ctx, term_elab) = elab_term(term)
    let (_, ty_elab) = elab_term(ty)
    ctx.check(term_elab, ty_elab)
  }

  fn assert_type_err(term: String) -> Unit raise {
    let (ctx, term_elab) = elab_term(term)
    let res = try? ctx.infer(term_elab)

    if res is Ok(ty) {
      fail("Expected type error for '\{term}', but got type '\{ty}'")
    }
  }

  assert_type("Prop", "Type")
  assert_type("Prop", "Type 1") // universe cumulativity
  assert_type("Bool", "Type")
  assert_type("Bool", "Type 1998")
  assert_type("Type", "Type 1")
  assert_type("Type 0", "Type 1")
  assert_type("(Bool: Type)", "Type")
  assert_type("(true: Bool)", "Bool")
  assert_type("Bool -> Bool", "Type")
  assert_type("((Bool -> Bool): Type)", "Type")
  assert_type("((Bool -> Bool): Type 1)", "Type 1")
  assert_type("Type -> Bool", "Type 1")
  assert_type("Bool -> Type", "Type 1")
  assert_type("Type -> Type", "Type 1")
  assert_type("Type 1 -> Type", "Type 2")
  assert_type("Type 2 -> Type 5", "Type 6")
  assert_type("Type 5 -> Type 4", "Type 6")
  assert_type("fun x: Bool => x", "Bool -> Bool")
  assert_type("fun x: Type => forall x: x, Bool", "Type -> Type")
  assert_type("(fun x: Bool => x) true", "Bool")
  assert_type("(fun A: Type => A -> Bool) Bool", "Type")
  assert_type("fun A: Type => fun B: Type => A -> B", "forall A: Type, forall B: Type, Type")
  assert_type("let x := true in fun y: Type => x", "forall A: Type, Bool")
  assert_type("let T := Bool -> Bool in fun (f: T) (x: Bool) => f x", "(Bool -> Bool) -> Bool -> Bool")
  assert_type("fun A: Type 1 => A -> Bool", "forall A: Type 1, Type 1")
  assert_type("fun x: Type 1 => x", "forall x: Type 1, Type 1")

  assert_type_err("((fun A: Type => A): Bool)")
  assert_type_err("(Type 7 : Type 5)")
  assert_type_err("(Type 7 : Prop)")

  // church encodings
  {
    let bool_ty = "forall A: Type, A -> A -> A"
    assert_type(bool_ty, "Type 1")
    assert_type("fun (A: Type) (t: A) (f: A) => t", bool_ty)
    assert_type("fun (A: Type) (t: A) (f: A) => f", bool_ty)
  }

  // church naturals
  {
    let nat_ty = "forall A: Type, (A -> A) -> A -> A"
    let c_zero = "fun (A: Type) (succ: A -> A) (z: A) => z"
    assert_type(nat_ty, "Type 1")
    assert_type(c_zero, nat_ty)
  }

  {
    // K-Combinator
    let k_comb = "fun (A: Type) (B: Type) (x: A) (y: B) => x"
    let k_type = "forall A: Type, forall B: Type, A -> B -> A"
    assert_type(k_comb, k_type)
  }

  {
    let id_ty = "fun A: Type => A"
    assert_type(id_ty, "Type -> Type")
    assert_type("(\{id_ty}) Bool", "Type")

    let type_alias = "((\{id_ty}) Bool)"
    let f = "fun x: \{type_alias} => x"
    assert_type(f, "\{type_alias} -> \{type_alias}")
    assert_type("(\{f}) true", "Bool")
  }

  {
    let dep_apply = "fun (f: Bool -> Type) (b: Bool) => f b"
    let dep_apply_ty = "forall f: Bool -> Type, Bool -> Type"
    assert_type(dep_apply, dep_apply_ty)
  }

  // applying to a non-function
  assert_type_err("true true")

  // un-typable self-application
  assert_type_err("fun x: Type => x x")

  // applying incorrect type to dependent function
  assert_type_err("(fun x: Bool => x) Prop")

  // let bindings
  assert_type("let id := fun x: Bool => x in id", "Bool -> Bool")
  assert_type("let T := Bool in (true: T)", "Bool")
  assert_type("let T := Type in let U := T in (Bool: U)", "Type")

  // dependent pair and logical operations
  assert_type("forall A: Type, forall B: A -> Type, Type", "Type 1")
  assert_type("fun (A: Type) (B: Type) => forall C: Type, (A -> B -> C) -> C", "forall (A: Type) (B: Type), Type 1")

  // function abstraction validation
  assert_type_err("fun x: true => x")
  assert_type("fun (A: Type) (P: A -> Type) (a: A) => P a", "forall A: Type, (A -> Type) -> A -> Type")

  // universe applications
  assert_type("(fun (A: Type) (x: A) => x) Bool", "Bool -> Bool")
  assert_type("(fun (A: Type 1) (x: A) => x) Bool", "Bool -> Bool")

  // logical operations (Church encoding)
  {
    // Conjunction (and)
    let and_ty = "fun (A: Prop) (B: Prop) => forall C: Prop, (A -> B -> C) -> C"
    assert_type(and_ty, "forall (A: Prop) (B: Prop), Prop")

    // Pair constructor for and: fun A, B, a, b, C, f => f a b
    let pair = "fun (A: Prop) (B: Prop) (a: A) (b: B) (C: Type) (f: A -> B -> C) => f a b"
    let pair_ty = "forall A: Prop, forall B: Prop, A -> B -> (forall C: Type, (A -> B -> C) -> C)"
    assert_type(pair, pair_ty)

    // Disjunction (or)
    let or_ty = "fun (A: Prop) (B: Prop) => forall C: Prop, (A -> C) -> (B -> C) -> C"
    assert_type(or_ty, "forall (A: Prop) (B: Prop), Prop")

    // Left constructor for or: fun A, B, a, C, l, r => l a
    let left = "fun (A: Prop) (B: Prop) (a: A) (C: Prop) (l: A -> C) (r: B -> C) => l a"
    let left_ty = "forall A: Prop, forall B: Prop, A -> (forall C: Prop, (A -> C) -> ((B -> C) -> C))"
    assert_type(left, left_ty)

    // Right constructor for or: fun A, B, b, C, l, r => r b
    let right = "fun (A: Prop) (B: Prop) (b: B) (C: Prop) (l: A -> C) (r: B -> C) => r b"
    let right_ty = "forall A: Prop, forall B: Prop, B -> (forall C: Prop, (A -> C) -> ((B -> C) -> C))"
    assert_type(right, right_ty)

    // False is the type that takes any type and returns it
    let false_ty = "forall X: Prop, X"
    assert_type(false_ty, "Prop")

    // Negation (not) is A -> False
    let not_ty = "fun A: Prop => A -> (\{false_ty})"
    assert_type(not_ty, "forall A: Prop, Prop")

    // Law of Non-contradiction: not (A and (not A))
    let ncontra = "fun (A: Prop) (p: (forall C: Prop, (A -> (A -> (\{false_ty})) -> C) -> C)) => p (\{false_ty}) (fun (a: A) (na: A -> (\{false_ty})) => na a)"
    let ncontra_ty = "forall A: Prop, (forall C: Prop, (A -> (A -> (\{false_ty})) -> C) -> C) -> (\{false_ty})"
    assert_type(ncontra, ncontra_ty)
  }
}
fn elab_program(program: String) -> Context raise {
  let prog = Parser::new(Lexer::new(program).tokenise()).parse()
  let elab = Elaborator::new()
  elab.elaborate(prog)
  elab.ctx
}

test "declarations" {
  fn assert_ok(program: String) -> Unit raise {
    try elab_program(program) |> ignore catch {
      err => {
        fail("Invalid program: '\{err}'\n\{program}")
      }
    }
  }

  fn assert_not_ok(program: String) -> Unit raise {
    try elab_program(program) |> ignore catch {
      _ => ()
    } noraise {
      _ => fail("Expected invalid program:\n\{program}")
    }
  }

  assert_ok("inductive False : Prop")
  assert_ok("inductive True : Prop | intro : True")
  assert_ok("inductive List (A : Type) : Type | nil : List A | cons : A -> List A")

  assert_ok((
    #|inductive Tree (A : Type) : Type
    #|  | leaf : A -> Tree A  
    #|  | node : Tree A -> Tree A -> Tree A
  ))

  assert_ok((
    #|inductive WellFormedRecursive : Type
    #|  | intro : WellFormedRecursive -> WellFormedRecursive
  ))

  assert_ok((
    #|inductive Vec (A : Type) : Nat -> Type
    #|  | nil : Vec A Nat.zero
    #|  | cons : A -> forall n : Nat, Vec A n -> Vec A (Nat.succ n)
  ))

  assert_ok((
    #|inductive Eq (A : Type) : A -> A -> Prop
    #|  | refl : forall x : A, Eq A x x
  ))
  
  // duplicate declaration
  assert_not_ok((
    #|inductive A : Type
    #|inductive A : Type
  ))

  // duplicate constructor
  assert_not_ok("inductive A : Type | mk : A | mk : A")
  
  // non-type constructor parameter
  assert_not_ok((
    #|inductive IllFormed1 (A : Type) : Type
    #|  | intro : Nat.zero -> IllFormed1 A
  ))

  // non-sort inductive type
  assert_not_ok("inductive IllFormed2 (A : Type) : Nat")

  // Invalid universe level in constructor
  assert_not_ok((
    #|inductive IllFormed3 : Sort 3
    #|  | intro : Sort 4 -> IllFormed3
  ))

  // non strictly-positive occurrence of inductive type in constructor
  assert_not_ok((
    #|inductive IllFormed4 : Type
    #|  | intro : (IllFormed4 -> IllFormed4) -> IllFormed4
  ))

  assert_not_ok((
    #|inductive False : Prop
    #|inductive P : Prop
    #|  | intro : (P -> False) -> P
  ))

  // Coquand's example of (non-strictly) positive occurence that can lead to a paradox
  assert_not_ok((
    #|inductive A : Type
    #|  | intro : ((A -> Prop) -> Prop) -> A
  ))
  
  // invalid constructor result type
  assert_not_ok((
    #|inductive IllFormed5 : Type
    #|  | nope : Nat -> Bool
  ))

  // constructor result type is a different inductive applied to wrong parameters   
  assert_not_ok((
    #|inductive MyNat : Type
    #|  | zero : MyNat
    #|  | succ : MyNat -> Nat
  ))

  // no beta reduction is performed in constructor parameters
  assert_not_ok((
    #|inductive Test : Type
    #|  | mk : (fun T : Type => (T -> T) -> T) Test
  ))

  assert_not_ok((
    #|inductive Test : Type
    #|  | mk : (fun T : Type => T -> T) Test
  ))

  // two Prop-valued parameters
  assert_ok((
    #|inductive And (A : Prop) (B : Prop) : Prop
    #|  | intro : A -> B -> And A B
  ))

  // multiple constructors with Prop-valued parameters
  assert_ok((
    #|inductive Or (A : Prop) (B : Prop) : Prop
    #|  | inl : A -> Or A B
    #|  | inr : B -> Or A B
  ))

  // no parameters, just an index
  assert_ok((
    #|inductive Fin : Nat -> Type
    #|  | zero : forall n : Nat, Fin n
    #|  | succ : forall n : Nat, Fin n -> Fin (Nat.succ n)
  ))

  // dependent parameter (P depends on A)
  assert_ok((
    #|inductive Exists (A : Type) (P : A -> Prop) : Prop
    #|  | intro : forall a : A, P a -> Exists A P
  ))

  // parameter with a large elimination (Type-valued inductive with Type param in ctor)
  assert_ok((
    #|inductive Wrap (A : Type) : Type
    #|  | mk : A -> Wrap A
  ))

  // swapped parameters in return type
  assert_not_ok((
    #|inductive Pair (A : Type) (B : Type) : Type
    #|  | mk : A -> B -> Pair B A
  ))

  // wrong number of indices (missing index)
  assert_not_ok((
    #|inductive BadVec (A : Type) : Nat -> Type
    #|  | nil : BadVec A
  ))

  // wrong number of indices (extra index)
  assert_not_ok((
    #|inductive BadInd : Type
    #|  | mk : BadInd Nat.zero
  ))

  // constructor returns a different inductive applied to wrong param
  assert_not_ok((
    #|inductive MyList (A : Type) : Type
    #|  | nil : MyList Bool
  ))

  // Well-Founded Trees
  assert_ok((
    #|inductive W (L : Type) (A : L -> Type) : Type
    #| | node : forall lbl : L, (A lbl -> W L A) -> W L A
  ))

  assert_ok((
    #|inductive Acc (A : Type) (ord : A -> A -> Prop) : A -> Prop
    #|  | intro : forall x : A, (forall y : A, ord y x -> Acc A ord y) -> Acc A ord x

    #|def well_founded_ord : forall A : Type, (A -> A -> Prop) -> (A -> Prop) :=
    #|  fun (A : Type) (ord : A -> A -> Prop) (x : A) => Acc A ord x
  ))
}

test "recursor" {
  fn assert_ok(program: String) -> Unit raise {
    try elab_program(program) |> ignore catch {
      err => fail("Invalid program: '\{err}'\n\{program}")
    }
  }

  fn assert_not_ok(program: String) -> Unit raise {
    try elab_program(program) |> ignore catch {
      _ => ()
    } noraise {
      _ => fail("Expected invalid program:\n\{program}")
    }
  }

  fn assert_has_type(program: String, name: String, expected_ty: String) -> Unit raise {
    let ctx = elab_program(program)
    // Elaborate the expected type in the same context (so user-defined types are available)
    let expected = elab_term(expected_ty, ctx=Some(ctx)).1
    let name_parsed = Parser::new(Lexer::new(name).tokenise()).parse_name()
    match ctx.env.decls.get(name_parsed) {
      Some(decl) => {
        let actual_ty = decl.ty()
        if !ctx.is_def_eq(actual_ty, expected) {
          fail("Expected '\{name}' to have type '\{expected}', but got '\{actual_ty}'")
        }
      }
      None => fail("'\{name}' not found in environment")
    }
  }

  // Bool.rec is generated for built-in Bool
  assert_has_type(
    "",
    "Bool.rec",
    "forall C: Bool -> Type, C true -> C false -> forall t: Bool, C t"
  )

  // Nat.rec is generated for built-in Nat
  assert_has_type(
    "",
    "Nat.rec",
    "forall C: Nat -> Type, C Nat.zero -> (forall n: Nat, C n -> C (Nat.succ n)) -> forall t: Nat, C t"
  )

  {
    let list_ind = 
        #|inductive List (A : Type) : Type
        #|  | nil : List A
        #|  | cons : A -> List A -> List A

    // List.rec: recursor with one recursive IH
    assert_has_type(
      list_ind,
      "List.rec",
      "forall A: Type, forall C: List A -> Type, C (List.nil A) -> (forall a: A, forall l: List A, C l -> C (List.cons A a l)) -> forall t: List A, C t"
    )

    assert_ok(
      list_ind + "\n" + (
      #|def List.len : forall A : Type, List A -> Nat :=
      #|  fun (A : Type) =>
      #|  List.rec A (fun _ : List A => Nat)
      #|    Nat.zero
      #|    (fun (h : A) (tl : List A) (ih : Nat) => Nat.succ ih)
    ))
  }

  // False: recursor with no minor premises (ex falso quodlibet)
  assert_has_type(
    "inductive False : Prop",
    "False.rec",
    "forall C: False -> Prop, forall t: False, C t"
  )

  // True: recursor with one constructor and no args
  assert_has_type(
    "inductive True : Prop | intro : True",
    "True.rec",
    "forall C: True -> Prop, C True.intro -> forall t: True, C t"
  )

  // Tree: two recursive arguments in one constructor
  assert_has_type((
      #|inductive Tree (A : Type) : Type
      #|  | leaf : A -> Tree A
      #|  | node : Tree A -> Tree A -> Tree A
    ),
    "Tree.rec",
    (
      #|forall A: Type, forall C: Tree A -> Type,
      #|  (forall a: A, C (Tree.leaf A a)) ->
      #|  (forall l: Tree A, forall r: Tree A, C l -> C r -> C (Tree.node A l r)) ->
      #|  forall t: Tree A, C t
    )
  )

  // Eq: recursor with indices, no recursive args
  assert_has_type((
      #|inductive Eq (A : Type) : A -> A -> Prop
      #|  | refl : forall x : A, Eq A x x
    ),
    "Eq.rec",
    "forall A: Type, forall C: forall a: A, forall b: A, Eq A a b -> Prop, (forall x: A, C x x (Eq.refl A x)) -> forall a: A, forall b: A, forall t: Eq A a b, C a b t"
  )

  // Vec: param + index + recursive arg
  assert_has_type((
      #|inductive Vec (A : Type) : Nat -> Type
      #|  | nil : Vec A Nat.zero
      #|  | cons : A -> forall n : Nat, Vec A n -> Vec A (Nat.succ n)
    ),
    "Vec.rec",
    (
      #|forall A: Type, forall C: forall n: Nat, Vec A n -> Type, C Nat.zero (Vec.nil A) ->
      #|  (forall a: A, forall n: Nat, forall v: Vec A n, C n v -> C (Nat.succ n) (Vec.cons A a n v)) -> forall n: Nat, forall t: Vec A n, C n t)
    )
  )

  // Fin: no params, one index, recursive arg
  assert_has_type((
      #|inductive Fin : Nat -> Type
      #|  | zero : forall n : Nat, Fin n
      #|  | succ : forall n : Nat, Fin n -> Fin (Nat.succ n)
    ),
    "Fin.rec",
    (
      #|forall C: forall n: Nat, Fin n -> Type, (forall n: Nat, C n (Fin.zero n)) ->
      #|  (forall n: Nat, forall f: Fin n, C n f -> C (Nat.succ n) (Fin.succ n f)) -> forall n: Nat, forall t: Fin n, C n t)
    )
  )

  // Exists: dependent parameter (P depends on A)
  assert_has_type((
      #|inductive Exists (A : Type) (P : A -> Prop) : Prop
      #|  | intro : forall a : A, P a -> Exists A P
    ),
    "Exists.rec",
    "forall A: Type, forall P: A -> Prop, forall C: Exists A P -> Prop, (forall a: A, forall h: P a, C (Exists.intro A P a h)) -> forall t: Exists A P, C t"
  )

  // And: two Prop params, simple constructor
  assert_has_type((
      #|inductive And (A : Prop) (B : Prop) : Prop
      #|  | intro : A -> B -> And A B
    ),
    "And.rec",
    "forall A: Prop, forall B: Prop, forall C: And A B -> Prop, (forall a: A, forall b: B, C (And.intro A B a b)) -> forall t: And A B, C t"
  )

  // Or: two constructors
  assert_has_type((
      #|inductive Or (A : Prop) (B : Prop) : Prop
      #|  | inl : A -> Or A B
      #|  | inr : B -> Or A B
    ),
    "Or.rec",
    "forall A: Prop, forall B: Prop, forall C: Or A B -> Prop, (forall a: A, C (Or.inl A B a)) -> (forall b: B, C (Or.inr A B b)) -> forall t: Or A B, C t"
  )

  // Wrap: simple wrapper
  assert_has_type((
    #|inductive Wrap (A : Type) : Type
    #|  | mk : A -> Wrap A
  ),
    "Wrap.rec",
    "forall A: Type, forall C: Wrap A -> Type, (forall a: A, C (Wrap.mk A a)) -> forall t: Wrap A, C t"
  )

  // Recursor is well-typed
  assert_ok((
    #|inductive List (A : Type) : Type
    #|  | nil : List A
    #|  | cons : A -> List A -> List A
    #|#valid List.rec
  ))

  assert_ok("#valid Nat.rec")
  assert_ok("#valid Bool.rec")

  // Recursor name conflicts with an existing declaration
  assert_not_ok((
    #|inductive Dummy : Type
    #|  | mk : Dummy
    #|  | rec : Dummy
  ))

  assert_ok((
    #|inductive False : Prop
    #|def False.elim : forall P : Prop, forall f : False, P :=
    #|  fun P : Prop => False.rec (fun _ : False => P)
  ))

  assert_ok((
    #|inductive Pair (A : Type) (B : Type) : Type
    #|  | mk : A -> B -> Pair A B
    #|
    #|def Pair.fst : forall (A : Type) (B : Type), Pair A B -> A :=
    #|  fun (A : Type) (B : Type) =>
    #|    Pair.rec A B (fun _ : Pair A B => A) (fun a : A => fun b : B => a)
    #|
    #|def Pair.snd : forall (A : Type) (B : Type), Pair A B -> B :=
    #|  fun (A : Type) (B : Type) =>
    #|    Pair.rec A B (fun _ : Pair A B => B) (fun a : A => fun b : B => b)
  ))
}

test "iota reduction" {
  fn assert_nf_with_program(program: String, term: String, nf: String) -> Unit raise {
    let ctx = elab_program(program)
    let term_elab = elab_term(term, ctx=Some(ctx)).1
    let nf_elab = elab_term(nf, ctx=Some(ctx)).1
    let result = ctx.normalise(term_elab)

    if !result.is_alpha_eq(nf_elab) {
      fail("Expected normal form of '\{term}' to be '\{nf}', got '\{result}'")
    }
  }

  assert_nf(
    "Bool.rec (fun _ : Bool => Bool) false true true",
    "false"
  )

  assert_nf(
    "Bool.rec (fun _ : Bool => Bool) false true false",
    "true"
  )

  assert_nf(
    "Nat.rec (fun _ : Nat => Nat) Nat.zero (fun m : Nat => fun ih : Nat => m) Nat.zero",
    "Nat.zero"
  )

  let pred = "Nat.rec (fun _ : Nat => Nat) Nat.zero (fun m : Nat => fun ih : Nat => m)"
  assert_nf(
    "\{pred} (Nat.succ Nat.zero)",
    "Nat.zero"
  )

  assert_nf(
    "\{pred} (Nat.succ (Nat.succ Nat.zero))",
    "Nat.succ Nat.zero"
  )

  let nat_id = "Nat.rec (fun _ : Nat => Nat) Nat.zero (fun (n : Nat) (ih : Nat) => Nat.succ ih)"
  assert_nf("\{nat_id} Nat.zero", "Nat.zero")
  assert_nf("\{nat_id} (Nat.succ Nat.zero)", "Nat.succ Nat.zero")
  let three = "Nat.succ (Nat.succ (Nat.succ Nat.zero))"
  assert_nf("\{nat_id} (\{three})", three)

  let nat_add = "fun (n : Nat) (m : Nat) => Nat.rec (fun _ : Nat => Nat) m (fun (_ : Nat) (ih : Nat) => Nat.succ ih) n"
  assert_nf("(\{nat_add}) Nat.zero Nat.zero", "Nat.zero")
  let two = "Nat.succ (Nat.succ Nat.zero)"
  let five = "Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))"
  assert_nf("(\{nat_add}) (\{two}) (\{three})", five)

  let list_program = (
    #|inductive List (A : Type) : Type
    #|  | nil : List A
    #|  | cons : A -> List A -> List A
  )

  assert_nf_with_program(
    list_program,
    "List.rec Bool (fun _ : List Bool => Nat) Nat.zero (fun (h : Bool) (tl : List Bool) (ih : Nat) => Nat.succ ih) (List.nil Bool)",
    "Nat.zero"
  )

  // len [true, false] = 2
  assert_nf_with_program(
    list_program,
    "List.rec Bool (fun _ : List Bool => Nat) Nat.zero (fun (h : Bool) (tl : List Bool) (ih : Nat) => Nat.succ ih) (List.cons Bool true (List.cons Bool false (List.nil Bool)))",
    "Nat.succ (Nat.succ Nat.zero)"
  )

  let pair_program = (
    #|inductive Pair (A : Type) (B : Type) : Type
    #|  | mk : A -> B -> Pair A B
  )

  // Pair.fst (Pair.mk true zero) => true
  assert_nf_with_program(
    pair_program,
    "Pair.rec Bool Nat (fun _ : Pair Bool Nat => Bool) (fun (a : Bool) (b : Nat) => a) (Pair.mk Bool Nat true Nat.zero)",
    "true"
  )

  // Pair.snd (Pair.mk true zero) => zero
  assert_nf_with_program(
    pair_program,
    "Pair.rec Bool Nat (fun _ : Pair Bool Nat => Nat) (fun (a : Bool) (b : Nat) => b) (Pair.mk Bool Nat true Nat.zero)",
    "Nat.zero"
  )

  // False.rec: stuck (no constructor), normalises to itself
  {
    let false_program = "inductive False : Prop"
    let ctx = elab_program(false_program)
    let term = elab_term("fun P : Prop => False.rec (fun _ : False => P)", ctx=Some(ctx)).1
    // Should not crash
    let _ = ctx.normalise(term)
  }

  // Tree: two recursive arguments
  let tree_program =
    #|inductive Tree (A : Type) : Type
    #|  | leaf : A -> Tree A
    #|  | node : Tree A -> Tree A -> Tree A
    #|
    #|def Tree.size (A : Type) : Tree A -> Nat :=
    #|  Tree.rec A (fun _ => Nat)
    #|    (fun _ : A => Nat.succ Nat.zero)
    #|    (fun (l : Tree A) (r : Tree A) (lih : Nat) (rih : Nat) =>
    #|      Nat.rec (fun _ => Nat)
    #|        rih
    #|        (fun _ ih => Nat.succ ih) lih
    #|    )
    
  assert_nf_with_program(
    tree_program,
    "Tree.size Bool (Tree.leaf Bool true)",
    "Nat.succ Nat.zero"
  )

  assert_nf_with_program(
    tree_program,
    "Tree.size Nat (Tree.node Nat (Tree.leaf Nat Nat.zero) (Tree.leaf Nat (Nat.succ Nat.zero)))",
    "Nat.succ (Nat.succ Nat.zero)"
  )

  {
    let program = (
      #|def Nat.add (m : Nat) : Nat -> Nat :=
      #|  Nat.rec (fun _ => Nat) m (fun _ ih => Nat.succ ih)
      #|
      #|def three : Nat := Nat.succ (Nat.succ (Nat.succ Nat.zero))
      #|def five : Nat := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
      #|
      #|def Bool.not : Bool -> Bool :=
      #|  Bool.rec (fun _ => Bool) false true
    )

    try elab_program(program) |> ignore catch {
      err => fail("Invalid program: '\{err}'\n\{program}")
    }
  }

  {
    let program = (
      #|def Nat.pred : Nat -> Nat :=
      #|  Nat.rec (fun _ => Nat) Nat.zero (fun m _ => m)
    )
    
    let ctx = elab_program(program)
    let term = elab_term("Nat.pred (Nat.succ (Nat.succ (Nat.succ Nat.zero)))", ctx=Some(ctx)).1
    let result = ctx.normalise(term)
    let expected = elab_term("Nat.succ (Nat.succ Nat.zero)", ctx=Some(ctx)).1

    if !result.is_alpha_eq(expected) {
      fail("Expected Nat.pred 3 = 2, got '\{result}'")
    }
  }
}
