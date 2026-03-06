// https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus#Bidirectional_Type_Checking

pub suberror TypeCheckError {
  ExpectedArrowTypeForAbs(expr~: Expr, ty~: Type)
  ExpectedTupleType(expr~: Expr, ty~: Type)
  InconsistentAbsAnnotation(expr~: Expr, ann~: Type, expected~: Type)
  LhsOfApplicationNotAFunction(expr~: Expr)
  TypeMismatch(expr~: Expr, expected~: Type, got~: Type)
  MissingLambdaArgAnnotation(expr~: Expr)
  TupleSizeMismatch(expr~: Expr, expected~: Int, got~: Int)
  ProjOutOfBounds(expr~: Expr, size~: Int)
  UnboundVariable(DeBruijnIndex)
} derive(Show)

pub struct TypeContext {
  bindings: Array[Type]
}

pub fn TypeContext::new() -> TypeContext {
  { bindings: [] }
}

fn TypeContext::lookup(self: TypeContext, index: DeBruijnIndex) -> Type? {
  self.bindings.get(self.bindings.length() - 1 - index)
}

fn TypeContext::push_binding(self: TypeContext, ty: Type) -> Unit {
  self.bindings.push(ty)
}

fn TypeContext::pop_binding(self: TypeContext) -> Unit {
  let _ = self.bindings.unsafe_pop()
}

pub fn TypeContext::infer(self: TypeContext, expr: Expr) -> Type raise TypeCheckError {
  match expr {
    Ann(e, ty) => { self.check(e, ty); ty }
    Const(c) => match c {
      Bool(_) => Bool
    }
    Var(idx) => {
      if self.lookup(idx) is Some(ty) {
        ty
      } else {
        raise UnboundVariable(idx)
      }
    }
    App(lhs, rhs) => {
      let lhs_ty = self.infer(lhs)
      match lhs_ty {
        Arrow(t0, t1) => {
          self.check(rhs, t0)
          t1
        }
        _ => raise LhsOfApplicationNotAFunction(expr~)
      }
    }
    Abs(_, Some(arg_ty), body) => {
      self.push_binding(arg_ty)
      defer self.pop_binding()
      let body_ty = self.infer(body)
      Arrow(arg_ty, body_ty)
    }
    Abs(_, None, _) => raise MissingLambdaArgAnnotation(expr~)  
    Tuple(elems) => {
      let elem_tys = elems.map(e => self.infer(e))
      Tuple(elem_tys)
    }
    Proj(lhs, idx) => {
      let lhs_ty = self.infer(lhs)
      if lhs_ty is Tuple(tys) {
        let idx_int = idx.reinterpret_as_int()
        if idx_int >= tys.length() {
          raise ProjOutOfBounds(expr~, size=tys.length())
        }
        
        tys[idx_int]
      } else {
        raise ExpectedTupleType(expr~, ty=lhs_ty)
      }
    }
  }
}

pub fn TypeContext::check(self: TypeContext, expr: Expr, ty: Type) -> Unit raise TypeCheckError {
  match expr {
    Abs(_, arg_ann, body) => {
      match ty {
        Arrow(t0, t1) => {
          if arg_ann is Some(expected_arg_ty) && expected_arg_ty != t0 {
            raise InconsistentAbsAnnotation(expr~, ann=expected_arg_ty, expected=t0)
          }

          self.push_binding(t0)
          defer self.pop_binding()
          self.check(body, t1)
        }
        _ => raise ExpectedArrowTypeForAbs(expr~, ty~)
      }
    }
    Tuple(elems) => {
      match ty {
        Tuple(tys) => {
          if elems.length() != tys.length() {
            raise TupleSizeMismatch(expr~, expected=tys.length(), got=elems.length())
          }

          for expr, ty in elems.zip_to_iter2(tys) {
            self.check(expr, ty)
          }
        }
        _ => raise ExpectedTupleType(expr~, ty~)
      }
    }
    _ => {
      let inferred_ty = self.infer(expr)
      if inferred_ty != ty {
        raise TypeMismatch(expr~, expected=ty, got=inferred_ty)
      }
    }
  }
}

pub fn proove(prop: String, proof: String) -> Unit raise {
  try {
    let prop_ty = parse_type(prop)
    let proof_term = parse(proof)
    let ctx = TypeContext::new()
    ctx.check(proof_term, prop_ty)
  } catch {
    err => {
      fail("Could not prove '\{prop}' with '\{proof}': \{err}")
    }
  }
}

test "check" {
  fn assert_type(expr: String, ty: String) -> Unit raise {
    let ctx = TypeContext::new()
    ctx.check(parse(expr), parse_type(ty))
  }

  fn assert_type_err(expr: String, ty: String) -> Unit raise {
    try assert_type(expr, ty) catch {
      _ => () 
    } noraise {
      _ => raise Failure::Failure("Expected type error") 
    }
  }

  fn assert_infer_err(expr: String) -> Unit raise {
    let ctx = TypeContext::new()
    try ctx.infer(parse(expr)) catch {
      _ => () 
    } noraise {
      ty => fail("Expected inferrence error for expr: \{expr}, got type: \{ty}") 
    }
  }

  assert_type("true", "Bool")
  assert_type("false", "Bool")
  assert_type("(true, false)", "(Bool, Bool)")
  assert_type("(fun x: A => x, true)", "(A -> A, Bool)")
  assert_type("((fun x => x, true): (A -> A, Bool))", "(A -> A, Bool)")
  assert_type("(true, fun x: A => x).0", "Bool")
  assert_type("(true, true, true, true).3", "Bool")
  assert_type("(true, fun x: A => x).1", "A -> A")
  assert_type("(true, fun x: (Bool, (Bool, Bool)) => x.1).1 (true, (false, false))", "(Bool, Bool)")
  assert_type("((fun x => x.0): (A, B) -> A)", "(A, B) -> A")
  assert_type("fun x: P => x", "P -> P")
  assert_type("fun x => fun y => x", "P -> Q -> P")
  assert_type("fun x: P => fun y => x", "P -> Q -> P")
  assert_type("fun x: P => fun y: Q => x", "P -> Q -> P")
  assert_type("(fun x: Bool => x) true", "Bool")
  assert_type("((fun x => fun y => x): P -> Q -> P)", "P -> Q -> P")
  assert_type("(fun x: Bool => fun y: Bool => x) true false", "Bool")

  assert_type_err("fun x: P => fun y: P => x", "P -> Q -> P")
  assert_type_err("(fun x: P => x) true", "Bool")
  assert_type_err("fun x => x x", "P -> P")

  // self-application is not typeable
  assert_infer_err("fun x: P -> P => x x")
  assert_infer_err("fun x: P => x x")
  assert_infer_err("(true, false).2")
}

test "proofs" {
  // A => B => (A ^ B)
  proove("A -> B -> (A, B)", "fun x => fun y => (x, y)")

  // S combinator
  proove("(A -> B -> C) -> (A -> B) -> A -> C", "fun f => fun g => fun x => f x (g x)")

  // transitivity of implication
  proove("(A -> B) -> (B -> C) -> A -> C", "fun f => fun g => fun x => g (f x)")
  
  // (A ^ B) => A
  proove("(A, B) -> A", "fun x => x.0")
  
  // (A ^ B) => B
  proove("(A, B) -> B", "fun x => x.1")

  // (A ^ B) => (B ^ A) (commutativity of conjunction)
  proove("(A, B) -> (B, A)", "fun x => (x.1, x.0)")

  // (A ^ B) ^ C => A ^ (B ^ C) (associativity of conjunction)
  proove("((A, B), C) -> (A, (B, C))", "fun x => (x.0.0, (x.0.1, x.1))")

  // ((A -> B) ^ (A -> C)) -> A -> B ^ C (distributivity of conjunction)
  proove("(A -> B, A -> C) -> A -> (B, C)", "fun p => fun x => (p.0 x, p.1 x)")
}
