// https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus#Bidirectional_Type_Checking

pub suberror TypeCheckError {
  ExpectedArrowTypeForAbs(expr~: Expr, ty~: Type)
  InconsistentAbsAnnotation(expr~: Expr, ann~: Type, expected~: Type)
  LhsOfApplicationNotAFunction(expr~: Expr)
  TypeMismatch(expr~: Expr, expected~: Type, got~: Type)
  MissingLambdaArgAnnotation(expr~: Expr)
  UnboundVariable(DeBruijnIndex)
} derive(Show)

pub struct TypeContext {
  bindings: Array[Type] // Type
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
  println("infer \{expr}")
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
    Abs(Some(arg_ty), body) => {
      self.push_binding(arg_ty)
      let body_ty = self.infer(body)
      self.pop_binding()
      Arrow(arg_ty, body_ty)
    }
    Abs(None, _) => raise MissingLambdaArgAnnotation(expr~)  
  }
}

pub fn TypeContext::check(self: TypeContext, expr: Expr, ty: Type) -> Unit raise TypeCheckError {
  println("check \{expr}: \{ty}")
  match expr {
    Abs(arg_ann, body) => {
      match ty {
        Arrow(t0, t1) => {
          if arg_ann is Some(expected_arg_ty) && expected_arg_ty != t0 {
            raise InconsistentAbsAnnotation(expr~, ann=expected_arg_ty, expected=t0)
          }

          self.push_binding(t0)
          self.check(body, t1)
          self.pop_binding()
        }
        _ => raise ExpectedArrowTypeForAbs(expr~, ty~)
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
}
