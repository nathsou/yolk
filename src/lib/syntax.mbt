// Syntax Term from the parser
pub enum STerm {
  Sort(UniverseLevel)
  Var(Name)
  App(STerm, STerm)
  Fun(String, STerm?, STerm)
  Pi(String?, STerm?, STerm)
  Let(String, STerm?, STerm, STerm)
  Ann(STerm, STerm)
  Match(scrutinee~: STerm, motive~: STerm?, cases~: Array[MatchCase])
} derive(Eq)

pub enum Decl[T] {
  Axiom(T) // type
  Definition(T, T) // type, body
  Theorem(T, T) // type, proof term
  Inductive(InductiveDecl[T])
  Constructor(
    ind~: InductiveDecl[T],
    ty~: T
  )
  Recursor(
    ind~: InductiveDecl[T],
    num_params~: Int,
    num_indices~: Int,
    num_minors~: Int,
    rules~: Array[RecRule],
    ty~: T,
  )
} derive(Eq)

pub struct InductiveDecl[T] {
  params: Array[(String, T)]
  constructors: Array[(String, T)]
  ty: T
} derive(Eq)

pub struct MatchCase {
  ctor: String
  args: Array[String]
  body: STerm
} derive(Eq)

pub fn[T] Decl::ty(self: Decl[T]) -> T {
  match self {
    Axiom(ty) => ty
    Definition(ty, _) => ty
    Theorem(ty, _) => ty
    Inductive({ ty, .. }) => ty
    Constructor(ty~, ..) => ty
    Recursor(ty~, ..) => ty
  }
}

pub struct RecRule {
  ctor: Name
  num_fields: Int
  rec_fields: Array[Int]
} derive(Eq)

pub fn Decl::mk_inductive(
  params~: Array[(String, STerm)],
  arity~: STerm,
  constructors~: Array[(String, STerm)],
) -> Decl[STerm] {
  let mut ty = arity

  for param in params.rev_iter() {
    ty = Pi(Some(param.0), Some(param.1), ty)
  }

  Inductive({ params, constructors, ty })
}

pub enum TopLevel[T] {
  Declaration(Name, Decl[T])
  Command(String, Array[T])
} derive(Eq)

pub struct Program[T](Array[TopLevel[T]])

pub enum Name {
  Leaf(String)
  Path(Name, String)
} derive(Eq, Hash)

pub impl Show for Name with output(self: Name, logger: &Logger) {
  match self {
    Leaf(s) => logger.write_string(s)
    Path(l, r) => {
      logger.write_object(l)
      logger.write_char('.')
      logger.write_string(r)
    }
  }
}

pub fn Name::from(path: Array[String]) -> Name? {
  if path.length() == 0 {
    None
  } else {
    let mut name = Leaf(path[0])

    for i in 1..<path.length() {
      name = Path(name, path[i])
    }

    Some(name)
  }
}

pub fn Name::root(self: Name) -> String {
  match self {
    Leaf(root) => root
    Path(lhs, _) => lhs.root()
  }
}

fn STerm::parens(self: STerm, wrap: Bool, logger: &Logger) -> Unit {
  if wrap {
    logger.write_char('(')
  }
  self.output(logger)
  if wrap {
    logger.write_char(')')
  }
}

pub impl Show for STerm with output(self: STerm, logger: &Logger) {
  match self {
    Sort(l) => logger.write_object(l)
    Var(v) => logger.write_object(v)
    App(lhs, rhs) => {
      let lhs_needs_parens = lhs is (Fun(_) | Pi(_) | Let(_) | Ann(_))
      let rhs_needs_parens = rhs is (Fun(_) | Pi(_) | Let(_) | Ann(_))
      lhs.parens(lhs_needs_parens, logger)
      logger.write_char(' ')
      rhs.parens(rhs_needs_parens, logger)
    }
    Fun(x, Some(ty), body) => {
      logger.write_string("fun ")
      logger.write_string(x)
      logger.write_string(" : ")
      ty.output(logger)
      logger.write_string(" => ")
      body.output(logger)
    }
    Fun(x, None, body) => {
      logger.write_string("fun ")
      logger.write_string(x)
      logger.write_string(" => ")
      body.output(logger)
    }
    Pi(Some(x), Some(a), b) => {
      logger.write_string("forall ")
      logger.write_string(x)
      logger.write_string(" : ")
      a.output(logger)
      logger.write_string(", ")
      b.output(logger)
    }
    Pi(Some(x), None, b) => {
      logger.write_string("forall ")
      logger.write_string(x)
      logger.write_string(", ")
      b.output(logger)
    }
    Pi(None, Some(a), b) => {
      a.parens(a is Pi(_), logger)
      logger.write_string(" -> ")
      b.parens(b is Pi(Some(_), _, _), logger)
    }
    Pi(None, None, _) => ()
    Let(x, ty, val, body) => {
      logger.write_string("let ")
      logger.write_string(x)
      if ty is Some(t) {
        logger.write_string(" : ")
        t.output(logger)
      }
      logger.write_string(" := ")
      val.output(logger)
      logger.write_string(" in ")
      body.output(logger)
    }
    Ann(e, ty) => {
      e.parens(e is (App(_) | Fun(_) | Pi(_) | Let(_)), logger)
      logger.write_string(": ")
      ty.output(logger)
    }
    Match(scrutinee~, motive~, cases~) => {
      logger.write_string("match ")
      scrutinee.parens(scrutinee is (App(_) | Fun(_) | Pi(_) | Let(_)), logger)
      
      if motive is Some(m) {
        logger.write_string(" return ")
        m.parens(m is (App(_) | Fun(_) | Pi(_) | Let(_)), logger)
      }

      logger.write_char('\n')

      for case in cases {
        logger.write_string("  | ")
        logger.write_string(case.ctor)

        for arg in case.args {
          logger.write_char(' ')
          logger.write_string(arg)
        }

        logger.write_string(" => ")
        case.body.output(logger)
        logger.write_char('\n')
      }
    }
  }
}

pub impl[T: Show] Show for TopLevel[T] with output(self: TopLevel[T], logger: &Logger) {
  match self {
    Declaration(name, Axiom(ty)) => {
      logger.write_string("axiom ")
      logger.write_object(name)
      logger.write_string(" : ")
      logger.write_object(ty)
    }
    Declaration(name, Definition(ty, val)) => {
      logger.write_string("def ")
      logger.write_object(name)
      logger.write_string(" : ")
      logger.write_object(ty)
      logger.write_string(" := ")
      logger.write_object(val)
    }
    Declaration(name, Theorem(ty, proof)) => {
      logger.write_string("theorem ")
      logger.write_object(name)
      logger.write_string(" : ")
      logger.write_object(ty)
      logger.write_string(" := ")
      logger.write_object(proof)
    }
    Declaration(name, Inductive({ constructors, ty, .. })) => {
      logger.write_string("inductive ")
      logger.write_object(name)
      logger.write_string(" : ")
      logger.write_object(ty)
      logger.write_char('\n')

      for ctor in constructors {
        logger.write_string("  | ")
        logger.write_string(ctor.0)
        logger.write_string(" : ")
        logger.write_object(ctor.1)
        logger.write_char('\n')
      }
    }
    Declaration(name, Constructor(ind=_, ty~)) => {
      logger.write_string("constructor ")
      logger.write_object(name)
      logger.write_string(" : ")
      logger.write_object(ty)
    }
    Declaration(name, Recursor(ty~, ..)) => {
      logger.write_string("recursor ")
      logger.write_object(name)
      logger.write_string(" : ")
      logger.write_object(ty)
    }
    Command(cmd, args) => {
      logger.write_char('#')
      logger.write_string(cmd)
      
      for arg in args {
        logger.write_char(' ')
        logger.write_object(arg)
      }
    }
  }
}

pub impl[T: Show] Show for Program[T] with output(self: Program[T], logger: &Logger) {
  logger.write_iter(self.0.iter(), sep="\n\n", prefix="", suffix="")
}
