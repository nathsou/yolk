// Syntax Term from the parser
pub enum STerm {
  Sort(UniverseLevel)
  Bool
  Const(Const)
  Var(String)
  App(STerm, STerm)
  Fun(String, STerm, STerm)
  Pi(String?, STerm, STerm)
  Let(String, STerm, STerm)
  Ann(STerm, STerm)
} derive(Eq)

pub enum Decl[T] {
  Axiom(T) // type
  Definition(T, T) // type, body
} derive(Eq)

pub enum TopLevel[T] {
  Declaration(Name, Decl[T])
  Command(String, Array[T])
} derive(Eq)

pub struct Program[T](Array[TopLevel[T]])

pub enum Name {
  Leaf(String)
  Path(String, Name)
} derive(Eq, Hash)

pub impl Show for Name with output(self: Name, logger: &Logger) {
  match self {
    Leaf(s) => logger.write_string(s)
    Path(s, parent) => {
      parent.output(logger)
      logger.write_char('.')
      logger.write_string(s)
    }
  }
}

pub fn Name::from(path: Array[String]) -> Name? {
  if path.length() == 0 {
    None
  } else {
    let mut name = Leaf(path[0])

    for i in 1..<path.length() {
      name = Path(path[i], name)
    }

    Some(name)
  }
}

pub fn show_sort(u: UniverseLevel) -> String {
  match u {
    0 => "Prop"
    1 => "Type" // Type 0
    _ => "Type \{u - 1}"
  }
}

fn STerm::parens(self: STerm, wrap~: Bool, logger: &Logger) -> Unit {
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
    Sort(u) => logger.write_string(show_sort(u))
    Bool => logger.write_string("Bool")
    Var(v) => logger.write_string(v)
    Const(c) => c.output(logger)
    App(lhs, rhs) => {
      let lhs_needs_parens = lhs is (Fun(_) | Pi(_) | Let(_) | Ann(_))
      let rhs_needs_parens = rhs is (Fun(_) | Pi(_) | Let(_) | Ann(_))
      lhs.parens(wrap=lhs_needs_parens, logger)
      logger.write_char(' ')
      rhs.parens(wrap=rhs_needs_parens, logger)
    }
    Fun(x, ty, body) => {
      logger.write_string("fun ")
      logger.write_string(x)
      logger.write_string(" : ")
      ty.output(logger)
      logger.write_string(" => ")
      body.output(logger)
    }
    Pi(Some(x), a, b) => {
      logger.write_string("forall ")
      logger.write_string(x)
      logger.write_string(" : ")
      a.output(logger)
      logger.write_string(", ")
      b.output(logger)
    }
    Pi(None, a, b) => {
      a.parens(wrap=a is Pi(_), logger)
      logger.write_string(" -> ")
      b.output(logger)
    }
    Let(x, val, body) => {
      logger.write_string("let ")
      logger.write_string(x)
      logger.write_string(" := ")
      val.output(logger)
      logger.write_string(" in ")
      body.output(logger)
    }
    Ann(e, ty) => {
      e.parens(wrap=e is (App(_) | Fun(_) | Pi(_) | Let(_)), logger)
      logger.write_string(": ")
      ty.output(logger)
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
