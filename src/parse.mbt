
pub enum Token {
  Lparen
  Rparen
  FatArrow
  Arrow
  Fun
  Colon
  Comma
  Dot
  True
  False
  Nat(UInt)
  Var(String)
  Bool
  Atom(String)
} derive(Show, Eq)

pub suberror LexerError {
  UnexpectedChar(char~: Char, index~: Int)
} derive(Show)

pub(all) struct Lexer {
  input: Array[Char]
  mut index: Int
}

pub fn Lexer::new(input: String) -> Lexer {
  { input: input.to_array(), index: 0 }
}

fn Lexer::advance(self: Lexer) -> Unit {
  self.index += 1
}

fn is_alpha(c: Char) -> Bool {
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
}

fn is_digit(c: Char) -> Bool {
  c >= '0' && c <= '9'
}

fn parse_digit(c: Char) -> UInt {
  c.to_uint() - 48
}

fn is_alphanumeric(c: Char) -> Bool {
  is_alpha(c) || is_digit(c)
}

fn Lexer::peek(self: Lexer) -> Char {
  self.input[self.index]
}

fn Lexer::matches(self: Lexer, char: Char) -> Bool {
  self.peek() == char
}

fn Lexer::consumes(self: Lexer, char: Char) -> Bool {
  if self.matches(char) {
    self.index += 1
    true
  } else {
    false
  }
}

fn is_whitespace(c: Char) -> Bool {
  match c {
    ' ' => true
    '\t' => true
    '\n' => true
    '\r' => true
    _ => false
  }
}

fn Lexer::skip_whitespaces(self: Lexer) -> Unit {
  while self.index < self.input.length() && is_whitespace(self.peek()) {
    self.index += 1
  }
}

fn Lexer::parse_identifier(self: Lexer) -> String {
  let identifier = StringBuilder::new()
  
  for i in self.index..<self.input.length() {
    let char = self.input[i]

    if is_alphanumeric(char) {
      identifier.write_char(char)
      self.advance()
    } else {
      break
    }
  }

  identifier.to_string()
}

priv enum LexerResult {
  Yay(Token)
  Grr(LexerError)
  EOF
}

fn Lexer::next(self: Lexer) -> LexerResult {
  self.skip_whitespaces()

  if self.index >= self.input.length() {
    return EOF
  }

  let char = self.peek()

  match char {
    '(' => { self.advance(); Yay(Lparen) }
    ')' => { self.advance(); Yay(Rparen) }
    ':' => { self.advance(); Yay(Colon) }
    ',' => { self.advance(); Yay(Comma) }
    '.' => { self.advance(); Yay(Dot) }
    '=' => {
      self.advance()
      if self.consumes('>') {
        Yay(FatArrow)
      } else {
        Grr(UnexpectedChar(char~, index=self.index))
      }
    }
    '-' => {
      self.advance()
      if self.consumes('>') {
        Yay(Arrow)
      } else {
        Grr(UnexpectedChar(char~, index=self.index))
      }
    }
    _ => {
      if is_alpha(char) {
        let identifier = self.parse_identifier()

        match identifier {
          "fun" => Yay(Fun)
          "true" => Yay(True)
          "false" => Yay(False)
          "Bool" => Yay(Bool)
          _ => {
            if char.is_ascii_lowercase() {
              Yay(Var(identifier))
            } else {
              Yay(Atom(identifier))
            }
          }
        }
      } else if is_digit(char) {
          let mut n = parse_digit(char)
          self.advance()

          while self.index < self.input.length() && is_digit(self.input[self.index]) {
            n *= 10
            n += parse_digit(self.input[self.index])
            self.advance()
          }

          Yay(Nat(n))
      } else {
        Grr(UnexpectedChar(char~, index=self.index))
      }
    }
  }
}

pub fn Lexer::tokenize(self: Lexer) -> Array[Token] raise LexerError {
  let tokens = []

  while true {
    match self.next() {
      Yay(token) => tokens.push(token)
      Grr(error) => raise error
      EOF => break
    }
  }

  tokens
}

pub struct Parser {
  tokens: Array[Token]
  variables: Array[String]
  mut index: Int
}

pub suberror ParserError {
  UnexpectedToken(Token)
  Expected(expected~: Token, received~: Token)
  Message(String)
  UnexpectedEOF
  ExpectedNat(Token)
} derive(Show, Eq)

pub fn Parser::new(tokens: Array[Token]) -> Parser {
  { tokens, variables: [], index: 0 }
}

fn Parser::peek(self: Parser) -> Token raise ParserError {
  if self.tokens.get(self.index) is Some(token) {
    token
  } else {
    raise UnexpectedEOF 
  }
}

fn Parser::advance(self: Parser) -> Unit {
  self.index += 1
}

fn Parser::matches(self: Parser, token: Token) -> Bool {
  self.index < self.tokens.length() && self.tokens[self.index] == token
}

fn Parser::expect(self: Parser, expected: Token) -> Unit raise ParserError {
  let token = self.peek()

  if token == expected {
    self.advance()
  } else {
    raise Expected(expected~, received=token)
  }
}

fn Parser::expect_BoundVar(self: Parser) -> String raise ParserError {
  if self.peek() is Var(v) {
    self.advance()
    v
  } else {
    raise Message("Expected BoundVariable")
  }
}

pub fn Parser::parse(self: Parser) -> Expr raise ParserError {
  let expr = self.parse_expr()

  if self.index != self.tokens.length() {
    raise UnexpectedToken(self.tokens[self.index])
  }

  expr
}

fn Parser::parse_expr(self: Parser) -> Expr raise ParserError {
  match self.peek() {
    Fun => self.parse_abs()
    _ => self.parse_app()
  }
}

fn Parser::parse_abs(self: Parser) -> Expr raise ParserError {
  self.expect(Fun)
  let v = self.expect_BoundVar()
  self.variables.push(v)
  defer { let _ = self.variables.unsafe_pop() }
  
  let ty = if self.matches(Colon) {
    self.advance()
    Some(self.parse_type())
  } else {
    None
  }

  self.expect(FatArrow)
  let body = self.parse_expr()
  Expr::Abs(v, ty, body) 
}

fn Parser::parse_app(self: Parser) -> Expr raise ParserError {
  let mut lhs = self.parse_proj()

  while (try? self.parse_proj()) is Ok(rhs) {
    lhs = Expr::App(lhs, rhs)
  }

  lhs
}

fn Parser::parse_proj(self: Parser) -> Expr raise ParserError {
  let mut lhs = self.parse_atom()

  while self.matches(Dot) {
    self.advance()

    match self.peek() {
      Nat(idx) => {
        self.advance()
        lhs = Proj(lhs, idx)
      }
      tok => raise ExpectedNat(tok)
    }
  }

  lhs
}

fn Parser::parse_atom(self: Parser) -> Expr raise ParserError {
  match self.peek() {
    Var(v) => {
      self.advance();

      for i = self.variables.length() - 1; i >= 0; i = i - 1 {
        if self.variables[i] == v {
          return Expr::BoundVar(self.variables.length() - 1 - i)
        }
      }

      FreeVar(v)
    }
    True => { self.advance(); Expr::Const(Bool(true)) }
    False => { self.advance(); Expr::Const(Bool(false)) }
    Lparen => {
      self.advance()
      let expr = self.parse_expr()

      match self.peek() {
        Colon => {
          self.advance()
          let ty = self.parse_type()
          self.expect(Rparen)
          Expr::Ann(expr, ty)
        }
        Comma => {
          let elems = [expr]

          while self.matches(Comma) {
            self.advance()
            elems.push(self.parse_expr())
          }

          self.expect(Rparen)
          Tuple(elems)
        }
        Rparen => { self.advance(); expr }
        tok => raise Expected(expected=Rparen, received=tok)
      }
    }
    tok => raise UnexpectedToken(tok)
  }
}

fn Parser::parse_type(self: Parser) -> Type raise ParserError {
  self.parse_arrow_type() 
}

fn Parser::parse_arrow_type(self: Parser) -> Type raise ParserError {
  let lhs = self.parse_base_type()

  if self.matches(Arrow) {
    self.advance()
    let rhs = self.parse_arrow_type()
    Arrow(lhs, rhs) 
  } else {
    lhs
  }
}

fn Parser::parse_base_type(self: Parser) -> Type raise ParserError {
  match self.peek() {
    Bool => { self.advance(); Type::Bool }
    Atom(a) => { self.advance(); Type::Atom(a) }
    Lparen => {
      self.advance()
      let ty = self.parse_type()

      match self.peek() {
        Comma => {
          let tys = [ty]

          while self.matches(Comma) {
            self.advance()
            tys.push(self.parse_type())
          }

          self.expect(Rparen)

          Tuple(tys)
        } 
        Rparen => { self.advance(); ty }
        tok => raise UnexpectedToken(tok)
      }
    }
    tok => raise UnexpectedToken(tok)
  }
}

pub fn parse(input: String) -> Expr raise {
  let tokens = Lexer::new(input).tokenize()
  Parser::new(tokens).parse()
}

pub fn parse_type(input: String) -> Type raise {
  let tokens = Lexer::new(input).tokenize()
  let parser = Parser::new(tokens)
  let ty = parser.parse_type()

  if parser.index != parser.tokens.length() {
    raise UnexpectedToken(parser.tokens[parser.index])
  }

  ty
}

test "parser" {
  fn expect_expr(input: String, expected_expr: Expr) raise {
    assert_eq(parse(input), expected_expr)
  }

  fn expect_expr_fail(input: String, expected_err: ParserError) raise {
    let tokens = Lexer::new(input).tokenize()

    try Parser::new(tokens).parse() catch {
      err => assert_eq(err, expected_err)
    } noraise {
      expr => fail("Expected error '\{expected_err}', got '\{expr}'")
    }
  }

  fn expect_type(input : String, expected_type : Type) raise {
    let tokens = Lexer::new(input).tokenize()
    let actual_type = Parser::new(tokens).parse_type()
    assert_eq(actual_type, expected_type)
  }

  // types
  expect_type("Bool", Bool)
  expect_type("Bool -> Bool", Arrow(Bool, Bool))
  expect_type("Bool -> Bool -> Bool", Arrow(Bool, Arrow(Bool, Bool)))
  expect_type("(Bool, Bool)", Tuple([Bool, Bool]))
  expect_type("(A, B, C, D, E, F)", Tuple([Atom("A"), Atom("B"), Atom("C"), Atom("D"), Atom("E"), Atom("F")]))
  expect_type("(A, B, (C, (D, E)))", Tuple([Atom("A"), Atom("B"), Tuple([Atom("C"), Tuple([Atom("D"), Atom("E")])])]))
  expect_type("A", Atom("A"))
  expect_type("P", Atom("P"))
  expect_type("Q71", Atom("Q71"))
  expect_type(
    "P -> Q -> (P -> Bool -> R)",
    Arrow(Atom("P"), Arrow(Atom("Q"), Arrow(Atom("P"), Arrow(Bool, Atom("R")))))
  )
  expect_type("(A -> B, (Bool -> Q, Bool))", Tuple([Arrow(Atom("A"), Atom("B")), Tuple([Arrow(Bool, Atom("Q")), Bool])]))

  // exprs
  expect_expr("true", Const(Bool(true)))
  expect_expr("false", Const(Bool(false)))
  expect_expr("x", FreeVar("x"))
  expect_expr("(z1: (Bool, A -> B))", Ann(FreeVar("z1"), Tuple([Bool, Arrow(Atom("A"), Atom("B"))])))
  expect_expr("fun x => y", Abs("x", None, FreeVar("y")))
  expect_expr("(true, false)", Tuple([Const(Bool(true)), Const(Bool(false))]))
  expect_expr("(true, (false, false))", Tuple([Const(Bool(true)), Tuple([Const(Bool(false)), Const(Bool(false))])]))
  expect_expr("(true, false, false)", Tuple([Const(Bool(true)), Const(Bool(false)), Const(Bool(false))]))
  expect_expr("(true, false).0", Proj(Tuple([Const(Bool(true)), Const(Bool(false))]), 0))
  expect_expr("(true, (false, true)).1.0", Proj(Proj(Tuple([Const(Bool(true)), Tuple([Const(Bool(false)), Const(Bool(true))])]), 1), 0))
  expect_expr("fun x => x", Abs("x", None, BoundVar(0)))
  expect_expr("fun x: A => x", Abs("x", Some(Atom("A")), BoundVar(0)))
  expect_expr("fun x: A => (x: A)", Abs("x", Some(Atom("A")), Ann(BoundVar(0), Atom("A"))))
  expect_expr("fun x => fun y => x", Abs("x", None, Abs("y", None, BoundVar(1))))
  expect_expr("fun x => fun y => y", Abs("x", None, Abs("y", None, BoundVar(0))))
  expect_expr("fun x => fun y => fun z => x", Abs("x", None, Abs("y", None, Abs("z", None, BoundVar(2)))))
  expect_expr("fun x => fun y => fun z => y", Abs("x", None, Abs("y", None, Abs("z", None, BoundVar(1)))))
  expect_expr("fun x => fun y => fun z => z", Abs("x", None, Abs("y", None, Abs("z", None, BoundVar(0)))))
  expect_expr("(fun x => x) true", App(Abs("x", None, BoundVar(0)), Const(Bool(true))))
  expect_expr("(fun x => x) (fun x => x)", App(Abs("x", None, BoundVar(0)), Abs("x", None, BoundVar(0))))
  expect_expr("(fun x => x) (fun y => y)", App(Abs("x", None, BoundVar(0)), Abs("y", None, BoundVar(0))))
  expect_expr("(true: Bool)", Ann(Const(Bool(true)), Bool))
  expect_expr("(fun x => x: Bool -> Bool)", Ann(Abs("x", None, BoundVar(0)), Arrow(Bool, Bool)))
  expect_expr(
    "(fun x => fun y => x: P -> Q -> P)",
    Ann(Abs("x", None, Abs("y", None, BoundVar(1))), Arrow(Atom("P"), Arrow(Atom("Q"), Atom("P"))))
  )
  expect_expr("fun x: Bool => x", Abs("x", Some(Bool), BoundVar(0)))
  expect_expr(
    "fun p: P => fun q: Q => fun f: P -> Q -> R => (f p) q",
    Abs("p", Some(Atom("P")), Abs("q", Some(Atom("Q")), Abs("f", Some(Arrow(Atom("P"), Arrow(Atom("Q"), Atom("R")))), App(App(BoundVar(0), BoundVar(2)), BoundVar(1)))))
  )
  expect_expr(
    "fun f => (fun x => f (x x)) (fun x => f (x x))",
    Abs("f", None, App(Abs("x", None, App(BoundVar(1), App(BoundVar(0), BoundVar(0)))), Abs("x", None, App(BoundVar(1), App(BoundVar(0), BoundVar(0))))))
  )
  expect_expr("fun x => fun y => (x, y)", Abs("x", None, Abs("y", None, Tuple([BoundVar(1), BoundVar(0)]))))
  
  expect_expr_fail("true)", UnexpectedToken(Rparen))
}
