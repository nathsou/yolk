
pub enum Token {
  Lparen
  Rparen
  FatArrow
  Arrow
  Fun
  Colon
  True
  False
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
fn is_decimal_digit(c: Char) -> Bool {
  c >= '0' && c <= '9'
} 

fn is_alphanumeric(c: Char) -> Bool {
  is_alpha(c) || is_decimal_digit(c)
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
  UnboundVar(String)
  Message(String)
  UnexpectedEOF
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

fn Parser::expect_var(self: Parser) -> String raise ParserError {
  if self.peek() is Var(v) {
    self.advance()
    v
  } else {
    raise Message("Expected variable")
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
  let v = self.expect_var()
  self.variables.push(v)
  
  let ty = if self.matches(Colon) {
    self.advance()
    Some(self.parse_type())
  } else {
    None
  }

  self.expect(FatArrow)
  let body = self.parse_expr()
  let _ = self.variables.unsafe_pop()
  Expr::Abs(ty, body) 
}

fn Parser::parse_app(self: Parser) -> Expr raise ParserError {
  let mut lhs = self.parse_atom()

  while (try? self.parse_atom()) is Ok(rhs) {
    lhs = Expr::App(lhs, rhs)
  }

  lhs
}

fn Parser::parse_atom(self: Parser) -> Expr raise ParserError {
  match self.peek() {
    Var(v) => {
      self.advance();

      for i = self.variables.length() - 1; i >= 0; i = i - 1 {
        if self.variables[i] == v {
          return Expr::Var(self.variables.length() - 1 - i)
        }
      }

      raise UnboundVar(v)
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
  let mut lhs = self.parse_base_type()

  while self.matches(Arrow) {
    self.advance()
    let rhs = self.parse_base_type()
    lhs = Type::Arrow(lhs, rhs)
  }

  lhs
}

fn Parser::parse_base_type(self: Parser) -> Type raise ParserError {
  match self.peek() {
    Bool => { self.advance(); Type::Bool }
    Atom(a) => { self.advance(); Type::Atom(a) }
    Lparen => {
      self.advance()
      let ty = self.parse_type()
      self.expect(Rparen)
      ty
    }
    tok => raise UnexpectedToken(tok)
  }
}

pub fn parse(input: String) -> Expr raise {
  let tokens = Lexer::new(input).tokenize()
  Parser::new(tokens).parse()
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
  expect_type("Bool -> Bool -> Bool", Arrow(Arrow(Bool, Bool), Bool))
  expect_type("A", Atom("A"))
  expect_type("P", Atom("P"))
  expect_type("Q71", Atom("Q71"))
  expect_type(
    "P -> Q -> (P -> Bool -> R)",
    Arrow(Arrow(Atom("P"), Atom("Q")), Arrow(Arrow(Atom("P"), Bool), Atom("R"))),
  )

  // exprs
  expect_expr("true", Const(Bool(true)))
  expect_expr("false", Const(Bool(false)))
  expect_expr("fun x => x", Abs(None, Var(0)))
  expect_expr("fun x => fun y => x", Abs(None, Abs(None, Var(1))))
  expect_expr("fun x => fun y => y", Abs(None, Abs(None, Var(0))))
  expect_expr("fun x => fun y => fun z => x", Abs(None, Abs(None, Abs(None, Var(2)))))
  expect_expr("fun x => fun y => fun z => y", Abs(None, Abs(None, Abs(None, Var(1)))))
  expect_expr("fun x => fun y => fun z => z", Abs(None, Abs(None, Abs(None, Var(0)))))
  expect_expr("(fun x => x) true", App(Abs(None, Var(0)), Const(Bool(true))))
  expect_expr("(fun x => x) (fun x => x)", App(Abs(None, Var(0)), Abs(None, Var(0))))
  expect_expr("(fun x => x) (fun y => y)", App(Abs(None, Var(0)), Abs(None, Var(0))))
  expect_expr("(true: Bool)", Ann(Const(Bool(true)), Bool))
  expect_expr("(fun x => x: Bool -> Bool)", Ann(Abs(None, Var(0)), Arrow(Bool, Bool)))
  expect_expr(
    "(fun x => fun y => x: P -> Q -> P)",
    Ann(Abs(None, Abs(None, Var(1))), Arrow(Arrow(Atom("P"), Atom("Q")), Atom("P")))
  )
  expect_expr("fun x: Bool => x", Abs(Some(Bool), Var(0)))
  expect_expr(
    "fun p: P => fun q: Q => fun f: P -> Q -> R => (f p) q",
    Abs(Some(Atom("P")), Abs(Some(Atom("Q")), Abs(Some(Arrow(Arrow(Atom("P"), Atom("Q")), Atom("R"))), App(App(Var(0), Var(2)), Var(1))))) 
  )
  expect_expr(
    "fun f => (fun x => f (x x)) (fun x => f (x x))",
    Abs(None, App(Abs(None, App(Var(1), App(Var(0), Var(0)))), Abs(None, App(Var(1), App(Var(0), Var(0))))))
  )
  
  expect_expr_fail("x", UnboundVar("x"))
  expect_expr_fail("fun x => y", UnboundVar("y"))
  expect_expr_fail("true)", UnexpectedToken(Rparen))
}
