
pub enum Token {
  Lparen; Rparen; ThickArrow; Arrow; Star; Box; Fun; Forall; Let; Equal; In
  Colon; Comma; Dot; True; False; Nat(UInt); Var(String); Bool
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
    '*' => { self.advance(); Yay(Star) }
    '□' => { self.advance(); Yay(Box) }
    '=' => {
      self.advance()
      if self.consumes('>') {
        Yay(ThickArrow)
      } else {
        Yay(Equal)
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
          "forall" => Yay(Forall)
          "let" => Yay(Let)
          "in" => Yay(In)
          "true" => Yay(True)
          "false" => Yay(False)
          "Bool" => Yay(Bool)
          "Box" => Yay(Box)
          _ => {
            Yay(Var(identifier))
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

pub fn Lexer::tokenise(self: Lexer) -> Array[Token] raise LexerError {
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
  bound_vars: Array[String]
  free_vars: Map[String, FreeVarId]
  mut index: Int
}

pub suberror ParserError {
  UnexpectedToken(Token)
  Expected(expected~: Token, received~: Token)
  Message(String)
  UnexpectedEOF
} derive(Show, Eq)

pub fn Parser::new(tokens: Array[Token]) -> Parser {
  { tokens, bound_vars: [], free_vars: {}, index: 0 }
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
    Fun => self.parse_fun()
    Forall => self.parse_forall()
    Let => self.parse_let()
    _ => self.parse_app()
  }
}

fn Parser::parse_fun(self: Parser) -> Expr raise ParserError {
  self.expect(Fun)
  let v = self.expect_var()
  self.expect(Colon)
  let ty = self.parse_expr()
  self.expect(ThickArrow)
  self.bound_vars.push(v)
  defer { let _ = self.bound_vars.unsafe_pop() }
  let body = self.parse_expr()
  Fun(v, ty, body) 
}

fn Parser::parse_forall(self: Parser) -> Expr raise ParserError {
  self.expect(Forall)
  let v = self.expect_var()
  self.expect(Colon)
  let ty = self.parse_expr()
  self.expect(Comma)
  self.bound_vars.push(v)
  defer { let _ = self.bound_vars.unsafe_pop() }
  let rhs = self.parse_expr()
  Pi(Some(v), ty, rhs)
}

fn Parser::parse_let(self: Parser) -> Expr raise ParserError {
  self.expect(Let)
  let name = self.expect_var()
  self.expect(Colon)
  let ty = self.parse_expr()
  self.expect(Equal)
  let val = self.parse_expr()
  self.expect(In)
  self.bound_vars.push(name)
  defer { let _ = self.bound_vars.unsafe_pop() }
  let rhs = self.parse_expr()
  Let(name~, ty~, val~, rhs~)
}

fn Parser::parse_app(self: Parser) -> Expr raise ParserError {
  let mut lhs = self.parse_arrow()

  while (try? self.parse_arrow()) is Ok(rhs) {
    lhs = App(lhs, rhs)
  }

  lhs
}

fn Parser::parse_arrow(self: Parser) -> Expr raise ParserError {
  let lhs = self.parse_atom()

  if self.matches(Arrow) {
    self.advance()
    let rhs = self.parse_arrow()
    // non-dependent Pi
    Pi(None, lhs, rhs)
  } else {
    lhs
  }
}

fn Parser::parse_atom(self: Parser) -> Expr raise ParserError {
  match self.peek() {
    Var(v) => {
      self.advance();
      Var(v)
    }
    Bool => { self.advance(); Bool }
    Star => { self.advance(); Star }
    Box => { self.advance(); Box }
    True => { self.advance(); Const(Bool(true)) }
    False => { self.advance(); Const(Bool(false)) }
    Lparen => {
      self.advance()
      let lhs = self.parse_expr()

      match self.peek() {
        Colon => {
          self.advance()
          let ty = self.parse_expr()
          self.expect(Rparen)

          Ann(lhs, ty)
        }
        Rparen => { self.advance(); lhs }
        tok => raise Expected(expected=Rparen, received=tok)
      }
    }
    tok => raise UnexpectedToken(tok)
  }
}

pub fn parse(input: String) -> Expr raise {
  let tokens = Lexer::new(input).tokenise()
  Parser::new(tokens).parse()
}

test "parser" {
  fn expect_expr(input: String, expected_expr: Expr) raise {
    assert_eq(parse(input), expected_expr)
  }

  fn expect_Expr_err(input: String, expected_err: ParserError) raise {
    let tokens = Lexer::new(input).tokenise()

    try Parser::new(tokens).parse() catch {
      err => assert_eq(err, expected_err)
    } noraise {
      expr => fail("Expected error '\{expected_err}', got '\{expr}'")
    }
  }

  expect_expr("*", Star)
  expect_expr("□", Box)
  expect_expr("Box", Box)
  expect_expr("Bool", Bool)
  expect_expr("Bool -> Bool", Pi(None, Bool, Bool))
  expect_expr("Bool -> Bool -> Bool", Pi(None, Bool, Pi(None, Bool, Bool)))
  expect_expr("A", Var("A"))
  expect_expr("P", Var("P"))
  expect_expr("Q71", Var("Q71"))
  expect_expr("P -> Q -> (P -> Bool -> R)",  Pi(None, Var("P"), Pi(None, Var("Q"), Pi(None, Var("P"), Pi(None, Bool, Var("R"))))))
  expect_expr("true", Const(Bool(true)))
  expect_expr("false", Const(Bool(false)))
  expect_expr("x", Var("x"))
  expect_expr("(true: Bool)", Ann(Const(Bool(true)), Bool))
  expect_expr("fun x: Bool => x", Fun("x", Bool, Var("x")))
  expect_expr("fun x: Bool => y", Fun("x", Bool, Var("y")))
  expect_expr("fun x: A => x", Fun("x", Var("A"), Var("x")))
  expect_expr("fun x: A => (x: A)", Fun("x", Var("A"), Ann(Var("x"), Var("A"))))
  expect_expr("fun x: A => fun y: B => x", Fun("x", Var("A"), Fun("y", Var("B"), Var("x"))))
  expect_expr("f x", App(Var("f"), Var("x")))
  expect_expr("(fun x: Bool => x) true", App(Fun("x", Bool, Var("x")), Const(Bool(true))))
  expect_expr("(fun f: (Bool -> Bool) => f true) (fun x: Bool => x)", App(Fun("f", Pi(None, Bool, Bool), App(Var("f"), Const(Bool(true)))), Fun("x", Bool, Var("x"))))
  expect_expr("forall A: *, A", Pi(Some("A"), Star, Var("A")))
  expect_expr("forall b: Bool, b", Pi(Some("b"), Bool, Var("b")))
  expect_expr("fun T: * => forall x: T, T", Fun("T", Star, Pi(Some("x"), Var("T"), Var("T"))))
  expect_expr(
    "let id: forall A: *, A -> A = fun A: * => fun x: A => x in id Bool true",
    Let(
      name="id",
      ty=Pi(Some("A"), Star, Pi(None, Var("A"), Var("A"))),
      val=Fun("A", Star, Fun("x", Var("A"), Var("x"))),
      rhs=App(App(Var("id"), Bool), Const(Bool(true)))
    )
  )
  
  expect_Expr_err("true)", UnexpectedToken(Rparen))
}
