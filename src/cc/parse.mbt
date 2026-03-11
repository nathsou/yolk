
pub enum Token {
  Lparen; Rparen; ThickArrow; Arrow; Star; Box; Fun; Forall; Let; In; Equal
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

pub fn Parser::parse(self: Parser) -> Term raise ParserError {
  let expr = self.parse_term()

  if self.index != self.tokens.length() {
    raise UnexpectedToken(self.tokens[self.index])
  }

  expr
}

fn Parser::parse_term(self: Parser) -> Term raise ParserError {
  match self.peek() {
    Fun => self.parse_fun()
    Forall => self.parse_forall()
    Let => self.parse_let()
    _ => self.parse_app()
  }
}

fn Parser::parse_fun(self: Parser) -> Term raise ParserError {
  self.expect(Fun)
  let v = self.expect_var()
  self.expect(Colon)
  let ty = self.parse_term()
  self.expect(ThickArrow)
  self.bound_vars.push(v)
  defer { let _ = self.bound_vars.unsafe_pop() }
  let body = self.parse_term()
  Lam(v, ty, body) 
}

fn Parser::parse_forall(self: Parser) -> Term raise ParserError {
  self.expect(Forall)
  let v = self.expect_var()
  self.expect(Colon)
  let ty = self.parse_term()
  self.expect(Comma)
  self.bound_vars.push(v)
  defer { let _ = self.bound_vars.unsafe_pop() }
  let rhs = self.parse_term()
  Pi(Some(v), ty, rhs)
}

fn Parser::parse_let(self: Parser) -> Term raise ParserError {
  self.expect(Let)
  let v = self.expect_var()
  self.expect(Equal)
  let val = self.parse_term()
  self.expect(In)
  self.bound_vars.push(v)
  defer { let _ = self.bound_vars.unsafe_pop() }
  let body = self.parse_term()
  Let(v, val, body)
}

fn Parser::parse_app(self: Parser) -> Term raise ParserError {
  let mut lhs = self.parse_arrow()

  while (try? self.parse_arrow()) is Ok(rhs) {
    lhs = App(lhs, rhs)
  }

  lhs
}

fn Parser::parse_arrow(self: Parser) -> Term raise ParserError {
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

fn Parser::parse_atom(self: Parser) -> Term raise ParserError {
  match self.peek() {
    Var(v) => {
      self.advance();

      for i = self.bound_vars.length() - 1; i >= 0; i = i - 1 {
        if self.bound_vars[i] == v {
          return BoundVar((self.bound_vars.length() - 1 - i).reinterpret_as_uint())
        }
      }

      let var_id: FreeVarId = if self.free_vars.get(v) is Some(var_id) {
        var_id
      } else {
        let var_id = self.free_vars.length().reinterpret_as_uint()
        self.free_vars[v] = var_id
        var_id
      }

      FreeVar(v, var_id)
    }
    Bool => { self.advance(); Bool }
    Star => { self.advance(); Star }
    Box => { self.advance(); Box }
    True => { self.advance(); Const(Bool(true)) }
    False => { self.advance(); Const(Bool(false)) }
    Lparen => {
      self.advance()
      let lhs = self.parse_term()

      match self.peek() {
        Colon => {
          self.advance()
          let ty = self.parse_term()
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

test "parser" {
  fn parse(input: String) -> Term raise {
    let tokens = Lexer::new(input).tokenise()
    Parser::new(tokens).parse()
  }

  fn expect_term(input: String, expected_term: Term) raise {
    assert_eq(parse(input), expected_term)
  }

  fn expect_term_err(input: String, expected_err: ParserError) raise {
    let tokens = Lexer::new(input).tokenise()

    try Parser::new(tokens).parse() catch {
      err => assert_eq(err, expected_err)
    } noraise {
      expr => fail("Expected error '\{expected_err}', got '\{expr}'")
    }
  }

  expect_term("*", Star)
  expect_term("□", Box)
  expect_term("Box", Box)
  expect_term("Bool", Bool)
  expect_term("Bool -> Bool", Pi(None, Bool, Bool))
  expect_term("Bool -> Bool -> Bool", Pi(None, Bool, Pi(None, Bool, Bool)))
  expect_term("A", FreeVar("A", 0))
  expect_term("P", FreeVar("P", 0))
  expect_term("Q71", FreeVar("Q71", 0))
  expect_term("P -> Q -> (P -> Bool -> R)",  Pi(None, FreeVar("P", 0), Pi(None, FreeVar("Q", 1), Pi(None, FreeVar("P", 0), Pi(None, Bool, FreeVar("R", 2))))))
  expect_term("true", Const(Bool(true)))
  expect_term("false", Const(Bool(false)))
  expect_term("x", FreeVar("x", 0))
  expect_term("(true: Bool)", Ann(Const(Bool(true)), Bool))
  expect_term("fun x: Bool => x", Lam("x", Bool, BoundVar(0)))
  expect_term("fun x: Bool => y", Lam("x", Bool, FreeVar("y", 0)))
  expect_term("fun x: A => x", Lam("x", FreeVar("A", 0), BoundVar(0)))
  expect_term("fun x: A => (x: A)", Lam("x", FreeVar("A", 0), Ann(BoundVar(0), FreeVar("A", 0))))
  expect_term("fun x: A => fun y: B => x", Lam("x", FreeVar("A", 0), Lam("y", FreeVar("B", 1), BoundVar(1))))
  expect_term("f x", App(FreeVar("f", 0), FreeVar("x", 1)))
  expect_term("(fun x: Bool => x) true", App(Lam("x", Bool, BoundVar(0)), Const(Bool(true))))
  expect_term("(fun f: (Bool -> Bool) => f true) (fun x: Bool => x)", App(Lam("x", Pi(None, Bool, Bool), App(BoundVar(0), Const(Bool(true)))), Lam("x", Bool, BoundVar(0))))
  expect_term("forall A: *, A", Pi(Some("A"), Star, BoundVar(0)))
  expect_term("forall b: Bool, b", Pi(Some("b"), Bool, BoundVar(0)))
  expect_term("fun T: * => forall x: T, T", Lam("T", Star, Pi(Some("x"), BoundVar(0), BoundVar(1))))
  expect_term("let id = fun x: A => x in id", Let("id", Lam("x", FreeVar("A", 0), BoundVar(0)), BoundVar(0)))
  
  expect_term_err("true)", UnexpectedToken(Rparen))
}
