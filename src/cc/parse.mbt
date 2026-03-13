
pub enum Token {
  Lparen; Rparen; ThickArrow; Arrow; Colon; Comma; Dot; Hash
  Sort; Prop; Type; Fun; Forall; Let; In; ColonEqual; Def; Axiom
  True; False; Nat(UInt); Var(String); Bool
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
    ':' => {
      self.advance()
      if self.consumes('=') {
        Yay(ColonEqual)
      } else {
        Yay(Colon)
      }
    }
    ',' => { self.advance(); Yay(Comma) }
    '.' => { self.advance(); Yay(Dot) }
    '=' => {
      self.advance()
      if self.consumes('>') {
        Yay(ThickArrow)
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
    '#' => { self.advance(); Yay(Hash) }
    _ => {
      if is_alpha(char) {
        let identifier = self.parse_identifier()

        match identifier {
          "axiom" => Yay(Axiom)
          "fun" => Yay(Fun)
          "forall" => Yay(Forall)
          "let" => Yay(Let)
          "in" => Yay(In)
          "def" => Yay(Def)
          "true" => Yay(True)
          "false" => Yay(False)
          "Bool" => Yay(Bool)
          "Sort" => Yay(Sort)
          "Prop" => Yay(Prop)
          "Type" => Yay(Type)
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
  mut index: Int
}

pub suberror ParserError {
  UnexpectedToken(Token)
  Expected(expected~: Token, received~: Token)
  Message(String)
  UnexpectedEOF
} derive(Show, Eq)

pub fn Parser::new(tokens: Array[Token]) -> Parser {
  { tokens, index: 0 }
}

fn Parser::has_next(self: Parser) -> Bool {
  self.index < self.tokens.length()
}

fn Parser::peek(self: Parser) -> Token raise ParserError {
  if self.tokens.get(self.index) is Some(token) {
    token
  } else {
    raise UnexpectedEOF 
  }
}

fn Parser::peek_safe(self: Parser) -> Token? {
  self.tokens.get(self.index)
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

pub fn Parser::parse(self: Parser) -> Program[STerm] raise ParserError {
  let elems: Array[TopLevel[STerm]] = []

  while self.index < self.tokens.length() {
    elems.push(self.parse_top_level())
  }

  Program(elems)
}

fn Parser::parse_top_level(self: Parser) -> TopLevel[STerm] raise ParserError {
  match self.peek() {
    Axiom => self.parser_axiom()
    Def => self.parse_definition()
    Hash => self.parse_command()
    _ => raise UnexpectedToken(self.peek())
  }
}

fn Parser::parse_name(self: Parser) -> Name raise ParserError {
  let parts = []

  while self.peek_safe() is Some(Var(part)) {
    self.advance()
    parts.push(part)

    if self.peek_safe() is Some(Dot) {
      self.advance()
    } else {
      break
    }
  }

  if Name::from(parts) is Some(name) {
    name
  } else {
    raise Message("Expected name")
  }
}

fn Parser::parser_axiom(self: Parser) -> TopLevel[STerm] raise ParserError {
  self.expect(Axiom)
  let name = self.parse_name()
  self.expect(Colon)
  let ty = self.parse_term()
  Declaration(name, Axiom(ty))
}

fn Parser::parse_definition(self: Parser) -> TopLevel[STerm] raise ParserError {
  self.expect(Def)
  let name = self.parse_name()
  self.expect(Colon)
  let ty = self.parse_term()
  self.expect(ColonEqual)
  let body = self.parse_term()
  Declaration(name, Definition(ty, body))
}

fn Parser::parse_command(self: Parser) -> TopLevel[STerm] raise ParserError {
  self.expect(Hash)
  let name = self.expect_var()
  let args: Array[STerm] = []

  while (try? self.parse_term()) is Ok(term) {
    args.push(term)
  }

  Command(name, args)
}

fn Parser::parse_term(self: Parser) -> STerm raise ParserError {
  match self.peek() {
    Fun => self.parse_fun()
    Forall => self.parse_forall()
    Let => self.parse_let()
    _ => self.parse_app()
  }
}

fn Parser::parse_fun(self: Parser) -> STerm raise ParserError {
  self.expect(Fun)
  let v = self.expect_var()
  self.expect(Colon)
  let ty = self.parse_term()
  self.expect(ThickArrow)
  let body = self.parse_term()
  Fun(v, ty, body) 
}

fn Parser::parse_forall(self: Parser) -> STerm raise ParserError {
  self.expect(Forall)
  let v = self.expect_var()
  self.expect(Colon)
  let ty = self.parse_term()
  self.expect(Comma)
  let rhs = self.parse_term()
  Pi(Some(v), ty, rhs)
}

fn Parser::parse_let(self: Parser) -> STerm raise ParserError {
  self.expect(Let)
  let v = self.expect_var()
  self.expect(ColonEqual)
  let val = self.parse_term()
  self.expect(In)
  let body = self.parse_term()
  Let(v, val, body)
}

fn Parser::parse_app(self: Parser) -> STerm raise ParserError {
  let mut lhs = self.parse_arrow()

  while (try? self.parse_arrow()) is Ok(rhs) {
    lhs = App(lhs, rhs)
  }

  lhs
}

fn Parser::parse_arrow(self: Parser) -> STerm raise ParserError {
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

fn Parser::parse_atom(self: Parser) -> STerm raise ParserError {
  match self.peek() {
    Var(x) => {
      self.advance();
      Var(x)
    }
    Bool => { self.advance(); Bool }
    Prop => { self.advance(); Sort(0) }
    (Sort | Type) as tok => {
      self.advance()
      if self.has_next() && self.peek() is Nat(u) {
        self.advance()
        match tok {
          Sort => Sort(u)
          _ => Sort(u + 1)
        }
      } else {
        match tok {
          Sort => {
            raise Message("Expected universe level after 'Sort'")
          }
          _ => Sort(1) // Type 0
        }
      }
    }
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
  fn parse_term(input: String) -> STerm raise {
    let tokens = Lexer::new(input).tokenise()
    Parser::new(tokens).parse_term()
  }

  fn parse_top_level(input: String) -> TopLevel[STerm] raise {
    let tokens = Lexer::new(input).tokenise()
    Parser::new(tokens).parse_top_level()
  }

  fn expect_term(input: String, expected_term: STerm) raise {
    let parsed = parse_term(input)
    if parsed != expected_term {
      fail("Expected term '\{expected_term}', got '\{parsed}'")
    }
  }

  fn expect_top_level(input: String, expected_top_level: TopLevel[STerm]) raise {
    let parsed = parse_top_level(input)
    if parsed != expected_top_level {
      fail("Expected top-level '\{expected_top_level}', got '\{parsed}'")
    }
  }

  fn expect_term_err(input: String, expected_err: ParserError) raise {
    let tokens = Lexer::new(input).tokenise()

    try Parser::new(tokens).parse_term() catch {
      err => assert_eq(err, expected_err)
    } noraise {
      expr => fail("Expected error '\{expected_err}', got '\{expr}'")
    }
  }

  expect_term("Type", Sort(1))
  expect_term("Type 0", Sort(1))
  expect_term("Prop", Sort(0))
  expect_term("Type 1", Sort(2))
  expect_term("Type 321", Sort(322))
  expect_term("Sort 321", Sort(321))
  expect_term("Bool", Bool)
  expect_term("Bool -> Bool", Pi(None, Bool, Bool))
  expect_term("Bool -> Bool -> Bool", Pi(None, Bool, Pi(None, Bool, Bool)))
  expect_term("A", Var("A"))
  expect_term("P", Var("P"))
  expect_term("Q71", Var("Q71"))
  expect_term("P -> Q -> (P -> Bool -> R)",  Pi(None, Var("P"), Pi(None, Var("Q"), Pi(None, Var("P"), Pi(None, Bool, Var("R"))))))
  expect_term("true", Const(Bool(true)))
  expect_term("false", Const(Bool(false)))
  expect_term("x", Var("x"))
  expect_term("(true: Bool)", Ann(Const(Bool(true)), Bool))
  expect_term("fun x: Bool => x", Fun("x", Bool, Var("x")))
  expect_term("fun x: Bool => y", Fun("x", Bool, Var("y")))
  expect_term("fun x: A => x", Fun("x", Var("A"), Var("x")))
  expect_term("fun x: A => (x: A)", Fun("x", Var("A"), Ann(Var("x"), Var("A"))))
  expect_term("fun x: A => fun y: B => x", Fun("x", Var("A"), Fun("y", Var("B"), Var("x"))))
  expect_term("f x", App(Var("f"), Var("x")))
  expect_term("(fun x: Bool => x) true", App(Fun("x", Bool, Var("x")), Const(Bool(true))))
  expect_term("(fun f: (Bool -> Bool) => f true) (fun x: Bool => x)", App(Fun("f", Pi(None, Bool, Bool), App(Var("f"), Const(Bool(true)))), Fun("x", Bool, Var("x"))))
  expect_term("forall A: Type, A", Pi(Some("A"), Sort(1), Var("A")))
  expect_term("forall b: Bool, b", Pi(Some("b"), Bool, Var("b")))
  expect_term("fun T: Type 2 => forall x: T, T", Fun("T", Sort(3), Pi(Some("x"), Var("T"), Var("T"))))
  expect_term("let id := fun x: A => x in id", Let("id", Fun("x", Var("A"), Var("x")), Var("id")))
  expect_term_err("fun x => x)", Expected(expected=Colon, received=ThickArrow))
  
  expect_top_level(
    "def id : forall A: Type, A := fun A: Type => fun x: A => x",
    Declaration(Leaf("id"), Definition(Pi(Some("A"), Sort(1), Var("A")), Fun("A", Sort(1), Fun("x", Var("A"), Var("x")))))
  )

  expect_top_level("#eval (fun x: Bool => x) true", Command("eval", [App(Fun("x", Bool, Var("x")), Const(Bool(true)))]))
}
