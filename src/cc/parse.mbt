
pub enum Token {
  Lparen; Rparen; ThickArrow; Arrow; Colon; Comma; Dot; Hash; Pipe
  Sort; Prop; Type; Fun; Forall; Let; In; ColonEqual; Def; Axiom; Inductive
  Nat(UInt); Var(String); Path(Name)
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

fn Lexer::has_next(self: Lexer) -> Bool {
  self.index < self.input.length()
}

fn Lexer::peek(self: Lexer) -> Char {
  self.input[self.index]
}

fn Lexer::matches(self: Lexer, char: Char) -> Bool {
  self.has_next() && self.peek() == char
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
  Next
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
      } else if self.consumes('-') {
        // skip comment until end of line
        while self.index < self.input.length() && self.peek() != '\n' {
          self.advance()
        }
        
        Next
      } else {
        Grr(UnexpectedChar(char~, index=self.index))
      }
    }
    '#' => { self.advance(); Yay(Hash) }
    '|' => { self.advance(); Yay(Pipe) }
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
          "inductive" => Yay(Inductive)
          "Sort" => Yay(Sort)
          "Prop" => Yay(Prop)
          "Type" => Yay(Type)
          _ => {
            if self.matches('.') {
              let mut name = Name::Leaf(identifier)

              while self.matches('.') {
                self.advance()
                let part = self.parse_identifier()
                name = Name::Path(name, part)
              }

              Yay(Path(name))
            } else {
              Yay(Var(identifier))
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

pub fn Lexer::tokenise(self: Lexer) -> Array[Token] raise LexerError {
  let tokens = []

  while true {
    match self.next() {
      Yay(token) => tokens.push(token)
      Grr(error) => raise error
      Next => ()
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
    Inductive => self.parse_inductive()
    _ => raise UnexpectedToken(self.peek())
  }
}

fn Parser::parse_name(self: Parser) -> Name raise ParserError {
  match self.peek_safe() {
    Some(Var(name)) => {
      self.advance()
      Name::Leaf(name)
    }
    Some(Path(name)) => {
      self.advance()
      name
    }
    Some(tok) => raise UnexpectedToken(tok)
    None => raise UnexpectedEOF
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

fn Parser::parse_inductive(self: Parser) -> TopLevel[STerm] raise ParserError {
  self.expect(Inductive)
  let name = self.parse_name()
  let params: Array[(String, STerm)] = []

  while self.peek_safe() is Some(Lparen) {
    params.push(self.parse_binder())
  }

  self.expect(Colon)
  let arity = self.parse_term()
  let constructors: Array[(String, STerm)] = []
  
  while self.peek_safe() is Some(Pipe) {
    self.advance()
    let ctor_name = self.expect_var()
    self.expect(Colon)
    let ctor_ty = self.parse_term()
    constructors.push((ctor_name, ctor_ty))
  }

  Declaration(name, Decl::inductive(params~, arity~, constructors~))
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

fn Parser::parse_binder(self: Parser) -> (String, STerm) raise ParserError {
  self.expect(Lparen)
  let x= self.expect_var()
  self.expect(Colon)
  let ty = self.parse_term()
  self.expect(Rparen)
  (x, ty)
}

fn Parser::parse_term(self: Parser) -> STerm raise ParserError {
  match self.peek() {
    Fun => self.parse_fun()
    Forall => self.parse_forall()
    Let => self.parse_let()
    _ => self.parse_arrow()
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
  let mut lhs = self.parse_atom()

  while (try? self.parse_atom()) is Ok(rhs) {
    lhs = App(lhs, rhs)
  }

  lhs
}

fn Parser::parse_arrow(self: Parser) -> STerm raise ParserError {
  let lhs = self.parse_app()

  if self.matches(Arrow) {
    self.advance()
    let rhs = self.parse_term()
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
      Var(Leaf(x))
    }
    Path(name) => {
      self.advance();
      Var(name)
    }
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

  fn v(name: String) -> STerm {
    Var(Leaf(name))
  }

  expect_term("Type", Sort(1))
  expect_term("Type 0", Sort(1))
  expect_term("Prop", Sort(0))
  expect_term("Type 1", Sort(2))
  expect_term("Type 321", Sort(322))
  expect_term("Sort 321", Sort(321))
  expect_term("Bool", v("Bool"))
  expect_term("Bool -> Bool", Pi(None, v("Bool"), v("Bool")))
  expect_term("Bool -> Bool -> Bool", Pi(None, v("Bool"), Pi(None, v("Bool"), v("Bool"))))
  expect_term("A", v("A"))
  expect_term("P", v("P"))
  expect_term("Q71", v("Q71"))
  expect_term("P -> Q -> (P -> Bool -> R)",  Pi(None, v("P"), Pi(None, v("Q"), Pi(None, v("P"), Pi(None, v("Bool"), v("R"))))))
  expect_term("true", v("true"))
  expect_term("false", v("false"))
  expect_term("x", v("x"))
  expect_term("(true: Bool)", Ann(v("true"), v("Bool")))
  expect_term("fun x: Bool => x", Fun("x", v("Bool"), v("x")))
  expect_term("fun x: Bool => y", Fun("x", v("Bool"), v("y")))
  expect_term("fun x: A => x", Fun("x", v("A"), v("x")))
  expect_term("fun x: A => (x: A)", Fun("x", v("A"), Ann(v("x"), v("A"))))
  expect_term("fun x: A => fun y: B => x", Fun("x", v("A"), Fun("y", v("B"), v("x"))))
  expect_term("f x", App(v("f"), v("x")))
  expect_term("(fun x: Bool => x) true", App(Fun("x", v("Bool"), v("x")), v("true")))
  expect_term("(fun f: (Bool -> Bool) => f true) (fun x: Bool => x)", App(Fun("f", Pi(None, v("Bool"), v("Bool")), App(v("f"), v("true"))), Fun("x", v("Bool"), v("x"))))
  expect_term("forall A: Type, A", Pi(Some("A"), Sort(1), v("A")))
  expect_term("forall b: Bool, b", Pi(Some("b"), v("Bool"), v("b")))
  expect_term("fun T: Type 2 => forall x: T, T", Fun("T", Sort(3), Pi(Some("x"), v("T"), v("T"))))
  expect_term("let id := fun x: A => x in id", Let("id", Fun("x", v("A"), v("x")), v("id")))
  expect_term_err("fun x => x)", Expected(expected=Colon, received=ThickArrow))
  
  expect_top_level(
    "def id : forall A: Type, A := fun A: Type => fun x: A => x",
    Declaration(Leaf("id"), Definition(Pi(Some("A"), Sort(1), v("A")), Fun("A", Sort(1), Fun("x", v("A"), v("x")))))
  )

  expect_top_level("#eval (fun x: Bool => x) true", Command("eval", [App(Fun("x", v("Bool"), v("x")), v("true"))]))
  
  expect_top_level(
    "inductive False : Prop",
    Declaration(Leaf("False"), Inductive(params=[], arity=Sort(0), constructors=[], ty=Sort(0)))
  )

  expect_top_level(
    "inductive True : Prop | intro : True",
    Declaration(Leaf("True"), Inductive(params=[], arity=Sort(0), constructors=[("intro", v("True"))], ty=Sort(0)))
  )

  expect_top_level(
    (
      #|inductive Vec (A : Type) : Nat -> Type
      #|    | nil : Vec A Nat.zero
      #|    | cons : A -> forall n : Nat, Vec A n -> Vec A (Nat.succ n)
    ),
    Declaration(
      Leaf("Vec"),
      Inductive(
        params=[("A", Sort(1))],
        arity=Pi(None, v("Nat"), Sort(1)),
        constructors=[
          ("nil", App(App(v("Vec"), v("A")), Var(Path(Leaf("Nat"), "zero")))),
          ("cons", Pi(None, v("A"), Pi(Some("n"), v("Nat"), Pi(None, App(App(v("Vec"), v("A")), v("n")), App(App(v("Vec"), v("A")), App(Var(Path(Leaf("Nat"), "succ")), v("n"))))))),
        ],
        ty=Pi(Some("A"), Sort(1), Pi(None, v("Nat"), Sort(1))),
      ),
    )
  )

}
