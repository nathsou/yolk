
pub enum Token {
  Lparen; Rparen; ThickArrow; Arrow; Colon; Comma; Dot; Hash; Pipe; ColonEqual; Lbrace; Rbrace
  Plus; Star
  Sort; Prop; Type; Fun; Forall; Let; In; Def; Axiom; Theorem; Inductive; Match; Return; MaxKw; IMaxKw
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
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || c == '\''
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
    '{' => { self.advance(); Yay(Lbrace) }
    '}' => { self.advance(); Yay(Rbrace) }
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
    '+' => { self.advance(); Yay(Plus) }
    '*' => { self.advance(); Yay(Star) }
    _ => {
      if is_alpha(char) {
        let identifier = self.parse_identifier()

        match identifier {
          "axiom" => Yay(Axiom)
          "theorem" => Yay(Theorem)
          "fun" => Yay(Fun)
          "forall" => Yay(Forall)
          "let" => Yay(Let)
          "in" => Yay(In)
          "def" => Yay(Def)
          "inductive" => Yay(Inductive)
          "match" => Yay(Match)
          "return" => Yay(Return)
          "Sort" => Yay(Sort)
          "Prop" => Yay(Prop)
          "Type" => Yay(Type)
          "max" => Yay(MaxKw)
          "imax" => Yay(IMaxKw)
          _ => {
            if self.matches('.') && self.index + 1 < self.input.length() && is_alpha(self.input[self.index + 1]) {
              let mut name = Name::Leaf(identifier)

              while self.matches('.') && self.index + 1 < self.input.length() && is_alpha(self.input[self.index + 1]) {
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
  match self.peek() {
    Var(name) => {
      self.advance()
      name
    }
    tok => raise Message("Expected variable, got '\{tok}'")
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
    Def | Theorem => self.parse_definition_or_theorem()
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

fn Parser::parse_universe_vars(self: Parser) -> Array[UniverseVar] raise ParserError {
  let uvs: Array[UniverseVar] = []

  if self.matches(Dot) {
    self.advance()
    self.expect(Lbrace)
    uvs.push(self.expect_var())

    while self.matches(Comma) {
      self.advance()
      
      if uvs.length() >= MAX_UNIVERSE_VARS {
        raise Message("Too many universe variables (max is \{MAX_UNIVERSE_VARS})")
      }

      uvs.push(self.expect_var())
    }

    self.expect(Rbrace)
  }

  uvs
}

fn Parser::parser_axiom(self: Parser) -> TopLevel[STerm] raise ParserError {
  self.expect(Axiom)
  let name = self.parse_name()
  let uvs = self.parse_universe_vars()
  self.expect(Colon)
  let ty = self.parse_term()
  Declaration(name, uvs, Axiom(ty))
}

fn Parser::parse_definition_or_theorem(self: Parser) -> TopLevel[STerm] raise ParserError {
  let is_theorem = self.matches(Theorem)
  if is_theorem {
    self.advance()
  } else {
    self.expect(Def)
  }

  let name = self.parse_name()
  let uvs = self.parse_universe_vars()

  match self.peek() {
    Colon => {
      self.advance()
      let ty = self.parse_term()
      self.expect(ColonEqual)
      let body = self.parse_term()
      
      let decl: Decl[STerm] = if is_theorem {
        Theorem(ty, body)
      } else {
        Definition(ty, body)
      }

      Declaration(name, uvs, decl)
    }
    Lparen => {
      let binders = self.parse_binders(until=Colon)
      self.expect(Colon)
      let ret_ty = self.parse_term()
      // desugar a definition with multiple binders into a Pi type
      let ty = binders.rev_fold(init=ret_ty, (acc, binder) => Pi(Some(binder.name), binder.ty, acc))
      self.expect(ColonEqual)
      let body = self.parse_term()
      // introduce lambdas for the binders in the body
      let body_lam = binders.rev_fold(init=body, (acc, binder) => Fun(binder.name, binder.ty, acc))
      
      let decl: Decl[STerm] = if is_theorem {
        Theorem(ty, body_lam)
      } else {
        Definition(ty, body_lam)
      }

      Declaration(name, uvs, decl)
    }
    tok => raise Message("Expected ':' or '(' in definition, got '\{tok}'")
  }
}

fn Parser::parse_inductive(self: Parser) -> TopLevel[STerm] raise ParserError {
  self.expect(Inductive)
  let name = self.parse_name()
  let uvs = self.parse_universe_vars()
  let params: Array[(String, STerm)] = []

  if self.matches(Lparen) {
    for binder in self.parse_binders(until=Colon) {
      let ty = match binder.ty {
        Some(ty) => ty
        None => raise Message("Inductive type parameter '\{binder.name}' requires a type annotation")
      }
      params.push((binder.name, ty))
    }
  }

  self.expect(Colon)
  let arity = self.parse_term()
  let constructors: Array[(String, STerm)] = []
  
  while self.matches(Pipe) {
    self.advance()
    let ctor_name = self.expect_var()
    self.expect(Colon)
    let ctor_ty = self.parse_term()
    constructors.push((ctor_name, ctor_ty))
  }

  Declaration(name, uvs, Decl::mk_inductive(params~, arity~, constructors~))
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

priv struct Binder { name: String; ty: STerm? }

priv struct BinderGroup { names: Array[String]; ty: STerm }

priv enum BinderOrGroup {
  Binder(Binder)
  Group(BinderGroup)
}

fn Parser::parse_binder(self: Parser) -> BinderOrGroup raise ParserError {
  let lparen_matched = self.matches(Lparen)
  if lparen_matched { self.advance() }
  let name = self.expect_var()

  if lparen_matched && !self.matches(Colon) {
    let names = [name]
    
    while !self.matches(Colon) {
      names.push(self.expect_var())
    }

    self.advance() // consume Colon
    let ty = self.parse_term()
    self.expect(Rparen)

    Group({ names, ty })
  } else {
    let ty = if self.matches(Colon) {
      self.advance()
      Some(self.parse_term())
    } else {
      None
    }
    
    if lparen_matched { self.expect(Rparen) }
    
    Binder({ name, ty })
  }
}

fn Parser::parse_binders(self: Parser, until~: Token) -> Array[Binder] raise ParserError {
  let binders_or_groups: Array[BinderOrGroup] = [self.parse_binder()]

  while !self.matches(until) {
    binders_or_groups.push(self.parse_binder())
  }

  let binders: Array[Binder] = []

  for bg in binders_or_groups {
    match bg {
      Binder(b) => binders.push(b)
      Group(g) => {
        for name in g.names {
          binders.push({ name, ty: Some(g.ty) })
        }
      }
    }
  }

  binders  
}

const MAX_LEVEL: UInt = 32 // same as Lean 4
const MAX_UNIVERSE_VARS: Int = 32

fn Parser::parse_level_atom(self: Parser) -> Level raise ParserError {
  match self.peek() {
    Nat(n) => {
      if n > MAX_LEVEL {
        raise Message("Universe level '\{n}' is too large (max is \{MAX_LEVEL})")
      }

      self.advance()
      Level::from(n)
    }
    Var(u) => {
      self.advance()
      Level::Param(u)
    }
    MaxKw => {
      self.advance()
      let l1 = self.parse_level_atom()
      let l2 = self.parse_level_atom()
      Level::Max(l1, l2)
    }
    IMaxKw => {
      self.advance()
      let l1 = self.parse_level_atom()
      let l2 = self.parse_level_atom()
      Level::IMax(l1, l2)
    }
    Lparen => {
      self.advance()
      let l = self.parse_level()
      self.expect(Rparen)
      l
    }
    tok => raise UnexpectedToken(tok)
  }
}

fn Parser::parse_level(self: Parser) -> Level raise ParserError {
  let l1 = self.parse_level_atom()

  if self.matches(Plus) {
    self.advance()

    let l2 = self.parse_level_atom()

    let (l, n) = if l2.as_nat() is Some(n) {
      // u + 2 => Succ(Succ(u))
      (l1, n)
    } else if l1.as_nat() is Some(n) {
      // 2 + u => Succ(Succ(u))
      (l2, n)
    } else {
      raise Message("Expected a concrete level on at least one side of '+'")
    }

    let mut result = l

    for _ in 0..<(n.reinterpret_as_int()) {
      result = Level::Succ(result)
    }

    result
  } else {
    l1
  }
}

fn Parser::parse_levels_list(self: Parser) -> Array[Level] raise ParserError {
  if self.matches(Dot) {
    self.advance()
    self.expect(Lbrace)
    let levels: Array[Level] = [self.parse_level()]

    while self.matches(Comma) {
      self.advance()

      if levels.length() >= MAX_UNIVERSE_VARS {
        raise Message("Too many universe levels (max is \{MAX_UNIVERSE_VARS})")
      }

      levels.push(self.parse_level())
    }

    self.expect(Rbrace)
    levels
  } else {
    []
  }
}

fn Parser::parse_term(self: Parser) -> STerm raise ParserError {
  match self.peek() {
    Fun => self.parse_fun()
    Forall => self.parse_forall()
    Let => self.parse_let()
    Match => self.parse_match()
    _ => self.parse_arrow()
  }
}

fn Parser::parse_fun(self: Parser) -> STerm raise ParserError {
  self.expect(Fun)
  let binders = self.parse_binders(until=ThickArrow)
  self.expect(ThickArrow)
  let body = self.parse_term()

  // desugar a fun with multiple binders into nested funs
  binders.rev_fold(init=body, (acc, binder) => Fun(binder.name, binder.ty, acc))
}

fn Parser::parse_forall(self: Parser) -> STerm raise ParserError {
  self.expect(Forall)
  let binders = self.parse_binders(until=Comma)
  self.expect(Comma)
  let rhs = self.parse_term()

  // desugar a forall with multiple binders into nested pis
  binders.rev_fold(init=rhs, (acc, binder) => Pi(Some(binder.name), binder.ty, acc))
}

fn Parser::parse_let(self: Parser) -> STerm raise ParserError {
  self.expect(Let)
  let v = self.expect_var()

  let ann = if self.matches(Colon) {
    self.advance()
    Some(self.parse_term())
  } else {
    None
  }

  self.expect(ColonEqual)
  let val = self.parse_term()
  self.expect(In)
  let body = self.parse_term()
  Let(v, ann, val, body)
}

fn Parser::parse_match(self: Parser) -> STerm raise ParserError {
  self.expect(Match)
  let scrutinee = self.parse_term()
  let motive: STerm? = if self.matches(Return) {
    self.advance()
    Some(self.parse_term())
  } else {
    None
  }
  let cases: Array[MatchCase] = []

  while self.matches(Pipe) {
    self.advance()
    let ctor_name = self.expect_var()
    let args: Array[String] = []

    while self.peek_safe() is Some(Var(arg)) {
      args.push(arg)
      self.advance()
    }

    self.expect(ThickArrow)
    let body = self.parse_term()
    cases.push({ ctor: ctor_name, args, body })
  }

  Match(scrutinee~, motive~, cases~)
}

fn Parser::parse_app(self: Parser) -> STerm raise ParserError {
  let mut lhs = self.parse_atom()

  while (try? self.parse_atom()) is Ok(rhs) {
    lhs = App(lhs, rhs)
  }

  lhs
}

fn Parser::parse_add(self: Parser) -> STerm raise ParserError {
  let mut lhs = self.parse_mul()

  while self.matches(Plus) {
    self.advance()
    let rhs = self.parse_mul()
    lhs = App(App(Var(Path(Leaf("Nat"), "add"), []), lhs), rhs)
  }

  lhs
}

fn Parser::parse_mul(self: Parser) -> STerm raise ParserError {
  let mut lhs = self.parse_app()

  while self.matches(Star) {
    self.advance()
    let rhs = self.parse_app()
    lhs = App(App(Var(Path(Leaf("Nat"), "mul"), []), lhs), rhs)
  }

  lhs
}

fn Parser::parse_arrow(self: Parser) -> STerm raise ParserError {
  let lhs = self.parse_add()

  if self.matches(Arrow) {
    self.advance()
    let rhs = self.parse_term()
    // non-dependent Pi
    Pi(None, Some(lhs), rhs)
  } else {
    lhs
  }
}

fn Parser::parse_atom(self: Parser) -> STerm raise ParserError {
  match self.peek() {
    Var(x) => {
      self.advance();
      let levels = self.parse_levels_list()
      Var(Leaf(x), levels)
    }
    Path(name) => {
      self.advance();
      let levels = self.parse_levels_list()
      Var(name, levels)
    }
    Prop => { self.advance(); Sort(Zero) }
    (Sort | Type) as tok => {
      self.advance()
      let has_level = match self.peek_safe() {
        Some(Nat(_) | Var(_) | MaxKw | IMaxKw | Lparen) => true
        _ => false
      }

      if has_level {
        let l = self.parse_level()
        if tok is Sort { Sort(l) } else { Sort(Succ(l)) }
      } else {
        if tok is Sort { Sort(Zero) } else { Sort(Succ(Zero)) }
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
    Nat(n) => {
      self.advance()
      let nat_name = Name::Leaf("Nat")
      let mut nat = STerm::Var(Path(nat_name, "zero"), [])

      for _ in 0..<(n.reinterpret_as_int()) {
        nat = STerm::App(STerm::Var(Path(nat_name, "succ"), []), nat)
      }

      nat
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
    Var(Leaf(name), [])
  }

  expect_term("Type", Sort(Succ(Zero)))
  expect_term("Type 0", Sort(Level::from(1)))
  expect_term("Prop", Sort(Zero))
  expect_term("Type 1", Sort(Level::from(2)))
  expect_term("Type 31", Sort(Level::from(32)))
  expect_term("Sort 32", Sort(Level::from(32)))
  expect_term("Bool", v("Bool"))
  expect_term("Bool -> Bool", Pi(None, Some(v("Bool")), v("Bool")))
  expect_term("Bool -> Bool -> Bool", Pi(None, Some(v("Bool")), Pi(None, Some(v("Bool")), v("Bool"))))
  expect_term("A", v("A"))
  expect_term("P", v("P"))
  expect_term("Q71", v("Q71"))
  expect_term("P -> Q -> (P -> Bool -> R)", Pi(None, Some(v("P")), Pi(None, Some(v("Q")), Pi(None, Some(v("P")), Pi(None, Some(v("Bool")), v("R"))))))
  expect_term("true", v("true"))
  expect_term("false", v("false"))
  expect_term("x", v("x"))
  expect_term("(true: Bool)", Ann(v("true"), v("Bool")))
  expect_term("fun x: Bool => x", Fun("x", Some(v("Bool")), v("x")))
  expect_term("fun x: Bool => y", Fun("x", Some(v("Bool")), v("y")))
  expect_term("fun x: A => x", Fun("x", Some(v("A")), v("x")))
  expect_term("fun x: A => (x: A)", Fun("x", Some(v("A")), Ann(v("x"), v("A"))))
  expect_term("fun x: A => fun y: B => x", Fun("x", Some(v("A")), Fun("y", Some(v("B")), v("x"))))
  expect_term("f x", App(v("f"), v("x")))
  expect_term("(fun x: Bool => x) true", App(Fun("x", Some(v("Bool")), v("x")), v("true")))
  expect_term("(fun f: (Bool -> Bool) => f true) (fun x: Bool => x)", App(Fun("f", Some(Pi(None, Some(v("Bool")), v("Bool"))), App(v("f"), v("true"))), Fun("x", Some(v("Bool")), v("x"))))
  expect_term("forall A: Type, A", Pi(Some("A"), Some(Sort(Level::from(1))), v("A")))
  expect_term("forall b: Bool, b", Pi(Some("b"), Some(v("Bool")), v("b")))
  expect_term("fun T: Type 2 => forall x: T, T", Fun("T", Some(Sort(Level::from(3))), Pi(Some("x"), Some(v("T")), v("T"))))
  expect_term("let id := fun x: A => x in id", Let("id", None, Fun("x", Some(v("A")), v("x")), v("id")))
  expect_term("let id: A -> A := fun x: A => x in id", Let("id", Some(Pi(None, Some(v("A")), v("A"))), Fun("x", Some(v("A")), v("x")), v("id")))
  expect_term("id.{1}", Var(Leaf("id"), [Level::from(1)]))
  expect_term("id.{imax u (v + 2)}", Var(Leaf("id"), [IMax(Param("u"), Succ(Succ(Param("v"))))]))
  expect_term("id.{1 + max u v}", Var(Leaf("id"), [Succ(Max(Param("u"), Param("v")))]))
  expect_term("fun (b : Bool) (n : Nat) => n", Fun("b", Some(v("Bool")), Fun("n", Some(v("Nat")), v("n"))))
  // unannotated binders
  expect_term("fun x => x", Fun("x", None, v("x")))
  expect_term("fun x => fun y => x", Fun("x", None, Fun("y", None, v("x"))))
  expect_term("forall x, x", Pi(Some("x"), None, v("x")))
  expect_term_err("fun => x", Message("Expected variable, got 'ThickArrow'"))
  
  expect_top_level(
    "def id : forall A: Type, A := fun A: Type => fun x: A => x",
    Declaration(Leaf("id"), [], Definition(Pi(Some("A"), Some(Sort(Level::from(1))), v("A")), Fun("A", Some(Sort(Level::from(1))), Fun("x", Some(v("A")), v("x")))))
  )

  expect_top_level("#eval (fun x: Bool => x) true", Command("eval", [App(Fun("x", Some(v("Bool")), v("x")), v("true"))]))
  
  expect_top_level(
    "inductive False : Prop",
    Declaration(Leaf("False"), [], Inductive({params: [], constructors: [], ty: Sort(Zero)}))
  )

  expect_top_level(
    "inductive True : Prop | intro : True",
    Declaration(Leaf("True"), [], Inductive({params: [], constructors: [("intro", v("True"))], ty: Sort(Zero)}))
  )

  expect_top_level(
    (
      #|inductive Vec (A : Type) : Nat -> Type
      #|    | nil : Vec A Nat.zero
      #|    | cons : A -> forall n : Nat, Vec A n -> Vec A (Nat.succ n)
    ),
    Declaration(
      Leaf("Vec"),
      [],
      Inductive({
        params: [("A", Sort(Level::from(1)))],
        constructors: [
          ("nil", App(App(v("Vec"), v("A")), Var(Path(Leaf("Nat"), "zero"), []))),
          ("cons", Pi(None, Some(v("A")), Pi(Some("n"), Some(v("Nat")), Pi(None, Some(App(App(v("Vec"), v("A")), v("n"))), App(App(v("Vec"), v("A")), App(Var(Path(Leaf("Nat"), "succ"), []), v("n"))))))),
        ],
        ty: Pi(Some("A"), Some(Sort(Level::from(1))), Pi(None, Some(v("Nat")), Sort(Level::from(1)))),
      }),
    )
  )
}
