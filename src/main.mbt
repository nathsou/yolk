fn main {
  let source = "((fun x => fun y => x) true) false"
  let lexer = Lexer::new(source)
  let tokens = try! lexer.tokenize()
  let parser = Parser::new(tokens)
  let expr = try! parser.parse_expr()
  println(expr)
}
