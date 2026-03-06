fn main {
  let source = "(fun x => x) true"
  let lexer = Lexer::new(source)
  let tokens = try! lexer.tokenize()
  let parser = Parser::new(tokens)
  let expr = try! parser.parse()
  let res = eval(expr)
  println(res)
}
