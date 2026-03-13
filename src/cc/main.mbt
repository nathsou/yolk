
fn run(path: String) -> Unit raise {
  let contents = @fs.read_file_to_string(path)
  let tokens = Lexer::new(contents).tokenise()
  let parser = Parser::new(tokens)
  let program = parser.parse()
  let elab = Elaborator::new()
  elab.elaborate(program)
}

fn main {
  let cmd = @argparse.Command(
    "yolk",
    options=[],
    positionals=[
      @argparse.PositionArg("source", about="Path to the .yolk file to check"),
    ],
  )

  try cmd.parse() catch {
    err => {
      println("Error parsing arguments: \{err}")
    }
  } else {
    matches => {
      if matches.values.get("source") is Some(path) {
        try run(path[0]) catch {
          err => {
            println("Error: \{err}")
          }
        }
      }
    }
  }
}
