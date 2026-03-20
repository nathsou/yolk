
pub(all) struct FileSystem {
  read_file_to_string: (String) -> String raise
}

pub(all) struct Externals {
  fs: FileSystem
  println: (String) -> Unit
  get_args: () -> Array[String]
}

fn run(path: String, ext: Externals) -> Unit raise {
  let contents = (ext.fs.read_file_to_string)(path)
  let tokens = Lexer::new(contents).tokenise()
  let parser = Parser::new(tokens)
  let program = parser.parse()
  let elab = Elaborator::new()
  elab.elaborate(program, on_command_output=ext.println)
}

fn print_usage(ext: Externals) -> Unit {
  (ext.println)("Usage: yolk <source.yolk>")
}

pub fn run_cli(ext: Externals) -> Unit {
  match (ext.get_args)() {
    [_, path] => {
      try run(path, ext) catch {
        err => {
          (ext.println)(err.to_string())
        }
      }
    }
    _ => {
      print_usage(ext)
    }
  }
}
