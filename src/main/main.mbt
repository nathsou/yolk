using @lib { type Externals }

fn main {
  let ext: Externals = {
    fs: {
      read_file_to_string: path => @fs.read_file_to_string(path),
    },
    println: str => println(str),
    get_args: @sys.get_cli_args,
  }

  @lib.run_cli(ext)
}
