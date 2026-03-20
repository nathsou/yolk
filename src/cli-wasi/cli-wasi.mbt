using @lib { type Externals }

pub fn start() -> Unit {
  let ext: Externals = {
    fs: {
      read_file_to_string: path => {
        let bytes = @fs.read_file_sync(path) catch {
          e => {
            try! @stdio.stderr.write_sync("Failed to read file \{path}: \{e}\n")
            @wasi.proc_exit(1)
          }
        }

        bytes.text()
      },
    },
    println: str => {
      try! @stdio.stdout.write_sync(str)
      try! @stdio.stdout.write_sync("\n")
    },
    get_args: () => {
      @wasi.args_get() catch {
        e => {
          try! @stdio.stderr.write_sync(
            "Failed to get command line arguments: \{e}\n",
          )
          @wasi.proc_exit(1)
        }
      }
    },
  }

  @lib.run_cli(ext)
}
