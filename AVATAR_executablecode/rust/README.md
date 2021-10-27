# Call Rust-Code from C-Code

## Dependencies
- rust
- cbindgen

## Run
```bash
$ make build 
cargo build --release && cbindgen --config cbindgen.toml --lang c --crate rust --output rust.h && gcc main.c target/release/librust.a
   Compiling rust v1.0.0 (/Users/kitamurataku/local/call-rust-from-c)
    Finished release [optimized] target(s) in 0.08s
$ make run 
./a.out
Hello, world!
Bye, world!
```
