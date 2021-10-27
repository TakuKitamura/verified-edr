build:
	cargo build --release && cbindgen --config cbindgen.toml --lang c --crate rust --output rust.h && gcc main.c target/release/librust.a
run:
	./a.out