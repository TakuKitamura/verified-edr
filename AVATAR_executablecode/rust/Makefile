all:
	cbindgen --version || cargo install --force cbindgen
	cargo build --release && cp target/release/librust.a .. && cbindgen --config cbindgen.toml --lang c --crate rust --output include/rust.h 