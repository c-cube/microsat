
build: microsat-c microsat-rs microsat-rs2

microsat-c: microsat.c
	@clang -O3 microsat.c -o $@

microsat-rs:
	@cd rust2 ; cargo build --release
	@ln -sf rust2/target/release/microsat $@

microsat-rs2:
	@cd rust3 ; cargo build --release
	@ln -sf rust3/target/release/microsat $@

test: build
	@./test.cr -- benchs/ -t 10 --json=test.json

test_fast: build
	@./test.cr -- benchs/ -t 2 --json=test.json

.PHONY: test microsat-rs microsat-rs2
