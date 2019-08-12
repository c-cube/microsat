
all:
	cargo build --release

run:
	cargo run --release

check:
	cargo check

clean:
	cargo clean

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		sleep 0.2; \
		make check all; \
	done
