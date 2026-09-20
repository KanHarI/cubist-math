CC ?= cc
CFLAGS ?= -O2 -g -std=c11 -Wall -Wextra -Wpedantic -Werror
CPPFLAGS ?= -Iinclude -Isrc
BUILD ?= build
SRC = $(wildcard src/*.c)
HEADERS = $(wildcard include/*.h src/*.h)
.PHONY: all test sanitize
all: $(BUILD)/lattice-cli $(BUILD)/test-lattice $(BUILD)/bench-lattice $(BUILD)/kernel-cli $(BUILD)/test-kernel-api
$(BUILD):
	mkdir -p $@
$(BUILD)/lattice-cli: tests/lattice_cli.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@
$(BUILD)/test-lattice: tests/test_lattice.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@
$(BUILD)/bench-lattice: tests/bench_lattice.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@
test: all
	$(BUILD)/test-lattice
	$(BUILD)/test-kernel-api
sanitize:
	$(MAKE) BUILD=build-sanitize CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -Werror -fsanitize=address,undefined -fno-omit-frame-pointer' test

$(BUILD)/kernel-cli: tests/kernel_cli.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-kernel-api: tests/test_kernel_api.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@
