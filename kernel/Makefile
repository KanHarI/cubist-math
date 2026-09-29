CC ?= cc
CFLAGS ?= -O2 -g -std=c11 -Wall -Wextra -Wpedantic -Werror
CPPFLAGS ?= -Iinclude -Isrc
BUILD ?= build
# The sanitizers of `make sanitize`, whose reports fail the build. Apple
# clang 17's address sanitizer never finishes starting on macOS 26: setting
# up its shadow memory walks the loader's shared cache, which allocates, and
# the allocation re-enters its unfinished startup. Run SANITIZERS=undefined
# there; CI runs both on Linux. Each set builds in a directory of its own,
# since the rules track sources, not flags.
SANITIZERS ?= address,undefined
comma := ,
SRC = $(wildcard src/*.c)
HEADERS = $(wildcard include/*.h src/*.h)
.PHONY: all test sanitize
all: $(BUILD)/lattice-cli $(BUILD)/test-lattice $(BUILD)/bench-lattice $(BUILD)/kernel-cli $(BUILD)/test-kernel-api $(BUILD)/test-conversion $(BUILD)/test-dimension-scope $(BUILD)/test-path-head $(BUILD)/test-unfolding-hints $(BUILD)/test-checkpoint $(BUILD)/test-check-cache $(BUILD)/test-instructions $(BUILD)/test-levels $(BUILD)/test-work $(BUILD)/test-signatures $(BUILD)/test-isolation
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
	$(BUILD)/test-conversion
	$(BUILD)/test-dimension-scope
	$(BUILD)/test-path-head
	$(BUILD)/test-unfolding-hints
	$(BUILD)/test-checkpoint
	$(BUILD)/test-check-cache
	$(BUILD)/test-instructions
	$(BUILD)/test-levels
	$(BUILD)/test-work
	$(BUILD)/test-signatures
	$(BUILD)/test-isolation
sanitize:
	$(MAKE) BUILD=build-sanitize-$(subst $(comma),-,$(SANITIZERS)) CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -Werror -fsanitize=$(SANITIZERS) -fno-sanitize-recover=all -fno-omit-frame-pointer' test

$(BUILD)/kernel-cli: tests/kernel_cli.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-kernel-api: tests/test_kernel_api.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-conversion: tests/test_conversion.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-dimension-scope: tests/test_dimension_scope.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-path-head: tests/test_path_head.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-unfolding-hints: tests/test_unfolding_hints.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-checkpoint: tests/test_checkpoint.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-check-cache: tests/test_check_cache.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-instructions: tests/test_instructions.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-levels: tests/test_levels.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

.PHONY: clean
clean:
	rm -rf build build-sanitize build-sanitize-*

$(BUILD)/test-work: tests/test_work.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-signatures: tests/test_signatures.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@

$(BUILD)/test-isolation: tests/test_isolation.c $(SRC) $(HEADERS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@
