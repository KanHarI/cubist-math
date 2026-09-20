CC ?= cc
CFLAGS ?= -O2 -g -std=c11 -Wall -Wextra -Wpedantic -Werror
CPPFLAGS ?= -Iinclude -Isrc
BUILD ?= build
SRC = src/formula.c src/interval.c src/faces.c
.PHONY: all test sanitize
all: $(BUILD)/lattice-cli $(BUILD)/test-lattice $(BUILD)/bench-lattice
$(BUILD):
	mkdir -p $@
$(BUILD)/lattice-cli: tests/lattice_cli.c $(SRC) include/cubical.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@
$(BUILD)/test-lattice: tests/test_lattice.c $(SRC) include/cubical.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@
$(BUILD)/bench-lattice: tests/bench_lattice.c $(SRC) include/cubical.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SRC) $< -o $@
test: all
	$(BUILD)/test-lattice
sanitize:
	$(MAKE) BUILD=build-sanitize CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -Werror -fsanitize=address,undefined -fno-omit-frame-pointer' test
