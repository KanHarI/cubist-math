CC ?= cc
AR ?= ar
CPPFLAGS ?= -Iinclude -Isrc
CFLAGS ?= -O3 -std=c11 -Wall -Wextra -Wpedantic
LDFLAGS ?= -pthread
BUILD ?= build
SRC = src/store.c src/ast.c src/kernel.c src/eliminators.c src/proofs.c
OBJ = $(SRC:src/%.c=$(BUILD)/%.o)
.PHONY: all test collision-test sanitize clean bench
all: $(BUILD)/libthth.a
$(BUILD):
	mkdir -p $(BUILD)
$(BUILD)/%.o: src/%.c include/thth.h include/tt_opcodes.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@
$(BUILD)/kernel.o: src/metadata.inc
$(BUILD)/proofs.o: src/proofs_generated.inc
$(BUILD)/libthth.a: $(OBJ)
	$(AR) rcs $@ $^
$(BUILD)/test: tests/test_engine.c $(BUILD)/libthth.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(BUILD)/libthth.a $(LDFLAGS) -o $@
test: $(BUILD)/test
	$(BUILD)/test
$(BUILD)/test-collisions: tests/test_collisions.c $(BUILD)/libthth.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(BUILD)/libthth.a $(LDFLAGS) -o $@
collision-test:
	$(MAKE) BUILD=build-collisions CPPFLAGS='-Iinclude -Isrc -DTT_TEST_CONSTANT_HASH' build-collisions/test-collisions
	build-collisions/test-collisions
sanitize:
	$(MAKE) BUILD=build-sanitize CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -fsanitize=address,undefined -fno-omit-frame-pointer' LDFLAGS='-fsanitize=address,undefined' test
clean:
	rm -rf build build-sanitize
