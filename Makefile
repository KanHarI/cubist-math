CC ?= cc
AR ?= ar
CPPFLAGS ?= -Iinclude -Isrc
CFLAGS ?= -O3 -std=c11 -Wall -Wextra -Wpedantic
LDFLAGS ?= -pthread
BUILD ?= build
CPPCHECK ?= cppcheck
KERNEL_SRC = $(wildcard src/kernel/*.c)
SRC = $(KERNEL_SRC) src/proofs.c
C_FILES = $(sort $(wildcard src/*.c src/kernel/*.c tests/*.c))
OBJ = $(SRC:src/%.c=$(BUILD)/%.o)
.PHONY: all test collision-test sanitize clean bench lint
all: $(BUILD)/libthth.a
$(BUILD):
	mkdir -p $(BUILD)
$(BUILD)/%.o: src/%.c include/thth.h include/tt_opcodes.h src/kernel/internal.h | $(BUILD)
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@
$(BUILD)/kernel/apply.o: src/kernel/metadata.inc
$(BUILD)/proofs.o: src/proofs_generated.inc
$(BUILD)/libthth.a: $(OBJ)
	$(RM) $@
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
lint:
	$(CPPCHECK) --enable=warning,style,performance,portability --std=c11 --language=c --library=posix --error-exitcode=1 --force -Iinclude -Isrc $(C_FILES)
clean:
	rm -rf build build-sanitize
