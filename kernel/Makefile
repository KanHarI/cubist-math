CC ?= cc
CFLAGS ?= -O2 -g -std=c11 -Wall -Wextra -Wpedantic -Werror
CPPFLAGS ?= -Iinclude -Isrc
BUILD ?= build
# The sanitizers of `make sanitize`, whose reports fail the build. Apple
# clang 17's address sanitizer never finishes starting on macOS 26: setting
# up its shadow memory walks the loader's shared cache, which allocates, and
# the allocation re-enters its unfinished startup. Run SANITIZERS=undefined
# there; CI runs both on Linux. Each set builds in a directory of its own, so
# switching between them rebuilds nothing.
SANITIZERS ?= address,undefined
comma := ,
SRC = $(wildcard src/*.c)
# The kernel's sources are compiled once per build directory, into objects
# every executable links, and each object records the headers it includes
# (-MMD), so an unchanged build does nothing. A build directory holds one
# configuration, the compiler's identity and flags, recorded in
# $(BUILD)/configuration: when they differ, its objects and programs are
# removed as the makefile is read, before anything is built, so nothing
# compiled otherwise survives, whatever the file times say. File times are
# still compared to the second by some makes, so a source restored within a
# second of a build may not rebuild: `make clean` after such experiments.
OBJ = $(SRC:src/%.c=$(BUILD)/obj/%.o)
TESTS = test-lattice test-kernel-api test-conversion test-dimension-scope test-path-head test-unfolding-hints \
	test-checkpoint test-check-cache test-instructions test-levels test-work test-signatures test-isolation
PROGRAMS = lattice-cli bench-lattice kernel-cli $(TESTS)
CONFIGURATION := $(CC) $(CPPFLAGS) $(CFLAGS) | $(shell $(CC) --version 2>/dev/null | head -n 1)
ifneq ($(shell cat $(BUILD)/configuration 2>/dev/null),$(CONFIGURATION))
reconfigured := $(shell rm -rf $(BUILD)/obj $(PROGRAMS:%=$(BUILD)/%) && mkdir -p $(BUILD) && printf '%s\n' '$(CONFIGURATION)' > $(BUILD)/configuration)
endif
.PHONY: all test sanitize clean
all: $(PROGRAMS:%=$(BUILD)/%)
$(BUILD)/obj $(BUILD)/obj/tests:
	mkdir -p $@
$(BUILD)/obj/%.o: src/%.c | $(BUILD)/obj
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@
$(BUILD)/obj/tests/%.o: tests/%.c | $(BUILD)/obj/tests
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@
# Each program is its source in tests/, named with underscores, linked with
# the kernel's objects.
define PROGRAM
$(BUILD)/$(1): $(BUILD)/obj/tests/$(subst -,_,$(1)).o $(OBJ)
	$$(CC) $$(CFLAGS) $$^ -o $$@
endef
$(foreach program,$(PROGRAMS),$(eval $(call PROGRAM,$(program))))
-include $(wildcard $(BUILD)/obj/*.d $(BUILD)/obj/tests/*.d)
test: all
	@set -e; for test in $(TESTS); do echo $(BUILD)/$$test; $(BUILD)/$$test; done
sanitize:
	$(MAKE) BUILD=build-sanitize-$(subst $(comma),-,$(SANITIZERS)) CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -Werror -fsanitize=$(SANITIZERS) -fno-sanitize-recover=all -fno-omit-frame-pointer' test
clean:
	rm -rf build build-sanitize build-sanitize-*
