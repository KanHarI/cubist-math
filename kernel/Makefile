CC ?= cc
CFLAGS ?= -O2 -g -std=c11 -Wall -Wextra -Wpedantic -Werror
CPPFLAGS ?= -Iinclude -Isrc
BUILD ?= build
# The sanitizers of `make sanitize`, whose reports fail the build. Apple
# clang 17's address sanitizer never finishes starting on macOS 26: setting
# up its shadow memory walks the loader's shared cache, which allocates, and
# the allocation re-enters its unfinished startup. Run SANITIZERS=undefined
# there; CI runs both on Linux.
SANITIZERS ?= address,undefined
comma := ,
SRC = $(wildcard src/*.c)
HEADERS = $(sort $(wildcard include/*.h src/*.h))
TESTS = test-lattice test-kernel-api test-conversion test-dimension-scope test-path-head test-unfolding-hints \
	test-checkpoint test-check-cache test-instructions test-levels test-work test-signatures test-isolation
PROGRAMS = lattice-cli bench-lattice kernel-cli $(TESTS)
# The kernel's sources compile once per configuration, into objects every
# program links, and each object records the headers it includes (-MMD), so
# an unchanged build does nothing. A configuration is the compiler's identity,
# its flags, and the headers there are, since a header added can change which
# one an include finds. Each has a directory of its own, $(BUILD)/<id>, named
# by a checksum of it: a build never mixes configurations, whatever the file
# times say, and nothing is removed as the makefile is read, so a dry run or
# another configuration's build leaves a directory as it was. The programs
# are linked there; $(BUILD)/<name> links to the last configuration built, and
# `make test` runs its own configuration's programs. File times are still
# compared to the second by some makes, so a source restored within a second
# of a build may not rebuild: `make clean` after such experiments.
quote = $(subst ','\'',$(1))
CONFIGURATION := $(CC) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) $(LDLIBS) | $(shell $(CC) --version 2>/dev/null | head -n 1) | $(HEADERS)
ID := $(shell printf '%s' '$(call quote,$(CONFIGURATION))' | cksum | cut -d ' ' -f 1)
ifeq ($(ID),)
$(error Could not name this configuration's build directory)
endif
OUT = $(BUILD)/$(ID)
OBJ = $(SRC:src/%.c=$(OUT)/obj/%.o)
.PHONY: all test sanitize clean FORCE
all: $(PROGRAMS:%=$(BUILD)/%)
$(OUT)/obj $(OUT)/obj/tests $(OUT)/bin:
	mkdir -p $@
$(OUT)/configuration: | $(OUT)/obj
	printf '%s\n' '$(call quote,$(CONFIGURATION))' > $@
$(OUT)/obj/%.o: src/%.c | $(OUT)/obj $(OUT)/configuration
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@
$(OUT)/obj/tests/%.o: tests/%.c | $(OUT)/obj/tests $(OUT)/configuration
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@
# Each program is its source in tests/, named with underscores, linked with
# the kernel's objects as one command once compiled and linked it.
define PROGRAM
$(OUT)/bin/$(1): $(OUT)/obj/tests/$(subst -,_,$(1)).o $(OBJ) | $(OUT)/bin
	$$(CC) $$(CPPFLAGS) $$(CFLAGS) $$(LDFLAGS) $$^ $$(LDLIBS) -o $$@
$(BUILD)/$(1): $(OUT)/bin/$(1) FORCE
	@ln -sfn $(ID)/bin/$(1) $$@
endef
$(foreach program,$(PROGRAMS),$(eval $(call PROGRAM,$(program))))
-include $(wildcard $(OUT)/obj/*.d $(OUT)/obj/tests/*.d)
test: all
	@set -e; for test in $(TESTS); do echo $(BUILD)/$$test; $(OUT)/bin/$$test; done
sanitize:
	$(MAKE) BUILD=build-sanitize-$(subst $(comma),-,$(SANITIZERS)) CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -Werror -fsanitize=$(SANITIZERS) -fno-sanitize-recover=all -fno-omit-frame-pointer' test
clean:
	rm -rf build build-sanitize build-sanitize-*
