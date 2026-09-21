CC ?= cc
AR ?= ar
CPPFLAGS ?= -Iinclude -Isrc
CFLAGS ?= -O3 -std=c11 -Wall -Wextra -Wpedantic
LDFLAGS ?= -pthread
BUILD ?= build
CPPCHECK ?= cppcheck
KERNEL_SRC = $(wildcard src/kernel/*.c)
SRC = $(KERNEL_SRC) src/proofs.c
C_FILES = $(sort $(wildcard src/*.c src/kernel/*.c tests/*.c wasm/*.c))
OBJ = $(SRC:src/%.c=$(BUILD)/%.o)
.PHONY: all test collision-test sanitize clean bench lint
all: $(BUILD)/libthth.a
$(BUILD):
	mkdir -p $(BUILD)
$(BUILD)/%.o: src/%.c include/thth.h include/tt_opcodes.h src/kernel/internal.h | $(BUILD)
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@
$(BUILD)/kernel/apply.o: src/kernel/metadata.inc
$(BUILD)/proofs.o: src/proofs_generated.inc src/univalence_generated.inc
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

EMCC ?= $(if $(wildcard .tools/emsdk/upstream/emscripten/emcc),.tools/emsdk/upstream/emscripten/emcc,emcc)
WASM_EXPORTS = '["_wb_new","_wb_free","_wb_apply","_wb_result","_wb_name","_wb_meta","_wb_view","_wb_node","_wb_node_name","_wb_stats","_wb_verify"]'
.PHONY: wasm wasm-test serve
wasm: web/dist/kernel.mjs
web/dist/kernel.mjs: $(KERNEL_SRC) src/kernel/internal.h src/kernel/metadata.inc include/thth.h wasm/bridge.c Makefile
	mkdir -p web/dist
	$(EMCC) -O3 -std=c11 -Wall -Wextra -Wpedantic -Werror -Iinclude -Isrc $(KERNEL_SRC) wasm/bridge.c --no-entry -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,worker,node -sALLOW_MEMORY_GROWTH -sINITIAL_MEMORY=16777216 -sMAXIMUM_MEMORY=4294967296 -sSTACK_SIZE=2097152 -sABORTING_MALLOC=0 -sFILESYSTEM=0 -sEXPORTED_FUNCTIONS=$(WASM_EXPORTS) -sEXPORTED_RUNTIME_METHODS='["UTF8ToString"]' -o $@
wasm-test: wasm
	npm test

# Independent cubical backend. Kept separate until the complete source library
# passes its checker; the production site must not silently fall back to Id/J.
CUBICAL_DIR = experiments/cubical/c
CUBICAL_SRC = $(wildcard $(CUBICAL_DIR)/src/*.c)
CUBICAL_EXPORTS = '["_cb_new","_cb_optimizations","_cb_step_budget","_cb_deadline_ms","_cb_checkpoint","_cb_rollback","_cb_commit_checkpoint","_cb_relocated","_cb_unfolding_clear","_cb_unfolding_add","_cb_free","_cb_error","_cb_term","_cb_formula_begin","_cb_formula_clause","_cb_formula_end","_cb_context_clear","_cb_context_add","_cb_check","_cb_check_in_cube","_cb_result","_cb_normalize","_cb_node","_cb_formula_view","_cb_define","_cb_definition","_cb_head"]'
.PHONY: cubical-wasm
cubical-wasm: web/dist/cubical.mjs
	node tools/build-cubical-runtime.mjs
web/dist/cubical.mjs: $(CUBICAL_SRC) $(wildcard $(CUBICAL_DIR)/include/*.h) $(CUBICAL_DIR)/src/term_internal.h wasm/cubical_bridge.c Makefile
	mkdir -p web/dist
	$(EMCC) -O3 -std=c11 -Wall -Wextra -Wpedantic -Werror -I$(CUBICAL_DIR)/include -I$(CUBICAL_DIR)/src $(CUBICAL_SRC) wasm/cubical_bridge.c --no-entry -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,worker,node -sALLOW_MEMORY_GROWTH -sINITIAL_MEMORY=16777216 -sMAXIMUM_MEMORY=4294967296 -sSTACK_SIZE=2097152 -sABORTING_MALLOC=0 -sFILESYSTEM=0 -sEXPORTED_FUNCTIONS=$(CUBICAL_EXPORTS) -sEXPORTED_RUNTIME_METHODS='["UTF8ToString"]' -o $@
PORT ?= 8088
serve: wasm
	@echo "MathScript: http://127.0.0.1:$(PORT)/"
	python3 tools/serve.py --port $(PORT)

.PHONY: cli browser-test
cli: wasm
	node cli/repl.mjs
browser-test: wasm
	npm run test:browser

.PHONY: proof-export
proof-export: wasm
	node tools/proofs/univalence.mjs
	python3 tools/export_workbench.py
	node tools/proofs/wnat_equiv.mjs
	node tools/proofs/primes.mjs
	node tools/export_mathscript.mjs
