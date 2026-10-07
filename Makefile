# The cubical C kernel is the sole trusted checker.
.PHONY: all test sanitize clean bench lint wasm cubical-wasm wasm-test serve cli browser-test
all sanitize:
	$(MAKE) -C kernel $@
# Serialize the recursive builds when CI requests `make -j2 all test`.
test: all
	$(MAKE) -C kernel test
clean:
	$(MAKE) -C kernel clean
bench:
	$(MAKE) -C kernel all
	kernel/build/bench-lattice
lint:
	cppcheck --enable=warning,performance,portability --std=c11 --error-exitcode=1 --force -Ikernel/include -Ikernel/src kernel/src kernel/tests wasm/cubical_bridge.c
EMCC ?= $(if $(wildcard .tools/emsdk/upstream/emscripten/emcc),.tools/emsdk/upstream/emscripten/emcc,emcc)
CUBICAL_DIR = kernel
CUBICAL_SRC = $(wildcard $(CUBICAL_DIR)/src/*.c)
CUBICAL_EXPORTS = '["_cb_abi_version","_cb_new","_cb_optimizations","_cb_step_budget","_cb_work","_cb_deadline_ms","_cb_checkpoint","_cb_rollback","_cb_commit_checkpoint","_cb_relocated","_cb_free","_cb_error","_cb_error_kind","_cb_mismatch","_cb_term","_cb_formula_begin","_cb_formula_clause","_cb_formula_end","_cb_normalize","_cb_node","_cb_formula_view","_cb_definition","_cb_head","_cb_position_clear","_cb_position_push","_cb_position_set","_cb_subterm","_cb_clear_error","_cb_instr","_cb_judgement_count","_cb_judgement","_cb_judgement_context","_cb_entry_count","_cb_entry","_cb_rename","_cb_equiv_type","_cb_fresh_symbol","_cb_endpoint_term","_cb_arena","_cb_extensions","_cb_signature","_cb_signature_constructor"]'
.PHONY: cubical-wasm wasm-locked
# The compiler's flags, before and after the sources; the stamp records them.
WASM_CFLAGS = -O3 -std=c11 -Wall -Wextra -Wpedantic -Werror -I$(CUBICAL_DIR)/include -I$(CUBICAL_DIR)/src
WASM_LDFLAGS = --no-entry -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,worker,node -sALLOW_MEMORY_GROWTH -sINITIAL_MEMORY=16777216 -sMAXIMUM_MEMORY=4294967296 -sSTACK_SIZE=2097152 -sABORTING_MALLOC=0 -sFILESYSTEM=0 -sEXPORTED_FUNCTIONS=$(CUBICAL_EXPORTS) -sEXPORTED_RUNTIME_METHODS='["UTF8ToString"]'
# One build of web/dist at a time, under a lock (tools/build-stamp.mjs). A
# kernel whose sources, compiler, flags or outputs no longer match its stamp
# is rebuilt, whatever the file times say: a source edited while emcc ran is
# older than the output by its file time, but no longer matches the hash.
wasm cubical-wasm:
	@node tools/build-stamp.mjs locked -- $(MAKE) --no-print-directory wasm-locked
wasm-locked:
	@node tools/build-stamp.mjs check-kernel -- $(EMCC) $(WASM_CFLAGS) $(WASM_LDFLAGS) 2>/dev/null || rm -f web/dist/cubical.mjs
	$(MAKE) --no-print-directory web/dist/cubical.mjs
# The stamp is cleared before emcc writes anything, and written after it succeeds.
web/dist/cubical.mjs: $(CUBICAL_SRC) $(wildcard $(CUBICAL_DIR)/include/*.h) $(CUBICAL_DIR)/src/term_internal.h wasm/cubical_bridge.c Makefile
	mkdir -p web/dist
	node tools/build-stamp.mjs invalidate kernel
	hash=$$(node tools/build-stamp.mjs hash kernel) && $(EMCC) $(WASM_CFLAGS) $(CUBICAL_SRC) wasm/cubical_bridge.c $(WASM_LDFLAGS) -o $@ && node tools/build-stamp.mjs write kernel $$hash -- $(EMCC) $(WASM_CFLAGS) $(WASM_LDFLAGS)
wasm-test: wasm
	npm test
PORT ?= 8088
serve: wasm
	python3 tools/serve.py --port $(PORT)
cli: wasm
	node cli/repl.mjs
browser-test: wasm
	npm run test:browser
