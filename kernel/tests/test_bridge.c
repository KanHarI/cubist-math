/* The browser bridge's handle generation (wasm/cubical_bridge.c), compiled
 * natively with the bridge itself: every rollback and commit moves it on,
 * nothing else does, it never repeats a value, and where it would wrap it
 * is spent and stays 0, which no reader accepts, as a freed session's. */
#include "../../wasm/cubical_bridge.c"
#include <assert.h>
#include <stdio.h>

int main(void) {
    uint32_t token = cb_new();
    assert(token && cb_generation(token) == 1);
    cb_checkpoint(token);
    uint32_t unit = cb_term(token, CC_UNIT, 0, 0, 0, 0, 0);
    assert(unit && cb_generation(token) == 1);
    cb_rollback(token);
    assert(cb_generation(token) == 2);
    cb_rollback(token); /* with no checkpoint open, still a move */
    assert(cb_generation(token) == 3);
    cb_checkpoint(token);
    int committed = cb_commit_checkpoint(token);
    assert(committed == 1 && cb_generation(token) == 4);

    /* The last live generations, reached without 2^32 calls. */
    lookup(token)->generation = UINT32_MAX - 1;
    cb_rollback(token);
    assert(cb_generation(token) == UINT32_MAX);
    /* Where it would wrap, it is spent: 0, for good, so neither a token
     * read before nor one read after is ever held again. */
    cb_checkpoint(token);
    committed = cb_commit_checkpoint(token);
    assert(committed == 1 && cb_generation(token) == 0);
    for (unsigned i = 0; i < 3; ++i) {
        cb_rollback(token);
        cb_checkpoint(token);
        committed = cb_commit_checkpoint(token);
        assert(committed == 1 && cb_generation(token) == 0);
    }
    /* The session still works; only its handles can no longer be held. */
    unit = cb_term(token, CC_UNIT, 0, 0, 0, 0, 0);
    assert(unit);

    cb_free(token);
    assert(cb_generation(token) == 0 && cb_generation(0) == 0);
    puts("bridge handle generations: ok");
    return 0;
}
