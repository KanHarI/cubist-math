/* A diagnostic deadline aborts work, never certifies it. It persists across
 * checks and budget retries until the caller explicitly replaces it. */
#define _POSIX_C_SOURCE 200809L
#include "term_internal.h"
#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
static double now_ms(void) { return emscripten_get_now(); }
#else
#include <time.h>
static double now_ms(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now)) return 0;
    return (double)now.tv_sec * 1000.0 + (double)now.tv_nsec / 1000000.0;
}
#endif
void cc_kernel_set_deadline_ms(cc_kernel *k, double duration_ms) {
    if (!k) return;
    k->deadline_ms = duration_ms > 0 ? now_ms() + duration_ms : 0;
    k->deadline_ticks = 0;
}
bool ck_deadline(cc_kernel *k) {
    return !k->deadline_ms || now_ms() < k->deadline_ms
        || ck_fail_as(k, CC_ERROR_DEADLINE, "Declaration time limit exceeded.");
}
