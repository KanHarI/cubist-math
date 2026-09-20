#include "cubical.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/resource.h>

int main(int argc, char **argv) {
    unsigned long iterations = 10000;
    if (argc == 2) { char *end; iterations = strtoul(argv[1], &end, 10); if (*end || !iterations || iterations > 10000000) return 2; }
    cc_formula i, j, k, reversed, a, b, product, backwards, face;
    cc_init(&i, CC_INTERVAL); cc_init(&j, CC_INTERVAL); cc_init(&k, CC_INTERVAL);
    cc_init(&reversed, CC_INTERVAL); cc_init(&a, CC_INTERVAL); cc_init(&b, CC_INTERVAL);
    cc_init(&product, CC_INTERVAL); cc_init(&backwards, CC_INTERVAL); cc_init(&face, CC_FACE);
    cc_status status = cc_generator(&i, 0, true);
    if (status == CC_OK) status = cc_generator(&j, 1, true);
    if (status == CC_OK) status = cc_generator(&k, 2, true);
    if (status == CC_OK) status = cc_reverse(&reversed, &i);
    if (status == CC_OK) status = cc_join(&a, &i, &j);
    if (status == CC_OK) status = cc_join(&b, &reversed, &k);
    size_t checksum = 0; clock_t start = clock();
    for (unsigned long n = 0; n < iterations && status == CC_OK; ++n) {
        status = cc_meet(&product, &a, &b);
        if (status == CC_OK) status = cc_reverse(&backwards, &product);
        if (status == CC_OK) status = cc_endpoint(&face, &backwards, 1);
        checksum += face.length;
    }
    double milliseconds = 1000.0 * (double)(clock() - start) / CLOCKS_PER_SEC;
    struct rusage usage; if (getrusage(RUSAGE_SELF, &usage)) return 3;
    unsigned long long rss = (unsigned long long)usage.ru_maxrss;
#ifndef __APPLE__
    rss *= 1024;
#endif
    if (status == CC_OK) printf("{\"iterations\":%lu,\"cpuMilliseconds\":%.3f,\"peakRssBytes\":%llu,\"checksum\":%zu}\n",iterations,milliseconds,rss,checksum);
    cc_clear(&i); cc_clear(&j); cc_clear(&k); cc_clear(&reversed); cc_clear(&a); cc_clear(&b);
    cc_clear(&product); cc_clear(&backwards); cc_clear(&face);
    return status == CC_OK ? 0 : 1;
}
