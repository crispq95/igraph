
#include <igraph.h>
#include <stdio.h>

igraph_fatal_handler_t hanlder;

void handler(const char *reason, const char *file, igraph_long_t line) {
    printf("Reason: %s\nFile: %s\nLine: %ld\n", reason, file, line);
    exit(0); /* We use exit(0) instead of abort() to allow the test to succeed. */
}

igraph_long_t main() {
    igraph_set_fatal_handler(&handler);

    igraph_fatal("REASON", "FILENAME", 123);

    /* The igraph_fatal() call must not return, so the following lines should not run. */

    printf("This should not be printed.");

    return 0;
}
