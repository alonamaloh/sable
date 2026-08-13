/*
 * Sable's versioned hosted array allocation boundary.
 *
 * The compiler passes a byte count, never an element count.  Zero-byte
 * arrays do not call either hook, but accepting zero here keeps this shim a
 * conventional allocator for non-Sable callers as well.
 */

#include <stdint.h>
#include <stdlib.h>

void *__sable_rt_array_alloc_v1(uint64_t bytes) {
    if (bytes > SIZE_MAX) {
        return NULL;
    }
    return malloc((size_t)bytes);
}

void __sable_rt_array_free_v1(void *storage) {
    free(storage);
}
