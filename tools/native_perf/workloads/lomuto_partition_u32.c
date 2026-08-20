#include <stddef.h>
#include <stdint.h>

void *__sable_rt_array_alloc_v1(uint64_t bytes);
void __sable_rt_array_free_v1(void *storage);

#ifndef WORK_UNITS
#error "WORK_UNITS must be supplied by the benchmark runner"
#endif

enum { VALUE_COUNT = 10 };

static size_t partition(uint32_t *values, size_t lo, size_t hi) {
  const size_t pivot_index = hi - 1;
  const uint32_t pivot = values[pivot_index];
  size_t next = lo;
  for (size_t scan = lo; scan < pivot_index; ++scan) {
    if (values[scan] < pivot) {
      const uint32_t temporary = values[next];
      values[next] = values[scan];
      values[scan] = temporary;
      ++next;
    }
  }
  const uint32_t final_temporary = values[next];
  values[next] = values[pivot_index];
  values[pivot_index] = final_temporary;
  return next;
}

int main(void) {
  static const uint32_t input[VALUE_COUNT] = {5, 3, 8, 1, 9, 2, 7, 3, 0, 6};
  static const uint32_t expected[VALUE_COUNT] = {5, 3, 1, 2, 3, 0, 6, 9, 8, 7};

  for (size_t iteration = 0; iteration < WORK_UNITS; ++iteration) {
    uint32_t *values = __sable_rt_array_alloc_v1(sizeof(input));
    if (values == NULL) {
      return 2;
    }
    for (size_t index = 0; index < VALUE_COUNT; ++index) {
      values[index] = input[index];
    }
    const size_t pivot = partition(values, 0, VALUE_COUNT);
    if (pivot != 6) {
      __sable_rt_array_free_v1(values);
      return 1;
    }
    for (size_t index = 0; index < VALUE_COUNT; ++index) {
      if (values[index] != expected[index]) {
        __sable_rt_array_free_v1(values);
        return 1;
      }
    }
    __sable_rt_array_free_v1(values);
  }
  return 42;
}
