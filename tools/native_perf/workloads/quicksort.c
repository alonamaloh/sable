#include <stddef.h>
#include <stdint.h>

void *__sable_rt_array_alloc_v1(uint64_t bytes);
void __sable_rt_array_free_v1(void *storage);

#ifndef WORK_UNITS
#error "WORK_UNITS must be supplied by the benchmark runner"
#endif

enum { VALUE_COUNT = 10 };

static size_t partition(int32_t *values, size_t lo, size_t hi) {
  const size_t pivot_index = hi - 1;
  const int32_t pivot = values[pivot_index];
  size_t next = lo;
  for (size_t scan = lo; scan < pivot_index; ++scan) {
    if (values[scan] < pivot) {
      const int32_t temporary = values[next];
      values[next] = values[scan];
      values[scan] = temporary;
      ++next;
    }
  }
  const int32_t temporary = values[next];
  values[next] = values[pivot_index];
  values[pivot_index] = temporary;
  return next;
}

static void quicksort_range(int32_t *values, size_t lo, size_t hi) {
  if (hi - lo > 1) {
    const size_t pivot = partition(values, lo, hi);
    quicksort_range(values, lo, pivot);
    quicksort_range(values, pivot + 1, hi);
  }
}

int main(void) {
  static const int32_t input[VALUE_COUNT] = {5, 3, 8, 1, 9, 2, 7, 3, 0, 6};
  static const int32_t expected[VALUE_COUNT] = {0, 1, 2, 3, 3, 5, 6, 7, 8, 9};

  for (size_t iteration = 0; iteration < WORK_UNITS; ++iteration) {
    int32_t *values = __sable_rt_array_alloc_v1(sizeof(input));
    if (values == NULL) {
      return 2;
    }
    for (size_t index = 0; index < VALUE_COUNT; ++index) {
      values[index] = input[index];
    }
    quicksort_range(values, 0, VALUE_COUNT);
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
