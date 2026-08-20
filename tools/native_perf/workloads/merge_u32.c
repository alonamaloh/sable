#include <stddef.h>
#include <stdint.h>

void *__sable_rt_array_alloc_v1(uint64_t bytes);
void __sable_rt_array_free_v1(void *storage);

#ifndef WORK_UNITS
#error "WORK_UNITS must be supplied by the benchmark runner"
#endif

enum { LEFT_COUNT = 4, RIGHT_COUNT = 3, OUTPUT_COUNT = 7 };

static void merge(const uint32_t *left, const uint32_t *right,
                  uint32_t *output) {
  size_t left_index = 0;
  size_t right_index = 0;
  size_t output_index = 0;
  while (left_index < LEFT_COUNT && right_index < RIGHT_COUNT) {
    if (left[left_index] <= right[right_index]) {
      output[output_index++] = left[left_index++];
    } else {
      output[output_index++] = right[right_index++];
    }
  }
  while (left_index < LEFT_COUNT) {
    output[output_index++] = left[left_index++];
  }
  while (right_index < RIGHT_COUNT) {
    output[output_index++] = right[right_index++];
  }
}

int main(void) {
  static const uint32_t left_input[LEFT_COUNT] = {1, 3, 5, 7};
  static const uint32_t right_input[RIGHT_COUNT] = {2, 3, 6};
  static const uint32_t expected[OUTPUT_COUNT] = {1, 2, 3, 3, 5, 6, 7};

  for (size_t iteration = 0; iteration < WORK_UNITS; ++iteration) {
    uint32_t *left = __sable_rt_array_alloc_v1(sizeof(left_input));
    uint32_t *right = __sable_rt_array_alloc_v1(sizeof(right_input));
    uint32_t *output = __sable_rt_array_alloc_v1(sizeof(expected));
    if (left == NULL || right == NULL || output == NULL) {
      __sable_rt_array_free_v1(left);
      __sable_rt_array_free_v1(right);
      __sable_rt_array_free_v1(output);
      return 2;
    }
    for (size_t index = 0; index < LEFT_COUNT; ++index) {
      left[index] = left_input[index];
    }
    for (size_t index = 0; index < RIGHT_COUNT; ++index) {
      right[index] = right_input[index];
    }
    for (size_t index = 0; index < OUTPUT_COUNT; ++index) {
      output[index] = 0;
    }
    merge(left, right, output);
    for (size_t index = 0; index < OUTPUT_COUNT; ++index) {
      if (output[index] != expected[index]) {
        __sable_rt_array_free_v1(left);
        __sable_rt_array_free_v1(right);
        __sable_rt_array_free_v1(output);
        return 1;
      }
    }
    __sable_rt_array_free_v1(left);
    __sable_rt_array_free_v1(right);
    __sable_rt_array_free_v1(output);
  }
  return 42;
}
