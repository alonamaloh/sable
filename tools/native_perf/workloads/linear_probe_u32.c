#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

void *__sable_rt_array_alloc_v1(uint64_t bytes);
void __sable_rt_array_free_v1(void *storage);

#ifndef WORK_UNITS
#error "WORK_UNITS must be supplied by the benchmark runner"
#endif

enum { CAPACITY = 8 };

static uint32_t map_insert(uint32_t *keys, uint32_t *values, uint32_t *occupied,
                           uint32_t key, uint32_t value) {
  const size_t home = key % CAPACITY;
  for (size_t distance = 0; distance < CAPACITY; ++distance) {
    size_t position = home + distance;
    if (position >= CAPACITY) {
      position -= CAPACITY;
    }
    if (occupied[position] == 0) {
      keys[position] = key;
      values[position] = value;
      occupied[position] = 1;
      return 2;
    }
    if (keys[position] == key) {
      values[position] = value;
      return 1;
    }
  }
  return 0;
}

static uint32_t map_get(const uint32_t *keys, const uint32_t *values,
                        const uint32_t *occupied, uint32_t key) {
  const size_t home = key % CAPACITY;
  for (size_t distance = 0; distance < CAPACITY; ++distance) {
    size_t position = home + distance;
    if (position >= CAPACITY) {
      position -= CAPACITY;
    }
    if (occupied[position] == 0) {
      return 0;
    }
    if (keys[position] == key) {
      return values[position];
    }
  }
  return 0;
}

int main(void) {
  for (size_t iteration = 0; iteration < WORK_UNITS; ++iteration) {
    uint32_t *keys = __sable_rt_array_alloc_v1(CAPACITY * sizeof(uint32_t));
    uint32_t *values = __sable_rt_array_alloc_v1(CAPACITY * sizeof(uint32_t));
    uint32_t *occupied = __sable_rt_array_alloc_v1(CAPACITY * sizeof(uint32_t));
    if (keys == NULL || values == NULL || occupied == NULL) {
      __sable_rt_array_free_v1(keys);
      __sable_rt_array_free_v1(values);
      __sable_rt_array_free_v1(occupied);
      return 2;
    }
    for (size_t index = 0; index < CAPACITY; ++index) {
      keys[index] = 0;
      values[index] = 0;
      occupied[index] = 0;
    }
    const uint32_t first = map_insert(keys, values, occupied, 1, 100);
    const uint32_t second = map_insert(keys, values, occupied, 9, 900);
    const uint32_t third = map_insert(keys, values, occupied, 17, 1700);
    const uint32_t overwrite = map_insert(keys, values, occupied, 9, 901);
    const uint32_t found = map_get(keys, values, occupied, 9);
    const uint32_t collision = map_get(keys, values, occupied, 17);
    const uint32_t missing = map_get(keys, values, occupied, 25);
    __sable_rt_array_free_v1(keys);
    __sable_rt_array_free_v1(values);
    __sable_rt_array_free_v1(occupied);
    if (first != 2 || second != 2 || third != 2 || overwrite != 1 ||
        found != 901 || collision != 1700 || missing != 0) {
      return 1;
    }
  }
  return 42;
}
