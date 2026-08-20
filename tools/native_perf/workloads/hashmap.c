#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

void *__sable_rt_array_alloc_v1(uint64_t bytes);
void __sable_rt_array_free_v1(void *storage);

#ifndef WORK_UNITS
#error "WORK_UNITS must be supplied by the benchmark runner"
#endif

enum { CAPACITY = 8 };

struct map {
  int32_t *keys;
  uint64_t *values;
  uint8_t *occupied;
  size_t length;
};

static size_t home_bucket(int32_t key) {
  return ((uint64_t)((int64_t)key + INT64_C(2147483648))) % CAPACITY;
}

static bool map_insert(struct map *map, int32_t key, uint64_t value) {
  const size_t home = home_bucket(key);
  for (size_t distance = 0; distance < CAPACITY; ++distance) {
    size_t position = home + distance;
    if (position >= CAPACITY) {
      position -= CAPACITY;
    }
    if (map->occupied[position] == 0) {
      map->keys[position] = key;
      map->values[position] = value;
      map->occupied[position] = 1;
      ++map->length;
      return true;
    }
    if (map->keys[position] == key) {
      map->values[position] = value;
      return true;
    }
  }
  return false;
}

static bool map_get(const struct map *map, int32_t key, uint64_t *value) {
  const size_t home = home_bucket(key);
  for (size_t distance = 0; distance < CAPACITY; ++distance) {
    size_t position = home + distance;
    if (position >= CAPACITY) {
      position -= CAPACITY;
    }
    if (map->occupied[position] == 0) {
      return false;
    }
    if (map->keys[position] == key) {
      *value = map->values[position];
      return true;
    }
  }
  return false;
}

int main(void) {
  for (size_t iteration = 0; iteration < WORK_UNITS; ++iteration) {
    struct map map = {
        .keys = __sable_rt_array_alloc_v1(CAPACITY * sizeof(int32_t)),
        .values = __sable_rt_array_alloc_v1(CAPACITY * sizeof(uint64_t)),
        .occupied = __sable_rt_array_alloc_v1(CAPACITY * sizeof(uint8_t)),
        .length = 0,
    };
    if (map.keys == NULL || map.values == NULL || map.occupied == NULL) {
      __sable_rt_array_free_v1(map.keys);
      __sable_rt_array_free_v1(map.values);
      __sable_rt_array_free_v1(map.occupied);
      return 2;
    }
    for (size_t index = 0; index < CAPACITY; ++index) {
      map.keys[index] = 0;
      map.values[index] = 0;
      map.occupied[index] = 0;
    }

    uint64_t found = 0;
    uint64_t collision = 0;
    uint64_t missing = 0;
    const bool ok = map_insert(&map, 1, 100) && map_insert(&map, 9, 900) &&
                    map_insert(&map, 17, 1700) && map_insert(&map, 9, 901) &&
                    map_get(&map, 9, &found) && map_get(&map, 17, &collision) &&
                    !map_get(&map, 25, &missing) && map.length == 3 &&
                    found == 901 && collision == 1700;
    __sable_rt_array_free_v1(map.keys);
    __sable_rt_array_free_v1(map.values);
    __sable_rt_array_free_v1(map.occupied);
    if (!ok) {
      return 1;
    }
  }
  return 42;
}
