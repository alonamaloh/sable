//! Deterministic differential coverage for the public free-list return path.
//!
//! Sable resources cannot yet live in arrays, so the host generates ordinary
//! source with one statically named `BlockLease` per block.  A deliberately
//! small Rust model inserts and coalesces extents; after every return the
//! generated Sable test reads every real header and compares `(key, size,
//! next)` with that model.  Fixed seeds make failures reproducible.

use sable::{Options, test_file};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

const BLOCK_SIZE: u64 = 16;
const BLOCKS: usize = 12;
const SEEDS: [u64; 12] = [
    0x243f_6a88_85a3_08d3,
    0x1319_8a2e_0370_7344,
    0xa409_3822_299f_31d0,
    0x082e_fa98_ec4e_6c89,
    0x4528_21e6_38d0_1377,
    0xbe54_66cf_34e9_0c6c,
    0xc0ac_29b7_c97c_50dd,
    0x3f84_d5b5_b547_0917,
    0x9216_d5d9_8979_fb1b,
    0xd131_0ba6_98df_b5ac,
    0x2ffd_72db_d01a_dfb7,
    0xb8e1_afed_6a26_7e96,
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Extent {
    key: u64,
    size: u64,
}

fn shuffled_blocks(mut state: u64) -> Vec<usize> {
    let mut order: Vec<usize> = (0..BLOCKS).collect();
    for i in (1..BLOCKS).rev() {
        // xorshift64: deterministic, dependency-free, and ample for exercising
        // return order.  This is test generation, not a source of entropy.
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        order.swap(i, state as usize % (i + 1));
    }
    order
}

/// Insert one disjoint extent and maximally coalesce adjacent neighbors.
fn model_return(free: &mut Vec<Extent>, returned: Extent) -> (bool, bool) {
    free.sort_by_key(|extent| extent.key);
    let pos = free.partition_point(|extent| extent.key < returned.key);
    let left_adjacent = pos > 0 && free[pos - 1].key + free[pos - 1].size == returned.key;
    let right_adjacent = pos < free.len() && returned.key + returned.size == free[pos].key;

    free.insert(pos, returned);
    let mut coalesced: Vec<Extent> = Vec::with_capacity(free.len());
    for extent in free.drain(..) {
        if let Some(previous) = coalesced.last_mut() {
            let previous_end = previous.key + previous.size;
            assert!(previous_end <= extent.key, "reference extents overlap");
            if previous_end == extent.key {
                previous.size += extent.size;
                continue;
            }
        }
        coalesced.push(extent);
    }
    *free = coalesced;
    (left_adjacent, right_adjacent)
}

fn write_observation(source: &mut String, step: usize, free: &[Extent]) {
    let limit = BLOCK_SIZE * BLOCKS as u64;
    writeln!(
        source,
        "    expect_eq_u64(list.head, {});",
        free.first().map_or(limit, |extent| extent.key)
    )
    .unwrap();

    for (index, extent) in free.iter().enumerate() {
        let next = free.get(index + 1).map_or(limit, |next| next.key);
        writeln!(source, "    resource FreeHeader observed_{step}_{index} =").unwrap();
        writeln!(
            source,
            "        allocator_take_header(&mut state, {});",
            extent.key
        )
        .unwrap();
        writeln!(source, "    mut u64 observed_size_{step}_{index} = 0;").unwrap();
        writeln!(source, "    mut u64 observed_next_{step}_{index} = 0;").unwrap();
        writeln!(source, "    unsafe {{").unwrap();
        writeln!(
            source,
            "        raw<u8> observed_ptr_{step}_{index} = raw_offset(base, {});",
            extent.key
        )
        .unwrap();
        writeln!(
            source,
            "        observed_size_{step}_{index} = raw_header_size("
        )
        .unwrap();
        writeln!(
            source,
            "            observed_ptr_{step}_{index}, &observed_{step}_{index});"
        )
        .unwrap();
        writeln!(
            source,
            "        observed_next_{step}_{index} = raw_header_next("
        )
        .unwrap();
        writeln!(
            source,
            "            observed_ptr_{step}_{index}, &observed_{step}_{index});"
        )
        .unwrap();
        writeln!(source, "    }}").unwrap();
        writeln!(
            source,
            "    expect_eq_u64(observed_size_{step}_{index}, {});",
            extent.size
        )
        .unwrap();
        writeln!(
            source,
            "    expect_eq_u64(observed_next_{step}_{index}, {next});"
        )
        .unwrap();
        writeln!(
            source,
            "    allocator_put_header(&mut state, observed_{step}_{index});"
        )
        .unwrap();
    }
}

fn write_scenario(source: &mut String, scenario: usize, seed: u64, coverage: &mut u8) {
    let limit = BLOCK_SIZE * BLOCKS as u64;
    writeln!(source, "fn test_seed_{scenario}() {{").unwrap();
    writeln!(
        source,
        "    unsafe system_alloc({limit}) as (base, resource mem, resource release);"
    )
    .unwrap();
    writeln!(
        source,
        "    mut resource AllocatorState state = allocator_create(mem);"
    )
    .unwrap();
    writeln!(
        source,
        "    mut resource FreeBlock block_0 = allocator_take_free(&mut state, 0);"
    )
    .unwrap();
    for block in 1..BLOCKS {
        writeln!(source, "    mut resource FreeBlock block_{block} =").unwrap();
        writeln!(
            source,
            "        free_block_split(&mut block_{}, {BLOCK_SIZE});",
            block - 1
        )
        .unwrap();
    }
    for block in 0..BLOCKS {
        writeln!(
            source,
            "    resource BlockLease lease_{block} = free_block_lease(block_{block});"
        )
        .unwrap();
    }
    writeln!(
        source,
        "    var mut list = FreeListState::make({limit}, {limit});"
    )
    .unwrap();

    let mut free = Vec::new();
    for (step, block) in shuffled_blocks(seed).into_iter().enumerate() {
        let extent = Extent {
            key: block as u64 * BLOCK_SIZE,
            size: BLOCK_SIZE,
        };
        let (left, right) = model_return(&mut free, extent);
        *coverage |= 1 << ((left as u8) * 2 + right as u8);
        writeln!(
            source,
            "\n    free_list_return(base, &mut list, &mut state, {}, {BLOCK_SIZE}, lease_{block});",
            extent.key
        )
        .unwrap();
        write_observation(source, step, &free);
    }

    writeln!(source).unwrap();
    writeln!(source, "    mut resource FreeHeader final_header =").unwrap();
    writeln!(source, "        allocator_take_header(&mut state, 0);").unwrap();
    writeln!(source, "    unsafe {{").unwrap();
    writeln!(source, "        raw_header_clear(base, &mut final_header);").unwrap();
    writeln!(source, "        resource FreeBlock whole_free =").unwrap();
    writeln!(
        source,
        "            raw_from_free_header(base, final_header);"
    )
    .unwrap();
    writeln!(source, "    }}").unwrap();
    writeln!(source, "    allocator_put_free(&mut state, whole_free);").unwrap();
    writeln!(
        source,
        "    resource RawSpan whole = allocator_destroy(state);"
    )
    .unwrap();
    writeln!(source, "    unsafe system_dealloc(base, whole, release);").unwrap();
    writeln!(source, "}}").unwrap();
    writeln!(source).unwrap();
}

fn generated_source() -> String {
    let mut source = String::from(
        "use free_list_return;\n\
         use free_list_remove_head;\n\n\
         /// pre actual = expected\n\
         fn expect_eq_u64(u64 actual, u64 expected) {\n\
         }\n\n",
    );
    let mut coverage = 0_u8;
    for (scenario, seed) in SEEDS.into_iter().enumerate() {
        write_scenario(&mut source, scenario, seed, &mut coverage);
    }
    assert_eq!(coverage, 0b1111, "seeds must cover all adjacency cases");
    source
}

fn verifies_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("corpus")
        .join("verifies")
}

struct Fixture {
    dir: PathBuf,
    file: PathBuf,
}

impl Fixture {
    fn create(source: &str) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "sable-free-list-return-random-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("generated.sable");
        std::fs::write(&file, source).unwrap();
        Self { dir, file }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.file);
        let _ = std::fs::remove_dir(&self.dir);
    }
}

#[test]
fn seeded_return_orders_match_reference_allocator() {
    let fixture = Fixture::create(&generated_source());
    let opts = Options {
        module_paths: vec![verifies_dir()],
        ..Options::default()
    };
    let reports = test_file(&fixture.file, &opts).unwrap_or_else(|failures| {
        panic!(
            "generated fixture failed the front end:\n{}",
            failures
                .iter()
                .map(|failure| failure.rendered.as_str())
                .collect::<Vec<_>>()
                .join("\n")
        )
    });

    assert_eq!(reports.len(), SEEDS.len());
    for report in reports {
        if let Err(message) = report.outcome {
            panic!(
                "{} diverged from the reference allocator: {message}",
                report.name
            );
        }
    }
}
