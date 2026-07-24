//@ compile-flags: -Zvalidate-mir -Zmir-opt-level=4 -Cpanic=abort

// EMIT_MIR loop_preload_marker.decode_baseline.LoopPreloadMarker.after.mir
// EMIT_MIR loop_preload_marker.decode_baseline_no_loop.LoopPreloadMarker.after.mir
// EMIT_MIR loop_preload_marker.same_name_wrong_shape.LoopPreloadMarker.after.mir

// CHECK-LABEL: fn decode_baseline(
// CHECK: loop_preload_candidate = SnappyCopy12Slice;
// CHECK-LABEL: fn decode_baseline_no_loop(
// CHECK-NOT: loop_preload_candidate = SnappyCopy12Slice;
// CHECK-LABEL: fn same_name_wrong_shape(
// CHECK-NOT: loop_preload_candidate = SnappyCopy12Slice;

const TABLE: [u16; 256] = [0; 256];

#[inline(always)]
unsafe fn load_u32(input: &[u8], pos: usize) -> u32 {
    unsafe { (input.as_ptr().add(pos) as *const u32).read_unaligned() }.to_le()
}

#[inline(never)]
fn decode_baseline(input: &[u8]) -> u64 {
    let mut pos = 0;
    let mut checksum = 0u64;
    let mut iterations = 0;
    while iterations < 8 {
        let tag = input[pos];
        let tag_type = (tag & 3) as usize;
        let entry = TABLE[tag as usize] as usize;
        let loaded = unsafe { load_u32(input, pos + 1) };
        let mask = (1u32 << (tag_type * 8)).wrapping_sub(1);
        let offset = (entry & 0x700) | (loaded & mask) as usize;
        checksum = checksum.wrapping_add((entry & 0xff) as u64).wrapping_add(offset as u64);
        pos += 1 + tag_type;
        iterations += 1;
    }
    checksum ^ pos as u64
}

#[inline(never)]
fn decode_baseline_no_loop(input: &[u8]) -> u64 { input.len() as u64 }

#[inline(never)]
fn same_name_wrong_shape(input: &[u8]) -> u64 {
    let mut i = 0;
    let mut sum = 0;
    while i < input.len() { sum += input[i] as u64; i += 1; }
    sum
}

fn main() {
    let input = [1u8; 64];
    let _ = decode_baseline(&input);
    assert_eq!(decode_baseline_no_loop(&input), 64);
    let _ = same_name_wrong_shape(&input);
}
