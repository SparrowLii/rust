//@ test-mir-pass: MulToShift
//! Checks that multiplications by a power of two are replaced by a left shift.

// EMIT_MIR mul_to_shift.mul_pow2.MulToShift.diff
// CHECK-LABEL: fn mul_pow2(
// CHECK-NOT: Mul(
// CHECK: Shl({{.*}}, const 3_u32)
pub fn mul_pow2(x: u32) -> u32 {
    x * 8
}

// EMIT_MIR mul_to_shift.mul_pow2_commuted.MulToShift.diff
// CHECK-LABEL: fn mul_pow2_commuted(
// CHECK-NOT: Mul(
// CHECK: Shl({{.*}}, const 4_i64)
pub fn mul_pow2_commuted(x: i64) -> i64 {
    16 * x
}

// EMIT_MIR mul_to_shift.mul_not_pow2.MulToShift.diff
// CHECK-LABEL: fn mul_not_pow2(
// CHECK: Mul(
// CHECK-NOT: Shl(
pub fn mul_not_pow2(x: u32) -> u32 {
    x * 7
}

// EMIT_MIR mul_to_shift.mul_variable.MulToShift.diff
// CHECK-LABEL: fn mul_variable(
// CHECK: Mul(
// CHECK-NOT: Shl(
pub fn mul_variable(x: u32, y: u32) -> u32 {
    x * y
}

fn main() {
    mul_pow2(5);
    mul_pow2_commuted(5);
    mul_not_pow2(5);
    mul_variable(5, 3);
}
