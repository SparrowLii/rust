//! Strength reduction: replaces `x * C` with `x << k` when `C == 2^k`.
//!
//! MIR `Mul` wraps on overflow and `Shl` masks the shift amount to the bit
//! width, so for every integer type `x * 2^k` and `x << k` agree modulo `2^n`,
//! including the `C == T::MIN` bit pattern for signed types.

use rustc_const_eval::interpret::Scalar;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

pub(super) struct MulToShift;

impl<'tcx> crate::MirPass<'tcx> for MulToShift {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() >= 2
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let typing_env = body.typing_env(tcx);
        for block in body.basic_blocks.as_mut_preserves_cfg() {
            for statement in block.statements.iter_mut() {
                let StatementKind::Assign((.., rvalue)) = &mut statement.kind else {
                    continue;
                };
                let Rvalue::BinaryOp(BinOp::Mul, ops) = &*rvalue else {
                    continue;
                };
                let (lhs, rhs) = &**ops;

                // `Mul` is commutative, so accept the constant on either side.
                let (operand, konst) =
                    if rhs.constant().is_some() { (lhs, rhs) } else { (rhs, lhs) };
                let Some(konst) = konst.constant() else { continue };
                let ty = konst.const_.ty();
                if !ty.is_integral() {
                    continue;
                }
                let Some(scalar) = konst.const_.try_eval_scalar_int(tcx, typing_env) else {
                    continue;
                };
                let bits = scalar.to_uint(scalar.size());
                // Skip `x * 1`: not a shift's job, GVN already folds it.
                if bits <= 1 || !bits.is_power_of_two() {
                    continue;
                }
                let amount = Operand::const_from_scalar(
                    tcx,
                    ty,
                    Scalar::from_uint(bits.trailing_zeros(), scalar.size()),
                    konst.span,
                );
                *rvalue = Rvalue::BinaryOp(BinOp::Shl, Box::new((operand.clone(), amount)));
            }
        }
    }

    fn is_required(&self) -> bool {
        false
    }
}
