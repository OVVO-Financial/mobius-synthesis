#!/usr/bin/env python3
"""Silence the linter diagnostics of the ported StrongPNT sources.

`scripts/strongpnt_424/apply.py`, `apply_post.py`, `apply_pnt5_mid.py` and
`apply_pnt5_strong.py` rewrite the pinned StrongPNT revision so it elaborates
against Mathlib 4.24.  Elaborating is not the same as being quiet: the pinned
sources were written against an older Mathlib and leave 257 diagnostics behind,
which Lake re-emits into the RHLean build log on every run.  Those sources are
repository-owned -- we rewrite them -- so the noise is ours, and this layer
removes it.

Run this last; the positions below describe the sources as the other four
scripts leave them.

Rather than 257 hand-written context patches, this is driven by the linter's
own report: every entry in `SITES` is a `file line col kind payload` record
copied from the `scripts/lean_diagnostic_inventory.py` output of a build, and
the rewrite for each kind is mechanical.  Each position is verified against the
source before it is touched, so drift in the pinned upstream revision fails the
run instead of corrupting a proof.

Every rewrite is a pure noise removal:

* `simp-arg`   -- drop a `simp` argument the `linter.unusedSimpArgs` linter
                  reports as never firing.  An argument that did not fire
                  cannot change what the call proves.
* `intro`      -- merge adjacent `intro`s exactly as Lean's own `Try this:`
                  suggestion spells them; the merged argument list is checked
                  against the suggestion before the edit is made.
* `ring-nf`    -- `ring` reported `Try this: ring_nf`, meaning it closed the
                  goal only through its own normalization fallback.  Call the
                  tactic that does the work.
* `rename`     -- a deprecated lemma replaced by the alias target named in its
                  own deprecation message, so the statement is unchanged.
* `drop-line`  -- a tactic Lean reports as doing nothing.
* `import`     -- a `deprecated_module` shim replaced by exactly the imports
                  that shim contains, so the import closure is unchanged.

None of this changes any proof's mathematical content.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STRONGPNT = ROOT / ".lake" / "packages" / "StrongPNT" / "StrongPNT"

# Bracketing characters that make a comma non-separating inside a `simp` list.
OPENERS = "([{⟨"
CLOSERS = ")]}⟩"
PAIRS = dict(zip(CLOSERS, OPENERS))

# Deprecated module shims, replaced by their own contents.  Each shim file in
# Mathlib 4.24 consists of these imports plus the `deprecated_module` command,
# so substituting them leaves the import closure of the file unchanged.
IMPORT_REPLACEMENTS: dict[str, tuple[str, ...]] = {
    "Mathlib.Data.Real.Pi.Bounds": ("Mathlib.Analysis.Real.Pi.Bounds",),
    "Mathlib.Data.Complex.ExponentialBounds": (
        "Mathlib.Analysis.Complex.ExponentialBounds",
    ),
    "Mathlib.Tactic.FunProp.Differentiable": (
        "Mathlib.Analysis.Calculus.FDeriv.Basic",
        "Mathlib.Analysis.Calculus.FDeriv.Comp",
        "Mathlib.Analysis.Calculus.FDeriv.Prod",
        "Mathlib.Analysis.Calculus.FDeriv.Pi",
        "Mathlib.Analysis.Calculus.FDeriv.Add",
        "Mathlib.Analysis.Calculus.FDeriv.Mul",
        "Mathlib.Analysis.Calculus.Deriv.Inv",
        "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
        "Mathlib.Analysis.SpecialFunctions.Log.Deriv",
        "Mathlib.Tactic.FunProp",
    ),
}

# file | line | col | kind | payload
#
# `simp-arg` payload is the argument text the linter printed; `intro` payload is
# the full suggested `intro` line; `rename` payload is `old -> new`; `ring-nf`,
# `drop-line` and `import` take no payload beyond what the position implies.
SITES = """
PNT1_ComplexAnalysis.lean 398 10 simp-arg dist_self_add_right
PNT1_ComplexAnalysis.lean 404 28 simp-arg hε_pos.le
PNT1_ComplexAnalysis.lean 596 34 simp-arg dist_zero_right
PNT1_ComplexAnalysis.lean 689 33 simp-arg dist_zero_right
PNT1_ComplexAnalysis.lean 833 8 simp-arg Complex.dist_eq
PNT1_ComplexAnalysis.lean 1017 10 simp-arg v
PNT1_ComplexAnalysis.lean 1108 10 simp-arg Complex.dist_eq
PNT1_ComplexAnalysis.lean 1125 12 simp-arg Complex.dist_eq
PNT1_ComplexAnalysis.lean 1501 10 simp-arg AbsoluteValue.map_zero
PNT1_ComplexAnalysis.lean 1888 8 simp-arg Complex.norm_real
PNT1_ComplexAnalysis.lean 2754 13 simp-arg show (r + R) / 2 = (r + R) / 2 from rfl
PNT1_ComplexAnalysis.lean 2790 13 simp-arg show (r + R) / 2 = (r + R) / 2 from rfl
PNT1_ComplexAnalysis.lean 2925 13 simp-arg show (r + R) / 2 = (r + R) / 2 from rfl
PNT1_ComplexAnalysis.lean 2929 13 simp-arg show (r + R) / 2 = (r + R) / 2 from rfl
PNT1_ComplexAnalysis.lean 4078 10 simp-arg norm_mul
PNT1_ComplexAnalysis.lean 4180 17 simp-arg γv
PNT1_ComplexAnalysis.lean 4252 26 simp-arg add_comm
PNT1_ComplexAnalysis.lean 4252 36 simp-arg add_left_comm
PNT1_ComplexAnalysis.lean 4252 51 simp-arg add_assoc
PNT1_ComplexAnalysis.lean 4252 62 simp-arg add_sub_cancel
PNT1_ComplexAnalysis.lean 4254 26 simp-arg add_comm
PNT1_ComplexAnalysis.lean 4254 36 simp-arg add_left_comm
PNT1_ComplexAnalysis.lean 4254 51 simp-arg add_assoc
PNT1_ComplexAnalysis.lean 4254 62 simp-arg add_sub_cancel
PNT1_ComplexAnalysis.lean 4255 54 simp-arg hre'
PNT1_ComplexAnalysis.lean 4256 54 simp-arg him'
PNT1_ComplexAnalysis.lean 4287 98 simp-arg hvertnorm
PNT1_ComplexAnalysis.lean 4419 123 simp-arg sub_zero
PNT1_ComplexAnalysis.lean 4424 113 simp-arg zero_sub
PNT1_ComplexAnalysis.lean 4437 10 simp-arg norm_mul
PNT1_ComplexAnalysis.lean 4443 8 simp-arg norm_mul
PNT1_ComplexAnalysis.lean 4623 52 simp-arg add_comm
PNT1_ComplexAnalysis.lean 4623 62 simp-arg add_left_comm
PNT1_ComplexAnalysis.lean 4676 32 simp-arg add_comm
PNT1_ComplexAnalysis.lean 4676 42 simp-arg add_left_comm
PNT1_ComplexAnalysis.lean 4680 45 simp-arg add_comm
PNT1_ComplexAnalysis.lean 4680 55 simp-arg add_left_comm
PNT1_ComplexAnalysis.lean 4964 49 simp-arg Algebra.id.smul_eq_mul
PNT1_ComplexAnalysis.lean 5485 10 simp-arg x
PNT1_ComplexAnalysis.lean 5790 10 simp-arg norm_ne_zero_iff
PNT2_LogDerivative.lean 365 14 simp-arg h_cases
PNT2_LogDerivative.lean 778 12 simp-arg Complex.norm_of_nonneg (le_of_lt hR_pos)
PNT2_LogDerivative.lean 999 2 intro intro h_f_rho_ne_zero h_rho_in_KfR1
PNT2_LogDerivative.lean 1007 2 intro intro h_f_zero_ne_zero h_f_eq_zero
PNT2_LogDerivative.lean 1038 2 intro intro h_f_zero_ne_zero h_zero_in_KfR1
PNT2_LogDerivative.lean 1053 2 intro intro ρ h_ρ_in_zeros h_ρ_eq_zero
PNT2_LogDerivative.lean 1156 33 simp-arg norm_mul
PNT2_LogDerivative.lean 1281 30 simp-arg hnorm_real
PNT2_LogDerivative.lean 2075 28 simp-arg smul_eq_mul
PNT2_LogDerivative.lean 2186 2 intro intro S_zeros _inst
PNT2_LogDerivative.lean 2355 31 simp-arg dist_zero_right
PNT2_LogDerivative.lean 2798 33 simp-arg dist_zero_right
PNT2_LogDerivative.lean 2912 12 simp-arg h1
PNT2_LogDerivative.lean 2920 13 rename mul_lt_mul_right -> mul_lt_mul_iff_left₀
PNT2_LogDerivative.lean 3158 2 intro intro w hw ρ hρ
PNT2_LogDerivative.lean 3267 49 simp-arg mul_assoc
PNT2_LogDerivative.lean 3648 73 simp-arg mul_assoc
PNT2_LogDerivative.lean 3649 10 simp-arg add_comm
PNT2_LogDerivative.lean 3649 20 simp-arg add_left_comm
PNT2_LogDerivative.lean 3649 35 simp-arg add_assoc
PNT2_LogDerivative.lean 3655 23 simp-arg deriv_const_mul
PNT2_LogDerivative.lean 3657 8 simp-arg hlin
PNT2_LogDerivative.lean 3657 24 simp-arg hderiv_ab
PNT2_LogDerivative.lean 3657 35 simp-arg a
PNT2_LogDerivative.lean 3657 38 simp-arg b
PNT2_LogDerivative.lean 3658 55 simp-arg add_left_comm
PNT2_LogDerivative.lean 3658 70 simp-arg add_assoc
PNT2_LogDerivative.lean 3676 54 simp-arg neg_mul_neg
PNT2_LogDerivative.lean 3692 35 simp-arg mul_comm
PNT2_LogDerivative.lean 3692 45 simp-arg mul_left_comm
PNT2_LogDerivative.lean 3861 8 simp-arg Complex.star_def
PNT2_LogDerivative.lean 3879 10 simp-arg abs_of_nonneg (sq_nonneg R)
PNT2_LogDerivative.lean 3884 20 simp-arg conj_norm_eq_norm
PNT3_RiemannZeta.lean 125 6 rename Units.eq_iff -> Units.val_inj
PNT3_RiemannZeta.lean 160 48 simp-arg inclusion_commutes_with_division
PNT3_RiemannZeta.lean 242 33 simp-arg norm_one
PNT3_RiemannZeta.lean 251 56 simp-arg mul_left_comm
PNT3_RiemannZeta.lean 251 71 simp-arg mul_assoc
PNT3_RiemannZeta.lean 325 110 simp-arg Complex.mul_I_re
PNT3_RiemannZeta.lean 327 77 simp-arg h3
PNT3_RiemannZeta.lean 350 107 simp-arg add_zero
PNT3_RiemannZeta.lean 355 44 simp-arg norm_one
PNT3_RiemannZeta.lean 486 15 simp-arg NNReal.coe_mk
PNT3_RiemannZeta.lean 549 95 simp-arg add_zero
PNT3_RiemannZeta.lean 645 31 simp-arg Complex.ofReal_re
PNT3_RiemannZeta.lean 645 68 simp-arg mul_zero
PNT3_RiemannZeta.lean 645 78 simp-arg add_zero
PNT3_RiemannZeta.lean 675 10 simp-arg Finset.sum_range_zero
PNT3_RiemannZeta.lean 758 10 simp-arg Nat.cast_zero
PNT3_RiemannZeta.lean 791 35 simp-arg one_div
PNT3_RiemannZeta.lean 878 16 simp-arg h
PNT3_RiemannZeta.lean 904 8 simp-arg h
PNT3_RiemannZeta.lean 1264 10 simp-arg mul_comm
PNT3_RiemannZeta.lean 1264 35 simp-arg mul_assoc
PNT3_RiemannZeta.lean 1275 41 simp-arg mul_comm
PNT3_RiemannZeta.lean 1275 51 simp-arg mul_left_comm
PNT3_RiemannZeta.lean 1275 66 simp-arg mul_assoc
PNT3_RiemannZeta.lean 1419 16 simp-arg Complex.ofReal_sub
PNT3_RiemannZeta.lean 1463 14 simp-arg add_comm
PNT3_RiemannZeta.lean 1463 39 simp-arg add_assoc
PNT3_RiemannZeta.lean 1513 22 simp-arg add_left_comm
PNT3_RiemannZeta.lean 1513 37 simp-arg add_assoc
PNT3_RiemannZeta.lean 1619 44 simp-arg hmul_eq
PNT3_RiemannZeta.lean 1692 51 simp-arg add_assoc
PNT3_RiemannZeta.lean 1729 55 simp-arg one_div
PNT3_RiemannZeta.lean 2415 30 simp-arg Complex.mul_re
PNT3_RiemannZeta.lean 2656 2 intro intro x hx y hy
PNT3_RiemannZeta.lean 2684 12 simp-arg Complex.sub_re
PNT3_RiemannZeta.lean 2684 44 simp-arg add_comm
PNT3_RiemannZeta.lean 2684 54 simp-arg add_left_comm
PNT3_RiemannZeta.lean 2684 69 simp-arg add_assoc
PNT3_RiemannZeta.lean 2966 53 simp-arg mul_left_comm
PNT3_RiemannZeta.lean 2966 68 simp-arg mul_assoc
PNT3_RiemannZeta.lean 2982 63 simp-arg mul_left_comm
PNT3_RiemannZeta.lean 2982 78 simp-arg mul_assoc
PNT3_RiemannZeta.lean 2989 69 simp-arg mul_left_comm
PNT3_RiemannZeta.lean 2989 84 simp-arg mul_assoc
PNT3_RiemannZeta.lean 2991 16 simp-arg mul_comm
PNT3_RiemannZeta.lean 2991 26 simp-arg mul_left_comm
PNT3_RiemannZeta.lean 3197 50 simp-arg hneg
PNT3_RiemannZeta.lean 3573 10 simp-arg Complex.ofReal_im
PNT3_RiemannZeta.lean 3722 26 simp-arg norm_mul
PNT3_RiemannZeta.lean 3831 41 simp-arg sub_add_cancel
PNT3_RiemannZeta.lean 3973 26 simp-arg hg0
PNT3_RiemannZeta.lean 4451 2 intro intro t ht r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 c hfin z hz
PNT3_RiemannZeta.lean 4564 28 simp-arg add_left_comm
PNT3_RiemannZeta.lean 4564 43 simp-arg add_assoc
PNT3_RiemannZeta.lean 4566 26 simp-arg add_left_comm
PNT3_RiemannZeta.lean 4566 41 simp-arg add_assoc
PNT3_RiemannZeta.lean 4614 44 simp-arg add_assoc
PNT3_RiemannZeta.lean 4706 23 simp-arg add_left_comm
PNT3_RiemannZeta.lean 4729 50 simp-arg div_mul_cancel
PNT4_ZeroFreeRegion.lean 354 10 simp-arg Complex.ofReal_add
PNT4_ZeroFreeRegion.lean 437 30 simp-arg add_left_comm
PNT4_ZeroFreeRegion.lean 437 45 simp-arg add_assoc
PNT4_ZeroFreeRegion.lean 655 14 simp-arg two_mul
PNT4_ZeroFreeRegion.lean 655 23 simp-arg add_comm
PNT4_ZeroFreeRegion.lean 655 33 simp-arg add_left_comm
PNT4_ZeroFreeRegion.lean 655 48 simp-arg add_assoc
PNT4_ZeroFreeRegion.lean 773 13 simp-arg Complex.ofReal_add
PNT4_ZeroFreeRegion.lean 773 33 simp-arg Complex.ofReal_sub
PNT4_ZeroFreeRegion.lean 1092 24 simp-arg Complex.re_ofReal_mul
PNT4_ZeroFreeRegion.lean 1168 13 simp-arg Function.update_of_ne h2ne1
PNT4_ZeroFreeRegion.lean 1335 8 simp-arg ne_of_gt h_pos
PNT4_ZeroFreeRegion.lean 1522 14 simp-arg add_comm
PNT4_ZeroFreeRegion.lean 1584 14 simp-arg add_comm
PNT4_ZeroFreeRegion.lean 1793 43 simp-arg Complex.ofReal_im
PNT4_ZeroFreeRegion.lean 1808 14 simp-arg mul_neg
PNT4_ZeroFreeRegion.lean 1808 33 simp-arg mul_left_comm
PNT4_ZeroFreeRegion.lean 1869 45 simp-arg Complex.mul_I_re
PNT4_ZeroFreeRegion.lean 1881 26 simp-arg Complex.I_re
PNT4_ZeroFreeRegion.lean 1881 40 simp-arg Complex.I_im
PNT4_ZeroFreeRegion.lean 1888 78 simp-arg Complex.I_re
PNT4_ZeroFreeRegion.lean 1888 92 simp-arg Complex.I_im
PNT4_ZeroFreeRegion.lean 2043 10 simp-arg ArithmeticFunction.vonMangoldt_apply
PNT4_ZeroFreeRegion.lean 2058 16 simp-arg h_vm_zero
PNT4_ZeroFreeRegion.lean 2312 14 simp-arg ArithmeticFunction.vonMangoldt_apply
PNT4_ZeroFreeRegion.lean 2314 14 simp-arg ArithmeticFunction.vonMangoldt_apply
PNT4_ZeroFreeRegion.lean 2315 18 simp-arg hv0C
PNT4_ZeroFreeRegion.lean 3002 13 simp-arg ArithmeticFunction.vonMangoldt_apply
PNT4_ZeroFreeRegion.lean 3038 10 simp-arg zero_add
PNT4_ZeroFreeRegion.lean 3100 58 simp-arg one_div
PNT4_ZeroFreeRegion.lean 3237 10 simp-arg add_comm
PNT4_ZeroFreeRegion.lean 3459 58 simp-arg Complex.mul_I_im
PNT4_ZeroFreeRegion.lean 3686 41 simp-arg mul_comm
PNT4_ZeroFreeRegion.lean 3704 47 simp-arg ht_im
PNT4_ZeroFreeRegion.lean 3711 47 simp-arg ht_re
PNT4_ZeroFreeRegion.lean 3716 61 simp-arg Complex.I_mul_re
PNT4_ZeroFreeRegion.lean 3717 80 simp-arg Complex.I_mul_im
PNT4_ZeroFreeRegion.lean 3873 67 simp-arg Complex.mul_I_im
PNT4_ZeroFreeRegion.lean 3914 76 simp-arg Complex.one_im
PNT4_ZeroFreeRegion.lean 4012 36 simp-arg Complex.mul_I_im
PNT4_ZeroFreeRegion.lean 4016 34 simp-arg mul_comm
PNT4_ZeroFreeRegion.lean 4017 57 simp-arg mul_comm
PNT4_ZeroFreeRegion.lean 4066 2 intro intro c h_rho_mem h_z
PNT4_ZeroFreeRegion.lean 4491 19 simp-arg hc
PNT4_ZeroFreeRegion.lean 4491 59 simp-arg add_left_comm
PNT4_ZeroFreeRegion.lean 4491 74 simp-arg add_assoc
PNT4_ZeroFreeRegion.lean 5044 30 simp-arg Complex.mul_I_im
PNT4_ZeroFreeRegion.lean 5311 26 simp-arg Complex.mul_I_im
PNT4_ZeroFreeRegion.lean 5379 38 simp-arg Complex.mul_I_im
PNT4_ZeroFreeRegion.lean 5585 28 simp-arg add_comm
PNT4_ZeroFreeRegion.lean 5585 53 simp-arg add_assoc
PNT4_ZeroFreeRegion.lean 5689 28 simp-arg add_comm
PNT4_ZeroFreeRegion.lean 5689 53 simp-arg add_assoc
PNT4_ZeroFreeRegion.lean 5941 8 simp-arg norm_div
PNT4_ZeroFreeRegion.lean 5951 10 simp-arg norm_div
PNT4_ZeroFreeRegion.lean 5952 8 simp-arg hfun
PNT4_ZeroFreeRegion.lean 5999 44 simp-arg norm_div
PNT4_ZeroFreeRegion.lean 6014 12 simp-arg norm_div
PNT4_ZeroFreeRegion.lean 6014 30 simp-arg hden_σ
PNT4_ZeroFreeRegion.lean 6049 38 simp-arg hnorm_abs
PNT4_ZeroFreeRegion.lean 6131 89 simp-arg norm_div
PNT4_ZeroFreeRegion.lean 6137 93 simp-arg norm_div
PNT4_ZeroFreeRegion.lean 6324 12 simp-arg norm_one
PNT4_ZeroFreeRegion.lean 6335 29 simp-arg add_comm
PNT4_ZeroFreeRegion.lean 6335 54 simp-arg add_assoc
PNT4_ZeroFreeRegion.lean 6384 12 simp-arg Complex.mul_I_im
PNT5_Strong.lean 7 7 import Mathlib.Data.Real.Pi.Bounds
PNT5_Strong.lean 8 7 import Mathlib.Data.Complex.ExponentialBounds
PNT5_Strong.lean 231 23 simp-arg re_ofNat
PNT5_Strong.lean 232 26 simp-arg rpow_two
PNT5_Strong.lean 244 36 simp-arg re_ofNat
PNT5_Strong.lean 245 35 simp-arg rpow_two
PNT5_Strong.lean 1389 33 simp-arg norm_neg
PNT5_Strong.lean 1397 25 simp-arg c
PNT5_Strong.lean 1850 43 simp-arg z
PNT5_Strong.lean 1850 46 simp-arg w
PNT5_Strong.lean 1895 8 simp-arg neg_add_cancel_right
PNT5_Strong.lean 1895 30 simp-arg sub_right_inj
PNT5_Strong.lean 2326 6 drop-line norm_num
PNT5_Strong.lean 2464 26 simp-arg measurableSet_Iic
PNT5_Strong.lean 2464 45 simp-arg ae_restrict_eq
PNT5_Strong.lean 2512 28 simp-arg measurableSet_Iic
PNT5_Strong.lean 2512 47 simp-arg ae_restrict_eq
PNT5_Strong.lean 2512 63 simp-arg deriv_inv'
PNT5_Strong.lean 2512 75 simp-arg neg_eq_zero
PNT5_Strong.lean 2514 6 drop-line norm_num
PNT5_Strong.lean 2531 12 simp-arg Set.Iio
PNT5_Strong.lean 2545 26 simp-arg measurableSet_Ici
PNT5_Strong.lean 2545 45 simp-arg ae_restrict_eq
PNT5_Strong.lean 2548 15 simp-arg inv_neg
PNT5_Strong.lean 2619 11 rename mul_le_mul_right -> mul_le_mul_iff_left₀
PNT5_Strong.lean 3036 10 rename Real.add_lt_add_iff_left -> add_lt_add_iff_left
PNT5_Strong.lean 3163 32 simp-arg sigma1Of
PNT5_Strong.lean 3166 32 simp-arg sigma1Of
PNT5_Strong.lean 3171 22 simp-arg sigma1Of
PNT5_Strong.lean 3811 25 simp-arg norm_eq_abs
PNT5_Strong.lean 3811 38 simp-arg abs_neg
PNT5_Strong.lean 3811 47 simp-arg abs_one
PNT5_Strong.lean 3811 56 simp-arg one_mul
PNT5_Strong.lean 3811 65 simp-arg mul_one
PNT5_Strong.lean 3813 15 simp-arg norm_mul
PNT5_Strong.lean 3813 25 simp-arg norm_eq_abs
PNT5_Strong.lean 3813 38 simp-arg abs_neg
PNT5_Strong.lean 3813 47 simp-arg abs_one
PNT5_Strong.lean 3813 65 simp-arg mul_one
PNT5_Strong.lean 3817 27 simp-arg norm_eq_abs
PNT5_Strong.lean 3817 40 simp-arg abs_neg
PNT5_Strong.lean 3817 49 simp-arg abs_one
PNT5_Strong.lean 3817 58 simp-arg one_mul
PNT5_Strong.lean 3817 67 simp-arg mul_one
PNT5_Strong.lean 4185 5 ring-nf ring
PNT5_Strong.lean 4420 2 intro intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
PNT5_Strong.lean 4517 37 simp-arg norm_neg
PNT5_Strong.lean 5033 32 simp-arg div_pos_iff_of_pos_left
PNT5_Strong.lean 5152 27 simp-arg pow_one
PNT5_Strong.lean 5418 8 rename mul_le_mul_left -> mul_le_mul_iff_right₀
Z0.lean 48 12 simp-arg tendsto_principal_principal
Z0.lean 51 20 simp-arg ne_eq
Z0.lean 51 27 simp-arg add_eq_right
Z0.lean 51 41 simp-arg Complex.ofReal_eq_zero
Z0.lean 64 40 simp-arg Pi.neg_apply
Z0.lean 64 54 simp-arg Pi.sub_apply
ZetaZeroFree.lean 19 7 import Mathlib.Tactic.FunProp.Differentiable
ZetaZeroFree.lean 210 33 simp-arg mem_Icc
ZetaZeroFree.lean 224 33 simp-arg mem_Icc
"""


class Source:
    """One StrongPNT file, edited by absolute offset."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.text = path.read_text()
        self.starts = [0]
        for line in self.text.splitlines(keepends=True):
            self.starts.append(self.starts[-1] + len(line))

    def offset(self, line: int, col: int) -> int:
        return self.starts[line - 1] + col

    def line_span(self, line: int) -> tuple[int, int]:
        """Offsets of the start of `line` and the start of the next line."""
        return self.starts[line - 1], self.starts[line]

    def expect(self, offset: int, literal: str, what: str) -> None:
        found = self.text[offset : offset + len(literal)]
        if found != literal:
            raise SystemExit(
                f"{self.path.name}: expected {literal!r} at offset {offset} "
                f"for {what}, found {found!r}"
            )


def enclosing_brackets(text: str, offset: int) -> tuple[int, int]:
    """Offsets of the `[` and `]` of the simp list containing `offset`."""
    depth = 0
    index = offset - 1
    while index >= 0:
        char = text[index]
        if char in CLOSERS:
            depth += 1
        elif char in OPENERS:
            if depth == 0:
                if char != "[":
                    raise SystemExit(f"expected a simp list at offset {offset}")
                open_at = index
                break
            depth -= 1
        index -= 1
    else:
        raise SystemExit(f"no enclosing simp list for offset {offset}")

    depth = 0
    index = open_at + 1
    while index < len(text):
        char = text[index]
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            if depth == 0:
                if char != "]":
                    raise SystemExit(f"unbalanced simp list at offset {open_at}")
                return open_at, index
            depth -= 1
        index += 1
    raise SystemExit(f"unterminated simp list at offset {open_at}")


def split_items(inner: str, base: int) -> list[tuple[int, int]]:
    """Top-level comma-separated spans of a simp list, as absolute offsets."""
    spans: list[tuple[int, int]] = []
    depth = 0
    start = 0
    for index, char in enumerate(inner):
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
        elif char == "," and depth == 0:
            spans.append((base + start, base + index))
            start = index + 1
    spans.append((base + start, base + len(inner)))
    return spans


def rebuild_list(
    source: Source, open_at: int, close_at: int, drop: list[int]
) -> tuple[int, int, str]:
    """The edit that removes the arguments covering `drop` from a simp list."""
    inner = source.text[open_at + 1 : close_at]
    spans = split_items(inner, open_at + 1)

    keep: list[str] = []
    dropped = 0
    for start, end in spans:
        item = source.text[start:end]
        if any(start <= site < end for site in drop):
            dropped += 1
            continue
        stripped = item.strip()
        if stripped:
            keep.append(stripped)
    if dropped != len(drop):
        raise SystemExit(
            f"{source.path.name}: expected to drop {len(drop)} simp arguments "
            f"from the list at offset {open_at}, matched {dropped}"
        )

    if not keep:
        # `simp only []` is the identity-lemma-set call and has to keep its
        # brackets, but a bare `simp [...]` whose every argument was unused is
        # just `simp`, so drop the empty list and the space in front of it.
        if preceded_by_only(source.text, open_at):
            return open_at, close_at + 1, "[]"
        start = open_at
        while start > 0 and source.text[start - 1] == " ":
            start -= 1
        return start, close_at + 1, ""

    # A list written across several lines stays across several lines: rejoining
    # 15 arguments onto one 300-column line is its own kind of noise.
    if "\n" not in inner:
        return open_at, close_at + 1, "[" + ", ".join(keep) + "]"

    indent = continuation_indent(source, open_at, inner)
    lines: list[str] = []
    current = ""
    for index, item in enumerate(keep):
        piece = item + ("," if index < len(keep) - 1 else "")
        candidate = piece if not current else f"{current} {piece}"
        if current and len(indent) + len(candidate) > 98:
            lines.append(current)
            current = piece
        else:
            current = candidate
    lines.append(current)
    return open_at, close_at + 1, "[" + ("\n" + indent).join(lines) + "]"


def preceded_by_only(text: str, open_at: int) -> bool:
    """Is this simp list the argument of a `simp only`-style call?"""
    end = open_at
    while end > 0 and text[end - 1] in " \n":
        end -= 1
    return text[max(0, end - len("only")) : end] == "only"


def continuation_indent(source: Source, open_at: int, inner: str) -> str:
    """Indent used by the original continuation lines of a wrapped list."""
    newline = inner.find("\n")
    tail = inner[newline + 1 :]
    existing = tail[: len(tail) - len(tail.lstrip(" "))]
    if existing:
        return existing
    line_start = source.text.rfind("\n", 0, open_at) + 1
    return " " * (len(source.text[line_start:open_at]) - len(source.text[line_start:open_at].lstrip()) + 2)


def intro_edit(source: Source, line: int, col: int, suggestion: str) -> tuple[int, int, str]:
    """Merge the run of `intro`s starting at `line` into Lean's suggestion."""
    lines = source.text.splitlines()
    indent = " " * col
    args: list[str] = []
    last = line
    index = line
    while index <= len(lines):
        raw = lines[index - 1]
        code = raw.split("--", 1)[0].rstrip()
        stripped = code.strip()
        if not stripped:
            # A blank line inside the run is layout, not a new tactic block.
            if index == line:
                break
            index += 1
            continue
        if not code.startswith(indent + "intro ") or code[: len(indent)].strip():
            break
        args.extend(stripped[len("intro ") :].split())
        last = index
        index += 1

    merged = "intro " + " ".join(args)
    if merged != suggestion:
        raise SystemExit(
            f"{source.path.name}:{line}: merged {merged!r} does not match Lean's "
            f"suggestion {suggestion!r}"
        )
    start, _ = source.line_span(line)
    _, end = source.line_span(last)
    return start, end, f"{indent}{merged}\n"


def import_edit(source: Source, line: int, col: int, module: str) -> tuple[int, int, str]:
    source.expect(source.offset(line, col), module, "deprecated import")
    replacements = IMPORT_REPLACEMENTS.get(module)
    if replacements is None:
        raise SystemExit(f"no recorded replacement for deprecated import {module}")
    start, end = source.line_span(line)
    return start, end, "".join(f"import {name}\n" for name in replacements)


def parse_sites() -> dict[str, list[tuple[int, int, str, str]]]:
    sites: dict[str, list[tuple[int, int, str, str]]] = {}
    for raw in SITES.strip().splitlines():
        name, line, col, kind, payload = raw.split(" ", 4)
        sites.setdefault(name, []).append((int(line), int(col), kind, payload))
    return sites


def build_edits(source: Source, records: list[tuple[int, int, str, str]]) -> list[tuple[int, int, str]]:
    edits: list[tuple[int, int, str]] = []
    simp_groups: dict[tuple[int, int], list[int]] = {}

    for line, col, kind, payload in records:
        offset = source.offset(line, col)
        if kind == "simp-arg":
            source.expect(offset, payload, "unused simp argument")
            simp_groups.setdefault(enclosing_brackets(source.text, offset), []).append(offset)
        elif kind == "intro":
            source.expect(offset, "intro ", "intro suggestion")
            edits.append(intro_edit(source, line, col, payload))
        elif kind == "ring-nf":
            source.expect(offset, "ring", "ring suggestion")
            edits.append((offset, offset + len("ring"), "ring_nf"))
        elif kind == "rename":
            old, new = payload.split(" -> ")
            source.expect(offset, old, "deprecated name")
            edits.append((offset, offset + len(old), new))
        elif kind == "drop-line":
            source.expect(offset, payload, "no-op tactic")
            start, end = source.line_span(line)
            edits.append((start, end, ""))
        elif kind == "import":
            edits.append(import_edit(source, line, col, payload))
        else:
            raise SystemExit(f"unknown lint site kind {kind!r}")

    for (open_at, close_at), drop in simp_groups.items():
        edits.append(rebuild_list(source, open_at, close_at, drop))
    return edits


def apply_edits(source: Source, edits: list[tuple[int, int, str]]) -> None:
    edits.sort(key=lambda edit: edit[0], reverse=True)
    previous_start = len(source.text) + 1
    text = source.text
    for start, end, replacement in edits:
        if end > previous_start:
            raise SystemExit(
                f"{source.path.name}: overlapping lint edits at offset {start}"
            )
        text = text[:start] + replacement + text[end:]
        previous_start = start
    source.path.write_text(text)


def main() -> int:
    sites = parse_sites()
    total = 0
    for name, records in sites.items():
        path = STRONGPNT / name
        if not path.is_file():
            raise SystemExit(f"StrongPNT source not found: {path}")
        source = Source(path)
        if "-- StrongPNT 4.24 lint patch applied" in source.text:
            print(f"already lint-patched {name}")
            continue
        edits = build_edits(source, records)
        apply_edits(source, edits)
        with path.open("a") as handle:
            handle.write("\n-- StrongPNT 4.24 lint patch applied\n")
        total += len(records)
        print(f"lint-patched {name}: {len(records)} diagnostics")
    if total:
        print(f"StrongPNT 4.24 lint patch removed {total} diagnostics")
    return 0


if __name__ == "__main__":
    sys.exit(main())
