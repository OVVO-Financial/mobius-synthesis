import Mathlib
import RHLean.Analysis.PrimeSieveAbelIdentity

/-!
# The honest two-obligation reading of the Abel identity

`RHLean.Analysis.PrimeSieveAbelIdentity` proves the exact, hypothesis-free
identity

```text
primeSievePNTError y x
  = primeSieveMoebiusDiscrepancySum y x - primeSieveAbelBoundary y x,
```

with boundary term `primeSieveAbelBoundary y x = M(x/(y+1)) * R(y)`,
`M = mertensSummatory`, `R = primeSievePrimeDiscrepancy`.  This module only
takes norms of that identity.  The theorems are one triangle-inequality step
from the merged identity — trivial on purpose: their point is what they say,
not how they are proved.

## Integrity notes (the reason this module exists)

1. **Bounding the PNT error requires BOTH obligations.**  The triangle
   inequality controls `‖E‖` by the Abel face `‖S‖` PLUS the boundary term
   `‖M(K)‖·‖R(y)‖`, and conversely controls `‖S‖` by `‖E‖` plus the same
   boundary term.  `S` and `E` differ by the single term `M(K)·R(y)`; neither
   obligation subsumes the other.

2. **No kernel arrow exists from the Abel face to RH.**  As of this commit,
   `primeSieveMoebiusDiscrepancySum` occurs in the kernel in exactly the
   Abel/excursion module family (`PrimeSieveAbelIdentity`,
   `PrimeSieveLipschitzExcursion`, `PrimeSieveBackwardAffineExcursion`, and
   the affine repair modules importing them), none of which mention
   `NonzeroResponseRHScale`, `MertensEnergyBoundedStatement`,
   `ProjectedRenewalQuadraticBoundedStatement`, or `RiemannHypothesis`.  Any
   claim that a kernel chain "reduces RH to the Abel face" is false at this
   commit; see the record-029 audit.

3. **The boundary term is a second obligation of RH strength at `y ≍ √x`**:
   both factors are then of size `~√x`, and the best unconditional inputs give
   only `|M(K)·R(y)| ≪ x^{1−o(1)}`.

4. **The two halves of the merged development never compose.**  The
   collapse-identity domain (`Nat.sqrt x < y`, i.e. `x < y²`) and the
   canonical-pin domain (`x₀ = (y+1)² − 1 ≥ y²`) are disjoint in `x` for fixed
   `y`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- The Abel boundary term in factored norm form. -/
theorem norm_primeSieveAbelBoundary (y x : ℕ) :
    ‖primeSieveAbelBoundary y x‖
      = ‖mertensSummatory (x / (y + 1))‖ * ‖primeSievePrimeDiscrepancy y‖ := by
  unfold primeSieveAbelBoundary
  exact norm_mul _ _

/-- **The honest two-obligation bound.**  Bounding the PNT error requires BOTH
the Abel face `S = primeSieveMoebiusDiscrepancySum` AND the boundary term
`M(K)·R(y)`; this triangle inequality is everything the kernel provides in
this direction.  It is NOT a reduction of anything to the Abel face alone. -/
theorem norm_primeSievePNTError_le_two_obligations (y x : ℕ) :
    ‖primeSievePNTError y x‖
      ≤ ‖primeSieveMoebiusDiscrepancySum y x‖
        + ‖mertensSummatory (x / (y + 1))‖ * ‖primeSievePrimeDiscrepancy y‖ := by
  rw [primeSievePNTError_eq_moebiusDiscrepancySum_sub_abelBoundary,
    ← norm_primeSieveAbelBoundary]
  exact norm_sub_le _ _

/-- The reverse triangle: the Abel face is in turn controlled by the PNT error
and the boundary term.  Together with the previous theorem this states the
exact relationship: `S` and `E` differ by the single term `M(K)·R(y)`. -/
theorem norm_primeSieveMoebiusDiscrepancySum_le_two_obligations (y x : ℕ) :
    ‖primeSieveMoebiusDiscrepancySum y x‖
      ≤ ‖primeSievePNTError y x‖
        + ‖mertensSummatory (x / (y + 1))‖ * ‖primeSievePrimeDiscrepancy y‖ := by
  have h : primeSieveMoebiusDiscrepancySum y x
      = primeSievePNTError y x + primeSieveAbelBoundary y x := by
    rw [primeSievePNTError_eq_moebiusDiscrepancySum_sub_abelBoundary]
    ring
  rw [h, ← norm_primeSieveAbelBoundary]
  exact norm_add_le _ _

end RHLean.Analysis

end
