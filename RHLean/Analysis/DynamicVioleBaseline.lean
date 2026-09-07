import Mathlib
import RHLean.Analysis.NativePNTNormalizedSignedRecurrence
import RHLean.Analysis.NativePNTSquarePrefixMobiusError
import RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence
import RHLean.Proof.SquareBlockTransportBaseline

/-!
# Dynamic-denominator Viole baseline

This module formalizes the square-block prime-counting baseline tested in
`experiments/vf_dynamic_e_asymptote_test.py`.

The original Viole function used one fixed logarithmic-base convergence rate.
The corrected empirical study replaces that fixed rate by

```text
log b(x) = 1 + a / log x + b / (log x)^2,
a = 40.64408021414064,
b = -233.433772115277.
```

The leading constant is `1`, so the effective base satisfies `b(x) -> e` as
`x -> infinity`. The coefficients below are represented as exact rationals.
They were fitted on square-block midpoints from `10^3` through `10^5` and then
frozen before testing through `10^8`.

This file formalizes only the deterministic function and its exact insertion
into the existing arbitrary-baseline decomposition. It does not assert any
prime-counting error estimate, asymptotic superiority over `li`, or RH
implication.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Proof

/-- Fitted coefficient of `1 / log x` in the corrected dynamic logarithmic-base
exponent. The full fitted decimal `40.64408021414064` is stored exactly. -/
def dynamicVioleFitA : ℝ :=
  4064408021414064 / 100000000000000

/-- Fitted coefficient of `1 / (log x)^2` in the corrected dynamic
logarithmic-base exponent. The full fitted decimal `-233.433772115277` is
stored exactly. -/
def dynamicVioleFitB : ℝ :=
  -(233433772115277 / 1000000000000)

/-- The fitted value of `log b(x)`, where `b(x)` is the effective logarithmic
base used by the dynamic Viole denominator. The leading constant `1` encodes
the intended asymptotic base `e`. -/
def dynamicVioleLogBaseExponent (x : ℝ) : ℝ :=
  1 + dynamicVioleFitA / Real.log x +
    dynamicVioleFitB / (Real.log x) ^ 2

/-- The corresponding positive formal base `b(x) = exp(log b(x))`.
Positivity follows from `Real.exp_pos`; no claim is made here that the fitted
exponent itself is positive on every real input. -/
def dynamicVioleLogBase (x : ℝ) : ℝ :=
  Real.exp (dynamicVioleLogBaseExponent x)

/-- Dynamic replacement for the original fixed-base convergence correction.
Writing `L = log x` and `s = log b(x)`, this is

`(1 + L / s) * log (1 + s / L)`,

the logarithm of `(1 + 1 / log_b x)^(1 + log_b x)`. -/
def dynamicVioleCorrection (x : ℝ) : ℝ :=
  let L := Real.log x
  let s := dynamicVioleLogBaseExponent x
  (1 + L / s) * Real.log (1 + s / L)

/-- Square-block midpoint `r^2 + r + 1/2`. -/
def dynamicVioleSquareMidpoint (r : ℕ) : ℝ :=
  ((r ^ 2 : ℕ) : ℝ) + (r : ℝ) + 1 / 2

/-- The original square-block numerator `r^2`. -/
def dynamicVioleSquareNumerator (r : ℕ) : ℝ :=
  ((r ^ 2 : ℕ) : ℝ)

/-- Dynamic Viole denominator at the midpoint of square block `r`.
This is the exact denominator used by the empirically selected model. -/
def dynamicVioleDenominator (r : ℕ) : ℝ :=
  Real.log (dynamicVioleSquareNumerator r) -
    dynamicVioleCorrection (dynamicVioleSquareMidpoint r)

/-- Dynamic Viole anchor attached to the midpoint of square block `r`. -/
def dynamicVioleAnchor (r : ℕ) : ℝ :=
  dynamicVioleSquareNumerator r / dynamicVioleDenominator r

/-- Distance between consecutive square-block midpoint nodes. -/
theorem dynamicVioleSquareMidpoint_succ_sub (r : ℕ) :
    dynamicVioleSquareMidpoint (r + 1) - dynamicVioleSquareMidpoint r =
      2 * (r : ℝ) + 2 := by
  unfold dynamicVioleSquareMidpoint
  push_cast
  ring

/-- Linear interpolation of the dynamic Viole anchors on the segment from the
`r`th square midpoint to the next midpoint. -/
def dynamicVioleLinearSegment (r : ℕ) (x : ℝ) : ℝ :=
  dynamicVioleAnchor r +
    ((x - dynamicVioleSquareMidpoint r) / (2 * (r : ℝ) + 2)) *
      (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r)

@[simp] theorem dynamicVioleLinearSegment_left (r : ℕ) :
    dynamicVioleLinearSegment r (dynamicVioleSquareMidpoint r) =
      dynamicVioleAnchor r := by
  simp [dynamicVioleLinearSegment]

@[simp] theorem dynamicVioleLinearSegment_right (r : ℕ) :
    dynamicVioleLinearSegment r (dynamicVioleSquareMidpoint (r + 1)) =
      dynamicVioleAnchor (r + 1) := by
  have h : (2 * (r : ℝ) + 2) ≠ 0 := by positivity
  simp [dynamicVioleLinearSegment, dynamicVioleSquareMidpoint_succ_sub, h]

/-- Index of the midpoint segment containing a nonnegative real coordinate.
The closed-form inversion comes from solving `r^2 + r + 1/2 ≤ x` for `r`.
For inputs below the first meaningful prime-counting block, natural flooring
provides the harmless fallback index `0`. -/
def dynamicVioleMidpointIndex (x : ℝ) : ℕ :=
  Nat.floor ((Real.sqrt (4 * x - 1) - 1) / 2)

/-- Continuous piecewise-linear dynamic Viole baseline through the midpoint
anchors. This is the cumulative real-valued baseline used in the exact-activity
interval experiment. -/
def dynamicVioleBaselineReal (x : ℝ) : ℝ :=
  dynamicVioleLinearSegment (dynamicVioleMidpointIndex x) x

/-- Complex-valued wrapper required by the generic square-block transport
baseline API. -/
def dynamicVioleBaseline (x : ℝ) : ℂ :=
  (dynamicVioleBaselineReal x : ℂ)

/-- Exact specialization of the existing arbitrary-baseline decomposition to
the corrected dynamic Viole baseline. This is algebraic and imports no
empirical error claim. -/
theorem squarePrefixMertens_eq_dynamicVioleMain_sub_error (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      squareBlockBaselineMainPrefix dynamicVioleBaseline n -
        squareBlockBaselineTransportErrorPrefix dynamicVioleBaseline n := by
  exact squarePrefixMertens_eq_baselineMain_sub_error dynamicVioleBaseline n

end RHLean.Proof

namespace RHLean.Analysis

open RHLean.Proof

/-! ## Reciprocal-square coupling to the square clock -/

/-- The remaining local arithmetic seam for the Viole-clock route.

The left-hand state is deliberately the pure tail predicate: there is no
affine intercept and no globalization through a finite prefix.  The square
cutoff at stage `r` is the already-compiled floor `r^2 + r`, and the gain is
measured directly against the increment of `dynamicVioleAnchor`.

A proof of this proposition must therefore produce the new tail slope from the
signed arithmetic born in the single square block `r`; consumers may telescope
the resulting reciprocal-square gains, but cannot manufacture them. -/
def VioleClockReciprocalSquareCoupling
    (r0 : Nat) (c : Real) (eps : Nat → Real) : Prop :=
  2 ≤ r0 ∧ 0 < c ∧
  ∀ (r : Nat) (alpha : Real),
    r0 ≤ r →
    PrimeSieveStateDependentSelbergTailAbove (r ^ 2 + r) alpha →
    ∃ alpha' : Real,
      PrimeSieveStateDependentSelbergTailAbove
        ((r + 1) ^ 2 + (r + 1)) alpha' ∧
      alpha' ≤ alpha ∧
      c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r
        ≤ 1 / alpha' ^ 2 - 1 / alpha ^ 2

/-- Projection of the frozen coupling to one admissible square block. -/
theorem violeClockReciprocalSquareCoupling_step
    {r0 : Nat} {c : Real} {eps : Nat → Real}
    (h : VioleClockReciprocalSquareCoupling r0 c eps)
    (r : Nat) (alpha : Real) (hr : r0 ≤ r)
    (htail : PrimeSieveStateDependentSelbergTailAbove (r ^ 2 + r) alpha) :
    ∃ alpha' : Real,
      PrimeSieveStateDependentSelbergTailAbove
        ((r + 1) ^ 2 + (r + 1)) alpha' ∧
      alpha' ≤ alpha ∧
      c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r
        ≤ 1 / alpha' ^ 2 - 1 / alpha ^ 2 :=
  h.2.2 r alpha hr htail

private theorem violeClock_sum_increment_Ico
    (f : Nat → Real) {a b : Nat} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, (f (k + 1) - f k)) = f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub f b,
    Finset.sum_range_sub f a]
  abel

/-- Deterministic consumption of any selected slope chain: the local
reciprocal-square gains telescope exactly against the same Viole clock. -/
theorem violeClockReciprocalSquare_telescope
    (r0 R : Nat) (c : Real) (eps : Nat → Real) (a : Nat → Real)
    (hR : r0 ≤ R)
    (hstep : ∀ r : Nat, r ∈ Finset.Ico r0 R →
      c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r
        ≤ 1 / (a (r + 1)) ^ 2 - 1 / (a r) ^ 2) :
    c * (dynamicVioleAnchor R - dynamicVioleAnchor r0) -
        ∑ r ∈ Finset.Ico r0 R, eps r
      ≤ 1 / (a R) ^ 2 - 1 / (a r0) ^ 2 := by
  have hsum :
      (∑ r ∈ Finset.Ico r0 R,
        (c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r))
        ≤
      ∑ r ∈ Finset.Ico r0 R,
        (1 / (a (r + 1)) ^ 2 - 1 / (a r) ^ 2) := by
    exact Finset.sum_le_sum (fun r hr => hstep r hr)
  have hV :=
    violeClock_sum_increment_Ico dynamicVioleAnchor hR
  have hA :=
    violeClock_sum_increment_Ico (fun r => 1 / (a r) ^ 2) hR
  calc
    c * (dynamicVioleAnchor R - dynamicVioleAnchor r0) -
          ∑ r ∈ Finset.Ico r0 R, eps r
        = c * (∑ r ∈ Finset.Ico r0 R,
            (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r)) -
            ∑ r ∈ Finset.Ico r0 R, eps r := by rw [hV]
    _ = ∑ r ∈ Finset.Ico r0 R,
          (c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ ≤ ∑ r ∈ Finset.Ico r0 R,
          (1 / (a (r + 1)) ^ 2 - 1 / (a r) ^ 2) := hsum
    _ = 1 / (a R) ^ 2 - 1 / (a r0) ^ 2 := hA

/-- If cumulative leakage costs at most half the clock, the selected slope
chain retains at least half of the reciprocal-square clock gain. -/
theorem violeClockReciprocalSquare_of_half_leakage
    (r0 R : Nat) (c : Real) (eps : Nat → Real) (a : Nat → Real)
    (hR : r0 ≤ R)
    (hstep : ∀ r : Nat, r ∈ Finset.Ico r0 R →
      c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r
        ≤ 1 / (a (r + 1)) ^ 2 - 1 / (a r) ^ 2)
    (hleak :
      (∑ r ∈ Finset.Ico r0 R, eps r) ≤
        (c / 2) * (dynamicVioleAnchor R - dynamicVioleAnchor r0)) :
    1 / (a r0) ^ 2 +
        (c / 2) * (dynamicVioleAnchor R - dynamicVioleAnchor r0)
      ≤ 1 / (a R) ^ 2 := by
  have htel :=
    violeClockReciprocalSquare_telescope r0 R c eps a hR hstep
  nlinarith

/-! ## Exact signed square-block cutoff consumer -/

/-- The physical cutoff beneath the `r`th Viole midpoint. -/
def violeClockCutoff (r : Nat) : Nat := r ^ 2 + r

/-- The exact normalized signed response of the divisor block `(M,L]` at a
later endpoint `N`.  This is the socket in which one additive square block can
enter the first signed Selberg recurrence. -/
def nativePNTNormalizedFloorSquareBlockResponse
    (N M L : Nat) : Real :=
  ∑ d ∈ Finset.Ioc M L,
    nativePNTNormalizedFloorWeight N d * nativePNTNormalizedError (N / d)

/-- All terms of the normalized floor average outside the designated divisor
block.  No absolute value is taken. -/
def nativePNTNormalizedFloorOutsideSquareBlock
    (N M L : Nat) : Real :=
  nativePNTNormalizedFloorAverage N -
    nativePNTNormalizedFloorSquareBlockResponse N M L

/-- The signed Selberg remainder before any absolute constant is applied,
after division by the current endpoint. -/
def nativePNTNormalizedExactSignedRemainder (N : Nat) : Real :=
  ((nativeSelbergPair N - 2 * (N : Real) * Real.log (N : Real)) -
      (Real.log ((Nat.factorial N : Nat) : Real) -
        (N : Real) * Real.log (N : Real))) / (N : Real)

/-- The normalized floor recurrence with its exact signed remainder.  This is
the equality hidden underneath the scale-free absolute bound. -/
theorem nativePNTNormalized_signed_floor_recurrence_eq_exactRemainder
    (N : Nat) (hN : 1 ≤ N) :
    nativePNTNormalizedError N * Real.log (N : Real) +
        nativePNTNormalizedFloorAverage N =
      nativePNTNormalizedExactSignedRemainder N := by
  rw [← nativePNTNormalizedFloorSelbergMass_eq_average N hN]
  have hdecomp := nativePNTError_selberg_decomposition N
  have hnum :
      nativePNTError N * Real.log (N : Real) +
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) =
        (nativeSelbergPair N - 2 * (N : Real) * Real.log (N : Real)) -
          (Real.log ((Nat.factorial N : Nat) : Real) -
            (N : Real) * Real.log (N : Real)) := by
    linarith
  unfold nativePNTNormalizedError nativePNTNormalizedFloorSelbergMass
    nativePNTNormalizedExactSignedRemainder
  calc
    nativePNTError N / (N : Real) * Real.log (N : Real) +
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) / (N : Real) =
        (nativePNTError N * Real.log (N : Real) +
          ∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) / (N : Real) := by
      ring
    _ = ((nativeSelbergPair N - 2 * (N : Real) * Real.log (N : Real)) -
          (Real.log ((Nat.factorial N : Nat) : Real) -
            (N : Real) * Real.log (N : Real))) / (N : Real) := by
      rw [hnum]

/-- Exact three-ledger form: endpoint error + everything outside the square
block + the square-block response equals the signed normalized remainder. -/
theorem nativePNTNormalized_signed_squareBlock_recurrence_eq
    (N M L : Nat) (hN : 1 ≤ N) :
    nativePNTNormalizedError N * Real.log (N : Real) +
        nativePNTNormalizedFloorOutsideSquareBlock N M L +
        nativePNTNormalizedFloorSquareBlockResponse N M L =
      nativePNTNormalizedExactSignedRemainder N := by
  have h := nativePNTNormalized_signed_floor_recurrence_eq_exactRemainder N hN
  unfold nativePNTNormalizedFloorOutsideSquareBlock
  linarith

/-- Total von-Mangoldt mass carried by the divisor block `(M,L]`. -/
def nativePNTLambdaSquareBlockMass (M L : Nat) : Real :=
  ∑ d ∈ Finset.Ioc M L, Λ d

@[simp] theorem violeClock_nativePNTNormalizedError_one :
    nativePNTNormalizedError 1 = -1 := by
  rw [nativePNTNormalizedError_eq_psi_div_sub_one 1 (by norm_num)]
  simp [nativePsi]

/-- At the first subdoubling endpoint, every divisor in `(M,L]` has quotient
one.  Therefore the entire signed square-block response is exactly the
negative block von-Mangoldt mass divided by `L`. -/
theorem nativePNTNormalizedFloorSquareBlockResponse_endpoint_of_subdoubling
    (M L : Nat) (hsub : L < 2 * M) :
    nativePNTNormalizedFloorSquareBlockResponse L M L =
      -nativePNTLambdaSquareBlockMass M L / (L : Real) := by
  unfold nativePNTNormalizedFloorSquareBlockResponse
    nativePNTLambdaSquareBlockMass
  calc
    (∑ d ∈ Finset.Ioc M L,
      nativePNTNormalizedFloorWeight L d * nativePNTNormalizedError (L / d)) =
        ∑ d ∈ Finset.Ioc M L, (-(Λ d)) / (L : Real) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdI := Finset.mem_Ioc.mp hd
      have hlo : 1 * d ≤ L := by simpa using hdI.2
      have hhi : L < (1 + 1) * d := by
        have htwo : 2 * M < 2 * d := by omega
        omega
      have hdiv : L / d = 1 := Nat.div_eq_of_lt_le hlo hhi
      rw [hdiv, violeClock_nativePNTNormalizedError_one]
      simp [nativePNTNormalizedFloorWeight, hdiv, neg_div]
    _ = -(∑ d ∈ Finset.Ioc M L, Λ d) / (L : Real) := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- The block von-Mangoldt mass is the exact Chebyshev increment. -/
theorem nativePNTLambdaSquareBlockMass_eq_psi_sub
    (M L : Nat) (hM : 1 ≤ M) (hML : M ≤ L) :
    nativePNTLambdaSquareBlockMass M L = nativePsi L - nativePsi M := by
  unfold nativePNTLambdaSquareBlockMass nativePsi
  have hset :
      Finset.Icc 1 L = Finset.Icc 1 M ∪ Finset.Ioc M L := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Icc 1 M) (Finset.Ioc M L) := by
    rw [Finset.disjoint_left]
    intro d hdM hdBlock
    rw [Finset.mem_Icc] at hdM
    rw [Finset.mem_Ioc] at hdBlock
    omega
  rw [hset, Finset.sum_union hdis]
  ring

/-- Consecutive Viole cutoffs are increasing. -/
theorem violeClockCutoff_le_succ (r : Nat) :
    violeClockCutoff r ≤ violeClockCutoff (r + 1) := by
  unfold violeClockCutoff
  have hsquare : r ^ 2 ≤ (r + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  exact Nat.add_le_add hsquare (by omega)

/-- From `r >= 3` onward, adjacent Viole cutoffs are subdoubling. -/
theorem violeClockCutoff_succ_lt_two_mul
    (r : Nat) (hr : 3 ≤ r) :
    violeClockCutoff (r + 1) < 2 * violeClockCutoff r := by
  have hrpos : 0 < r := by omega
  have h2r : 2 * r < r * r :=
    Nat.mul_lt_mul_of_pos_right (by omega : 2 < r) hrpos
  have hsmall : r + 2 ≤ 2 * r := by omega
  have hrr : r + 2 < r * r := hsmall.trans_lt h2r
  unfold violeClockCutoff
  calc
    (r + 1) ^ 2 + (r + 1) = r ^ 2 + 2 * r + (r + 2) := by ring
    _ < r ^ 2 + 2 * r + r ^ 2 := by
      simpa [pow_two] using Nat.add_lt_add_left hrr (r ^ 2 + 2 * r)
    _ = 2 * (r ^ 2 + r) := by ring

/-- At a Viole adjacent-square endpoint the new signed divisor block is
literally the negative Chebyshev block increment divided by the endpoint. -/
theorem violeClockNormalizedFloorSquareBlockResponse_endpoint
    (r : Nat) (hr : 3 ≤ r) :
    nativePNTNormalizedFloorSquareBlockResponse
        (violeClockCutoff (r + 1))
        (violeClockCutoff r)
        (violeClockCutoff (r + 1)) =
      -(nativePsi (violeClockCutoff (r + 1)) -
          nativePsi (violeClockCutoff r)) /
        (violeClockCutoff (r + 1) : Real) := by
  have hM : 1 ≤ violeClockCutoff r := by
    unfold violeClockCutoff
    nlinarith
  have hML := violeClockCutoff_le_succ r
  rw [nativePNTNormalizedFloorSquareBlockResponse_endpoint_of_subdoubling
      (violeClockCutoff r) (violeClockCutoff (r + 1))
      (violeClockCutoff_succ_lt_two_mul r hr),
    nativePNTLambdaSquareBlockMass_eq_psi_sub _ _ hM hML]

/-- Raising the physical cutoff preserves a true tail at the same slope. -/
theorem primeSieveStateDependentSelbergTailAbove_mono_cutoff
    (M L : Nat) (alpha : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hML : M ≤ L) :
    PrimeSieveStateDependentSelbergTailAbove L alpha := by
  rcases htail with ⟨hM2, halpha, htail⟩
  exact ⟨hM2.trans hML, halpha, fun q hLq => htail q (hML.trans hLq)⟩

/-- A true tail is an absolute bound on the normalized error at every later
endpoint. -/
theorem primeSieveStateDependentSelbergTailAbove_normalizedError_abs_le
    (M N : Nat) (alpha : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hMN : M ≤ N) :
    |nativePNTNormalizedError N| ≤ alpha := by
  have hM2 : 2 ≤ M := htail.1
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : Real) < (N : Real) := by
    exact_mod_cast hNposNat
  have hraw := htail.2.2 N hMN
  unfold nativePNTNormalizedError
  rw [abs_div, abs_of_pos hNpos]
  exact (div_le_iff₀ hNpos).2 hraw

/-- **Direct signed square-block exclusion law.**

The old tail already confines `e(N)` to `[-alpha,alpha]`.  The only arithmetic
obligation is to exclude the two extremal strips using the actual signed
response of the one divisor block `(M,L]`.  The outside terms and the Selberg
remainder remain signed and exact; no universal constant is inserted. -/
def NativePNTSignedSquareBlockDirectCutoffExclusion
    (M L : Nat) (alpha alpha' : Real) : Prop :=
  3 ≤ L ∧ M ≤ L ∧ 0 < alpha' ∧ alpha' ≤ alpha ∧
    ∀ N : Nat, L ≤ N →
      (alpha' < nativePNTNormalizedError N →
        nativePNTNormalizedError N ≤ alpha →
          nativePNTNormalizedExactSignedRemainder N -
              nativePNTNormalizedFloorOutsideSquareBlock N M L -
              alpha' * Real.log (N : Real) ≤
            nativePNTNormalizedFloorSquareBlockResponse N M L) ∧
      (nativePNTNormalizedError N < -alpha' →
        -alpha ≤ nativePNTNormalizedError N →
          nativePNTNormalizedFloorSquareBlockResponse N M L ≤
            nativePNTNormalizedExactSignedRemainder N -
              nativePNTNormalizedFloorOutsideSquareBlock N M L +
              alpha' * Real.log (N : Real))

/-- The exact signed block exclusion upgrades the old tail directly. -/
theorem nativePNTSignedSquareBlockDirectCutoffExclusion_step
    (M L : Nat) (alpha alpha' : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hexcl : NativePNTSignedSquareBlockDirectCutoffExclusion M L alpha alpha') :
    PrimeSieveStateDependentSelbergTailAbove L alpha' := by
  rcases hexcl with ⟨hL3, hML, halpha', _hale, hexcl⟩
  refine ⟨by omega, halpha', ?_⟩
  intro N hLN
  have hN3 : 3 ≤ N := hL3.trans hLN
  have hNpos : (0 : Real) < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hold :=
    primeSieveStateDependentSelbergTailAbove_normalizedError_abs_le
      M N alpha htail (hML.trans hLN)
  have holdBounds := abs_le.mp hold
  have hrec :=
    nativePNTNormalized_signed_squareBlock_recurrence_eq N M L (by omega)
  have hbar := hexcl N hLN
  have hnorm : |nativePNTNormalizedError N| ≤ alpha' := by
    rw [abs_le]
    constructor
    · by_contra hneg
      have hextreme : nativePNTNormalizedError N < -alpha' :=
        lt_of_not_ge hneg
      have hblock := hbar.2 hextreme holdBounds.1
      have hmul :
          nativePNTNormalizedError N * Real.log (N : Real) <
            (-alpha') * Real.log (N : Real) :=
        mul_lt_mul_of_pos_right hextreme hlog
      linarith
    · by_contra hpos
      have hextreme : alpha' < nativePNTNormalizedError N :=
        lt_of_not_ge hpos
      have hblock := hbar.1 hextreme holdBounds.2
      have hmul :
          alpha' * Real.log (N : Real) <
            nativePNTNormalizedError N * Real.log (N : Real) :=
        mul_lt_mul_of_pos_right hextreme hlog
      linarith
  unfold nativePNTNormalizedError at hnorm
  rw [abs_div, abs_of_pos hNpos] at hnorm
  exact (div_le_iff₀ hNpos).1 hnorm

/-- Exact slope whose reciprocal square increases by `delta`. -/
def nativePNTReciprocalSquareSlope
    (alpha delta : Real) : Real :=
  alpha / Real.sqrt (1 + delta * alpha ^ 2)

theorem nativePNTReciprocalSquareSlope_pos
    (alpha delta : Real) (halpha : 0 < alpha) (hdelta : 0 ≤ delta) :
    0 < nativePNTReciprocalSquareSlope alpha delta := by
  have hins : 0 < 1 + delta * alpha ^ 2 := by
    nlinarith [mul_nonneg hdelta (sq_nonneg alpha)]
  exact div_pos halpha (Real.sqrt_pos.2 hins)

theorem nativePNTReciprocalSquareSlope_le
    (alpha delta : Real) (halpha : 0 < alpha) (hdelta : 0 ≤ delta) :
    nativePNTReciprocalSquareSlope alpha delta ≤ alpha := by
  have hins : 1 ≤ 1 + delta * alpha ^ 2 := by
    nlinarith [mul_nonneg hdelta (sq_nonneg alpha)]
  have hsqrt : 1 ≤ Real.sqrt (1 + delta * alpha ^ 2) := by
    simpa using Real.sqrt_le_sqrt hins
  have hsqrtPos : 0 < Real.sqrt (1 + delta * alpha ^ 2) :=
    lt_of_lt_of_le zero_lt_one hsqrt
  unfold nativePNTReciprocalSquareSlope
  apply (div_le_iff₀ hsqrtPos).2
  have hmul := mul_le_mul_of_nonneg_left hsqrt halpha.le
  simpa using hmul

/-- Exact reciprocal-square gain of the scalar update. -/
theorem nativePNTReciprocalSquareSlope_inv_sq_sub
    (alpha delta : Real) (halpha : 0 < alpha) (hdelta : 0 ≤ delta) :
    1 / (nativePNTReciprocalSquareSlope alpha delta) ^ 2 -
        1 / alpha ^ 2 = delta := by
  have hins0 : 0 ≤ 1 + delta * alpha ^ 2 := by
    nlinarith [mul_nonneg hdelta (sq_nonneg alpha)]
  have hins : 0 < 1 + delta * alpha ^ 2 := by
    nlinarith [mul_nonneg hdelta (sq_nonneg alpha)]
  have hsqrtSq :
      (Real.sqrt (1 + delta * alpha ^ 2)) ^ 2 =
        1 + delta * alpha ^ 2 := Real.sq_sqrt hins0
  have hsqrtPos : 0 < Real.sqrt (1 + delta * alpha ^ 2) :=
    Real.sqrt_pos.2 hins
  have halpha0 : alpha ≠ 0 := ne_of_gt halpha
  have hsqrt0 : Real.sqrt (1 + delta * alpha ^ 2) ≠ 0 := ne_of_gt hsqrtPos
  have hsqrtSq' :
      (Real.sqrt (1 + alpha ^ 2 * delta)) ^ 2 =
        1 + alpha ^ 2 * delta := by
    simpa [mul_comm] using hsqrtSq
  have hsqrt0' : Real.sqrt (1 + alpha ^ 2 * delta) ≠ 0 := by
    simpa [mul_comm] using hsqrt0
  unfold nativePNTReciprocalSquareSlope
  field_simp [halpha0, hsqrt0, hsqrt0']
  nlinarith [hsqrtSq, hsqrtSq']

/-- One exact reciprocal-square direct cutoff step. -/
theorem nativePNTReciprocalSquareSignedBlockDirectCutoff_step
    (M L : Nat) (alpha delta : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hdelta : 0 ≤ delta)
    (hexcl : NativePNTSignedSquareBlockDirectCutoffExclusion
      M L alpha (nativePNTReciprocalSquareSlope alpha delta)) :
    PrimeSieveStateDependentSelbergTailAbove
        L (nativePNTReciprocalSquareSlope alpha delta) ∧
      nativePNTReciprocalSquareSlope alpha delta ≤ alpha ∧
      1 / (nativePNTReciprocalSquareSlope alpha delta) ^ 2 -
          1 / alpha ^ 2 = delta := by
  have halpha : 0 < alpha := htail.2.1
  exact ⟨
    nativePNTSignedSquareBlockDirectCutoffExclusion_step
      M L alpha (nativePNTReciprocalSquareSlope alpha delta) htail hexcl,
    nativePNTReciprocalSquareSlope_le alpha delta halpha hdelta,
    nativePNTReciprocalSquareSlope_inv_sq_sub alpha delta halpha hdelta⟩

/-- Reciprocal-square gain requested from block `r` after its explicit leakage. -/
def violeClockBlockReciprocalSquareGain
    (c : Real) (eps : Nat → Real) (r : Nat) : Real :=
  c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r

/-- **Remaining arithmetic seam.**  On every positive-gain block, the literal
signed divisor-block response must exclude the old-tail extremal strip. -/
def VioleClockSignedSquareBlockDirectCutoffLaw
    (r0 : Nat) (c : Real) (eps : Nat → Real) : Prop :=
  3 ≤ r0 ∧ 0 < c ∧
    ∀ (r : Nat) (alpha : Real),
      r0 ≤ r →
      PrimeSieveStateDependentSelbergTailAbove (violeClockCutoff r) alpha →
      0 < violeClockBlockReciprocalSquareGain c eps r →
      NativePNTSignedSquareBlockDirectCutoffExclusion
        (violeClockCutoff r) (violeClockCutoff (r + 1)) alpha
        (nativePNTReciprocalSquareSlope alpha
          (violeClockBlockReciprocalSquareGain c eps r))

/-- A signed square-block direct cutoff law implies the frozen coupling
without `CubicGainFromTo`, an affine envelope, or an onset lemma. -/
theorem violeClockReciprocalSquareCoupling_of_signedSquareBlockDirectCutoffLaw
    (r0 : Nat) (c : Real) (eps : Nat → Real)
    (hlaw : VioleClockSignedSquareBlockDirectCutoffLaw r0 c eps) :
    VioleClockReciprocalSquareCoupling r0 c eps := by
  rcases hlaw with ⟨hr0, hc, hlaw⟩
  refine ⟨by omega, hc, ?_⟩
  intro r alpha hr htail
  have hML := violeClockCutoff_le_succ r
  have htailCut :
      PrimeSieveStateDependentSelbergTailAbove (violeClockCutoff (r + 1)) alpha :=
    primeSieveStateDependentSelbergTailAbove_mono_cutoff
      (violeClockCutoff r) (violeClockCutoff (r + 1)) alpha htail hML
  let delta : Real := violeClockBlockReciprocalSquareGain c eps r
  by_cases hdelta : 0 < delta
  · have hexcl := hlaw r alpha hr htail (by simpa [delta] using hdelta)
    have hstep := nativePNTReciprocalSquareSignedBlockDirectCutoff_step
      (violeClockCutoff r) (violeClockCutoff (r + 1)) alpha delta htail
      hdelta.le (by simpa [delta] using hexcl)
    refine ⟨nativePNTReciprocalSquareSlope alpha delta, hstep.1, hstep.2.1, ?_⟩
    have hgain := hstep.2.2
    simpa [delta, violeClockCutoff, violeClockBlockReciprocalSquareGain] using
      hgain.ge
  · have hdeltaNonpos : delta ≤ 0 := le_of_not_gt hdelta
    refine ⟨alpha, ?_, le_rfl, ?_⟩
    · simpa [violeClockCutoff] using htailCut
    · have hzero : 1 / alpha ^ 2 - 1 / alpha ^ 2 = 0 := by ring
      rw [hzero]
      simpa [delta, violeClockBlockReciprocalSquareGain] using hdeltaNonpos

/-! ## Möbius-correlation realization of the block socket -/

/-- Response seen from one Möbius cofactor when the total divisor is restricted
to the physical block `(M,L]`.  The PNT error is attached to the total divisor
`d`, so it is frozen under internal divisor-fibre pairing. -/
def nativePNTSignedSquareBlockCofactorResponse
    (N M L m : Nat) : Real :=
  ∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
    Real.log ((d / m : Nat) : Real) * nativePNTError (N / d)

/-- Uncentered Möbius-parity correlation of the complete signed block. -/
def nativePNTSignedSquareBlockMobiusCorrelation
    (N M L : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 L,
    (μ : ArithmeticFunction Real) m *
      nativePNTSignedSquareBlockCofactorResponse N M L m

/-- Exact interval Fubini identity: the `Lambda`-weighted block is literally a
Möbius-parity/response correlation. -/
theorem nativeLambdaSquareBlockWeighted_eq_mobiusCorrelation
    (N M L : Nat) :
    (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (N / d)) =
      nativePNTSignedSquareBlockMobiusCorrelation N M L := by
  classical
  have hmem : ∀ (d m : Nat),
      d ∈ Finset.Ioc M L ∧ m ∈ d.divisors ↔
        d ∈ (Finset.Ioc M L).filter (fun x => m ∣ x) ∧
          m ∈ Finset.Icc 1 L := by
    intro d m
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc,
      Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdM, hdL⟩, hmd, hd0⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hd0 (Nat.eq_zero_of_zero_dvd hmd)
      have hmdle : m ≤ d := Nat.le_of_dvd (by omega) hmd
      exact ⟨⟨⟨hdM, hdL⟩, hmd⟩,
        Nat.one_le_iff_ne_zero.mpr hm0, hmdle.trans hdL⟩
    · rintro ⟨⟨⟨hdM, hdL⟩, hmd⟩, _hm1, _hmL⟩
      exact ⟨⟨hdM, hdL⟩, hmd, Nat.ne_of_gt (by omega : 0 < d)⟩
  calc
    (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (N / d)) =
        ∑ d ∈ Finset.Ioc M L,
          ∑ m ∈ d.divisors,
            ((μ : ArithmeticFunction Real) m *
              Real.log ((d / m : Nat) : Real)) *
                nativePNTError (N / d) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← nativeMobiusLogDivisorFiber_eq_vonMangoldt d,
        nativeMobiusLogDivisorFiber, Finset.sum_mul]
    _ = ∑ m ∈ Finset.Icc 1 L,
          ∑ d ∈ (Finset.Ioc M L).filter (fun x => m ∣ x),
            ((μ : ArithmeticFunction Real) m *
              Real.log ((d / m : Nat) : Real)) *
                nativePNTError (N / d) :=
      Finset.sum_comm' hmem
    _ = ∑ m ∈ Finset.Icc 1 L,
          (μ : ArithmeticFunction Real) m *
            (∑ d ∈ (Finset.Ioc M L).filter (fun x => m ∣ x),
              Real.log ((d / m : Nat) : Real) *
                nativePNTError (N / d)) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ = nativePNTSignedSquareBlockMobiusCorrelation N M L := by
      rfl

/-- At every genuine later endpoint, the literal normalized square-block
response is the Möbius correlation divided by that endpoint. -/
theorem nativePNTNormalizedFloorSquareBlockResponse_eq_mobiusCorrelation_div
    (N M L : Nat) (hL : 1 ≤ L) (hLN : L ≤ N) :
    nativePNTNormalizedFloorSquareBlockResponse N M L =
      nativePNTSignedSquareBlockMobiusCorrelation N M L / (N : Real) := by
  have hN : 1 ≤ N := hL.trans hLN
  have hNR0 : (N : Real) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold nativePNTNormalizedFloorSquareBlockResponse
  calc
    (∑ d ∈ Finset.Ioc M L,
        nativePNTNormalizedFloorWeight N d *
          nativePNTNormalizedError (N / d)) =
      ∑ d ∈ Finset.Ioc M L,
        (Λ d * nativePNTError (N / d)) / (N : Real) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdI := Finset.mem_Ioc.mp hd
        have hdpos : 0 < d := by omega
        have hdN : d ≤ N := hdI.2.trans hLN
        have hq1 : 1 ≤ N / d :=
          (Nat.one_le_div_iff hdpos).2 hdN
        have hqR0 : (((N / d : Nat) : Real)) ≠ 0 := by
          exact_mod_cast (show N / d ≠ 0 by omega)
        unfold nativePNTNormalizedFloorWeight nativePNTNormalizedError
        field_simp [hNR0, hqR0]
    _ = (∑ d ∈ Finset.Ioc M L,
          Λ d * nativePNTError (N / d)) / (N : Real) := by
      rw [Finset.sum_div]
    _ = nativePNTSignedSquareBlockMobiusCorrelation N M L / (N : Real) := by
      rw [nativeLambdaSquareBlockWeighted_eq_mobiusCorrelation]

/-- Number of cofactor coordinates in the block correlation. -/
def nativePNTSignedSquareBlockCofactorCard (L : Nat) : Nat :=
  (Finset.Icc 1 L).card

/-- Total Möbius parity on the cofactor carrier. -/
def nativePNTSignedSquareBlockParitySum (L : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 L, (μ : ArithmeticFunction Real) m

/-- Total unweighted response on the same carrier. -/
def nativePNTSignedSquareBlockResponseSum
    (N M L : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 L,
    nativePNTSignedSquareBlockCofactorResponse N M L m

/-- Uniform mean of the Möbius parity field. -/
def nativePNTSignedSquareBlockParityMean (L : Nat) : Real :=
  nativePNTSignedSquareBlockParitySum L /
    (nativePNTSignedSquareBlockCofactorCard L : Real)

/-- Uniform mean of the cofactor response field. -/
def nativePNTSignedSquareBlockResponseMean
    (N M L : Nat) : Real :=
  nativePNTSignedSquareBlockResponseSum N M L /
    (nativePNTSignedSquareBlockCofactorCard L : Real)

/-- Uniform centered covariance of Möbius parity with the block response. -/
def nativePNTSignedSquareBlockCovariance
    (N M L : Nat) : Real :=
  ((nativePNTSignedSquareBlockCofactorCard L : Real) *
        nativePNTSignedSquareBlockMobiusCorrelation N M L -
      nativePNTSignedSquareBlockParitySum L *
        nativePNTSignedSquareBlockResponseSum N M L) /
    (nativePNTSignedSquareBlockCofactorCard L : Real) ^ 2

/-- Exact mean-plus-covariance decomposition of the uncentered correlation. -/
theorem nativePNTSignedSquareBlockMobiusCorrelation_eq_card_mul_mean_add_covariance
    (N M L : Nat) (hL : 1 ≤ L) :
    nativePNTSignedSquareBlockMobiusCorrelation N M L =
      (nativePNTSignedSquareBlockCofactorCard L : Real) *
        (nativePNTSignedSquareBlockParityMean L *
            nativePNTSignedSquareBlockResponseMean N M L +
          nativePNTSignedSquareBlockCovariance N M L) := by
  have hcardNat : 0 < nativePNTSignedSquareBlockCofactorCard L := by
    unfold nativePNTSignedSquareBlockCofactorCard
    apply Finset.card_pos.mpr
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩⟩
  have hcard0 : (nativePNTSignedSquareBlockCofactorCard L : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardNat)
  unfold nativePNTSignedSquareBlockParityMean
    nativePNTSignedSquareBlockResponseMean
    nativePNTSignedSquareBlockCovariance
  field_simp [hcard0]
  ring

/-- The direct block socket is therefore exactly the centered covariance plus
its parity/response mean mode, divided by the later endpoint. -/
theorem nativePNTNormalizedFloorSquareBlockResponse_eq_mean_add_covariance
    (N M L : Nat) (hL : 1 ≤ L) (hLN : L ≤ N) :
    nativePNTNormalizedFloorSquareBlockResponse N M L =
      ((nativePNTSignedSquareBlockCofactorCard L : Real) *
        (nativePNTSignedSquareBlockParityMean L *
            nativePNTSignedSquareBlockResponseMean N M L +
          nativePNTSignedSquareBlockCovariance N M L)) / (N : Real) := by
  rw [nativePNTNormalizedFloorSquareBlockResponse_eq_mobiusCorrelation_div
      N M L hL hLN,
    nativePNTSignedSquareBlockMobiusCorrelation_eq_card_mul_mean_add_covariance
      N M L hL]

/-- Reciprocal uncentered correlation coordinate for one cofactor. -/
def nativePNTSignedSquareBlockCorrelationReciprocalSummand
    (N M L m : Nat) : Real :=
  (((μ m : Int) : Real) *
      nativePNTSignedSquareBlockCofactorResponse N M L m) / (m : Real)

/-- Explicit physical defect created by adjoining one fresh prime: it is exactly
the failure of the cofactor response to be invariant under `m -> m*p`. -/
def nativePNTSignedSquareBlockFreshPrimePhysicalDefect
    (N M L m p : Nat) : Real :=
  (((μ m : Int) : Real) *
      (nativePNTSignedSquareBlockCofactorResponse N M L m -
        nativePNTSignedSquareBlockCofactorResponse N M L (m * p))) /
    ((m * p : Nat) : Real)

/-- **Exact prime-by-prime Euler law on the direct block correlation.**
The reciprocal parent/child pair receives the factor `1 - 1/p`; all leakage is
retained in the explicit response-difference defect. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
    (N M L : Nat) {m p : Nat}
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p) =
      (1 - 1 / (p : Real)) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p := by
  have hm0 : (m : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hp0 : (p : Real) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  unfold nativePNTSignedSquareBlockCorrelationReciprocalSummand
    nativePNTSignedSquareBlockFreshPrimePhysicalDefect
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  field_simp [hm0, hp0]
  ring

end RHLean.Analysis