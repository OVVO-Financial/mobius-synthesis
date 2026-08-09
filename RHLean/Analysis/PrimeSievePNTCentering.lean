import Mathlib
import RHLean.Proof.PrimeSievePostSqrtGap
import RHLean.Analysis.SquareWheelQuantitativeBridge
import RHLean.Analysis.SquareWheelNesting
import RHLean.Proof.ConcreteLiCoreExtensionWeight

/-!
# PNT centering of the prime-sieve tail and the square-wheel response

The elementary post-square-root identity writes the Mertens discrepancy as a
prime sum

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

This module separates the prime indicator into a deterministic logarithmic-
integral increment and its exact discrepancy.  The density convention matches
the repository's existing exact-activity prime-density route: the model mass at
integer `q` is `Li(q) - Li(q-1)`.

No prime-number-theorem error estimate is assumed or proved.  The purpose is to
make the deterministic PNT bulk and the remaining prime-distribution error
visible as distinct signed objects.

The second half pushes this centering through the actual square-wheel zero-mode
subtraction.  At a synchronized square sample the canonical nonzero response
`H_{k,n}` is proved equal to

```text
centered all-plus comb
  - 2 * centered PNT bulk
  - 2 * centered prime-distribution error.
```

The centering coefficient is the repository's actual wheel coefficient
`(X_n - L_k) / Q_k`; it is not replaced by linear interpolation across the
arithmetic block.  In particular, this file makes no claim that the PNT bulk is
annihilated by the zero-mode subtraction.  It identifies exactly what survives.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Deterministic logarithmic-integral mass assigned to the integer site `q`.
This is the singleton version of the existing exact-activity Li model. -/
def primeSievePNTDensity (q : ℕ) : ℂ :=
  ((logarithmicIntegralFromTwo (q : ℝ) -
      logarithmicIntegralFromTwo ((q - 1 : ℕ) : ℝ) : ℝ) : ℂ)

/-- Exact complex-valued prime indicator. -/
def primeSievePrimeIndicator (q : ℕ) : ℂ :=
  if q.Prime then 1 else 0

/-- The deterministic Li-density bulk in the prime-first transport tail. -/
def primeSievePNTBulk (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    primeSievePNTDensity q * mertensSummatory (x / q)

/-- The exact error left after subtracting the Li density from the prime
indicator.  This is the object on which genuine prime-distribution input would
have to act. -/
def primeSievePNTError (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    (primeSievePrimeIndicator q - primeSievePNTDensity q) *
      mertensSummatory (x / q)

/-- Exact Li-density decomposition of the prime-sieve Mertens tail. -/
theorem primeSieveMertensPrimeTail_eq_pntBulk_add_error
    (y x : ℕ) :
    primeSieveMertensPrimeTail y x =
      primeSievePNTBulk y x + primeSievePNTError y x := by
  classical
  unfold primeSieveMertensPrimeTail primeSievePNTBulk primeSievePNTError
    primeSievePrimeIndicator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hp : q.Prime
  · simp [hp]
    ring
  · simp [hp]

/-- The all-plus sieve state after subtracting twice the deterministic PNT bulk.
The factor two is the exact sign change between an unresolved source and its
final Mobius sign. -/
def primeSievePNTCorrectedAllPlusMass (y x : ℕ) : ℂ :=
  allPlusPrimeCombPrefixMass y x - 2 * primeSievePNTBulk y x

/-- Once the prime cutoff is strictly above `sqrt x`, Mertens is the PNT-corrected
all-plus state minus twice the prime-distribution error. -/
theorem mertensSummatory_eq_pntCorrectedAllPlus_sub_two_error
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    mertensSummatory x =
      primeSievePNTCorrectedAllPlusMass y x - 2 * primeSievePNTError y x := by
  have hgap :=
    allPlusPrimeCombPrefixMass_sub_mertens_eq_two_mertensPrimeTail y x hroot
  rw [primeSieveMertensPrimeTail_eq_pntBulk_add_error y x] at hgap
  calc
    mertensSummatory x =
        allPlusPrimeCombPrefixMass y x -
          2 * (primeSievePNTBulk y x + primeSievePNTError y x) := by
      linear_combination -hgap
    _ = primeSievePNTCorrectedAllPlusMass y x -
          2 * primeSievePNTError y x := by
      unfold primeSievePNTCorrectedAllPlusMass
      ring

/-- A block-safe prime-sieve cutoff.  The wheel itself uses `sqrt U_k`; adding
one lets the already-proved strict post-square-root theorem be applied
simultaneously at every point `x <= U_k`, including the endpoint `U_k`. -/
def primorialPNTPrimeSieveCutoff (k : ℕ) : ℕ :=
  primorialWheelCutoff k + 1

/-- Every point in the synchronized primorial block lies strictly below the
square of the block-safe prime-sieve cutoff. -/
theorem sqrt_lt_primorialPNTPrimeSieveCutoff_of_le_upper
    {k x : ℕ} (hupper : x ≤ primorialBlockUpper k) :
    Nat.sqrt x < primorialPNTPrimeSieveCutoff k := by
  unfold primorialPNTPrimeSieveCutoff primorialWheelCutoff
  have hsqrt : Nat.sqrt x ≤ Nat.sqrt (primorialBlockUpper k) :=
    Nat.sqrt_le_sqrt hupper
  omega

/-- The exact centering operator used by the minimal square wheel.  It subtracts
`sampleRatio * endpointIncrement`; the coefficient is the actual torus ratio,
not the arithmetic-block interpolation ratio. -/
def primorialSquareZeroModeCenter
    (k n : ℕ) (f : ℕ → ℂ) : ℂ :=
  (f (squarePrefixEndpoint n) - f (primorialBlockLower k)) -
    squareWheelSampleRatio (primorialMinimalWheelSystem k) n *
      (f (primorialBlockUpper k) - f (primorialBlockLower k))

/-- The nonzero square-wheel response is exactly the zero-mode centering of the
ordinary Mertens function on the synchronized block. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      primorialSquareZeroModeCenter k n mertensSummatory := by
  have hsample :=
    primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
      (primorialMinimalWheelSystem k) n hlower hupper
  have hminSample :
      (primorialMinimalWheelSystem k).residual (squarePrefixEndpoint n) =
        (primorialWheelSystem k).residual (squarePrefixEndpoint n) :=
    primorialMinimalWheel_residual_eq_primorialWheel_residual k hupper
  have hminUpper :
      (primorialMinimalWheelSystem k).residual (primorialBlockUpper k) =
        (primorialWheelSystem k).residual (primorialBlockUpper k) :=
    primorialMinimalWheel_residual_eq_primorialWheel_residual k le_rfl
  have hupperSys :
      (primorialMinimalWheelSystem k).upper = primorialBlockUpper k := rfl
  rw [hupperSys, hminSample, hminUpper] at hsample
  have hblock : primorialBlockLower k ≤ primorialBlockUpper k :=
    (primorialEndpoint_strictMono (Nat.lt_succ_self k)).le
  rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
      k hlower.le hupper,
    RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
      k hblock le_rfl] at hsample
  unfold primorialSquareZeroModeCenter
  rw [eq_sub_iff_add_eq]
  exact hsample.symm

/-- Zero-mode centered all-plus prime-sieve response at the block-safe cutoff. -/
def primorialAllPlusPrimeSieveCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x => allPlusPrimeCombPrefixMass (primorialPNTPrimeSieveCutoff k) x)

/-- The deterministic PNT bulk after the *same* square-wheel zero-mode centering
used in `H_{k,n}`. -/
def primorialPNTBulkCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x => primeSievePNTBulk (primorialPNTPrimeSieveCutoff k) x)

/-- The prime-indicator-minus-Li-density error after the same square-wheel
zero-mode centering. -/
def primorialPNTErrorCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x => primeSievePNTError (primorialPNTPrimeSieveCutoff k) x)

/-- The PNT-corrected all-plus state after square-wheel zero-mode centering. -/
def primorialPNTCorrectedCombCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x =>
      primeSievePNTCorrectedAllPlusMass
        (primorialPNTPrimeSieveCutoff k) x)

/-- Centering is linear across the deterministic PNT subtraction. -/
theorem primorialPNTCorrectedCombCenteredResponse_eq_allPlus_sub_two_bulk
    (k n : ℕ) :
    primorialPNTCorrectedCombCenteredResponse k n =
      primorialAllPlusPrimeSieveCenteredResponse k n -
        2 * primorialPNTBulkCenteredResponse k n := by
  unfold primorialPNTCorrectedCombCenteredResponse
    primorialAllPlusPrimeSieveCenteredResponse
    primorialPNTBulkCenteredResponse
    primorialSquareZeroModeCenter
    primeSievePNTCorrectedAllPlusMass
  ring

/-- **PNT centering pushed through `H_{k,n}`.**  The canonical nonzero
square-wheel response is exactly the centered PNT-corrected comb minus twice the
centered prime-distribution error. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_error
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      primorialPNTCorrectedCombCenteredResponse k n -
        2 * primorialPNTErrorCenteredResponse k n := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter
    k n hlower hupper]
  let y := primorialPNTPrimeSieveCutoff k
  have hxroot : Nat.sqrt (squarePrefixEndpoint n) < y := by
    dsimp [y]
    exact sqrt_lt_primorialPNTPrimeSieveCutoff_of_le_upper hupper
  have hblock : primorialBlockLower k ≤ primorialBlockUpper k :=
    (primorialEndpoint_strictMono (Nat.lt_succ_self k)).le
  have hlroot : Nat.sqrt (primorialBlockLower k) < y := by
    dsimp [y]
    exact sqrt_lt_primorialPNTPrimeSieveCutoff_of_le_upper hblock
  have huroot : Nat.sqrt (primorialBlockUpper k) < y := by
    dsimp [y]
    exact sqrt_lt_primorialPNTPrimeSieveCutoff_of_le_upper (k := k) le_rfl
  have hxM :=
    mertensSummatory_eq_pntCorrectedAllPlus_sub_two_error
      y (squarePrefixEndpoint n) hxroot
  have hlM :=
    mertensSummatory_eq_pntCorrectedAllPlus_sub_two_error
      y (primorialBlockLower k) hlroot
  have huM :=
    mertensSummatory_eq_pntCorrectedAllPlus_sub_two_error
      y (primorialBlockUpper k) huroot
  unfold primorialPNTCorrectedCombCenteredResponse
    primorialPNTErrorCenteredResponse
    primorialSquareZeroModeCenter
  dsimp [y] at hxM hlM huM ⊢
  rw [hxM, hlM, huM]
  ring_nf

/-- Fully expanded three-term form: `H_{k,n}` is the centered all-plus comb,
minus the deterministic PNT bulk, minus the residual prime-distribution error.
This theorem records explicitly that the PNT bulk generally survives the wheel
zero-mode centering rather than being silently identified with it. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_allPlus_sub_pntBulk_sub_error
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      primorialAllPlusPrimeSieveCenteredResponse k n -
        2 * primorialPNTBulkCenteredResponse k n -
        2 * primorialPNTErrorCenteredResponse k n := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_error
    k n hlower hupper]
  rw [primorialPNTCorrectedCombCenteredResponse_eq_allPlus_sub_two_bulk]

/-- Exact norm transfer from the PNT-centered decomposition to the canonical
nonzero response.  Any bounds for the corrected centered comb and centered
prime error combine without losing the signed decomposition. -/
theorem norm_primorialMinimalSquareWheelNonzeroResponse_le_pntCentered
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
      ‖primorialPNTCorrectedCombCenteredResponse k n‖ +
        2 * ‖primorialPNTErrorCenteredResponse k n‖ := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_error
    k n hlower hupper]
  simpa [norm_mul] using
    (norm_sub_le
      (primorialPNTCorrectedCombCenteredResponse k n)
      (2 * primorialPNTErrorCenteredResponse k n))

end RHLean.Analysis
