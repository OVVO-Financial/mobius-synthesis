import Mathlib
import RHLean.Analysis.CorrectedConductorSmallSectorBound
import RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse

/-!
# Signed high-conductor Gram reduction

The low-conductor estimate disposes of the actual nontrivial packets `2 <= q <= R`
only after each corrected `raw - 2 * smooth` packet has been formed.  The remaining
object must not be estimated packetwise.  This file therefore keeps conductor one
and every conductor above the cutoff in one signed sum and moves the cutoff through
the already-proved all-conductor Moebius reindexing before taking a norm.

The decisive exact point is that the all-conductor raw boundary pairing can be
split by its *boundary divisor* `d`, not by the original conductor `q`.  Removing
only the reindexed raw boundary divisors `d <= R` leaves one collapsed signed core
containing the conductor-one bulk, every large raw expansion layer, and the fully
collapsed smooth term.  The original high-conductor-plus-zero sector differs from
this core only by

* the small reindexed raw boundary piece, minus
* the already-controlled low corrected-conductor sector.

Thus no absolute value is placed on the high conductor packets.  Their complete
cross-conductor interaction remains inside one Gram quantity.
-/

open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Actual divisor conductors retained in the hard sector: conductor one and all
conductors strictly above `R`. -/
def primorialHighConductorWithZeroConductors
    (k R : ℕ) : Finset ℕ :=
  ((primorialMinimalWheelSystem k).modulus.divisors).filter fun q =>
    q = 1 ∨ R < q

/-- The complete signed hard conductor sector.  No norm is taken inside the sum. -/
def primorialHighConductorWithZeroSector
    (k x R : ℕ) : ℂ :=
  ∑ q ∈ primorialHighConductorWithZeroConductors k R,
    primorialPeriodicRawJointConductorResponse k x q

/-- One full cross-conductor Gram block for the periodic-raw conductor packets. -/
def primorialPeriodicRawConductorGramBlock
    (k x q q' : ℕ) : ℂ :=
  primorialPeriodicRawJointConductorResponse k x q *
    conj (primorialPeriodicRawJointConductorResponse k x q')

/-- The signed Gram of the hard sector. -/
def primorialHighConductorWithZeroSignedGram
    (k x R : ℕ) : ℂ :=
  primorialHighConductorWithZeroSector k x R *
    conj (primorialHighConductorWithZeroSector k x R)

/-- Exact hard-sector Gram expansion.  Every diagonal and every cross-conductor
term is retained; no packetwise absolute values occur. -/
theorem primorialHighConductorWithZeroSignedGram_eq_sum_blocks
    (k x R : ℕ) :
    primorialHighConductorWithZeroSignedGram k x R =
      ∑ q ∈ primorialHighConductorWithZeroConductors k R,
        ∑ q' ∈ primorialHighConductorWithZeroConductors k R,
          primorialPeriodicRawConductorGramBlock k x q q' := by
  unfold primorialHighConductorWithZeroSignedGram
    primorialHighConductorWithZeroSector
    primorialPeriodicRawConductorGramBlock
  rw [map_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]

/-- The actual divisor-conductor family is exactly the disjoint union of the
already-controlled nontrivial low sector and the hard sector containing `q=1`. -/
theorem sum_divisorConductorResponses_eq_small_add_high
    (k x R : ℕ) (hR : 1 ≤ R) :
    (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
      primorialPeriodicRawJointConductorResponse k x q) =
      primorialSmallNontrivialConductorSector k x R +
        primorialHighConductorWithZeroSector k x R := by
  classical
  unfold primorialSmallNontrivialConductorSector
    primorialSmallNontrivialConductors
    primorialHighConductorWithZeroSector
    primorialHighConductorWithZeroConductors
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hqmem
  have hqpos : 0 < q := Nat.pos_of_mem_divisors hqmem
  by_cases hq1 : q = 1
  · subst q
    simp [hR]
  · have hqgt : 1 < q := by omega
    by_cases hqR : q ≤ R
    · have hnhigh : ¬ R < q := Nat.not_lt_of_ge hqR
      simp [hqgt, hqR, hq1, hnhigh]
    · have hhigh : R < q := Nat.lt_of_not_ge hqR
      simp [hqgt, hqR, hq1, hhigh]

/-- The historical residual splits exactly into the controlled low conductor
sector and the signed hard conductor sector. -/
theorem primorialPeriodicRawResidual_eq_small_add_high
    (k : ℕ) {x R : ℕ}
    (hR : 1 ≤ R)
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      primorialSmallNontrivialConductorSector k x R +
        primorialHighConductorWithZeroSector k x R := by
  rw [primorialPeriodicRawResidual_eq_sum_divisorConductorResponses
    k hlower hupper]
  exact sum_divisorConductorResponses_eq_small_add_high k x R hR

private def primorialRawBoundarySummand
    (k x d : ℕ) : ℂ :=
  primeWheelRawUpperMobiusTransform
      (primorialWheelPrimes k)
      (primorialMinimalWheelSystem k).modulus d *
    (((divisorIntervalBoundary d 0
      (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))

/-- Fully reindexed raw boundary piece supported on small boundary divisors. -/
def primorialRawSmallCollapsedBoundaryPairing
    (k x R : ℕ) : ℂ :=
  ∑ d ∈ (primorialMinimalWheelSystem k).modulus.divisors,
    if d ≤ R then primorialRawBoundarySummand k x d else 0

/-- Fully reindexed raw boundary piece supported on large boundary divisors. -/
def primorialRawLargeCollapsedBoundaryPairing
    (k x R : ℕ) : ℂ :=
  ∑ d ∈ (primorialMinimalWheelSystem k).modulus.divisors,
    if R < d then primorialRawBoundarySummand k x d else 0

/-- Exact split of the all-conductor raw boundary pairing at the *reindexed
boundary divisor* cutoff. -/
theorem primorialRawCollapsedBoundaryPairing_eq_small_add_large
    (k x R : ℕ) :
    primorialRawCollapsedBoundaryPairing k x =
      primorialRawSmallCollapsedBoundaryPairing k x R +
        primorialRawLargeCollapsedBoundaryPairing k x R := by
  classical
  unfold primorialRawCollapsedBoundaryPairing
    primorialRawSmallCollapsedBoundaryPairing
    primorialRawLargeCollapsedBoundaryPairing
    primorialRawBoundarySummand
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hsmall : d ≤ R
  · have hlarge : ¬ R < d := Nat.not_lt_of_ge hsmall
    simp [hsmall, hlarge]
  · have hlarge : R < d := Nat.lt_of_not_ge hsmall
    simp [hsmall, hlarge]

/-- The small reindexed raw boundary after the common torus normalization. -/
def primorialNormalizedRawSmallBoundary
    (k x R : ℕ) : ℂ :=
  (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    primorialRawSmallCollapsedBoundaryPairing k x R

/-- The hard collapsed core.  It retains every large reindexed raw boundary
layer together with the conductor-one raw bulk and the complete collapsed
smooth correction.  These three signed pieces are not normed separately. -/
def primorialHighCollapsedCore
    (k x R : ℕ) : ℂ :=
  (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    (primorialRawLargeCollapsedBoundaryPairing k x R +
      primorialRawRetainedBulk k x -
      2 * (((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ)))

/-- Exact reindexed residual split into the large collapsed core and the small
raw boundary remainder. -/
theorem primorialPeriodicRawResidual_eq_highCore_add_smallRaw
    (k : ℕ) {x R : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      primorialHighCollapsedCore k x R +
        primorialNormalizedRawSmallBoundary k x R := by
  rw [primorialPeriodicRawResidual_eq_mobiusReindexed k hlower hupper]
  rw [primorialRawCollapsedBoundaryPairing_eq_small_add_large k x R]
  unfold primorialHighCollapsedCore primorialNormalizedRawSmallBoundary
  ring

/-- The only discrepancy between the original hard conductor sector and the
collapsed high core is a signed root-scale candidate: small reindexed raw
boundary minus the already-controlled low corrected-conductor sector. -/
def primorialHighConductorReindexError
    (k x R : ℕ) : ℂ :=
  primorialNormalizedRawSmallBoundary k x R -
    primorialSmallNontrivialConductorSector k x R

/-- **Exact high-sector collapse.**  The full `q=1` plus `q>R` conductor family
is one collapsed signed core plus the explicit cutoff-reindexing error. -/
theorem primorialHighConductorWithZeroSector_eq_core_add_error
    (k : ℕ) {x R : ℕ}
    (hR : 1 ≤ R)
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    primorialHighConductorWithZeroSector k x R =
      primorialHighCollapsedCore k x R +
        primorialHighConductorReindexError k x R := by
  have hcond := primorialPeriodicRawResidual_eq_small_add_high
    k hR hlower hupper
  have hcore := primorialPeriodicRawResidual_eq_highCore_add_smallRaw
    k hlower hupper (R := R)
  unfold primorialHighConductorReindexError
  calc
    primorialHighConductorWithZeroSector k x R =
        (primorialSmallNontrivialConductorSector k x R +
          primorialHighConductorWithZeroSector k x R) -
            primorialSmallNontrivialConductorSector k x R := by ring
    _ = ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) -
          primorialSmallNontrivialConductorSector k x R := by rw [← hcond]
    _ = (primorialHighCollapsedCore k x R +
          primorialNormalizedRawSmallBoundary k x R) -
            primorialSmallNontrivialConductorSector k x R := by rw [hcore]
    _ = primorialHighCollapsedCore k x R +
          (primorialNormalizedRawSmallBoundary k x R -
            primorialSmallNontrivialConductorSector k x R) := by ring

private theorem norm_sq_add_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Gram transfer after exact high-conductor recombination.  The high packet
family is never bounded term-by-term: only the collapsed core and the single
reindexing error appear on the right. -/
theorem norm_sq_primorialHighConductorWithZeroSector_le_core_add_error
    (k : ℕ) {x R : ℕ}
    (hR : 1 ≤ R)
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ‖primorialHighConductorWithZeroSector k x R‖ ^ 2 ≤
      2 * ‖primorialHighCollapsedCore k x R‖ ^ 2 +
        2 * ‖primorialHighConductorReindexError k x R‖ ^ 2 := by
  rw [primorialHighConductorWithZeroSector_eq_core_add_error
    k hR hlower hupper]
  exact norm_sq_add_le_two _ _

/-- The reindexing error is controlled by one small reindexed raw boundary norm
plus the already-proved low-conductor bound.  This theorem does not open or
absolutely sum the high conductor family. -/
theorem norm_primorialHighConductorReindexError_le
    (k x R : ℕ)
    (hlower : (primorialMinimalWheelSystem k).lower ≤ x)
    (hupper : x ≤ (primorialMinimalWheelSystem k).upper) :
    ‖primorialHighConductorReindexError k x R‖ ≤
      ‖primorialNormalizedRawSmallBoundary k x R‖ +
        6 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := by
  unfold primorialHighConductorReindexError
  calc
    ‖primorialNormalizedRawSmallBoundary k x R -
        primorialSmallNontrivialConductorSector k x R‖ ≤
      ‖primorialNormalizedRawSmallBoundary k x R‖ +
        ‖primorialSmallNontrivialConductorSector k x R‖ := norm_sub_le _ _
    _ ≤ ‖primorialNormalizedRawSmallBoundary k x R‖ +
        6 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := by
      gcongr
      exact norm_primorialSmallNontrivialConductorSector_le
        k x R hlower hupper

end RHLean.Analysis
