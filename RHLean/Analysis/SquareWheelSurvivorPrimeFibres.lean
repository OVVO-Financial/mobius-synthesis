import Mathlib
import RHLean.Analysis.SquareWheelSurvivorRun
import RHLean.Proof.SurvivorPrimeFaceRealization

/-!
# Prime-fibre form of the survivor-centered square-wheel run

The survivor-run reduction leaves one signed global object

```text
Z_16(b) - Z_16(a)
  - (rho_b-rho_a) * R_k(U_k).
```

This file distributes both pieces over the same distinguished-prime coordinate
before any norm is taken.

The survivor zero mode is already represented by canonical source pairs
`(c,q)`.  Summing the actual fixed-`q` cofactor masses over `q` recovers the full
survivor exactly.  The wheel-end residual is a Möbius sum over the block
endpoint interval; partitioning each nontrivial integer by its unique canonical
largest prime gives an exact endpoint prime fibre as well.

Consequently the full survivor-centered run is a sum of centered prime fibres

```text
F_b(q) - F_a(q) - (rho_b-rho_a) * E_k(q),
```

where `F_t(q)` is the actual fixed-prime survivor mass and `E_k(q)` is the
Möbius mass at the wheel endpoint whose canonical largest prime is `q`.

This does not assert cancellation between prime fibres.  It exposes the exact
signed cross-`q` family on which such a theorem would have to act.  In
particular, the rank-one wheel correction is no longer a separate global scalar:
it is distributed over the same prime coordinate as the survivor population.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryBridge
open RHLean.Arithmetic
open RHLean.Analysis

/-- Public local copy of the source sign law needed by the prime-fibre
reindexing.  The corresponding theorem in `SurvivorZeroMode` is intentionally
private to that module. -/
private theorem canonicalMoebiusWeight_mul_eq_neg_of_sourceData_fibre
    {c q : ℕ} (hdata : CanonicalSourceData q c) :
    canonicalMoebiusWeight (c * q) = -canonicalMoebiusWeight c := by
  rcases hdata with ⟨hq, _hc1, _hsq, hcop, _hdom⟩
  have hmu :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm
  unfold canonicalMoebiusWeight
  rw [hmu, ArithmeticFunction.moebius_apply_prime hq]
  push_cast
  ring

/-- The full survivor zero mode is the exact sum of the actual fixed-prime
cofactor fibres. -/
theorem survivorZeroMode_eq_sum_fixedPrimeCofactorMass
    (Λ : ℝ) (t : ℕ) :
    survivorZeroMode Λ t =
      ∑ q ∈ Finset.Icc 2 (squarePrefixEndpoint t),
        survivorFixedPrimeCofactorMass Λ t q := by
  classical
  rw [← survivorZeroModePairSourceMass_eq_zeroMode]
  unfold survivorZeroModePairSourceMass survivorZeroModePairSet
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈
        (Finset.Icc 1 (squarePrefixEndpoint t)).product
          (Finset.Icc 2 (squarePrefixEndpoint t)),
        if IsSurvivorZeroModePair Λ t cq.1 cq.2 then
          canonicalMoebiusWeight (cq.1 * cq.2)
        else 0) =
      ∑ c ∈ Finset.Icc 1 (squarePrefixEndpoint t),
        ∑ q ∈ Finset.Icc 2 (squarePrefixEndpoint t),
          if IsSurvivorZeroModePair Λ t c q then
            canonicalMoebiusWeight (c * q)
          else 0 := by
            simpa only using
              (Finset.sum_product
                (s := Finset.Icc 1 (squarePrefixEndpoint t))
                (t := Finset.Icc 2 (squarePrefixEndpoint t))
                (f := fun cq : ℕ × ℕ =>
                  if IsSurvivorZeroModePair Λ t cq.1 cq.2 then
                    canonicalMoebiusWeight (cq.1 * cq.2)
                  else 0))
    _ =
      ∑ q ∈ Finset.Icc 2 (squarePrefixEndpoint t),
        ∑ c ∈ Finset.Icc 1 (squarePrefixEndpoint t),
          if IsSurvivorZeroModePair Λ t c q then
            canonicalMoebiusWeight (c * q)
          else 0 := by
            rw [Finset.sum_comm]
    _ =
      ∑ q ∈ Finset.Icc 2 (squarePrefixEndpoint t),
        survivorFixedPrimeCofactorMass Λ t q := by
          apply Finset.sum_congr rfl
          intro q hq
          unfold survivorFixedPrimeCofactorMass
          apply Finset.sum_congr rfl
          intro c hc
          unfold survivorFixedPrimeCofactorTerm
            survivorFixedPrimeActivityIndicator
          by_cases hpair : IsSurvivorZeroModePair Λ t c q
          · have hweight :=
              canonicalMoebiusWeight_mul_eq_neg_of_sourceData_fibre hpair.1
            simp [hpair, hweight]
          · simp [hpair]

/-- A fixed-prime survivor fibre vanishes once its prime coordinate lies beyond
the current square endpoint. -/
theorem survivorFixedPrimeCofactorMass_eq_zero_of_endpoint_lt_prime
    (Λ : ℝ) (t q : ℕ) (hq : squarePrefixEndpoint t < q) :
    survivorFixedPrimeCofactorMass Λ t q = 0 := by
  classical
  unfold survivorFixedPrimeCofactorMass
  apply Finset.sum_eq_zero
  intro c hc
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
  have hnotPair : ¬ IsSurvivorZeroModePair Λ t c q := by
    intro hpair
    have hprod := hpair.2.1
    have hqle : q ≤ c * q := by
      simpa using Nat.mul_le_mul_right q hc1
    exact (not_le_of_gt hq) (hqle.trans hprod)
  simp [survivorFixedPrimeCofactorTerm,
    survivorFixedPrimeActivityIndicator, hnotPair]

/-- The survivor may be summed over any larger prime range without changing its
value.  This is the form used to put both run endpoints and the wheel endpoint
on the same `q`-index set. -/
theorem survivorZeroMode_eq_sum_fixedPrimeCofactorMass_to_upper
    (Λ : ℝ) (t U : ℕ) (hXU : squarePrefixEndpoint t ≤ U) :
    survivorZeroMode Λ t =
      ∑ q ∈ Finset.Icc 2 U, survivorFixedPrimeCofactorMass Λ t q := by
  rw [survivorZeroMode_eq_sum_fixedPrimeCofactorMass Λ t]
  have hsubset :
      Finset.Icc 2 (squarePrefixEndpoint t) ⊆ Finset.Icc 2 U := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨hq2, hqX⟩
    exact Finset.mem_Icc.mpr ⟨hq2, hqX.trans hXU⟩
  apply Finset.sum_subset hsubset
  intro q hqU hqNotSmall
  have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hqU).1
  have hqX : squarePrefixEndpoint t < q := by
    by_contra hnot
    exact hqNotSmall (Finset.mem_Icc.mpr ⟨hq2, Nat.le_of_not_gt hnot⟩)
  exact survivorFixedPrimeCofactorMass_eq_zero_of_endpoint_lt_prime Λ t q hqX

/-- Möbius mass in the wheel-end interval whose canonical largest prime is the
specified `q`. -/
def primorialMinimalWheelEndpointPrimeFiber (k q : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc (primorialBlockLower k) (primorialBlockUpper k),
    if canonicalLargestPrimeFactor m = q then canonicalMoebiusWeight m else 0

/-- Every integer in the nonempty primorial block has a canonical largest prime
lying in the common endpoint range `2,...,U_k`. -/
private theorem canonicalLargestPrimeFactor_mem_primorialEndpointRange
    (k m : ℕ)
    (hm : m ∈ Finset.Ioc (primorialBlockLower k) (primorialBlockUpper k)) :
    canonicalLargestPrimeFactor m ∈ Finset.Icc 2 (primorialBlockUpper k) := by
  rcases Finset.mem_Ioc.mp hm with ⟨hmLower, hmUpper⟩
  have hLowerPos : 0 < primorialBlockLower k := by
    exact primorialEndpoint_pos k
  have hmgt : 1 < m := by omega
  have hqPrime := canonicalLargestPrimeFactor_prime hmgt
  have hqDvd := canonicalLargestPrimeFactor_dvd hmgt
  have hqLeM : canonicalLargestPrimeFactor m ≤ m :=
    Nat.le_of_dvd (by omega) hqDvd
  exact Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqLeM.trans hmUpper⟩

/-- The minimal-wheel endpoint residual is exactly the sum of the endpoint
prime fibres.  This is a partition by the unique canonical largest prime. -/
theorem primorialMinimalWheel_endpointResidual_eq_sum_primeFibers
    (k : ℕ) :
    ((((primorialMinimalWheelSystem k).residual
        (primorialBlockUpper k) : ℤ) : ℂ)) =
      ∑ q ∈ Finset.Icc 2 (primorialBlockUpper k),
        primorialMinimalWheelEndpointPrimeFiber k q := by
  rw [primorialMinimalWheel_residual_eq_moebiusInterval k (le_refl _)]
  push_cast
  unfold primorialMinimalWheelEndpointPrimeFiber canonicalMoebiusWeight
  calc
    (∑ m ∈ Finset.Ioc (primorialBlockLower k) (primorialBlockUpper k),
        ((μ m : ℤ) : ℂ)) =
      ∑ m ∈ Finset.Ioc (primorialBlockLower k) (primorialBlockUpper k),
        ∑ q ∈ Finset.Icc 2 (primorialBlockUpper k),
          if canonicalLargestPrimeFactor m = q then ((μ m : ℤ) : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro m hm
            have hqmem :=
              canonicalLargestPrimeFactor_mem_primorialEndpointRange k m hm
            symm
            rw [Finset.sum_eq_single (canonicalLargestPrimeFactor m)]
            · simp
            · intro q hq hne
              simp [hne.symm]
            · intro hnot
              exact (hnot hqmem).elim
    _ =
      ∑ q ∈ Finset.Icc 2 (primorialBlockUpper k),
        ∑ m ∈ Finset.Ioc (primorialBlockLower k) (primorialBlockUpper k),
          if canonicalLargestPrimeFactor m = q then ((μ m : ℤ) : ℂ) else 0 := by
            rw [Finset.sum_comm]

/-- One centered prime fibre of a survivor run.  The wheel-end correction is
now distributed over the same distinguished-prime coordinate as the survivor
masses. -/
def primorialMinimalSquareWheelSurvivorCenteredPrimeRunFiber
    (k a b q : ℕ) : ℂ :=
  survivorFixedPrimeCofactorMass 16 b q -
    survivorFixedPrimeCofactorMass 16 a q -
    (squareWheelSampleRatio (primorialMinimalWheelSystem k) b -
      squareWheelSampleRatio (primorialMinimalWheelSystem k) a) *
      primorialMinimalWheelEndpointPrimeFiber k q

/-- **Prime-fibre decomposition of the survivor-centered run.**  When both
square samples lie before the wheel endpoint, the complete run coordinate is
the signed sum of its centered fixed-prime fibres. -/
theorem primorialMinimalSquareWheelSurvivorRunCentered_eq_sum_primeFibers
    (k a b : ℕ)
    (haUpper : squarePrefixEndpoint a ≤ primorialBlockUpper k)
    (hbUpper : squarePrefixEndpoint b ≤ primorialBlockUpper k) :
    primorialMinimalSquareWheelSurvivorRunCentered k a b =
      ∑ q ∈ Finset.Icc 2 (primorialBlockUpper k),
        primorialMinimalSquareWheelSurvivorCenteredPrimeRunFiber k a b q := by
  have ha :=
    survivorZeroMode_eq_sum_fixedPrimeCofactorMass_to_upper
      16 a (primorialBlockUpper k) haUpper
  have hb :=
    survivorZeroMode_eq_sum_fixedPrimeCofactorMass_to_upper
      16 b (primorialBlockUpper k) hbUpper
  have hend := primorialMinimalWheel_endpointResidual_eq_sum_primeFibers k
  unfold primorialMinimalSquareWheelSurvivorRunCentered
    primorialMinimalSquareWheelSurvivorCenteredPrimeRunFiber
  rw [ha, hb, hend]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]

end RHLean.Proof
