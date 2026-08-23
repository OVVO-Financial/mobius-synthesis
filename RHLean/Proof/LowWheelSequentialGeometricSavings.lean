import Mathlib
import RHLean.Proof.LowWheelDoubleFaceFiniteDifference
import RHLean.Proof.PrimeCombVisualizationRecurrence
import RHLean.Analysis.SquareRootMiddleSequentialCoherence

/-!
# Sequential geometric savings in the low-wheel transport

The low-wheel survivor rewrite and the ordered-prime recurrence must be used
together.  At the complete square endpoint `X_R = R^2 - 1`:

* a high integer `q` is prime exactly when it survives every low-prime wheel
  coordinate through `R`;
* when such a fresh `q > R` arrives, the frozen prime universe changes by the
  already-completed lower-scale Mertens value `M(floor(X_R/q))`;
* the reciprocal parent cutoff is strictly below `R`;
* the number of multiplier seats available to the fresh prime is exactly
  `floor(X_R/q)-1`, and these seat sets shrink monotonically as the admitted
  prime increases;
* inside the two-copy low-wheel expansion, a fixed fresh coordinate acts by a
  mixed multiplicative finite difference supported only on its two geometric
  shells.

Thus the high transport is not a static collection of unrelated prime fibres.
It is a sequential filtration of geometrically shrinking low-wheel updates.
All statements here are exact and finite; no norm, PNT estimate, or asymptotic
input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The prime predicate in the exact Mertens transform can be removed entirely:
on the high square interval it is exactly the low-wheel survivor predicate. -/
theorem squareRootTransportPrimeFirst_eq_lowWheelSequentialMertens
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportPrimeFirst R =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if lowWheelHighSurvivor R q then
          mertensSummatory (squareRootEndpoint R / q)
        else
          0 := by
  rw [squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)]
  apply Finset.sum_congr rfl
  intro q hq
  have hqI := Finset.mem_Ioc.mp hq
  have hiff := lowWheelHighSurvivor_iff_prime hR hqI.1 hqI.2
  by_cases hp : q.Prime
  · have hs : lowWheelHighSurvivor R q := hiff.mpr hp
    simp [hp, hs]
  · have hs : ¬ lowWheelHighSurvivor R q := by
      intro h
      exact hp (hiff.mp h)
    simp [hp, hs]

/-- Every active post-root update reads a genuinely lower-scale parent prefix. -/
theorem lowWheelSequential_parentCutoff_lt_root
    {R q : ℕ} (hR : 2 ≤ R) (hRq : R < q) :
    squareRootEndpoint R / q < R :=
  squareRootEndpoint_div_lt_root_of_postRoot (by omega) hRq

/-- Exact geometric seat count for one post-root fresh prime.  The update has
only `floor(X_R/q)-1` possible proper-multiple seats, strictly fewer than `R`. -/
theorem lowWheelSequential_postRootSeatCount
    {R q : ℕ} (hR : 2 ≤ R) (hRq : R < q) :
    (primeCombProperMultiplierSet q (squareRootEndpoint R)).card =
        squareRootEndpoint R / q - 1 ∧
      (primeCombProperMultiplierSet q (squareRootEndpoint R)).card < R := by
  constructor
  · exact card_primeCombProperMultiplierSet q (squareRootEndpoint R)
  · rw [card_primeCombProperMultiplierSet]
    have hcut := lowWheelSequential_parentCutoff_lt_root hR hRq
    omega

/-- **Shrinking sequential rake.**  Later admitted primes can act on no more
multiplier seats than earlier admitted primes. -/
theorem lowWheelSequential_postRootSeats_antitone
    {R p q : ℕ} (hp : p.Prime) (hpq : p ≤ q) :
    primeCombProperMultiplierSet q (squareRootEndpoint R) ⊆
      primeCombProperMultiplierSet p (squareRootEndpoint R) :=
  primeCombProperMultiplierSet_antitone hp.pos hpq

/-- Cardinal form of the sequential shrinking-rake law. -/
theorem lowWheelSequential_postRootSeatCount_antitone
    {R p q : ℕ} (hp : p.Prime) (hpq : p ≤ q) :
    (primeCombProperMultiplierSet q (squareRootEndpoint R)).card ≤
      (primeCombProperMultiplierSet p (squareRootEndpoint R)).card :=
  card_primeCombProperMultiplierSet_antitone hp.pos hpq

/-- **One sequential high-prime update with its geometric saving attached.**
The same fresh-prime step simultaneously has the exact Mertens recurrence and a
strictly sub-root multiplier support. -/
theorem squareRootFrozenPrimeUniverse_step_and_support
    (R q : ℕ) (hR : 2 ≤ R) (hq : q.Prime) (hRq : R < q) :
    ((frozenPrimeUniverseMass (primesUpTo q) (squareRootEndpoint R) : ℤ) : ℂ) =
        ((frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R) : ℤ) : ℂ) -
          mertensSummatory (squareRootEndpoint R / q) ∧
      squareRootEndpoint R / q < R ∧
      (primeCombProperMultiplierSet q (squareRootEndpoint R)).card < R := by
  refine ⟨squareRootFrozenPrimeUniverse_primesUpTo_step
      R q (by omega) hq hRq, ?_, ?_⟩
  · exact lowWheelSequential_parentCutoff_lt_root hR hRq
  · exact (lowWheelSequential_postRootSeatCount hR hRq).2

/-- Monotonicity chain for two successive post-root prime updates: both parent
cutoffs and actual rake cardinalities shrink as the fresh prime increases. -/
theorem lowWheelSequential_twoPrimeGeometry
    {R p q : ℕ} (hR : 2 ≤ R)
    (hp : p.Prime) (_hq : q.Prime) (hRp : R < p) (hpq : p ≤ q) :
    squareRootEndpoint R / q ≤ squareRootEndpoint R / p ∧
      (primeCombProperMultiplierSet q (squareRootEndpoint R)).card ≤
        (primeCombProperMultiplierSet p (squareRootEndpoint R)).card ∧
      squareRootEndpoint R / q < R := by
  refine ⟨Nat.div_le_div_left hpq hp.pos, ?_, ?_⟩
  · exact lowWheelSequential_postRootSeatCount_antitone hp hpq
  · have hRq : R < q := hRp.trans_le hpq
    exact lowWheelSequential_parentCutoff_lt_root hR hRq

/-- Endpoint first-difference shell for any multiplicative coordinate `p >= 1`. -/
theorem lowWheelEndpointCrossingDifference_eq_primeShell
    {p X n : ℕ} (hp : 1 ≤ p) :
    lowWheelEndpointCrossingDifference p X n =
      if p * n ≤ X ∧ X < p * p * n then 1 else 0 := by
  unfold lowWheelEndpointCrossingDifference lowWheelEndpointIndicator
  have hnle : n ≤ p * n := by
    simpa [one_mul] using Nat.mul_le_mul_right n hp
  have hple : p * n ≤ p * p * n := by
    calc
      p * n ≤ p * (p * n) := Nat.mul_le_mul_left p hnle
      _ = p * p * n := by ring
  split_ifs <;> omega

/-- Endpoint second difference for any coordinate `p >= 1`: all interior mass
cancels and only the two adjacent multiplicative shells remain. -/
theorem lowWheelEndpointSecondDifference_eq_twoPrimeShells
    {p X n : ℕ} (hp : 1 ≤ p) :
    lowWheelEndpointSecondDifference p X n =
      (if n ≤ X ∧ X < p * n then 1 else 0) -
        (if p * n ≤ X ∧ X < p * p * n then 1 else 0) := by
  unfold lowWheelEndpointSecondDifference lowWheelEndpointIndicator
  have hnle : n ≤ p * n := by
    simpa [one_mul] using Nat.mul_le_mul_right n hp
  have hple : p * n ≤ p * p * n := by
    calc
      p * n ≤ p * (p * n) := Nat.mul_le_mul_left p hnle
      _ = p * p * n := by ring
  split_ifs <;> omega

/-- Lower root-crossing shell for any multiplicative coordinate `p >= 1`. -/
theorem lowWheelRootCrossingDifference_eq_primeShell
    {p R q : ℕ} (hp : 1 ≤ p) :
    lowWheelRootCrossingDifference p R q =
      if q ≤ R ∧ R < p * q then -1 else 0 := by
  unfold lowWheelRootCrossingDifference lowWheelRootHighIndicator
  have hqle : q ≤ p * q := by
    simpa [one_mul] using Nat.mul_le_mul_right q hp
  split_ifs <;> omega

/-- **Sequential geometric localization of one mixed low-wheel coordinate.**
For every prime-sized multiplicative step `p >= 1`, the four-corner cell has no
interior contribution: it is exactly the difference of two adjacent geometric
shells.  The second shell carries the enlarged lower cutoff `R < p*q`, so the
chronology of adding `p` is visible in the same formula as the geometric
support saving. -/
theorem lowWheelMixedPrimeCell_eq_sequentialShellDifference
    {p R X q n : ℕ} (hp : 1 ≤ p) :
    lowWheelMixedPrimeCell p R X q n =
      (if R < q ∧ n ≤ X ∧ X < p * n then 1 else 0) -
        (if R < p * q ∧ p * n ≤ X ∧ X < p * p * n then 1 else 0) := by
  unfold lowWheelMixedPrimeCell lowWheelTransportIndicator
    lowWheelRootHighIndicator lowWheelEndpointIndicator
  have hnle : n ≤ p * n := by
    simpa [one_mul] using Nat.mul_le_mul_right n hp
  have hple : p * n ≤ p * p * n := by
    calc
      p * n ≤ p * (p * n) := Nat.mul_le_mul_left p hnle
      _ = p * p * n := by ring
  have hqle : q ≤ p * q := by
    simpa [one_mul] using Nat.mul_le_mul_right q hp
  split_ifs <;> omega

/-- Support form: a nonzero mixed cell must lie in one of the two sequential
multiplicative shells. -/
theorem lowWheelMixedPrimeCell_ne_zero_imp_shell
    {p R X q n : ℕ} (hp : 1 ≤ p)
    (h : lowWheelMixedPrimeCell p R X q n ≠ 0) :
    (R < q ∧ n ≤ X ∧ X < p * n) ∨
      (R < p * q ∧ p * n ≤ X ∧ X < p * p * n) := by
  by_cases hfirst : R < q ∧ n ≤ X ∧ X < p * n
  · exact Or.inl hfirst
  · by_cases hsecond : R < p * q ∧ p * n ≤ X ∧ X < p * p * n
    · exact Or.inr hsecond
    · rw [lowWheelMixedPrimeCell_eq_sequentialShellDifference hp] at h
      simp [hfirst, hsecond] at h

end RHLean.Proof
