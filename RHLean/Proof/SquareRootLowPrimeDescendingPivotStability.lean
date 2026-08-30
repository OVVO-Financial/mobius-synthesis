import Mathlib
import RHLean.Proof.SquareRootLowPrimeDisplacementDiamond

/-!
# Descending-prime stability of processed-seat pivots

The increasing-prime matching exposes an artificial unstable-pivot population:
a proposed `p`-edge may become one-sided because one endpoint was consumed by a
strictly larger prime coordinate.  The strict-larger-prime charge means that
the dependency graph is upper triangular.  Process the same zero-mass matchings
in descending prime order instead.

This file records the order reversal and the elementary commuting-square lemma
behind it.  If the two endpoints of a `p`-edge have the same availability in a
fresh `q`-direction, then the complete `q`-matching removes either both
endpoints or neither endpoint.  Thus a larger coordinate cannot destabilize the
smaller pivot except where that arithmetic square fails to lie in the carrier.
Those failures are the genuine born/cutoff first-failure populations, not an
independent unstable population.

No estimate is asserted here.  The next carrier-specific theorem must prove the
required square closure away from the already isolated first-failure and
root-crossing frontiers.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The same fresh-prime coordinates as before, but processed from largest to
smallest. -/
def squareRootLowPrimeFreshPrimeListDescending
    (K U : ℕ) : List ℕ :=
  (squareRootLowPrimeFreshPrimeList K U).reverse

/-- Every coordinate in the descending list is still an actual fresh prime. -/
theorem prime_of_mem_squareRootLowPrimeFreshPrimeListDescending
    {K U p : ℕ}
    (hp : p ∈ squareRootLowPrimeFreshPrimeListDescending K U) :
    p.Prime := by
  apply prime_of_mem_squareRootLowPrimeFreshPrimeList
  simpa [squareRootLowPrimeFreshPrimeListDescending] using hp

/-- Complete processed-seat frontier formed in descending prime order. -/
def squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
    (R K j U : ℕ) : Finset (Option (ℕ × ℕ)) :=
  squareRootLowPrimeProcessedSeatMatchingFrontier
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- Reordering the zero-mass prime matchings does not change the represented
terminal state. -/
theorem squareRootLowPrimeProcessedSeatDescendingTerminalFrontier_weight_sum
    {R K j U : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  have hmatch := squareRootLowPrimeProcessedSeat_weight_sum_eq_matchingFrontier
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
    (fun p hp =>
      prime_of_mem_squareRootLowPrimeFreshPrimeListDescending hp)
  rw [squareRootLowPrimeProcessedSeatCarrier_mass_eq_runningImbalanceReal hR]
    at hmatch
  exact hmatch.symm

/-- A state fresh in the `q` coordinate cannot be an upper endpoint of a
`q`-pair. -/
theorem squareRootLowPrimeProcessedSeat_not_mem_pairUpper_of_fresh
    {S : Finset (Option (ℕ × ℕ))} {q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hfresh : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor x) :
    x ∉ squareRootLowPrimeProcessedSeatPairUpper S q := by
  intro hxUpper
  rcases Finset.mem_image.mp hxUpper with ⟨y, hyLower, hyx⟩
  have hyData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hyLower
  rcases y with _ | w
  · exact (hyData.2.1 rfl).elim
  · rcases x with _ | z
    · simp [squareRootLowPrimeProcessedSeatExtend] at hyx
    · simp only [squareRootLowPrimeProcessedSeatExtend,
        Option.some.injEq] at hyx
      have hfirst := congrArg Prod.fst hyx
      apply hfresh
      change q ∣ z.1
      exact ⟨w.1, hfirst.symm⟩

/-- If the two endpoints of a `p`-edge see the same `q`-extension membership,
then they are simultaneously lower endpoints of the `q`-matching. -/
theorem squareRootLowPrimeProcessedSeatPairLower_mem_iff_of_fresh_square
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hxS : x ∈ S)
    (hpxS : squareRootLowPrimeProcessedSeatExtend p x ∈ S)
    (hxNone : x ≠ none)
    (hpxNone : squareRootLowPrimeProcessedSeatExtend p x ≠ none)
    (hqFreshX : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hqFreshPX : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
      (squareRootLowPrimeProcessedSeatExtend p x))
    (hsquare :
      squareRootLowPrimeProcessedSeatExtend q x ∈ S ↔
        squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x) ∈ S) :
    x ∈ squareRootLowPrimeProcessedSeatPairLower S q ↔
      squareRootLowPrimeProcessedSeatExtend p x ∈
        squareRootLowPrimeProcessedSeatPairLower S q := by
  constructor
  · intro hxLower
    have hxData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower
    apply mem_squareRootLowPrimeProcessedSeatPairLower.mpr
    exact ⟨hpxS, hpxNone, hqFreshPX, hsquare.mp hxData.2.2.2⟩
  · intro hpxLower
    have hpxData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hpxLower
    apply mem_squareRootLowPrimeProcessedSeatPairLower.mpr
    exact ⟨hxS, hxNone, hqFreshX, hsquare.mpr hpxData.2.2.2⟩

/-- **One-step pivot synchronization.**  Under the commuting-square condition,
a fresh `q`-matching preserves the two endpoints of a `p`-edge together: after
the `q` step either both remain or neither remains. -/
theorem squareRootLowPrimeProcessedSeatFrontierStep_mem_iff_of_fresh_square
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hxS : x ∈ S)
    (hpxS : squareRootLowPrimeProcessedSeatExtend p x ∈ S)
    (hxNone : x ≠ none)
    (hpxNone : squareRootLowPrimeProcessedSeatExtend p x ≠ none)
    (hqFreshX : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hqFreshPX : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
      (squareRootLowPrimeProcessedSeatExtend p x))
    (hsquare :
      squareRootLowPrimeProcessedSeatExtend q x ∈ S ↔
        squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x) ∈ S) :
    x ∈ squareRootLowPrimeProcessedSeatFrontierStep S q ↔
      squareRootLowPrimeProcessedSeatExtend p x ∈
        squareRootLowPrimeProcessedSeatFrontierStep S q := by
  have hlower :=
    squareRootLowPrimeProcessedSeatPairLower_mem_iff_of_fresh_square
      hxS hpxS hxNone hpxNone hqFreshX hqFreshPX hsquare
  have hxNotUpper :=
    squareRootLowPrimeProcessedSeat_not_mem_pairUpper_of_fresh
      (S := S) hqFreshX
  have hpxNotUpper :=
    squareRootLowPrimeProcessedSeat_not_mem_pairUpper_of_fresh
      (S := S) hqFreshPX
  constructor
  · intro hxStep
    rcases Finset.mem_sdiff.mp hxStep with ⟨_hxIn, hxNotPaired⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hpxS, ?_⟩
    intro hpxPaired
    rcases Finset.mem_union.mp hpxPaired with hpxLower | hpxUpper
    · apply hxNotPaired
      exact Finset.mem_union.mpr (Or.inl (hlower.mpr hpxLower))
    · exact hpxNotUpper hpxUpper
  · intro hpxStep
    rcases Finset.mem_sdiff.mp hpxStep with ⟨_hpxIn, hpxNotPaired⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hxS, ?_⟩
    intro hxPaired
    rcases Finset.mem_union.mp hxPaired with hxLower | hxUpper
    · apply hpxNotPaired
      exact Finset.mem_union.mpr (Or.inl (hlower.mp hxLower))
    · exact hxNotUpper hxUpper

end RHLean.Proof
