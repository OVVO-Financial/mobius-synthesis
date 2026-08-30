import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchingDisplacement

/-!
# Upper-endpoint displacement in the processed-seat matching

The instability observed in the sequential processed-seat frontier is naturally
an upper-endpoint phenomenon.  A terminal state may have the form

`x = p * y`

with the same seat coordinate, even though the fresh `p`-edge was available in
the original carrier.  Since `x` survives the stage at which `p` is processed,
its parent `y` cannot still be present then.  Therefore `y` was consumed by an
earlier coordinate `q<p`.

This is the first alternating-path move:

`q-edge used earlier, p-edge available later`.

Replacing the used `q`-edge by the available `p`-edge matches `x` and displaces
only the opposite endpoint of the earlier `q`-edge.  The blocker label has
strictly decreased from `p` to `q`.  Iterating this move pushes every apparent
unstable terminal state toward a genuine first-failure root and cannot cycle.

The theorem below is purely finite and carrier-level.  No arithmetic estimate,
norm, or asymptotic input is used.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **A surviving upper endpoint has an earlier blocker.**

Assume `x = extend p y`, the parent `y` and child `x` both belonged to the
original carrier, and `x` survives the complete matching with `p` processed
after the prefix `pre`.  Then `y` was paired at one concrete prefix coordinate
`q`, necessarily with `q<p` when the prefix is ordered below `p`. -/
theorem squareRootLowPrimeProcessedSeatTerminal_upper_has_earlier_blocker
    (pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x y : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
      (pre ++ p :: post) S)
    (hyS : y ∈ S)
    (hyHead : y ≠ none)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor y)
    (hxy : squareRootLowPrimeProcessedSeatExtend p y = x)
    (hpre : ∀ q ∈ pre, q < p) :
    ∃ pre' q post' z,
      pre = pre' ++ q :: post' ∧ q < p ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre' S ∧
        ((y ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q y) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            y = squareRootLowPrimeProcessedSeatExtend q z)) := by
  have hxRewritten :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier post
        (squareRootLowPrimeProcessedSeatFrontierStep
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p) := by
    rw [squareRootLowPrimeProcessedSeatMatchingFrontier_append] at hx
    simpa [squareRootLowPrimeProcessedSeatMatchingFrontier] using hx
  have hxStep :
      x ∈ squareRootLowPrimeProcessedSeatFrontierStep
        (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' post _ hxRewritten
  have hxPre :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre S :=
    (Finset.mem_sdiff.mp hxStep).1
  have hyLost :
      y ∉ squareRootLowPrimeProcessedSeatMatchingFrontier pre S := by
    intro hyPre
    have hyLower :
        y ∈ squareRootLowPrimeProcessedSeatPairLower
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
      mem_squareRootLowPrimeProcessedSeatPairLower.mpr
        ⟨hyPre, hyHead, hpFresh, by simpa [hxy] using hxPre⟩
    have hxUpper :
        x ∈ squareRootLowPrimeProcessedSeatPairUpper
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p := by
      unfold squareRootLowPrimeProcessedSeatPairUpper
      exact Finset.mem_image.mpr ⟨y, hyLower, hxy⟩
    exact (Finset.mem_sdiff.mp hxStep).2
      (Finset.mem_union.mpr (Or.inr hxUpper))
  rcases squareRootLowPrimeProcessedSeat_removed_has_owner
      pre S hyS hyLost with
    ⟨pre', q, post', hpreSplit, hpaired⟩
  have hqpre : q ∈ pre := by
    rw [hpreSplit]
    simp
  have hqp : q < p := hpre q hqpre
  rcases squareRootLowPrimeProcessedSeatPaired_has_partner hpaired with
    ⟨z, hz, hedge⟩
  exact ⟨pre', q, post', z, hpreSplit, hqp, hz, hedge⟩

/-- The blocker strictly decreases, so one upper-displacement move cannot return
to the same prime coordinate. -/
theorem squareRootLowPrimeProcessedSeatTerminal_upper_blocker_ne
    {p q : ℕ} (hqp : q < p) : q ≠ p := by
  omega

end RHLean.Proof
