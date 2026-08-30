import Mathlib
import RHLean.Proof.SquareRootLowPrimeDescendingPivotStability

/-!
# Four-corner defects behind processed-seat instability

For two fresh-prime coordinates `p` and `q`, the relevant arithmetic square is

```text
x -------- p*x
|            |
q            q
|            |
q*x ------ q*p*x.
```

A `q`-matching can desynchronize the endpoints of the horizontal `p`-edge only
when exactly one vertical extension is present.  Thus an unstable pivot is not
an additional population: it is an orientation of the four-corner square
defect.

On the arithmetic carriers used in the low-prime argument, downward product
closure rules out the reverse orientation.  The only remaining defect is the
upper/product first-failure boundary `q*x in S`, `q*p*x notin S`.

This module is finite combinatorics.  The carrier-specific next step is to
identify that one surviving defect orientation with the existing born
first-failure, root-crossing, and shallow crossing ledgers.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The ordinary outward square defect: the left vertical extension is present
but the upper-right corner is absent. -/
def squareRootLowPrimeProcessedSeatOutwardSquareDefect
    (S : Finset (Option (ℕ × ℕ))) (p q : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  S.filter fun x =>
    x ≠ none ∧
      squareRootLowPrimeProcessedSeatExtend p x ∈ S ∧
      squareRootLowPrimeProcessedSeatExtend q x ∈ S ∧
      squareRootLowPrimeProcessedSeatExtend q
        (squareRootLowPrimeProcessedSeatExtend p x) ∉ S

/-- The reverse square defect.  This orientation is impossible on a carrier
that is downward closed from `q*p*x` to `q*x`. -/
def squareRootLowPrimeProcessedSeatReverseSquareDefect
    (S : Finset (Option (ℕ × ℕ))) (p q : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  S.filter fun x =>
    x ≠ none ∧
      squareRootLowPrimeProcessedSeatExtend p x ∈ S ∧
      squareRootLowPrimeProcessedSeatExtend q x ∉ S ∧
      squareRootLowPrimeProcessedSeatExtend q
        (squareRootLowPrimeProcessedSeatExtend p x) ∈ S

@[simp] theorem mem_squareRootLowPrimeProcessedSeatOutwardSquareDefect
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)} :
    x ∈ squareRootLowPrimeProcessedSeatOutwardSquareDefect S p q ↔
      x ∈ S ∧ x ≠ none ∧
        squareRootLowPrimeProcessedSeatExtend p x ∈ S ∧
        squareRootLowPrimeProcessedSeatExtend q x ∈ S ∧
        squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x) ∉ S := by
  simp [squareRootLowPrimeProcessedSeatOutwardSquareDefect]

@[simp] theorem mem_squareRootLowPrimeProcessedSeatReverseSquareDefect
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)} :
    x ∈ squareRootLowPrimeProcessedSeatReverseSquareDefect S p q ↔
      x ∈ S ∧ x ≠ none ∧
        squareRootLowPrimeProcessedSeatExtend p x ∈ S ∧
        squareRootLowPrimeProcessedSeatExtend q x ∉ S ∧
        squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x) ∈ S := by
  simp [squareRootLowPrimeProcessedSeatReverseSquareDefect]

/-- For a non-head state fresh in `q`, surviving the `q` step means precisely
that the `q` extension is absent.  Freshness excludes the upper-endpoint case. -/
theorem mem_squareRootLowPrimeProcessedSeatFrontierStep_iff_of_fresh
    {S : Finset (Option (ℕ × ℕ))} {q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hxNone : x ≠ none)
    (hqFresh : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor x) :
    x ∈ squareRootLowPrimeProcessedSeatFrontierStep S q ↔
      x ∈ S ∧ squareRootLowPrimeProcessedSeatExtend q x ∉ S := by
  have hxNotUpper :
      x ∉ squareRootLowPrimeProcessedSeatPairUpper S q :=
    squareRootLowPrimeProcessedSeat_not_mem_pairUpper_of_fresh hqFresh
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxNotPaired⟩
    refine ⟨hxS, ?_⟩
    intro hqxS
    apply hxNotPaired
    apply Finset.mem_union.mpr
    left
    exact mem_squareRootLowPrimeProcessedSeatPairLower.mpr
      ⟨hxS, hxNone, hqFresh, hqxS⟩
  · rintro ⟨hxS, hqxNot⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hxS, ?_⟩
    intro hxPaired
    rcases Finset.mem_union.mp hxPaired with hxLower | hxUpper
    · exact hqxNot
        (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower).2.2.2
    · exact hxNotUpper hxUpper

/-- **Outward desynchronization is exactly the outward square defect.** -/
theorem squareRootLowPrimeProcessedSeatFrontierStep_outwardDesync_iff
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hxS : x ∈ S)
    (hpxS : squareRootLowPrimeProcessedSeatExtend p x ∈ S)
    (hxNone : x ≠ none)
    (hpxNone : squareRootLowPrimeProcessedSeatExtend p x ≠ none)
    (hqFreshX : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hqFreshPX : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
      (squareRootLowPrimeProcessedSeatExtend p x)) :
    (squareRootLowPrimeProcessedSeatExtend p x ∈
          squareRootLowPrimeProcessedSeatFrontierStep S q ∧
        x ∉ squareRootLowPrimeProcessedSeatFrontierStep S q) ↔
      x ∈ squareRootLowPrimeProcessedSeatOutwardSquareDefect S p q := by
  rw [mem_squareRootLowPrimeProcessedSeatFrontierStep_iff_of_fresh
      hpxNone hqFreshPX]
  constructor
  · rintro ⟨⟨_hpxS, hqpxNot⟩, hxNotStep⟩
    have hqxS : squareRootLowPrimeProcessedSeatExtend q x ∈ S := by
      by_contra hqxNot
      exact hxNotStep
        ((mem_squareRootLowPrimeProcessedSeatFrontierStep_iff_of_fresh
          hxNone hqFreshX).2 ⟨hxS, hqxNot⟩)
    exact mem_squareRootLowPrimeProcessedSeatOutwardSquareDefect.mpr
      ⟨hxS, hxNone, hpxS, hqxS, hqpxNot⟩
  · intro hdefect
    rcases mem_squareRootLowPrimeProcessedSeatOutwardSquareDefect.mp hdefect with
      ⟨_hxS, _hxNone, _hpxS, hqxS, hqpxNot⟩
    refine ⟨⟨hpxS, hqpxNot⟩, ?_⟩
    intro hxStep
    exact
      ((mem_squareRootLowPrimeProcessedSeatFrontierStep_iff_of_fresh
        hxNone hqFreshX).1 hxStep).2 hqxS

/-- **Reverse desynchronization is exactly the reverse square defect.** -/
theorem squareRootLowPrimeProcessedSeatFrontierStep_reverseDesync_iff
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hxS : x ∈ S)
    (hpxS : squareRootLowPrimeProcessedSeatExtend p x ∈ S)
    (hxNone : x ≠ none)
    (hpxNone : squareRootLowPrimeProcessedSeatExtend p x ≠ none)
    (hqFreshX : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hqFreshPX : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
      (squareRootLowPrimeProcessedSeatExtend p x)) :
    (x ∈ squareRootLowPrimeProcessedSeatFrontierStep S q ∧
        squareRootLowPrimeProcessedSeatExtend p x ∉
          squareRootLowPrimeProcessedSeatFrontierStep S q) ↔
      x ∈ squareRootLowPrimeProcessedSeatReverseSquareDefect S p q := by
  rw [mem_squareRootLowPrimeProcessedSeatFrontierStep_iff_of_fresh
      hxNone hqFreshX]
  constructor
  · rintro ⟨⟨_hxS, hqxNot⟩, hpxNotStep⟩
    have hqpxS :
        squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x) ∈ S := by
      by_contra hqpxNot
      exact hpxNotStep
        ((mem_squareRootLowPrimeProcessedSeatFrontierStep_iff_of_fresh
          hpxNone hqFreshPX).2 ⟨hpxS, hqpxNot⟩)
    exact mem_squareRootLowPrimeProcessedSeatReverseSquareDefect.mpr
      ⟨hxS, hxNone, hpxS, hqxNot, hqpxS⟩
  · intro hdefect
    rcases mem_squareRootLowPrimeProcessedSeatReverseSquareDefect.mp hdefect with
      ⟨_hxS, _hxNone, _hpxS, hqxNot, hqpxS⟩
    refine ⟨⟨hxS, hqxNot⟩, ?_⟩
    intro hpxStep
    exact
      ((mem_squareRootLowPrimeProcessedSeatFrontierStep_iff_of_fresh
        hpxNone hqFreshPX).1 hpxStep).2 hqpxS

/-- Downward square closure makes the reverse defect population empty. -/
theorem squareRootLowPrimeProcessedSeatReverseSquareDefect_eq_empty_of_downward
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    (hdown : ∀ x,
      squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x) ∈ S →
        squareRootLowPrimeProcessedSeatExtend q x ∈ S) :
    squareRootLowPrimeProcessedSeatReverseSquareDefect S p q = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases mem_squareRootLowPrimeProcessedSeatReverseSquareDefect.mp hx with
    ⟨_hxS, _hxNone, _hpxS, hqxNot, hqpxS⟩
  exact hqxNot (hdown x hqpxS)

end RHLean.Proof
