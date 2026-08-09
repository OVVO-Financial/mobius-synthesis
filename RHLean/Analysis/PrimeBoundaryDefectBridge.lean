import Mathlib
import RHLean.Arithmetic.FullPrimeFactorizationState
import RHLean.Proof.RealSquareBlockIncrements

/-!
# Prime-coordinate boundary defects

This module keeps two exact coordinate systems for a square-block Möbius
increment separate:

* canonical terminal-prime channels provide a unique arithmetic decomposition;
* fixed-prime Boolean matchings provide cancellation coordinates.

The second representation is redundant: every complete prime coordinate equals
the same increment.  Consequently raw summation over prime coordinates
multiplies the increment by the number of coordinates, while normalized
averaging preserves it.  The redundancy is useful because its second moment is
exactly the coordinate count times the square of the block increment.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- Integer-valued indicator of a finite arithmetic window. -/
def windowIndicator (W : Finset ℕ) (n : ℕ) : ℤ :=
  if n ∈ W then 1 else 0

/-- Boundary term contributed by one fresh parent-child transport edge. -/
def primePairBoundaryTerm (W : Finset ℕ) (e : PrimeTransportEdge) : ℤ :=
  μ e.parent * (windowIndicator W e.parent - windowIndicator W e.child)

/-- A fresh prime-extension pair contributes only when the window separates its
parent and child.  If both lie inside, or both lie outside, the contribution is
zero. -/
theorem freshPrime_pair_eq_boundaryTerm
    (W : Finset ℕ) (e : PrimeTransportEdge)
    (hfresh : ¬ e.terminal ∣ e.parent) :
    μ e.parent * windowIndicator W e.parent +
        μ e.child * windowIndicator W e.child =
      primePairBoundaryTerm W e := by
  rw [PrimeTransportEdge.moebius_child_eq_neg_parent e hfresh]
  unfold primePairBoundaryTerm
  ring

/-- If both endpoints of a fresh edge lie in the window, their Möbius
contributions cancel exactly. -/
theorem freshPrime_pair_cancel_of_both_mem
    (W : Finset ℕ) (e : PrimeTransportEdge)
    (hfresh : ¬ e.terminal ∣ e.parent)
    (_hparent : e.parent ∈ W) (_hchild : e.child ∈ W) :
    μ e.parent + μ e.child = 0 := by
  rw [PrimeTransportEdge.moebius_child_eq_neg_parent e hfresh]
  ring

/-- If neither endpoint lies in the window, its boundary term vanishes. -/
theorem primePairBoundaryTerm_eq_zero_of_neither_mem
    (W : Finset ℕ) (e : PrimeTransportEdge)
    (hparent : e.parent ∉ W) (hchild : e.child ∉ W) :
    primePairBoundaryTerm W e = 0 := by
  simp [primePairBoundaryTerm, windowIndicator, hparent, hchild]

/-- If both endpoints lie in the window, its boundary term also vanishes. -/
theorem primePairBoundaryTerm_eq_zero_of_both_mem
    (W : Finset ℕ) (e : PrimeTransportEdge)
    (hparent : e.parent ∈ W) (hchild : e.child ∈ W) :
    primePairBoundaryTerm W e = 0 := by
  simp [primePairBoundaryTerm, windowIndicator, hparent, hchild]

/-- Abstract data for a finite family of exact fixed-prime representations of
one increment.  Concrete arithmetic modules supply `defect`; this structure
records the exact fact that every represented prime coordinate equals the same
window sum. -/
structure ExactPrimeBoundaryFamily (P : Finset ℕ) (increment : ℤ) where
  defect : ℕ → ℤ
  exact_on_primes : ∀ q ∈ P, q.Prime ∧ defect q = increment

namespace ExactPrimeBoundaryFamily

variable {P : Finset ℕ} {increment : ℤ}

/-- Raw summation over exact prime coordinates duplicates the increment once
per coordinate. -/
theorem sum_defect_eq_card_mul
    (F : ExactPrimeBoundaryFamily P increment) :
    ∑ q ∈ P, F.defect q = (P.card : ℤ) * increment := by
  calc
    (∑ q ∈ P, F.defect q) = ∑ _q ∈ P, increment := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (F.exact_on_primes q hq).2
    _ = (P.card : ℤ) * increment := by simp

/-- The averaged identity in division-free form.  This is the preferred exact
statement over integers: the sum of all coordinates is the coordinate count
times the original increment. -/
theorem averaged_defect_crossMultiplied
    (F : ExactPrimeBoundaryFamily P increment) :
    ∑ q ∈ P, F.defect q = (P.card : ℤ) * increment :=
  F.sum_defect_eq_card_mul

/-- Exact second-moment rigidity: because every coordinate represents the same
increment, the coordinate energy is the number of coordinates times the square
of that increment. -/
theorem sum_sq_defect_eq_card_mul_sq
    (F : ExactPrimeBoundaryFamily P increment) :
    ∑ q ∈ P, (F.defect q) ^ 2 = (P.card : ℤ) * increment ^ 2 := by
  calc
    (∑ q ∈ P, (F.defect q) ^ 2) = ∑ _q ∈ P, increment ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(F.exact_on_primes q hq).2]
    _ = (P.card : ℤ) * increment ^ 2 := by simp

/-- Any two represented prime directions give the same boundary defect. -/
theorem defect_eq_defect
    (F : ExactPrimeBoundaryFamily P increment)
    {q r : ℕ} (hq : q ∈ P) (hr : r ∈ P) :
    F.defect q = F.defect r := by
  rw [(F.exact_on_primes q hq).2, (F.exact_on_primes r hr).2]

end ExactPrimeBoundaryFamily

/-- A unique canonical decomposition and a redundant fixed-prime family are
bridged by their common increment.  This structure deliberately does not
identify the two coordinate systems term by term. -/
structure CanonicalAndBoundaryBridge (P : Finset ℕ) where
  increment : ℤ
  canonicalContribution : ℤ
  canonical_eq_increment : canonicalContribution = increment
  boundaryFamily : ExactPrimeBoundaryFamily P increment

namespace CanonicalAndBoundaryBridge

variable {P : Finset ℕ}

/-- The canonical terminal-prime total equals every represented fixed-prime
boundary coordinate. -/
theorem canonical_eq_boundary
    (B : CanonicalAndBoundaryBridge P)
    {q : ℕ} (hq : q ∈ P) :
    B.canonicalContribution = B.boundaryFamily.defect q := by
  rw [B.canonical_eq_increment,
    (B.boundaryFamily.exact_on_primes q hq).2]

/-- The canonical total also equals the normalized prime average in exact
cross-multiplied form. -/
theorem card_mul_canonical_eq_sum_boundary
    (B : CanonicalAndBoundaryBridge P) :
    (P.card : ℤ) * B.canonicalContribution =
      ∑ q ∈ P, B.boundaryFamily.defect q := by
  rw [B.canonical_eq_increment,
    B.boundaryFamily.sum_defect_eq_card_mul]

end CanonicalAndBoundaryBridge

/-- Every product entering the concrete block `[100,121)` through a nontrivial
terminal factor has parent at most `60`. -/
theorem parent_le_sixty_of_mem_block_100_121
    {c q n : ℕ} (hq : 2 ≤ q) (hprod : c * q = n)
    (hn : n < 121) :
    c ≤ 60 := by
  have htwo : c * 2 ≤ c * q := Nat.mul_le_mul_left c hq
  rw [hprod] at htwo
  omega

/-- Therefore every such parent lies in the completed square prefix `[1,64)`.
This is the exact `60 < 8²` frontier used by the block schedule. -/
theorem parent_lt_sixtyFour_of_mem_block_100_121
    {c q n : ℕ} (hq : 2 ≤ q) (hprod : c * q = n)
    (hn : n < 121) :
    c < 64 := by
  have hc := parent_le_sixty_of_mem_block_100_121 hq hprod hn
  omega

end RHLean.Analysis
