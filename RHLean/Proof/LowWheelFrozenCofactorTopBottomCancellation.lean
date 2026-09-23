import Mathlib
import RHLean.Proof.LowWheelFrozenCofactorTopBottomToggle
import RHLean.Proof.LowWheelCanonicalRepeatedMovableCancellation

/-!
# Global top/bottom cancellation of the frozen nontrivial-cofactor sector

`LowWheelFrozenCofactorTopBottomToggle` establishes, pointwise, that every
frozen repeated-parent downcross state with nontrivial cofactor `c > 1` has an
explicit opposite-sign partner obtained by moving `q = P⁺(c)` out of the
cofactor and into the quotient,

`(t,(c,p)) ↦ (t,(c/q, q*p))`.

That file proves the four local facts — the move stays on the physical carrier,
preserves the canonical least-prime pivot, reverses the signed weight, and is
involutive at its own coordinate — but it never sums.  This file performs the
missing global subtraction.

Three things are established.

1.  The move is **injective** on the frozen nontrivial-cofactor sector.  The
    inverse is explicit: from `z = (t,(c/q, q*p))` the pivot recovers `p`, the
    ratio `z.2.2 / p` recovers `q`, and multiplying it back into the cofactor
    recovers `c`.  No counting or choice is involved.

2.  Consequently the frozen nontrivial-cofactor ledger is *exactly* minus the
    signed mass of its image,

    `∑_{z ∈ TopImage R} w z = - ∑_{y ∈ FrozenCofactor R} w y`.

3.  The image is **disjoint from the entire downcross carrier**: every image
    state has normalized root-side parent strictly above `R`, whereas every
    downcross state has parent at most `R`.  So this is a genuine relocation of
    the frozen sector onto the post-root side of the same physical carrier, not
    an internal reshuffle of the downcross population.

Combining with the exact late-parent cancellation already proved in
`LowWheelCanonicalRepeatedMovableCancellation` (the repeated *movable* sector
sums to zero) gives the sharpened endpoint identity

`D_R = U_R + F_R^{c=1} - T_R`,

where `U_R` is the unique-parent ledger, `F_R^{c=1}` is the literal terminal
`c = 1` monotone first-crossing boundary, and `T_R` is the post-root image
ledger.  The remaining quantitative seam is restated on that carrier and is
shown to still imply the Riemann hypothesis through the existing square-prefix
energy bridge.

No norm, estimate, or density input is used anywhere in this file.  Every step
is an exact finite identity or an exact sign-reversing reindexing.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

namespace FrozenCofactorTopBottom

/-! ## The explicit inverse coordinate move -/

/-- Inverse of the top/bottom move: read the descending prime off the quotient
and multiply it back into the cofactor.  On the image of the frozen sector this
undoes `lowWheelFrozenCofactorTopToggle` exactly. -/
def lowWheelFrozenCofactorTopUntoggle
    (z : LowWheelTaggedDowncrossState) : LowWheelTaggedDowncrossState :=
  (z.1,
    (z.2.1 * (z.2.2 / lowWheelCanonicalCofactorQuotientPivot z.2),
      lowWheelCanonicalCofactorQuotientPivot z.2))

/-- On the frozen nontrivial-cofactor sector the top/bottom move has the
explicit removal shape `(c,p) ↦ (c/q, q*p)`. -/
theorem lowWheelFrozenCofactorTopToggle_eq
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenCofactorTopToggle y =
      (y.1,
        (y.2.1 / lowWheelFrozenCofactorTopPrime y,
          lowWheelFrozenCofactorTopPrime y * y.2.2)) := by
  rcases lowWheelFrozenCofactorTopPrime_data hy with ⟨_hqPrime, hqDvd, _hpq⟩
  unfold lowWheelFrozenCofactorTopToggle lowWheelCofactorQuotientToggleAt
  simp only [hqDvd, if_true]

/-- The frozen shape puts the quotient exactly at the canonical pivot. -/
theorem lowWheelFrozenCofactor_quotient_eq_pivot
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2.2 = lowWheelTaggedDowncrossPivot y := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  exact (Finset.mem_filter.mp hfrozen).2.1

/-- The canonical pivot of a frozen state is prime. -/
theorem lowWheelFrozenCofactor_pivot_prime
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelTaggedDowncrossPivot y).Prime := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
  simpa [lowWheelTaggedDowncrossPivot] using hshell.1

/-- **Exact inversion.**  The explicit untoggle recovers the frozen state. -/
theorem lowWheelFrozenCofactorTopUntoggle_toggle
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenCofactorTopUntoggle (lowWheelFrozenCofactorTopToggle y) = y := by
  rcases lowWheelFrozenCofactorTopPrime_data hy with ⟨_hqPrime, hqDvd, _hpq⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime :=
    lowWheelFrozenCofactor_pivot_prime hy
  have hshape : y.2.2 = lowWheelTaggedDowncrossPivot y :=
    lowWheelFrozenCofactor_quotient_eq_pivot hy
  -- the pivot is invariant under the move
  have hpivot :
      lowWheelCanonicalCofactorQuotientPivot
          (lowWheelFrozenCofactorTopToggle y).2 =
        lowWheelTaggedDowncrossPivot y :=
    lowWheelFrozenCofactorTopToggle_pivot y
  -- reading the descending prime back off the quotient
  have hquot :
      lowWheelFrozenCofactorTopPrime y * y.2.2 /
          lowWheelTaggedDowncrossPivot y =
        lowWheelFrozenCofactorTopPrime y := by
    rw [hshape]
    simp [hp.ne_zero]
  -- and multiplying it back into the cofactor
  have hcofactor :
      y.2.1 / lowWheelFrozenCofactorTopPrime y *
          lowWheelFrozenCofactorTopPrime y = y.2.1 :=
    Nat.div_mul_cancel hqDvd
  unfold lowWheelFrozenCofactorTopUntoggle
  rw [hpivot, lowWheelFrozenCofactorTopToggle_eq hy]
  dsimp only
  rw [hquot, hcofactor, ← hshape]

/-- The top/bottom move is injective on the frozen nontrivial-cofactor sector. -/
theorem lowWheelFrozenCofactorTopToggle_injOn
    (R : ℕ) :
    Set.InjOn lowWheelFrozenCofactorTopToggle
      (lowWheelCanonicalRepeatedFrozenCofactorPart R :
        Set LowWheelTaggedDowncrossState) := by
  intro a ha b hb hab
  have ha' :=
    lowWheelFrozenCofactorTopUntoggle_toggle (Finset.mem_coe.mp ha)
  have hb' :=
    lowWheelFrozenCofactorTopUntoggle_toggle (Finset.mem_coe.mp hb)
  rw [← ha', ← hb', hab]

/-! ## The post-root image and its exact signed mass -/

/-- Explicit post-root image of the frozen nontrivial-cofactor sector. -/
def lowWheelFrozenCofactorTopImage
    (R : ℕ) : Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenCofactorPart R).image
    lowWheelFrozenCofactorTopToggle

@[simp] theorem mem_lowWheelFrozenCofactorTopImage
    {R : ℕ} {z : LowWheelTaggedDowncrossState} :
    z ∈ lowWheelFrozenCofactorTopImage R ↔
      ∃ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
        lowWheelFrozenCofactorTopToggle y = z := by
  simp [lowWheelFrozenCofactorTopImage]

/-- Signed ledger of the frozen nontrivial-cofactor sector. -/
def lowWheelCanonicalFrozenCofactorLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
    lowWheelTaggedDowncrossWeight y

/-- Signed ledger of the literal terminal `c = 1` first-crossing boundary. -/
def lowWheelCanonicalTerminalBoundaryLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedTerminalBoundary R,
    lowWheelTaggedDowncrossWeight y

/-- Signed ledger of the post-root image. -/
def lowWheelFrozenCofactorTopImageLedger (R : ℕ) : ℂ :=
  ∑ z ∈ lowWheelFrozenCofactorTopImage R,
    lowWheelTaggedDowncrossWeight z

/-- **Exact top/bottom cancellation.**  The frozen nontrivial-cofactor ledger is
literally minus the signed mass of its post-root image.  No estimate is
taken. -/
theorem lowWheelFrozenCofactorTopImageLedger_eq_neg
    (R : ℕ) :
    lowWheelFrozenCofactorTopImageLedger R =
      -lowWheelCanonicalFrozenCofactorLedger R := by
  unfold lowWheelFrozenCofactorTopImageLedger lowWheelFrozenCofactorTopImage
    lowWheelCanonicalFrozenCofactorLedger
  rw [Finset.sum_image (lowWheelFrozenCofactorTopToggle_injOn R)]
  calc
    ∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
        lowWheelTaggedDowncrossWeight (lowWheelFrozenCofactorTopToggle y) =
        ∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
          -lowWheelTaggedDowncrossWeight y :=
      Finset.sum_congr rfl fun y hy =>
        lowWheelFrozenCofactorTopToggle_weight_neg hy
    _ = -∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
          lowWheelTaggedDowncrossWeight y := by
      simp

/-! ## The image genuinely leaves the downcross region -/

/-- Every image state has normalized root-side parent strictly above `R`. -/
theorem lowWheelFrozenCofactorTopImage_parent_gt_root
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    R < primeFaceProduct z.1 *
      (z.2.2 / lowWheelCanonicalCofactorQuotientPivot z.2) := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  exact lowWheelFrozenCofactorTopToggle_parent_gt_root hy

/-- Every image state still lies on the physical transport carrier of its own
Boolean face.  The relocation does not leave the carrier. -/
theorem lowWheelFrozenCofactorTopImage_mem_physical
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    z.2 ∈ lowWheelCanonicalPhysicalStateSet R z.1 := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  exact lowWheelFrozenCofactorTopToggle_mem_physical hy

/-- **The relocation is real.**  The post-root image is disjoint from the entire
canonical downcross carrier, because downcross states have parent at most `R`
and image states have parent strictly above `R`. -/
theorem lowWheelFrozenCofactorTopImage_disjoint_downcrossCarrier
    (R : ℕ) :
    Disjoint (lowWheelFrozenCofactorTopImage R)
      (lowWheelCanonicalTaggedDowncrossCarrier R) := by
  rw [Finset.disjoint_left]
  intro z hzImage hzCarrier
  have hgt := lowWheelFrozenCofactorTopImage_parent_gt_root hzImage
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hzCarrier with ⟨_ht, hx⟩
  have hle := (mem_lowWheelCanonicalDowncrossPart.mp hx).2.2
  omega

/-! ## The repeated sector after exact movable cancellation -/

/-- Canonical and lightweight movable repeated populations are the same finite
set. -/
theorem lowWheelCanonicalRepeatedMovablePart_eq_othello
    (R : ℕ) :
    lowWheelCanonicalRepeatedMovablePart R =
      lowWheelOthelloRepeatedMovablePart R := rfl

/-- Exact zero sum of the canonical movable repeated population, transported
from the compiled lightweight involution. -/
theorem sum_lowWheelCanonicalRepeatedMovablePart_eq_zero
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedMovablePart R,
        lowWheelTaggedDowncrossWeight y) = 0 := by
  rw [lowWheelCanonicalRepeatedMovablePart_eq_othello]
  simpa [lowWheelTaggedDowncrossWeight, lowWheelOthelloWeight] using
    LateParentCancellation.sum_lowWheelOthelloRepeatedMovablePart_eq_zero R

/-- Movable and frozen canonical repeated populations are disjoint. -/
theorem lowWheelCanonicalRepeatedMovable_disjoint_frozen
    (R : ℕ) :
    Disjoint (lowWheelCanonicalRepeatedMovablePart R)
      (lowWheelCanonicalRepeatedFrozenPart R) := by
  rw [Finset.disjoint_left]
  intro y hmov hfrozen
  have hmovData := (Finset.mem_filter.mp hmov).2
  have hfrozenData := (Finset.mem_filter.mp hfrozen).2
  rcases hmovData with ⟨q, hqPrime, hpq, hactive⟩
  rcases hactive with hface | htail
  · have hqlt := hfrozenData.2 q hface
    omega
  · have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
      have hrepeated := (Finset.mem_filter.mp hfrozen).1
      have hcarrier := (Finset.mem_filter.mp hrepeated).1
      rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
      simpa [lowWheelTaggedDowncrossPivot] using
        (lowWheelCanonicalDowncrossPart_adjacent_shell hx).1
    have hone : y.2.2 / lowWheelTaggedDowncrossPivot y = 1 := by
      rw [hfrozenData.1]
      exact Nat.div_self hp.pos
    rw [hone] at htail
    exact hqPrime.not_dvd_one htail

/-- Nontrivial-cofactor and terminal frozen populations are disjoint. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_disjoint_terminal
    (R : ℕ) :
    Disjoint (lowWheelCanonicalRepeatedFrozenCofactorPart R)
      (lowWheelCanonicalRepeatedTerminalBoundary R) := by
  rw [Finset.disjoint_left]
  intro y hcof hterm
  have hgt := (Finset.mem_filter.mp hcof).2
  have heq := (Finset.mem_filter.mp hterm).2
  omega

/-- **The repeated-parent ledger after exact movable cancellation.**  Only the
frozen nontrivial-cofactor sector and the terminal `c = 1` boundary survive. -/
theorem lowWheelCanonicalDowncrossRepeatedParentLedger_eq_frozen_split
    (R : ℕ) :
    lowWheelCanonicalDowncrossRepeatedParentLedger R =
      lowWheelCanonicalFrozenCofactorLedger R +
        lowWheelCanonicalTerminalBoundaryLedger R := by
  unfold lowWheelCanonicalDowncrossRepeatedParentLedger
    lowWheelCanonicalFrozenCofactorLedger
    lowWheelCanonicalTerminalBoundaryLedger
  rw [lowWheelCanonicalRepeatedParent_eq_movable_union_frozen R,
    Finset.sum_union (lowWheelCanonicalRepeatedMovable_disjoint_frozen R),
    sum_lowWheelCanonicalRepeatedMovablePart_eq_zero R,
    lowWheelCanonicalRepeatedFrozen_eq_cofactor_union_terminal R,
    Finset.sum_union
      (lowWheelCanonicalRepeatedFrozenCofactor_disjoint_terminal R)]
  ring

/-! ## The sharpened endpoint identity -/

/-- **Main identity.**  The complete canonical downcross ledger is the
unique-parent ledger plus the terminal `c = 1` boundary minus the post-root
image ledger.  Every step is an exact finite identity: the repeated *movable*
sector cancels to zero by the compiled Othello involution, and the frozen
nontrivial-cofactor sector is transported off the downcross region by the exact
sign-reversing top/bottom move. -/
theorem lowWheelCanonicalDowncrossLedger_eq_unique_add_terminal_sub_topImage
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      lowWheelCanonicalDowncrossUniqueParentLedger R +
        lowWheelCanonicalTerminalBoundaryLedger R -
          lowWheelFrozenCofactorTopImageLedger R := by
  rw [lowWheelCanonicalDowncrossLedger_eq_tagged,
    lowWheelCanonicalTaggedDowncrossLedger_eq_unique_add_repeated,
    lowWheelCanonicalDowncrossRepeatedParentLedger_eq_frozen_split,
    lowWheelFrozenCofactorTopImageLedger_eq_neg]
  ring

/-- The same identity read as an exact three-term decomposition of the oriented
first-crossing ledger, which is the current terminal object. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_unique_add_terminal_sub_topImage
    (R : ℕ) :
    LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger R =
      lowWheelCanonicalDowncrossUniqueParentLedger R +
        lowWheelCanonicalTerminalBoundaryLedger R -
          lowWheelFrozenCofactorTopImageLedger R := by
  rw [← LateParentCancellation.downcrossLedger_eq_orientedLedger]
  exact lowWheelCanonicalDowncrossLedger_eq_unique_add_terminal_sub_topImage R

/-! ## The restated quantitative seam -/

/-- Remaining quantitative core after the exact top/bottom relocation.  Compared
with `SquareRootCanonicalOrientedLinearBound` the frozen nontrivial-cofactor
sector no longer appears on the downcross side at all: it has been replaced by
its post-root image, which lies strictly above the root wall. -/
def SquareRootFrozenTopBottomLinearBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖lowWheelCanonicalDowncrossUniqueParentLedger R +
          lowWheelCanonicalTerminalBoundaryLedger R -
            lowWheelFrozenCofactorTopImageLedger R‖ ≤ C * (R : ℝ)

/-- The relocated bound is exactly strong enough to discharge the primitive
downcross seam. -/
theorem canonicalDowncrossLinear_of_frozenTopBottomLinear
    (h : SquareRootFrozenTopBottomLinearBound) :
    SquareRootCanonicalDowncrossLinearBound := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro R hR
  rw [lowWheelCanonicalDowncrossLedger_eq_unique_add_terminal_sub_topImage]
  exact hbound R hR

/-- Consequently the relocated seam still implies the Riemann hypothesis through
the already-compiled square-prefix energy bridge. -/
theorem riemannHypothesis_of_frozenTopBottomLinear
    (h : SquareRootFrozenTopBottomLinearBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalDowncrossLinear
    (canonicalDowncrossLinear_of_frozenTopBottomLinear h)

end FrozenCofactorTopBottom

end RHLean.Proof
