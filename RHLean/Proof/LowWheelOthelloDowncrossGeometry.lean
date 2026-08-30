import Mathlib
import RHLean.Proof.LowWheelCanonicalPairingFrontier

/-!
# Lightweight canonical downcross geometry for Othello

This module extracts only the elementary square-root downcross geometry needed
for the two-direction Othello argument.  It deliberately avoids the later
analytic endpoint modules.

The carrier is definitionally the same one-sided least-prime root downcross
used by `LowWheelCanonicalDefectReduction`:

* `(c,k)` is an existing physical transport state;
* `p = minFac(c*k)` is absent from the cofactor;
* removing `p` from the quotient crosses the high coordinate down through `R`.

Every state therefore lies in the adjacent shell

`P(t)*(k/p) <= R < P(t)*p*(k/p)`.

The tagged carrier is split by the literal parent `P(t)*(k/p)` into unique and
repeated fibres.  The unique part already has cardinality at most `R`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Lightweight one-sided canonical downcross carrier. -/
def lowWheelOthelloDowncrossPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalPhysicalStateSet R t).filter fun x =>
    ¬ lowWheelCanonicalCofactorQuotientPivot x ∣ x.1 ∧
      primeFaceProduct t *
          (x.2 / lowWheelCanonicalCofactorQuotientPivot x) ≤ R

@[simp] theorem mem_lowWheelOthelloDowncrossPart
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelOthelloDowncrossPart R t ↔
      x ∈ lowWheelCanonicalPhysicalStateSet R t ∧
      ¬ lowWheelCanonicalCofactorQuotientPivot x ∣ x.1 ∧
      primeFaceProduct t *
          (x.2 / lowWheelCanonicalCofactorQuotientPivot x) ≤ R := by
  simp [lowWheelOthelloDowncrossPart]

/-- Every lightweight downcross state is an adjacent multiplicative
least-prime shell. -/
theorem lowWheelOthelloDowncrossPart_adjacent_shell
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelOthelloDowncrossPart R t) :
    (lowWheelCanonicalCofactorQuotientPivot (c, k)).Prime ∧
      ¬ lowWheelCanonicalCofactorQuotientPivot (c, k) ∣ c ∧
      lowWheelCanonicalCofactorQuotientPivot (c, k) ∣ k ∧
      primeFaceProduct t *
          (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) ≤ R ∧
      R < primeFaceProduct t *
          (lowWheelCanonicalCofactorQuotientPivot (c, k) *
            (k / lowWheelCanonicalCofactorQuotientPivot (c, k))) := by
  rcases mem_lowWheelOthelloDowncrossPart.mp hx with
    ⟨hxF, hpc, hdown⟩
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  have hprod : c * k ≠ 1 := by
    intro hone
    apply hpc
    unfold lowWheelCanonicalCofactorQuotientPivot
    rw [hone]
    simp
  have hp := lowWheelCanonicalCofactorQuotientPivot_prime hprod
  have hactive := lowWheelCanonicalCofactorQuotientPivot_active hprod
  have hpk := hactive.resolve_left hpc
  refine ⟨hp, hpc, hpk, hdown, ?_⟩
  have hkCancel :
      lowWheelCanonicalCofactorQuotientPivot (c, k) *
          (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) = k :=
    Nat.mul_div_cancel' hpk
  rw [hkCancel]
  exact hcarrier.2.2.1

/-- Tagged occurrence retains the Boolean face, so multiplicity is literal. -/
abbrev LowWheelOthelloTaggedDowncrossState :=
  Finset ℕ × LowWheelCofactorQuotientState

/-- Exact tagged support of the lightweight downcross ledger. -/
def lowWheelOthelloTaggedDowncrossCarrier
    (R : ℕ) : Finset LowWheelOthelloTaggedDowncrossState := by
  classical
  exact (primesUpTo R).powerset.biUnion fun t =>
    (lowWheelOthelloDowncrossPart R t).image fun x => (t, x)

@[simp] theorem mem_lowWheelOthelloTaggedDowncrossCarrier
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState} :
    y ∈ lowWheelOthelloTaggedDowncrossCarrier R ↔
      y.1 ∈ (primesUpTo R).powerset ∧
        y.2 ∈ lowWheelOthelloDowncrossPart R y.1 := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_biUnion.mp hy with ⟨t, ht, hy⟩
    rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
    subst y
    exact ⟨ht, hx⟩
  · intro hy
    rcases hy with ⟨ht, hx⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨y.1, ht, ?_⟩
    exact Finset.mem_image.mpr ⟨y.2, hx, Prod.ext rfl rfl⟩

/-- Canonical least-prime pivot of one tagged downcross state. -/
def lowWheelOthelloDowncrossPivot
    (y : LowWheelOthelloTaggedDowncrossState) : ℕ :=
  lowWheelCanonicalCofactorQuotientPivot y.2

/-- Root-side parent of a tagged downcross occurrence. -/
def lowWheelOthelloDowncrossParent
    (y : LowWheelOthelloTaggedDowncrossState) : ℕ :=
  primeFaceProduct y.1 *
    (y.2.2 / lowWheelOthelloDowncrossPivot y)

/-- Every tagged downcross parent lies at or below the root. -/
theorem lowWheelOthelloDowncrossParent_le_root
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R) :
    lowWheelOthelloDowncrossParent y ≤ R := by
  rcases mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy with ⟨_ht, hx⟩
  exact (mem_lowWheelOthelloDowncrossPart.mp hx).2.2

/-- Every tagged downcross parent is positive. -/
theorem lowWheelOthelloDowncrossParent_pos
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R) :
    0 < lowWheelOthelloDowncrossParent y := by
  rcases mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy with ⟨ht, hx⟩
  rcases y with ⟨t, ⟨c, k⟩⟩
  have hshell := lowWheelOthelloDowncrossPart_adjacent_shell hx
  rcases hshell with ⟨hp, _hpc, hpk, _hdown, _hup⟩
  have hP : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hkpos : 0 < k := by
    have hxF := (mem_lowWheelOthelloDowncrossPart.mp hx).1
    have hkge : 1 ≤ k := (Finset.mem_Icc.mp
      (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.1).1
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one hkge
  have hpLeK : lowWheelCanonicalCofactorQuotientPivot (c, k) ≤ k :=
    Nat.le_of_dvd hkpos hpk
  have hdivpos : 0 < k / lowWheelCanonicalCofactorQuotientPivot (c, k) :=
    Nat.div_pos hpLeK hp.pos
  exact Nat.mul_pos hP hdivpos

/-- Unique-parent portion of the tagged downcross carrier. -/
def lowWheelOthelloDowncrossUniqueParentPart
    (R : ℕ) : Finset LowWheelOthelloTaggedDowncrossState :=
  (lowWheelOthelloTaggedDowncrossCarrier R).filter fun y =>
    ∀ z ∈ lowWheelOthelloTaggedDowncrossCarrier R,
      lowWheelOthelloDowncrossParent z = lowWheelOthelloDowncrossParent y →
        z = y

/-- Repeated-parent portion: the exact multiplicity obstruction. -/
def lowWheelOthelloDowncrossRepeatedParentPart
    (R : ℕ) : Finset LowWheelOthelloTaggedDowncrossState :=
  (lowWheelOthelloTaggedDowncrossCarrier R).filter fun y =>
    ¬ ∀ z ∈ lowWheelOthelloTaggedDowncrossCarrier R,
      lowWheelOthelloDowncrossParent z = lowWheelOthelloDowncrossParent y →
        z = y

/-- Unique and repeated parent fibres partition the tagged carrier. -/
theorem lowWheelOthelloTaggedDowncrossCarrier_eq_unique_union_repeated
    (R : ℕ) :
    lowWheelOthelloTaggedDowncrossCarrier R =
      lowWheelOthelloDowncrossUniqueParentPart R ∪
        lowWheelOthelloDowncrossRepeatedParentPart R := by
  ext y
  constructor
  · intro hy
    by_cases hunique :
        ∀ z ∈ lowWheelOthelloTaggedDowncrossCarrier R,
          lowWheelOthelloDowncrossParent z = lowWheelOthelloDowncrossParent y →
            z = y
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hy, hunique⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, hunique⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · exact (Finset.mem_filter.mp hy).1

/-- The two parent populations are disjoint. -/
theorem lowWheelOthelloDowncrossUnique_disjoint_repeated
    (R : ℕ) :
    Disjoint
      (lowWheelOthelloDowncrossUniqueParentPart R)
      (lowWheelOthelloDowncrossRepeatedParentPart R) := by
  rw [Finset.disjoint_left]
  intro y hyU hyR
  exact (Finset.mem_filter.mp hyR).2 (Finset.mem_filter.mp hyU).2

/-- Parent charge is injective on the unique population. -/
theorem lowWheelOthelloDowncrossParent_injOn_unique
    (R : ℕ) :
    Set.InjOn lowWheelOthelloDowncrossParent
      (lowWheelOthelloDowncrossUniqueParentPart R) := by
  intro a ha b hb hab
  have haData := Finset.mem_filter.mp ha
  have hbData := Finset.mem_filter.mp hb
  exact (haData.2 b hbData.1 hab.symm).symm

/-- The unique-parent population costs at most one state per positive root. -/
theorem lowWheelOthelloDowncrossUniqueParentPart_card_le_root
    (R : ℕ) :
    (lowWheelOthelloDowncrossUniqueParentPart R).card ≤ R := by
  let parent := lowWheelOthelloDowncrossParent
  have hinj : Set.InjOn parent
      (lowWheelOthelloDowncrossUniqueParentPart R) := by
    simpa [parent] using lowWheelOthelloDowncrossParent_injOn_unique R
  have himage :
      (lowWheelOthelloDowncrossUniqueParentPart R).image parent ⊆
        Finset.Icc 1 R := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨y, hy, rfl⟩
    have hyCarrier := (Finset.mem_filter.mp hy).1
    exact Finset.mem_Icc.mpr
      ⟨lowWheelOthelloDowncrossParent_pos hyCarrier,
        lowWheelOthelloDowncrossParent_le_root hyCarrier⟩
  have hcard :
      ((lowWheelOthelloDowncrossUniqueParentPart R).image parent).card =
        (lowWheelOthelloDowncrossUniqueParentPart R).card :=
    Finset.card_image_iff.mpr hinj
  rw [← hcard]
  have hle := Finset.card_le_card himage
  simpa [Nat.card_Icc] using hle

end RHLean.Proof
