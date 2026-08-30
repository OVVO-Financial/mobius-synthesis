import Mathlib
import RHLean.Proof.LowWheelCanonicalDefectReduction

/-!
# Parent fibers of the canonical root-downcross frontier

The surviving square-endpoint defect is already an explicit adjacent
first-failure ledger.  For a tagged downcross occurrence `(t,(c,k))`, let `p`
be the canonical least-prime pivot of `(c,k)`.  The adjacent-shell theorem gives

`P(t) * (k / p) <= R < P(t) * (p * (k / p))`.

Thus every defect state has a concrete parent coordinate

`n = P(t) * (k / p)`

inside the root interval.  This file makes that ownership map literal and
splits the complete downcross carrier into two disjoint pieces:

* unique-parent states, on which the parent map is injective and hence the
  carrier has at most `R` elements;
* repeated-parent states, which are the exact remaining multiplicity
  obstruction and must be discharged by an already-present transport mate.

No absolute value, prime-count estimate, asymptotic input, or further Euler
descent is used here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A downcross occurrence tagged by the Boolean face on which it appears. -/
abbrev LowWheelTaggedDowncrossState :=
  Finset ℕ × LowWheelCofactorQuotientState

/-- The exact support of the nested canonical downcross ledger, with face tags
retained so multiplicity is not collapsed. -/
def lowWheelCanonicalTaggedDowncrossCarrier
    (R : ℕ) : Finset LowWheelTaggedDowncrossState := by
  classical
  exact (primesUpTo R).powerset.biUnion fun t =>
    (lowWheelCanonicalDowncrossPart R t).image fun x => (t, x)

@[simp] theorem mem_lowWheelCanonicalTaggedDowncrossCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState} :
    y ∈ lowWheelCanonicalTaggedDowncrossCarrier R ↔
      y.1 ∈ (primesUpTo R).powerset ∧
        y.2 ∈ lowWheelCanonicalDowncrossPart R y.1 := by
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

/-- The literal root-side parent of one tagged downcross occurrence. -/
def lowWheelCanonicalDowncrossParent
    (y : LowWheelTaggedDowncrossState) : ℕ :=
  primeFaceProduct y.1 *
    (y.2.2 / lowWheelCanonicalCofactorQuotientPivot y.2)

/-- Every tagged downcross parent lies at or below the root. -/
theorem lowWheelCanonicalDowncrossParent_le_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R) :
    lowWheelCanonicalDowncrossParent y ≤ R := by
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨_ht, hx⟩
  exact (mem_lowWheelCanonicalDowncrossPart.mp hx).2.2

/-- Every tagged downcross parent is positive. -/
theorem lowWheelCanonicalDowncrossParent_pos
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R) :
    0 < lowWheelCanonicalDowncrossParent y := by
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨ht, hx⟩
  rcases y with ⟨t, ⟨c, k⟩⟩
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
  rcases hshell with ⟨hp, _hpc, hpk, _hdown, _hup⟩
  have hP : 0 < primeFaceProduct t := primeFaceProduct_pos_of_mem_powerset ht
  have hkpos : 0 < k := by
    have hkge : 1 ≤ k := by
      have hxF := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
      exact (Finset.mem_Icc.mp
        (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.1).1
    omega
  have hpLeK : lowWheelCanonicalCofactorQuotientPivot (c, k) ≤ k :=
    Nat.le_of_dvd hkpos hpk
  have hdivpos : 0 < k / lowWheelCanonicalCofactorQuotientPivot (c, k) :=
    Nat.div_pos hpLeK hp.pos
  unfold lowWheelCanonicalDowncrossParent
  exact Nat.mul_pos hP hdivpos

/-- The portion of the downcross frontier whose root-side parent occurs only
once in the complete tagged carrier. -/
def lowWheelCanonicalDowncrossUniqueParentPart
    (R : ℕ) : Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalTaggedDowncrossCarrier R).filter fun y =>
    ∀ z ∈ lowWheelCanonicalTaggedDowncrossCarrier R,
      lowWheelCanonicalDowncrossParent z = lowWheelCanonicalDowncrossParent y →
        z = y

/-- The exact complementary obstruction: states lying in a repeated parent
fiber. -/
def lowWheelCanonicalDowncrossRepeatedParentPart
    (R : ℕ) : Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalTaggedDowncrossCarrier R).filter fun y =>
    ¬ ∀ z ∈ lowWheelCanonicalTaggedDowncrossCarrier R,
      lowWheelCanonicalDowncrossParent z = lowWheelCanonicalDowncrossParent y →
        z = y

/-- Unique-parent and repeated-parent populations partition the complete
canonical downcross carrier. -/
theorem lowWheelCanonicalTaggedDowncrossCarrier_eq_unique_union_repeated
    (R : ℕ) :
    lowWheelCanonicalTaggedDowncrossCarrier R =
      lowWheelCanonicalDowncrossUniqueParentPart R ∪
        lowWheelCanonicalDowncrossRepeatedParentPart R := by
  ext y
  constructor
  · intro hy
    by_cases hunique :
        ∀ z ∈ lowWheelCanonicalTaggedDowncrossCarrier R,
          lowWheelCanonicalDowncrossParent z = lowWheelCanonicalDowncrossParent y →
            z = y
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hy, hunique⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, hunique⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · exact (Finset.mem_filter.mp hy).1

/-- The two parent-fiber populations are disjoint. -/
theorem lowWheelCanonicalDowncrossUnique_disjoint_repeated
    (R : ℕ) :
    Disjoint
      (lowWheelCanonicalDowncrossUniqueParentPart R)
      (lowWheelCanonicalDowncrossRepeatedParentPart R) := by
  rw [Finset.disjoint_left]
  intro y hyU hyC
  have hU := (Finset.mem_filter.mp hyU).2
  have hC := (Finset.mem_filter.mp hyC).2
  exact hC hU

/-- On the unique-parent population, the explicit parent coordinate loses no
multiplicity. -/
theorem lowWheelCanonicalDowncrossParent_injOn_unique
    (R : ℕ) :
    Set.InjOn lowWheelCanonicalDowncrossParent
      (lowWheelCanonicalDowncrossUniqueParentPart R) := by
  intro a ha b hb hab
  have haData := Finset.mem_filter.mp ha
  have hbData := Finset.mem_filter.mp hb
  exact (haData.2 b hbData.1 hab.symm).symm

/-- The unique-parent population has at most `R` states: its parent map lands
injectively in the positive root interval `1..R`. -/
theorem lowWheelCanonicalDowncrossUniqueParentPart_card_le_root
    (R : ℕ) :
    (lowWheelCanonicalDowncrossUniqueParentPart R).card ≤ R := by
  let parent := lowWheelCanonicalDowncrossParent
  have hinj : Set.InjOn parent
      (lowWheelCanonicalDowncrossUniqueParentPart R) := by
    simpa [parent] using lowWheelCanonicalDowncrossParent_injOn_unique R
  have himage :
      (lowWheelCanonicalDowncrossUniqueParentPart R).image parent ⊆
        Finset.Icc 1 R := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨y, hy, rfl⟩
    have hyCarrier := (Finset.mem_filter.mp hy).1
    exact Finset.mem_Icc.mpr
      ⟨lowWheelCanonicalDowncrossParent_pos hyCarrier,
        lowWheelCanonicalDowncrossParent_le_root hyCarrier⟩
  have hcard :
      ((lowWheelCanonicalDowncrossUniqueParentPart R).image parent).card =
        (lowWheelCanonicalDowncrossUniqueParentPart R).card :=
    Finset.card_image_iff.mpr hinj
  rw [← hcard]
  have hle := Finset.card_le_card himage
  simpa [Nat.card_Icc] using hle

end RHLean.Proof
