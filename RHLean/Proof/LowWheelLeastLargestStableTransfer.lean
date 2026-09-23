import Mathlib
import RHLean.Proof.LowWheelLeastLargestOthello
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Proof.LowWheelFrozenCofactorTopBottomToggle
import RHLean.Proof.CanonicalGapAncestryBridge

/-!
# Stable-mass transfer from the least-prime downcross to the largest-prime top defect

On one physical Boolean face, the completed least- and largest-prime Othello
mates have the same signed stable mass.  Their stable sets share the same
product-one fixed population.  After removing that common population, the
least stable defect is exactly the already-proved canonical root-downcross,
while the largest stable defect is the failure of the largest-prime insertion
move.

Thus the bottom canonical downcross mass is *exactly equal* to a top-oriented
largest-prime defect mass.  No absolute value or estimate enters this change of
coordinates.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Product-one fixed states in one physical face. -/
def lowWheelPhysicalProductOnePart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalPhysicalStateSet R t).filter fun x => x.1 * x.2 = 1

/-- Largest-prime boundary defect in one physical face. -/
def lowWheelLargestDefectPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalPhysicalStateSet R t).filter fun x =>
    x.1 * x.2 ≠ 1 ∧
      lowWheelLargestCofactorQuotientToggle x ∉
        lowWheelCanonicalPhysicalStateSet R t

/-- Product-one and largest-defect populations are disjoint. -/
theorem lowWheelPhysicalProductOne_disjoint_largestDefect
    (R : ℕ) (t : Finset ℕ) :
    Disjoint
      (lowWheelPhysicalProductOnePart R t)
      (lowWheelLargestDefectPart R t) := by
  rw [Finset.disjoint_left]
  intro x h1 hd
  exact (Finset.mem_filter.mp hd).2.1 (Finset.mem_filter.mp h1).2

private theorem lowWheelLargestRawToggle_ne
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : x.1 * x.2 ≠ 1) :
    lowWheelLargestCofactorQuotientToggle x ≠ x := by
  have hp := lowWheelLargestCofactorQuotientPivot_prime ht hx hne
  have hactive := lowWheelLargestCofactorQuotientPivot_active ht hx hne
  have hxData := mem_lowWheelCanonicalPhysicalStateSet.mp hx
  have hcPos : 0 < x.1 := by
    have hc1 := (Finset.mem_Ico.mp hxData.1).1
    omega
  unfold lowWheelLargestCofactorQuotientToggle
  unfold lowWheelCofactorQuotientToggleAt
  by_cases hpc : lowWheelLargestCofactorQuotientPivot x ∣ x.1
  · simp only [hpc, if_true]
    intro heq
    have hfirst : x.1 / lowWheelLargestCofactorQuotientPivot x = x.1 :=
      congrArg Prod.fst heq
    have hlt :
        x.1 / lowWheelLargestCofactorQuotientPivot x < x.1 :=
      Nat.div_lt_self hcPos hp.one_lt
    omega
  · have hpk := hactive.resolve_left hpc
    simp only [hpc, if_false, hpk, if_true]
    intro heq
    have hfirst : x.1 * lowWheelLargestCofactorQuotientPivot x = x.1 :=
      congrArg Prod.fst heq
    have hlt :
        x.1 < x.1 * lowWheelLargestCofactorQuotientPivot x := by
      calc
        x.1 = x.1 * 1 := by simp
        _ < x.1 * lowWheelLargestCofactorQuotientPivot x :=
          Nat.mul_lt_mul_of_pos_left hp.one_lt hcPos
    omega

/-- Stable states of the completed least-prime mate are exactly product-one
fixed states plus the canonical defect. -/
theorem finiteOthelloStablePart_least_eq_productOne_union_defect
    {R : ℕ} {t : Finset ℕ} :
    finiteOthelloStablePart
        (lowWheelCanonicalPhysicalStateSet R t)
        (lowWheelLeastOthelloMate R t) =
      lowWheelPhysicalProductOnePart R t ∪
        lowWheelCanonicalDefectPart (lowWheelCanonicalPhysicalStateSet R t) := by
  ext x
  constructor
  · intro hxStable
    rcases Finset.mem_filter.mp hxStable with ⟨hx, hfix⟩
    by_cases hprod : x.1 * x.2 = 1
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hx, hprod⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hx, ?_⟩
      intro hmate
      unfold lowWheelLeastOthelloMate at hfix
      simp only [hprod, hmate, if_true] at hfix
      have hxData := mem_lowWheelCanonicalPhysicalStateSet.mp hx
      have hcPos : 0 < x.1 := by
        have hc1 := (Finset.mem_Ico.mp hxData.1).1
        omega
      have hiff := lowWheelCanonicalToggle_eq_self_iff_product_eq_one
        (c := x.1) (k := x.2) hcPos
      exact hprod (hiff.mp hfix)
  · intro hxUnion
    rcases Finset.mem_union.mp hxUnion with h1 | hd
    · rcases Finset.mem_filter.mp h1 with ⟨hx, hprod⟩
      apply Finset.mem_filter.mpr
      refine ⟨hx, ?_⟩
      simp [lowWheelLeastOthelloMate, hprod]
    · rcases Finset.mem_filter.mp hd with ⟨hx, hnot⟩
      apply Finset.mem_filter.mpr
      refine ⟨hx, ?_⟩
      have hprod : x.1 * x.2 ≠ 1 := by
        intro hprod
        have htoggle := lowWheelCanonicalToggle_eq_self_of_product_eq_one hprod
        apply hnot
        rw [htoggle]
        exact hx
      simp [lowWheelLeastOthelloMate, hprod, hnot]

/-- Stable states of the completed largest-prime mate are exactly product-one
states plus the largest-prime top defect. -/
theorem finiteOthelloStablePart_largest_eq_productOne_union_defect
    {R : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    finiteOthelloStablePart
        (lowWheelCanonicalPhysicalStateSet R t)
        (lowWheelLargestOthelloMate R t) =
      lowWheelPhysicalProductOnePart R t ∪ lowWheelLargestDefectPart R t := by
  ext x
  constructor
  · intro hxStable
    rcases Finset.mem_filter.mp hxStable with ⟨hx, hfix⟩
    by_cases hprod : x.1 * x.2 = 1
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hx, hprod⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hx, hprod, ?_⟩
      intro hmate
      unfold lowWheelLargestOthelloMate at hfix
      simp only [hprod, hmate, if_true] at hfix
      exact (lowWheelLargestRawToggle_ne ht hx hprod) hfix
  · intro hxUnion
    rcases Finset.mem_union.mp hxUnion with h1 | hd
    · rcases Finset.mem_filter.mp h1 with ⟨hx, hprod⟩
      apply Finset.mem_filter.mpr
      exact ⟨hx, by simp [lowWheelLargestOthelloMate, hprod]⟩
    · rcases Finset.mem_filter.mp hd with ⟨hx, hprod, hnot⟩
      apply Finset.mem_filter.mpr
      exact ⟨hx, by simp [lowWheelLargestOthelloMate, hprod, hnot]⟩

/-- Product-one fixed part and canonical least defect are disjoint. -/
theorem lowWheelPhysicalProductOne_disjoint_canonicalDefect
    (R : ℕ) (t : Finset ℕ) :
    Disjoint
      (lowWheelPhysicalProductOnePart R t)
      (lowWheelCanonicalDefectPart (lowWheelCanonicalPhysicalStateSet R t)) := by
  rw [Finset.disjoint_left]
  intro x h1 hd
  have hprod := (Finset.mem_filter.mp h1).2
  have hnot := (Finset.mem_filter.mp hd).2
  exact hnot (by
    rw [lowWheelCanonicalToggle_eq_self_of_product_eq_one hprod]
    exact (Finset.mem_filter.mp h1).1)

/-- **Per-face top/bottom stable transfer.**  The signed canonical least-prime
defect equals the signed largest-prime defect. -/
theorem sum_lowWheelCanonicalDefect_eq_largestDefect
    {R : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    (∑ x ∈ lowWheelCanonicalDefectPart
        (lowWheelCanonicalPhysicalStateSet R t),
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
    ∑ x ∈ lowWheelLargestDefectPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ) := by
  have hstable := sum_lowWheelLeastStable_eq_largestStable ht
  rw [finiteOthelloStablePart_least_eq_productOne_union_defect,
    finiteOthelloStablePart_largest_eq_productOne_union_defect ht] at hstable
  rw [Finset.sum_union
      (lowWheelPhysicalProductOne_disjoint_canonicalDefect R t),
    Finset.sum_union
      (lowWheelPhysicalProductOne_disjoint_largestDefect R t)] at hstable
  exact add_left_cancel hstable

/-- Global signed largest-prime defect ledger. -/
def lowWheelLargestDefectLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelLargestDefectPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- **Global top/bottom coordinate synthesis.**  The original canonical
root-downcross ledger is exactly the largest-prime top defect ledger. -/
theorem lowWheelCanonicalDowncrossLedger_eq_largestDefectLedger
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R = lowWheelLargestDefectLedger R := by
  rw [← lowWheelCanonicalDefectLedger_eq_downcrossLedger]
  unfold lowWheelCanonicalDefectLedger lowWheelLargestDefectLedger
  apply Finset.sum_congr rfl
  intro t ht
  exact sum_lowWheelCanonicalDefect_eq_largestDefect ht

/-! ## Frozen `c > 1` states are moving edges of the largest-prime matching

The frozen top/bottom toggle was originally introduced as a separate coordinate
move.  On a frozen state `y = (t,(c,p))` with `c > 1`, however, its prime
`q = P⁺(c)` is the largest prime factor of the invariant product `c*p`: the
frozen least pivot satisfies `p < q`.  Hence the top/bottom move is literally
the raw largest-prime Othello move already used above.

This is stronger than trying to place the composite quotient `q*p` inside an
external single-prime grid.  The two endpoints cancel as one moving edge on the
same complete physical carrier, so they never belong to the largest-prime
stable defect.
-/

/-- On a repeated frozen state with nontrivial cofactor, the largest-prime pivot
of the invariant cofactor/quotient product is exactly the frozen top prime. -/
theorem lowWheelLargestCofactorQuotientPivot_eq_frozenTopPrime
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelLargestCofactorQuotientPivot y.2 =
      lowWheelFrozenCofactorTopPrime y := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hcgt : 1 < y.2.1 := (Finset.mem_filter.mp hy).2
  have hshape := (Finset.mem_filter.mp hfrozen).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
  have hpPrime : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hshell.1
  rcases lowWheelFrozenCofactorTopPrime_data hy with
    ⟨hqPrime, hqDvd, hpq⟩
  have hprodgt :
      1 < y.2.1 * lowWheelTaggedDowncrossPivot y := by
    have hp2 := hpPrime.two_le
    nlinarith
  have hqDvdProd :
      lowWheelFrozenCofactorTopPrime y ∣
        y.2.1 * lowWheelTaggedDowncrossPivot y :=
    dvd_mul_of_dvd_left hqDvd _
  have htopPrime :
      (canonicalLargestPrimeFactor
        (y.2.1 * lowWheelTaggedDowncrossPivot y)).Prime :=
    canonicalLargestPrimeFactor_prime hprodgt
  have htopDvd :
      canonicalLargestPrimeFactor
          (y.2.1 * lowWheelTaggedDowncrossPivot y) ∣
        y.2.1 * lowWheelTaggedDowncrossPivot y :=
    canonicalLargestPrimeFactor_dvd hprodgt
  have htopLe :
      canonicalLargestPrimeFactor
          (y.2.1 * lowWheelTaggedDowncrossPivot y) ≤
        lowWheelFrozenCofactorTopPrime y := by
    rcases htopPrime.dvd_mul.mp htopDvd with hdivC | hdivP
    · simpa [lowWheelFrozenCofactorTopPrime] using
        (CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
          hcgt htopPrime hdivC)
    · have heq :
          canonicalLargestPrimeFactor
              (y.2.1 * lowWheelTaggedDowncrossPivot y) =
            lowWheelTaggedDowncrossPivot y :=
        (Nat.prime_dvd_prime_iff_eq htopPrime hpPrime).mp hdivP
      rw [heq]
      exact hpq.le
  have hqLe :
      lowWheelFrozenCofactorTopPrime y ≤
        canonicalLargestPrimeFactor
          (y.2.1 * lowWheelTaggedDowncrossPivot y) :=
    CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
      hprodgt hqPrime hqDvdProd
  have htopEq :
      canonicalLargestPrimeFactor
          (y.2.1 * lowWheelTaggedDowncrossPivot y) =
        lowWheelFrozenCofactorTopPrime y :=
    le_antisymm htopLe hqLe
  simpa [lowWheelLargestCofactorQuotientPivot, hshape.1] using htopEq

/-- The previously separate frozen top toggle is exactly the raw largest-prime
Othello toggle on every repeated frozen `c > 1` source. -/
theorem lowWheelLargestCofactorQuotientToggle_eq_frozenTopToggle
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelLargestCofactorQuotientToggle y.2 =
      (lowWheelFrozenCofactorTopToggle y).2 := by
  change lowWheelCofactorQuotientToggleAt
      (lowWheelLargestCofactorQuotientPivot y.2) y.2 =
    lowWheelCofactorQuotientToggleAt
      (lowWheelFrozenCofactorTopPrime y) y.2
  rw [lowWheelLargestCofactorQuotientPivot_eq_frozenTopPrime hy]

/-- The completed largest-prime Othello mate therefore sends the frozen source
exactly to its physical top image; it does not freeze at that source. -/
theorem lowWheelLargestOthelloMate_eq_frozenTopToggle
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelLargestOthelloMate R y.1 y.2 =
      (lowWheelFrozenCofactorTopToggle y).2 := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hcgt : 1 < y.2.1 := (Finset.mem_filter.mp hy).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hphysicalData := mem_lowWheelCanonicalPhysicalStateSet.mp hphysical
  have hkpos : 0 < y.2.2 := by
    have hk1 := (Finset.mem_Icc.mp hphysicalData.2.1).1
    omega
  have hprod : y.2.1 * y.2.2 ≠ 1 := by
    have hle : y.2.1 ≤ y.2.1 * y.2.2 :=
      Nat.le_mul_of_pos_right y.2.1 hkpos
    exact ne_of_gt (hcgt.trans_le hle)
  have hmate :
      lowWheelLargestCofactorQuotientToggle y.2 ∈
        lowWheelCanonicalPhysicalStateSet R y.1 := by
    rw [lowWheelLargestCofactorQuotientToggle_eq_frozenTopToggle hy]
    exact lowWheelFrozenCofactorTopToggle_mem_physical hy
  calc
    lowWheelLargestOthelloMate R y.1 y.2 =
        lowWheelLargestCofactorQuotientToggle y.2 := by
      simp [lowWheelLargestOthelloMate, hprod, hmate]
    _ = (lowWheelFrozenCofactorTopToggle y).2 :=
      lowWheelLargestCofactorQuotientToggle_eq_frozenTopToggle hy

/-- Consequently a repeated frozen `c > 1` source is not part of the
largest-prime stable defect.  Its raw largest-prime mate is already physical. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_not_mem_largestDefect
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2 ∉ lowWheelLargestDefectPart R y.1 := by
  intro hyDefect
  have hnot := (Finset.mem_filter.mp hyDefect).2.2
  apply hnot
  rw [lowWheelLargestCofactorQuotientToggle_eq_frozenTopToggle hy]
  exact lowWheelFrozenCofactorTopToggle_mem_physical hy

/-- More explicitly, every repeated frozen `c > 1` source belongs to the moving
part of the completed largest-prime Othello matching. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_mem_largestMovingPart
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2 ∈ finiteOthelloMovingPart
      (lowWheelCanonicalPhysicalStateSet R y.1)
      (lowWheelLargestOthelloMate R y.1) := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hcgt : 1 < y.2.1 := (Finset.mem_filter.mp hy).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hphysicalData := mem_lowWheelCanonicalPhysicalStateSet.mp hphysical
  have hkpos : 0 < y.2.2 := by
    have hk1 := (Finset.mem_Icc.mp hphysicalData.2.1).1
    omega
  have hprod : y.2.1 * y.2.2 ≠ 1 := by
    have hle : y.2.1 ≤ y.2.1 * y.2.2 :=
      Nat.le_mul_of_pos_right y.2.1 hkpos
    exact ne_of_gt (hcgt.trans_le hle)
  have hrawNe : lowWheelLargestCofactorQuotientToggle y.2 ≠ y.2 :=
    lowWheelLargestRawToggle_ne ht hphysical hprod
  rw [lowWheelLargestCofactorQuotientToggle_eq_frozenTopToggle hy] at hrawNe
  apply Finset.mem_filter.mpr
  refine ⟨hphysical, ?_⟩
  rw [lowWheelLargestOthelloMate_eq_frozenTopToggle hy]
  exact hrawNe

end RHLean.Proof
