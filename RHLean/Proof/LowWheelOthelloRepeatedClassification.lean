import Mathlib
import RHLean.Proof.LowWheelOthelloDowncrossGeometry

/-!
# Lightweight repeated-parent classification

Inside one repeated parent fibre, every state is either movable in a
face/tail prime coordinate or frozen at the literal first crossing.  The frozen
population then splits according to whether the low cofactor is nontrivial or
one.

This is the same arithmetic trichotomy used by the canonical downcross
analysis, restated on the lightweight Othello carrier so it can be kernel
checked without importing the analytic endpoint stack.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A prime coordinate which may move between the Boolean face and the
root-side residual tail without changing the parent. -/
def LowWheelOthelloMovablePrime
    (y : LowWheelOthelloTaggedDowncrossState) (q : ℕ) : Prop :=
  q.Prime ∧ lowWheelOthelloDowncrossPivot y ≤ q ∧
    (q ∈ y.1 ∨ q ∣ y.2.2 / lowWheelOthelloDowncrossPivot y)

/-- Frozen first-crossing shape. -/
def LowWheelOthelloFrozenShape
    (y : LowWheelOthelloTaggedDowncrossState) : Prop :=
  y.2.2 = lowWheelOthelloDowncrossPivot y ∧
    ∀ q ∈ y.1, q < lowWheelOthelloDowncrossPivot y

/-- Every actual downcross state is either movable or frozen. -/
theorem lowWheelOthelloDowncross_movable_or_frozen
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R) :
    (∃ q, LowWheelOthelloMovablePrime y q) ∨
      LowWheelOthelloFrozenShape y := by
  rcases y with ⟨t, ⟨c, k⟩⟩
  rcases mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy with ⟨ht, hx⟩
  have hshell := lowWheelOthelloDowncrossPart_adjacent_shell hx
  rcases hshell with ⟨hp, _hpc, hpk, _hdown, _hup⟩
  let p := lowWheelCanonicalCofactorQuotientPivot (c, k)
  by_cases hface : ∃ q ∈ t, p ≤ q
  · rcases hface with ⟨q, hqt, hpq⟩
    left
    refine ⟨q, ?_, hpq, Or.inl hqt⟩
    exact prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hqt)
  · have hfaceLt : ∀ q ∈ t, q < p := by
      intro q hqt
      have hnot : ¬ p ≤ q := by
        intro hpq
        exact hface ⟨q, hqt, hpq⟩
      omega
    by_cases hkp : k = p
    · right
      exact ⟨hkp, hfaceLt⟩
    · have hkCancel : p * (k / p) = k := Nat.mul_div_cancel' hpk
      have hmNe : k / p ≠ 1 := by
        intro hm
        have : p = k := by simpa [hm] using hkCancel
        exact hkp this.symm
      let q := Nat.minFac (k / p)
      have hqPrime : q.Prime := by
        simpa [q] using Nat.minFac_prime hmNe
      have hqDvdM : q ∣ k / p := by
        simpa [q] using Nat.minFac_dvd (k / p)
      have hqDvdK : q ∣ k := by
        rcases hqDvdM with ⟨a, ha⟩
        refine ⟨p * a, ?_⟩
        calc
          k = p * (k / p) := hkCancel.symm
          _ = p * (q * a) := by rw [ha]
          _ = q * (p * a) := by ring
      have hqDvdProd : q ∣ c * k := dvd_mul_of_dvd_right hqDvdK c
      have hpLeQ : p ≤ q := by
        have hmin := Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
        simpa [p, lowWheelCanonicalCofactorQuotientPivot] using hmin
      left
      exact ⟨q, hqPrime, hpLeQ, Or.inr hqDvdM⟩

/-- Repeated states with an available face/tail coordinate. -/
def lowWheelOthelloRepeatedMovablePart (R : ℕ) :
    Finset LowWheelOthelloTaggedDowncrossState :=
  (lowWheelOthelloDowncrossRepeatedParentPart R).filter fun y =>
    ∃ q, LowWheelOthelloMovablePrime y q

/-- Repeated states with frozen parent factorization. -/
def lowWheelOthelloRepeatedFrozenPart (R : ℕ) :
    Finset LowWheelOthelloTaggedDowncrossState :=
  (lowWheelOthelloDowncrossRepeatedParentPart R).filter
    LowWheelOthelloFrozenShape

/-- Frozen states with a nontrivial low cofactor. -/
def lowWheelOthelloRepeatedFrozenCofactorPart (R : ℕ) :
    Finset LowWheelOthelloTaggedDowncrossState :=
  (lowWheelOthelloRepeatedFrozenPart R).filter fun y => 1 < y.2.1

/-- Literal terminal first-crossing boundary `c=1`. -/
def lowWheelOthelloRepeatedTerminalBoundary (R : ℕ) :
    Finset LowWheelOthelloTaggedDowncrossState :=
  (lowWheelOthelloRepeatedFrozenPart R).filter fun y => y.2.1 = 1

/-- Movable and frozen states exhaust the repeated-parent carrier. -/
theorem lowWheelOthelloRepeatedParent_eq_movable_union_frozen
    (R : ℕ) :
    lowWheelOthelloDowncrossRepeatedParentPart R =
      lowWheelOthelloRepeatedMovablePart R ∪
        lowWheelOthelloRepeatedFrozenPart R := by
  ext y
  constructor
  · intro hy
    have hyCarrier := (Finset.mem_filter.mp hy).1
    rcases lowWheelOthelloDowncross_movable_or_frozen hyCarrier with hm | hf
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hy, hm⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, hf⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · exact (Finset.mem_filter.mp hy).1

/-- Frozen states split into nontrivial cofactor and terminal boundary. -/
theorem lowWheelOthelloRepeatedFrozen_eq_cofactor_union_terminal
    (R : ℕ) :
    lowWheelOthelloRepeatedFrozenPart R =
      lowWheelOthelloRepeatedFrozenCofactorPart R ∪
        lowWheelOthelloRepeatedTerminalBoundary R := by
  ext y
  constructor
  · intro hy
    have hyCarrier := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
    rcases mem_lowWheelOthelloTaggedDowncrossCarrier.mp hyCarrier with ⟨_ht, hx⟩
    have hc1 := (Finset.mem_Ico.mp
      (mem_lowWheelCanonicalPhysicalStateSet.mp
        (mem_lowWheelOthelloDowncrossPart.mp hx).1).1).1
    by_cases hc : y.2.1 = 1
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, hc⟩
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hy, by omega⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · exact (Finset.mem_filter.mp hy).1

/-- Complete finite trichotomy on repeated-parent occurrences. -/
theorem lowWheelOthelloRepeatedParent_trichotomy
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloDowncrossRepeatedParentPart R) :
    y ∈ lowWheelOthelloRepeatedMovablePart R ∨
      y ∈ lowWheelOthelloRepeatedFrozenCofactorPart R ∨
      y ∈ lowWheelOthelloRepeatedTerminalBoundary R := by
  rw [lowWheelOthelloRepeatedParent_eq_movable_union_frozen R] at hy
  rcases Finset.mem_union.mp hy with hm | hf
  · exact Or.inl hm
  · rw [lowWheelOthelloRepeatedFrozen_eq_cofactor_union_terminal R] at hf
    rcases Finset.mem_union.mp hf with hc | ht
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ht)

/-- Terminal frozen states are literal monotone prime first crossings. -/
theorem lowWheelOthelloRepeatedTerminalBoundary_geometry
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloRepeatedTerminalBoundary R) :
    y.2.1 = 1 ∧
      y.2.2 = lowWheelOthelloDowncrossPivot y ∧
      (lowWheelOthelloDowncrossPivot y).Prime ∧
      (∀ q ∈ y.1, q < lowWheelOthelloDowncrossPivot y) ∧
      primeFaceProduct y.1 ≤ R ∧
      R < lowWheelOthelloDowncrossPivot y * primeFaceProduct y.1 := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hc := (Finset.mem_filter.mp hy).2
  have hshape := (Finset.mem_filter.mp hfrozen).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelOthelloTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hshell := lowWheelOthelloDowncrossPart_adjacent_shell hx
  rcases hshell with ⟨hpRaw, _hpc, _hpk, hdown, hup⟩
  have hp : (lowWheelOthelloDowncrossPivot y).Prime := by
    simpa [lowWheelOthelloDowncrossPivot] using hpRaw
  change primeFaceProduct y.1 *
      (y.2.2 / lowWheelOthelloDowncrossPivot y) ≤ R at hdown
  change R < primeFaceProduct y.1 *
      (lowWheelOthelloDowncrossPivot y *
        (y.2.2 / lowWheelOthelloDowncrossPivot y)) at hup
  have hquot : y.2.2 / lowWheelOthelloDowncrossPivot y = 1 := by
    rw [hshape.1]
    exact Nat.div_self hp.pos
  have hdown' : primeFaceProduct y.1 ≤ R := by
    rw [hquot, Nat.mul_one] at hdown
    exact hdown
  have hup' : R < primeFaceProduct y.1 * lowWheelOthelloDowncrossPivot y := by
    rw [hquot, Nat.mul_one] at hup
    exact hup
  refine ⟨hc, hshape.1, hp, hshape.2, hdown', ?_⟩
  simpa [Nat.mul_comm] using hup'

end RHLean.Proof
