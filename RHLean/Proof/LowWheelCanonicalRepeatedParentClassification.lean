import Mathlib
import RHLean.Proof.LowWheelCanonicalDowncrossParentFibers

/-!
# Repeated-parent classification for the canonical downcross frontier

The full square-endpoint residual is the tagged canonical downcross carrier.  A
state `y = (t,(c,k))` has canonical least-prime pivot

`p = minFac (c*k)`

and root-side parent

`n = P(t) * (k/p) <= R < p*n`.

This file isolates the only three finite shapes that can occur inside a repeated
parent fiber.

* **movable face/quotient state:** some prime `q >= p` occurs either in the
  Boolean face or in `k/p`; this is the coordinate on which a parent-preserving
  Boolean toggle acts;
* **frozen cofactor state:** no such coordinate remains, hence `k = p` and every
  face prime is `< p`, but `c > 1`; this exposes a concrete transport candidate
  for subsequent global mate accounting;
* **terminal Euler boundary:** `c = 1`, `k = p`, and every face prime is `< p`.
  This is the literal monotone first crossing `P(t) <= R < p*P(t)`.

No norm, asymptotic estimate, PNT input, or further Euler descent appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Canonical pivot of a tagged downcross state. -/
def lowWheelTaggedDowncrossPivot (y : LowWheelTaggedDowncrossState) : ℕ :=
  lowWheelCanonicalCofactorQuotientPivot y.2

/-- A prime coordinate that can move between the Boolean face and the
root-side quotient factor without changing the parent. -/
def LowWheelDowncrossMovablePrime
    (y : LowWheelTaggedDowncrossState) (q : ℕ) : Prop :=
  q.Prime ∧ lowWheelTaggedDowncrossPivot y ≤ q ∧
    (q ∈ y.1 ∨ q ∣ y.2.2 / lowWheelTaggedDowncrossPivot y)

/-- Frozen first-crossing shape: the quotient is exactly the canonical pivot
and all Boolean-face primes are strictly smaller. -/
def LowWheelDowncrossFrozenShape
    (y : LowWheelTaggedDowncrossState) : Prop :=
  y.2.2 = lowWheelTaggedDowncrossPivot y ∧
    ∀ q ∈ y.1, q < lowWheelTaggedDowncrossPivot y

/-- Every downcross state is either movable along a parent coordinate or has the
frozen shape. -/
theorem lowWheelCanonicalDowncross_movable_or_frozen
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R) :
    (∃ q, LowWheelDowncrossMovablePrime y q) ∨
      LowWheelDowncrossFrozenShape y := by
  rcases y with ⟨t, ⟨c, k⟩⟩
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨ht, hx⟩
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
  rcases hshell with ⟨hp, _hpc, hpk, _hdown, _hup⟩
  let p := lowWheelCanonicalCofactorQuotientPivot (c, k)
  by_cases hface : ∃ q ∈ t, p ≤ q
  · rcases hface with ⟨q, hqt, hpq⟩
    left
    refine ⟨q, ?_, hpq, Or.inl hqt⟩
    have hqtGlobal := (Finset.mem_powerset.mp ht) hqt
    exact prime_of_mem_primesUpTo hqtGlobal
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

/-- Repeated-parent states with an available face/quotient coordinate. -/
def lowWheelCanonicalRepeatedMovablePart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalDowncrossRepeatedParentPart R).filter fun y =>
    ∃ q, LowWheelDowncrossMovablePrime y q

/-- Repeated-parent states whose parent factorization is frozen. -/
def lowWheelCanonicalRepeatedFrozenPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalDowncrossRepeatedParentPart R).filter
    LowWheelDowncrossFrozenShape

/-- Frozen repeated-parent states with a nontrivial cofactor. -/
def lowWheelCanonicalRepeatedFrozenCofactorPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenPart R).filter fun y => 1 < y.2.1

/-- Literal terminal repeated-parent boundary. -/
def lowWheelCanonicalRepeatedTerminalBoundary (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenPart R).filter fun y => y.2.1 = 1

/-- Movable and frozen states exhaust the repeated-parent carrier. -/
theorem lowWheelCanonicalRepeatedParent_eq_movable_union_frozen
    (R : ℕ) :
    lowWheelCanonicalDowncrossRepeatedParentPart R =
      lowWheelCanonicalRepeatedMovablePart R ∪
        lowWheelCanonicalRepeatedFrozenPart R := by
  ext y
  constructor
  · intro hy
    have hyCarrier := (Finset.mem_filter.mp hy).1
    rcases lowWheelCanonicalDowncross_movable_or_frozen hyCarrier with hm | hf
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hy, hm⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, hf⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · exact (Finset.mem_filter.mp hy).1

/-- The frozen population splits exactly into nontrivial-cofactor states and the
`c = 1` terminal Euler boundary. -/
theorem lowWheelCanonicalRepeatedFrozen_eq_cofactor_union_terminal
    (R : ℕ) :
    lowWheelCanonicalRepeatedFrozenPart R =
      lowWheelCanonicalRepeatedFrozenCofactorPart R ∪
        lowWheelCanonicalRepeatedTerminalBoundary R := by
  ext y
  constructor
  · intro hy
    have hyCarrier := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
    rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hyCarrier with ⟨_ht, hx⟩
    have hc1 := (Finset.mem_Ico.mp
      (mem_lowWheelCanonicalPhysicalStateSet.mp
        (mem_lowWheelCanonicalDowncrossPart.mp hx).1).1).1
    by_cases hc : y.2.1 = 1
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, hc⟩
    · have hcgt : 1 < y.2.1 := by omega
      exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hy, hcgt⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · exact (Finset.mem_filter.mp hy).1

/-- Complete finite trichotomy for every repeated-parent occurrence. -/
theorem lowWheelCanonicalRepeatedParent_trichotomy
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalDowncrossRepeatedParentPart R) :
    y ∈ lowWheelCanonicalRepeatedMovablePart R ∨
      y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R ∨
      y ∈ lowWheelCanonicalRepeatedTerminalBoundary R := by
  rw [lowWheelCanonicalRepeatedParent_eq_movable_union_frozen R] at hy
  rcases Finset.mem_union.mp hy with hm | hf
  · exact Or.inl hm
  · rw [lowWheelCanonicalRepeatedFrozen_eq_cofactor_union_terminal R] at hf
    rcases Finset.mem_union.mp hf with hc | ht
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ht)

/-- The terminal boundary is exactly a monotone prime first crossing: its
cofactor is one, its quotient is the fresh canonical prime, every old face prime
is smaller, and the child crosses the root. -/
theorem lowWheelCanonicalRepeatedTerminalBoundary_geometry
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalBoundary R) :
    y.2.1 = 1 ∧
      y.2.2 = lowWheelTaggedDowncrossPivot y ∧
      (lowWheelTaggedDowncrossPivot y).Prime ∧
      (∀ q ∈ y.1, q < lowWheelTaggedDowncrossPivot y) ∧
      primeFaceProduct y.1 ≤ R ∧
      R < lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hc := (Finset.mem_filter.mp hy).2
  have hshape := (Finset.mem_filter.mp hfrozen).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
  rcases hshell with ⟨hpRaw, _hpc, _hpk, hdown, hup⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hpRaw
  change primeFaceProduct y.1 *
      (y.2.2 / lowWheelTaggedDowncrossPivot y) ≤ R at hdown
  change R < primeFaceProduct y.1 *
      (lowWheelTaggedDowncrossPivot y *
        (y.2.2 / lowWheelTaggedDowncrossPivot y)) at hup
  have hquot : y.2.2 / lowWheelTaggedDowncrossPivot y = 1 := by
    rw [hshape.1]
    exact Nat.div_self hp.pos
  have hdown' : primeFaceProduct y.1 ≤ R := by
    rw [hquot, Nat.mul_one] at hdown
    exact hdown
  have hup' : R < primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y := by
    rw [hquot, Nat.mul_one] at hup
    exact hup
  refine ⟨hc, hshape.1, hp, hshape.2, hdown', ?_⟩
  simpa [Nat.mul_comm] using hup'

end RHLean.Proof
