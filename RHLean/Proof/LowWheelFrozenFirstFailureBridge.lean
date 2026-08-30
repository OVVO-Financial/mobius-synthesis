import Mathlib
import RHLean.Proof.LowWheelCanonicalFrozenReduction
import RHLean.Arithmetic.PrimeProductCubeFrontier

/-!
# Frozen downcrosses are literal first-failure faces

After the movable Othello population cancels, every remaining state has frozen
shape

`y = (t,(c,p))`,

where `p = minFac(c*p)`, every face prime is below `p`, and

`P(t) <= R < p*P(t)`.

This file makes the resulting dichotomy exact on the complete frozen carrier.
If `c > 1`, then `c` has a prime divisor strictly above the least pivot `p`;
since the physical carrier has `c < R`, necessarily `p < R`.  Hence every
nontrivial-cofactor frozen state is internal to the low-prime cube.

For every internal frozen state, the old face `t` is literally the existing
`primeProductFirstFailureBoundary (primesUpTo R) R p`: it is below the root and
adjoining the fresh prime `p` is the first crossing.  Conversely, a frozen state
with `p > R` must have `c = 1`, so the only external frozen population is the
terminal high-prime coordinate already present elsewhere in the repository.

No estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A nontrivial frozen cofactor forces the canonical crossing prime strictly
below the root. -/
theorem lowWheelCanonicalFrozenDowncross_pivot_lt_root_of_cofactor_gt_one
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R)
    (hcgt : 1 < y.2.1) :
    lowWheelTaggedDowncrossPivot y < R := by
  have hcarrier := (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hcRange := (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).1
  have hcR : y.2.1 < R := (Finset.mem_Ico.mp hcRange).2
  have hpNotC := (mem_lowWheelCanonicalDowncrossPart.mp hx).2.1
  let q := canonicalLargestPrimeFactor y.2.1
  have hqPrime : q.Prime := by
    simpa [q] using canonicalLargestPrimeFactor_prime hcgt
  have hqDvdC : q ∣ y.2.1 := by
    simpa [q] using canonicalLargestPrimeFactor_dvd hcgt
  have hqDvdProd : q ∣ y.2.1 * y.2.2 :=
    dvd_mul_of_dvd_left hqDvdC y.2.2
  have hpLeQ : lowWheelTaggedDowncrossPivot y ≤ q := by
    change Nat.minFac (y.2.1 * y.2.2) ≤ q
    exact Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
  have hpNeQ : lowWheelTaggedDowncrossPivot y ≠ q := by
    intro heq
    apply hpNotC
    have hpDvd : lowWheelTaggedDowncrossPivot y ∣ y.2.1 := by
      simpa [heq] using hqDvdC
    simpa [lowWheelTaggedDowncrossPivot] using hpDvd
  have hpLtQ : lowWheelTaggedDowncrossPivot y < q :=
    lt_of_le_of_ne hpLeQ hpNeQ
  have hqLeC : q ≤ y.2.1 := Nat.le_of_dvd (by omega) hqDvdC
  exact hpLtQ.trans (hqLeC.trans_lt hcR)

/-- Every frozen external crossing has forced cofactor `1`. -/
theorem lowWheelCanonicalFrozenDowncross_cofactor_eq_one_of_root_lt_pivot
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R)
    (hpR : R < lowWheelTaggedDowncrossPivot y) :
    y.2.1 = 1 := by
  have hcarrier := (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hcRange := (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).1
  have hcOne : 1 ≤ y.2.1 := (Finset.mem_Ico.mp hcRange).1
  by_contra hne
  have hcgt : 1 < y.2.1 := by omega
  have hpLtR := lowWheelCanonicalFrozenDowncross_pivot_lt_root_of_cofactor_gt_one
    hy hcgt
  omega

/-- In frozen shape the adjacent-shell inequalities simplify to the literal
first-crossing inequalities `P(t) <= R < p*P(t)`. -/
theorem lowWheelCanonicalFrozenDowncross_firstCrossing_geometry
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R) :
    primeFaceProduct y.1 ≤ R ∧
      R < lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
  have hshape := (Finset.mem_filter.mp hy).2
  have hcarrier := (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  rcases lowWheelCanonicalDowncrossPart_adjacent_shell hx with
    ⟨hpRaw, _hpNotC, _hpDvdK, hdown, hup⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hpRaw
  change primeFaceProduct y.1 *
      (y.2.2 / lowWheelTaggedDowncrossPivot y) ≤ R at hdown
  change R < primeFaceProduct y.1 *
      (lowWheelTaggedDowncrossPivot y *
        (y.2.2 / lowWheelTaggedDowncrossPivot y)) at hup
  have hdiv :
      y.2.2 / lowWheelTaggedDowncrossPivot y = 1 := by
    rw [hshape.1]
    exact Nat.div_self hp.pos
  have hdown' : primeFaceProduct y.1 ≤ R := by
    rw [hdiv, Nat.mul_one] at hdown
    exact hdown
  have hup' : R < primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y := by
    rw [hdiv, Nat.mul_one] at hup
    exact hup
  exact ⟨hdown', by simpa [Nat.mul_comm] using hup'⟩

/-- An internal frozen crossing is exactly an existing truncated Boolean-cube
first-failure face at its canonical pivot. -/
theorem lowWheelCanonicalFrozenDowncross_face_mem_firstFailureBoundary
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R)
    (hpR : lowWheelTaggedDowncrossPivot y ≤ R) :
    y.1 ∈ primeProductFirstFailureBoundary
      (primesUpTo R) R (lowWheelTaggedDowncrossPivot y) := by
  have hshape := (Finset.mem_filter.mp hy).2
  have hcarrier := (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨ht, hx⟩
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hshell.1
  have hpGlobal : lowWheelTaggedDowncrossPivot y ∈ primesUpTo R :=
    mem_primesUpTo.mpr ⟨hp, hpR⟩
  have htSub : y.1 ⊆ primesUpTo R := Finset.mem_powerset.mp ht
  have hpNotFace : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hmem
    have hlt := hshape.2 _ hmem
    exact (Nat.lt_irrefl _) hlt
  have htErase : y.1 ⊆ (primesUpTo R).erase (lowWheelTaggedDowncrossPivot y) := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨by
      intro heq
      subst q
      exact hpNotFace hq, htSub hq⟩
  rcases lowWheelCanonicalFrozenDowncross_firstCrossing_geometry hy with
    ⟨hbelow, hcross⟩
  exact mem_primeProductFirstFailureBoundary.mpr
    ⟨htErase, hbelow, hcross⟩

/-- Every frozen state is either an internal first-failure crossing or a forced
external terminal state. -/
theorem lowWheelCanonicalFrozenDowncross_internal_or_externalTerminal
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R) :
    (lowWheelTaggedDowncrossPivot y ≤ R ∧
      y.1 ∈ primeProductFirstFailureBoundary
        (primesUpTo R) R (lowWheelTaggedDowncrossPivot y)) ∨
    (R < lowWheelTaggedDowncrossPivot y ∧ y.2.1 = 1) := by
  by_cases hpR : lowWheelTaggedDowncrossPivot y ≤ R
  · exact Or.inl ⟨hpR,
      lowWheelCanonicalFrozenDowncross_face_mem_firstFailureBoundary hy hpR⟩
  · have hRp : R < lowWheelTaggedDowncrossPivot y := Nat.lt_of_not_ge hpR
    exact Or.inr ⟨hRp,
      lowWheelCanonicalFrozenDowncross_cofactor_eq_one_of_root_lt_pivot hy hRp⟩

end RHLean.Proof
