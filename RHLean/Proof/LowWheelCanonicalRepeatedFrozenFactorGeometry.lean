import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification

/-!
# Prime geometry of frozen repeated-parent states with nontrivial cofactor

For a frozen repeated-parent source `y=(t,(c,k))`, classification gives
`k=p`, where `p=minFac(c*k)`, while the downcross condition gives `p ∤ c`.
If `c>1`, every prime factor `q|c` is therefore strictly above `p`.  Since the
physical cofactor satisfies `c<R`, all of those factors are still low-wheel
coordinates.  In particular `p<R` as well.

This is the key fact allowing the whole signed cofactor, rather than one factor,
to be moved into the Boolean face and terminated at a product-one fixed state.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Basic arithmetic data carried by a frozen repeated state with `c>1`. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_source_data
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2.2 = lowWheelTaggedDowncrossPivot y ∧
      (lowWheelTaggedDowncrossPivot y).Prime ∧
      ¬ lowWheelTaggedDowncrossPivot y ∣ y.2.1 ∧
      Squarefree y.2.1 ∧
      1 < y.2.1 ∧ y.2.1 < R := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hcgt := (Finset.mem_filter.mp hy).2
  have hshape := (Finset.mem_filter.mp hfrozen).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hdown := mem_lowWheelCanonicalDowncrossPart.mp htag.2
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp hdown.1
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell htag.2
    simpa [lowWheelTaggedDowncrossPivot] using hshell.1
  exact ⟨hshape.1, hp, hdown.2.1, hphys.2.2.1, hcgt,
    (Finset.mem_Ico.mp hphys.1).2⟩

/-- Every prime factor of the frozen cofactor lies strictly above the canonical
pivot. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R)
    {q : ℕ} (hq : q ∈ y.2.1.primeFactors) :
    lowWheelTaggedDowncrossPivot y < q := by
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hqData := Nat.mem_primeFactors.mp hq
  have hqPrime : q.Prime := hqData.1
  have hqDvdC : q ∣ y.2.1 := hqData.2.1
  have hk := hdata.1
  have hqDvdProd : q ∣ y.2.1 * y.2.2 := dvd_mul_of_dvd_left hqDvdC _
  have hpLe : lowWheelTaggedDowncrossPivot y ≤ q := by
    have h := Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
    simpa [lowWheelTaggedDowncrossPivot] using h
  exact hpLe.lt_of_ne fun heq =>
    hdata.2.2.1 (by simpa [heq] using hqDvdC)

/-- Every prime factor of the frozen cofactor is an actual low-wheel coordinate
strictly below the root cutoff. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_primeFactor_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R)
    {q : ℕ} (hq : q ∈ y.2.1.primeFactors) :
    q < R := by
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hqDvdC := (Nat.mem_primeFactors.mp hq).2.1
  have hqLeC : q ≤ y.2.1 := Nat.le_of_dvd (by omega) hqDvdC
  exact hqLeC.trans_lt hdata.2.2.2.2.2

/-- Consequently the complete prime support of the frozen cofactor belongs to
the low Boolean wheel. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_primeFactors_subset_primesUpTo
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2.1.primeFactors ⊆ primesUpTo R := by
  intro q hq
  exact mem_primesUpTo.mpr
    ⟨(Nat.mem_primeFactors.mp hq).1,
      (lowWheelCanonicalRepeatedFrozenCofactor_primeFactor_lt_root hy hq).le⟩

/-- A frozen nontrivial-cofactor pivot itself is strictly below the root.  Thus
there are no `c>1` frozen states in the external `R<p` obstruction. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossPivot y < R := by
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  let q := Nat.minFac y.2.1
  have hqPrime : q.Prime := by
    simpa [q] using Nat.minFac_prime (by omega : y.2.1 ≠ 1)
  have hqDvd : q ∣ y.2.1 := by
    simpa [q] using Nat.minFac_dvd y.2.1
  have hqMem : q ∈ y.2.1.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, by omega⟩
  exact (lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy hqMem).trans
    (lowWheelCanonicalRepeatedFrozenCofactor_primeFactor_lt_root hy hqMem)

/-- The frozen pivot is therefore itself an available low-wheel coordinate. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_pivot_mem_primesUpTo
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossPivot y ∈ primesUpTo R := by
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  exact mem_primesUpTo.mpr
    ⟨hdata.2.1,
      (lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_root hy).le⟩

end RHLean.Proof
