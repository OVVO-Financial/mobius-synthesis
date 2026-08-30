import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification
import RHLean.Proof.LowWheelCanonicalDowncrossSignedParentSplit
import RHLean.Proof.LowWheelCofactorQuotientToggle

/-!
# Top/bottom toggle for frozen canonical downcross states

After the face/tail Othello cancellation, a frozen repeated state has shape

`y = (t,(c,p))`,

where `p = minFac(c*p)`, every face prime is `< p`, and

`P(t) <= R < P(t)*p`.

If `c > 1`, let `q = P+(c)`.  Since `p` is the least prime of `c*p` and does not
divide `c`, one has `p < q`.  Move `q` out of the cofactor and into the quotient
using the already-existing same-product toggle

`(c,p) -> (c/q, q*p)`.

The represented integer and Boolean face are unchanged, the Möbius sign flips,
and the canonical least-prime pivot stays `p`.  But the normalized root-side
parent changes from `P(t)` to `P(t)*q`, which is strictly above `R` because
`q > p` and `R < P(t)*p`.

Thus every frozen nontrivial-cofactor bottom state has a literal opposite-sign
partner on the top/post-root side of the *same* physical carrier.  This is an
exact coordinate move, not a bound.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Descending/top coordinate attached to one frozen cofactor state. -/
def lowWheelFrozenCofactorTopPrime
    (y : LowWheelTaggedDowncrossState) : ℕ :=
  canonicalLargestPrimeFactor y.2.1

/-- Move the largest cofactor prime to the quotient, retaining the Boolean face. -/
def lowWheelFrozenCofactorTopToggle
    (y : LowWheelTaggedDowncrossState) : LowWheelTaggedDowncrossState :=
  (y.1,
    lowWheelCofactorQuotientToggleAt
      (lowWheelFrozenCofactorTopPrime y) y.2)

/-- Arithmetic data of the descending prime on a frozen nontrivial-cofactor
state. -/
theorem lowWheelFrozenCofactorTopPrime_data
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelFrozenCofactorTopPrime y).Prime ∧
      lowWheelFrozenCofactorTopPrime y ∣ y.2.1 ∧
      lowWheelTaggedDowncrossPivot y < lowWheelFrozenCofactorTopPrime y := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hcgt := (Finset.mem_filter.mp hy).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  rcases mem_lowWheelCanonicalDowncrossPart.mp hx with
    ⟨_hphysical, hpNotC, _hdown⟩
  have hqPrime : (lowWheelFrozenCofactorTopPrime y).Prime := by
    simpa [lowWheelFrozenCofactorTopPrime] using
      canonicalLargestPrimeFactor_prime hcgt
  have hqDvd : lowWheelFrozenCofactorTopPrime y ∣ y.2.1 := by
    simpa [lowWheelFrozenCofactorTopPrime] using
      canonicalLargestPrimeFactor_dvd hcgt
  have hqDvdProd :
      lowWheelFrozenCofactorTopPrime y ∣ y.2.1 * y.2.2 :=
    dvd_mul_of_dvd_left hqDvd y.2.2
  have hpLeQ :
      lowWheelTaggedDowncrossPivot y ≤ lowWheelFrozenCofactorTopPrime y := by
    change Nat.minFac (y.2.1 * y.2.2) ≤ lowWheelFrozenCofactorTopPrime y
    exact Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
  have hpNeQ :
      lowWheelTaggedDowncrossPivot y ≠ lowWheelFrozenCofactorTopPrime y := by
    intro heq
    apply hpNotC
    have hpDvd : lowWheelTaggedDowncrossPivot y ∣ y.2.1 := by
      simpa [heq] using hqDvd
    simpa [lowWheelTaggedDowncrossPivot] using hpDvd
  have hpLtQ :
      lowWheelTaggedDowncrossPivot y < lowWheelFrozenCofactorTopPrime y := by
    omega
  exact ⟨hqPrime, hqDvd, hpLtQ⟩

/-- The top/bottom move preserves the complete cofactor-times-quotient product,
so in particular it preserves the canonical least-prime pivot. -/
theorem lowWheelFrozenCofactorTopToggle_pivot
    (y : LowWheelTaggedDowncrossState) :
    lowWheelCanonicalCofactorQuotientPivot
        (lowWheelFrozenCofactorTopToggle y).2 =
      lowWheelTaggedDowncrossPivot y := by
  unfold lowWheelFrozenCofactorTopToggle lowWheelTaggedDowncrossPivot
    lowWheelCanonicalCofactorQuotientPivot
  rw [lowWheelCofactorQuotientToggleAt_product]

/-- The top/bottom move stays on the same physical transport carrier. -/
theorem lowWheelFrozenCofactorTopToggle_mem_physical
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelFrozenCofactorTopToggle y).2 ∈
      lowWheelCanonicalPhysicalStateSet R y.1 := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  rcases mem_lowWheelCanonicalPhysicalStateSet.mp hphysical with
    ⟨_hcRange, _hkRange, hsq, hpair⟩
  rcases lowWheelFrozenCofactorTopPrime_data hy with
    ⟨hqPrime, hqDvd, _hpq⟩
  have hpairNew :=
    lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
      hqPrime hpair hqDvd
  have hranges := lowWheelTransportPairCarrier_mem_ranges hpairNew
  have hdivisor :
      y.2.1 / lowWheelFrozenCofactorTopPrime y ∣ y.2.1 :=
    ⟨lowWheelFrozenCofactorTopPrime y,
      (Nat.div_mul_cancel hqDvd).symm⟩
  have hsqNew :
      Squarefree
        (lowWheelCofactorQuotientToggleAt
          (lowWheelFrozenCofactorTopPrime y) y.2).1 := by
    unfold lowWheelCofactorQuotientToggleAt
    simp only [hqDvd, if_true]
    exact hsq.squarefree_of_dvd hdivisor
  apply mem_lowWheelCanonicalPhysicalStateSet.mpr
  exact ⟨hranges.1, hranges.2, hsqNew, hpairNew⟩

/-- The normalized parent of the top image is strictly above the square root. -/
theorem lowWheelFrozenCofactorTopToggle_parent_gt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    R < primeFaceProduct y.1 *
      ((lowWheelFrozenCofactorTopToggle y).2.2 /
        lowWheelCanonicalCofactorQuotientPivot
          (lowWheelFrozenCofactorTopToggle y).2) := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hshape := (Finset.mem_filter.mp hfrozen).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨ht, hx⟩
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
  rcases hshell with ⟨hpRaw, _hpc, _hpk, _hdown, hup⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hpRaw
  rcases lowWheelFrozenCofactorTopPrime_data hy with
    ⟨_hqPrime, hqDvd, hpq⟩
  have hPpos : 0 < primeFaceProduct y.1 :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hquotOld : y.2.2 / lowWheelTaggedDowncrossPivot y = 1 := by
    rw [hshape.1]
    exact Nat.div_self hp.pos
  have hbottom :
      R < primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y := by
    change R < primeFaceProduct y.1 *
      (lowWheelTaggedDowncrossPivot y *
        (y.2.2 / lowWheelTaggedDowncrossPivot y)) at hup
    rw [hquotOld, Nat.mul_one] at hup
    exact hup
  have htop :
      R < primeFaceProduct y.1 * lowWheelFrozenCofactorTopPrime y := by
    exact hbottom.trans
      (Nat.mul_lt_mul_of_pos_left hpq hPpos)
  rw [lowWheelFrozenCofactorTopToggle_pivot]
  unfold lowWheelFrozenCofactorTopToggle
  unfold lowWheelCofactorQuotientToggleAt
  simp only [hqDvd, if_true]
  rw [hshape.1]
  have hdiv :
      (lowWheelFrozenCofactorTopPrime y * lowWheelTaggedDowncrossPivot y) /
          lowWheelTaggedDowncrossPivot y =
        lowWheelFrozenCofactorTopPrime y := by
    simp [hp.ne_zero]
  rw [hdiv]
  exact htop

/-- The top/bottom move reverses the signed tagged weight. -/
theorem lowWheelFrozenCofactorTopToggle_weight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossWeight (lowWheelFrozenCofactorTopToggle y) =
      -lowWheelTaggedDowncrossWeight y := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hsq := (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).2.2.1
  rcases lowWheelFrozenCofactorTopPrime_data hy with
    ⟨hqPrime, hqDvd, _hpq⟩
  unfold lowWheelTaggedDowncrossWeight lowWheelFrozenCofactorTopToggle
  exact lowWheelCofactorQuotientToggleAt_weight_neg
    (t := y.1) hqPrime hsq (Or.inl hqDvd)

/-- Fixed-coordinate involutivity gives the exact return edge from top to bottom. -/
theorem lowWheelFrozenCofactorTopToggle_involutive
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    let q := lowWheelFrozenCofactorTopPrime y
    lowWheelCofactorQuotientToggleAt q
      (lowWheelCofactorQuotientToggleAt q y.2) = y.2 := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hsq := (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).2.2.1
  rcases lowWheelFrozenCofactorTopPrime_data hy with
    ⟨hqPrime, hqDvd, _hpq⟩
  exact lowWheelCofactorQuotientToggleAt_involutive
    hqPrime hsq (Or.inl hqDvd)

end RHLean.Proof
