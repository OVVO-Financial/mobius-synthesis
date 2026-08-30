import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope

/-!
# Canonical smaller-owner fibres for unfinished Go territory

An unfinished predecessor cofactor `c` satisfies

`q <= c <= B`,  `Squarefree c`,  `P+(c) < q`.

Its unique next-largest prime is therefore `r = P+(c)`.  Stripping `r` gives
`d = canonicalCofactor c`, and the physical interval becomes exactly

`(q-1)/r < d <= B/r`.

The parent is squarefree and `r`-rough from above (`P+(d) < r`), while
`mu(c) = -mu(d)`.  Conversely every such parent `d` reconstructs the unique
child `r*d` with canonical owner `r`.

This is the literal set-level population behind the signed recursive Go law.
No path multiplicity is introduced: the owner is recovered from the child by
its canonical largest prime factor.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Unfinished smooth cofactors whose unique next-largest prime is `r`. -/
def squareRootLowPrimeGoSmallerOwnerChildren
    (q B r : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSmoothCofactors q B).filter fun c =>
    q ≤ c ∧ canonicalLargestPrimeFactor c = r

@[simp] theorem mem_squareRootLowPrimeGoSmallerOwnerChildren
    {q B r c : ℕ} :
    c ∈ squareRootLowPrimeGoSmallerOwnerChildren q B r ↔
      c ∈ squareRootLowPrimeGoSmoothCofactors q B ∧
        q ≤ c ∧ canonicalLargestPrimeFactor c = r := by
  simp [squareRootLowPrimeGoSmallerOwnerChildren]

/-- Canonical parents in the exact quotient strip attached to smaller owner
`r`. -/
def squareRootLowPrimeGoSmallerOwnerParentStrip
    (q B r : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSmoothCofactors r (B / r)).filter fun d =>
    (q - 1) / r < d

@[simp] theorem mem_squareRootLowPrimeGoSmallerOwnerParentStrip
    {q B r d : ℕ} :
    d ∈ squareRootLowPrimeGoSmallerOwnerParentStrip q B r ↔
      d ∈ squareRootLowPrimeGoSmoothCofactors r (B / r) ∧
        (q - 1) / r < d := by
  simp [squareRootLowPrimeGoSmallerOwnerParentStrip]

/-- A genuine smaller-owner child strips to the corresponding exact quotient
strip. -/
theorem squareRootLowPrimeGoSmallerOwnerChild_parent_mem
    {q B r c : ℕ} (hq : q.Prime)
    (hc : c ∈ squareRootLowPrimeGoSmallerOwnerChildren q B r) :
    canonicalCofactor c ∈
      squareRootLowPrimeGoSmallerOwnerParentStrip q B r := by
  rcases mem_squareRootLowPrimeGoSmallerOwnerChildren.mp hc with
    ⟨hcSmooth, hqc, howner⟩
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hcSmooth with
    ⟨hc1, hcB, hsq, _hcq⟩
  have hcgt : 1 < c := by
    exact lt_of_lt_of_le hq.one_lt hqc
  have hrPrime : r.Prime := by
    rw [← howner]
    exact canonicalLargestPrimeFactor_prime hcgt
  have hparentPos : 1 ≤ canonicalCofactor c :=
    canonicalCofactor_pos hcgt
  have hparentSq : Squarefree (canonicalCofactor c) :=
    squarefree_canonicalCofactor hsq hcgt
  have hsource := canonicalSourceData_of_squarefree hsq hcgt
  have hparentRough :
      canonicalLargestPrimeFactor (canonicalCofactor c) < r := by
    by_cases hparentOne : canonicalCofactor c = 1
    · rw [hparentOne]
      simp [canonicalLargestPrimeFactor, hrPrime.one_lt]
    · have hparentGt : 1 < canonicalCofactor c := by omega
      have hpPrime := canonicalLargestPrimeFactor_prime hparentGt
      have hpDvd := canonicalLargestPrimeFactor_dvd hparentGt
      have hlt := hsource.2.2.2.2
        (canonicalLargestPrimeFactor (canonicalCofactor c)) hpPrime hpDvd
      simpa [howner] using hlt
  have hprod : canonicalCofactor c * r = c := by
    simpa [howner] using canonicalCofactor_mul_largestPrimeFactor hcgt
  have hparentB : canonicalCofactor c ≤ B / r := by
    apply (Nat.le_div_iff_mul_le hrPrime.pos).2
    rw [hprod]
    exact hcB
  have hlower : (q - 1) / r < canonicalCofactor c := by
    apply (Nat.div_lt_iff_lt_mul hrPrime.pos).2
    rw [hprod]
    omega
  exact mem_squareRootLowPrimeGoSmallerOwnerParentStrip.mpr
    ⟨mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨hparentPos, hparentB, hparentSq, hparentRough⟩,
      hlower⟩

/-- The child is exactly the owner times its canonical parent. -/
theorem squareRootLowPrimeGoSmallerOwnerChild_eq_owner_mul_parent
    {q B r c : ℕ} (hq : q.Prime)
    (hc : c ∈ squareRootLowPrimeGoSmallerOwnerChildren q B r) :
    r * canonicalCofactor c = c := by
  rcases mem_squareRootLowPrimeGoSmallerOwnerChildren.mp hc with
    ⟨_hcSmooth, hqc, howner⟩
  have hcgt : 1 < c := lt_of_lt_of_le hq.one_lt hqc
  have hprod := canonicalCofactor_mul_largestPrimeFactor hcgt
  simpa [howner, Nat.mul_comm] using hprod

/-- Stripping the unique smaller owner reverses the Möbius sign. -/
theorem squareRootLowPrimeGoSmallerOwnerChild_moebius
    {q B r c : ℕ} (hq : q.Prime)
    (hc : c ∈ squareRootLowPrimeGoSmallerOwnerChildren q B r) :
    (μ c : ℤ) = -(μ (canonicalCofactor c) : ℤ) := by
  rcases mem_squareRootLowPrimeGoSmallerOwnerChildren.mp hc with
    ⟨hcSmooth, hqc, _howner⟩
  have hsq := (mem_squareRootLowPrimeGoSmoothCofactors.mp hcSmooth).2.2.1
  have hcgt : 1 < c := lt_of_lt_of_le hq.one_lt hqc
  exact canonicalSignedParent_moebius hsq hcgt

/-- Conversely, every parent in the exact quotient strip reconstructs a unique
unfinished child with owner `r`. -/
theorem squareRootLowPrimeGoSmallerOwnerParent_child_mem
    {q B r d : ℕ} (_hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerParentStrip q B r) :
    r * d ∈ squareRootLowPrimeGoSmallerOwnerChildren q B r := by
  rcases mem_squareRootLowPrimeGoSmallerOwnerParentStrip.mp hd with
    ⟨hdSmooth, hlower⟩
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hdSmooth with
    ⟨hd1, hdB, hsq, hrough⟩
  have hdPos : 0 < d := by omega
  have howner : canonicalLargestPrimeFactor (r * d) = r := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hdPos hr hrough
    simpa [Nat.mul_comm] using h
  have hrNotDvd : ¬ r ∣ d := by
    intro hrd
    by_cases hdOne : d = 1
    · subst d
      exact hr.not_dvd_one hrd
    · have hdgt : 1 < d := by omega
      have hrLe := prime_dvd_le_canonicalLargestPrimeFactor hdgt hr hrd
      omega
  have hmuD : μ d ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
  have hcop : Nat.Coprime r d :=
    (hr.coprime_iff_not_dvd).2 hrNotDvd
  have hmuChild : μ (r * d) ≠ 0 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hr]
    exact mul_ne_zero (by norm_num) hmuD
  have hsqChild : Squarefree (r * d) :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuChild
  have hchildB : r * d ≤ B := by
    have h := (Nat.le_div_iff_mul_le hr.pos).1 hdB
    simpa [Nat.mul_comm] using h
  have hchildLower : q ≤ r * d := by
    have hlt : q - 1 < d * r :=
      (Nat.div_lt_iff_lt_mul hr.pos).1 hlower
    simpa [Nat.mul_comm] using (show q ≤ d * r by omega)
  apply mem_squareRootLowPrimeGoSmallerOwnerChildren.mpr
  refine ⟨mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨?_, hchildB, hsqChild, ?_⟩,
    hchildLower, howner⟩
  · exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hr.ne_zero (Nat.ne_of_gt hdPos))
  · rw [howner]
    exact hrq

/-- Reconstructing a parent and stripping its child returns the same parent. -/
theorem squareRootLowPrimeGoSmallerOwnerParent_child_cofactor
    {q B r d : ℕ} (_hq : q.Prime) (hr : r.Prime) (_hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerParentStrip q B r) :
    canonicalCofactor (r * d) = d := by
  have hdData := mem_squareRootLowPrimeGoSmallerOwnerParentStrip.mp hd
  have hsmooth := mem_squareRootLowPrimeGoSmoothCofactors.mp hdData.1
  have hdPos : 0 < d := by omega
  have h := canonicalCofactor_mul_prime_eq_of_rough hdPos hr hsmooth.2.2.2
  simpa [Nat.mul_comm] using h

/-- Distinct smaller owners have disjoint child fibres because the owner is
encoded by `P+(c)`. -/
theorem squareRootLowPrimeGoSmallerOwnerChildren_disjoint
    {q B r s : ℕ} (hrs : r ≠ s) :
    Disjoint (squareRootLowPrimeGoSmallerOwnerChildren q B r)
      (squareRootLowPrimeGoSmallerOwnerChildren q B s) := by
  rw [Finset.disjoint_left]
  intro c hcr hcs
  have hrOwner :=
    (mem_squareRootLowPrimeGoSmallerOwnerChildren.mp hcr).2.2
  have hsOwner :=
    (mem_squareRootLowPrimeGoSmallerOwnerChildren.mp hcs).2.2
  exact hrs (hrOwner.symm.trans hsOwner)

end RHLean.Proof
