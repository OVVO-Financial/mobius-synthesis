import Mathlib
import RHLean.Proof.LowPrimeFreshLayerBridge
import RHLean.Proof.LowWheelDoubleCubeSequentialFold
import RHLean.Proof.LowWheelSequentialPrimeWindows
import RHLean.Proof.PrimeCombVisualizationRecurrence
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm

/-!
# Fresh low-prime faces as parent/child reciprocal-window differences

`LowPrimeFreshLayerBridge` identifies the numerical prime step

`S(p) - S(p-1)`

with the Boolean faces whose canonical largest prime factor is the fresh prime
`p`.  This module opens those fresh faces one level further.

A fresh face is uniquely `insert p u`, where `u` is a face of the previously
processed primes `primesUpTo (p-1)`.  Restoring the matching old-parent term
therefore gives the exact signed finite difference

`(-1)^|u| * (F(P(u)) - F(p * P(u)))`.

For the post-root prime-prefix part of the BornPostTail response this finite
difference is literally the prime count in the existing reciprocal
prime-dilate window

`max R (X/(p*a)) < q <= X/a`.

Thus the same geometric window appearing in the LPR parent/child difference is
the window in `LowWheelSequentialPrimeWindows`, where the local mixed cell is
already kernel-checked as

`1_W(q) - 1_W(p*q)`.

The only non-window high-response case is the explicit shallow transition
`a <= K < p*a`; parents and children both below `K` have zero high-response
difference.  The born-orientation finite difference is retained exactly and is
not estimated here.

No norm, absolute value, dissipation inequality, PNT estimate, Mertens bound,
or RH input appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Fresh child faces and their unique old parents -/

/-- Old Boolean faces whose fresh `p`-child remains below the arithmetic cutoff
`B`. -/
def lowPrimeFreshParentFaces (B p : ℕ) : Finset (Finset ℕ) :=
  ((primesUpTo (p - 1)).powerset).filter fun u =>
    p * primeFaceProduct u ≤ B

/-- Admissible Boolean faces whose canonical largest prime factor is exactly the
fresh coordinate `p`. -/
def lowPrimeFreshChildFaces (B p : ℕ) : Finset (Finset ℕ) :=
  (admissiblePrimeFaces B).filter fun v =>
    canonicalLargestPrimeFactor (primeFaceProduct v) = p

@[simp] theorem mem_lowPrimeFreshParentFaces
    {B p : ℕ} {u : Finset ℕ} :
    u ∈ lowPrimeFreshParentFaces B p ↔
      u ∈ (primesUpTo (p - 1)).powerset ∧
        p * primeFaceProduct u ≤ B := by
  simp [lowPrimeFreshParentFaces]

@[simp] theorem mem_lowPrimeFreshChildFaces
    {B p : ℕ} {v : Finset ℕ} :
    v ∈ lowPrimeFreshChildFaces B p ↔
      v ∈ admissiblePrimeFaces B ∧
        canonicalLargestPrimeFactor (primeFaceProduct v) = p := by
  simp [lowPrimeFreshChildFaces]

private theorem prime_le_canonicalLargestPrimeFactor_of_dvd
    {n q : ℕ} (hn : 1 < n) (hq : q.Prime) (hqdvd : q ∣ n) :
    q ≤ canonicalLargestPrimeFactor n := by
  have hmem : q ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hqdvd, by omega⟩
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hn]
  exact Finset.le_max' n.primeFactors q hmem

/-- Every old face is genuinely rough below the fresh prime.  The product can
be much larger than `p`; what matters is that every *prime coordinate* in it is
strictly smaller than `p`. -/
theorem canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime
    {p : ℕ} (hp : p.Prime) {u : Finset ℕ}
    (hu : u ∈ (primesUpTo (p - 1)).powerset) :
    canonicalLargestPrimeFactor (primeFaceProduct u) < p := by
  have huPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  by_cases huOne : 1 < primeFaceProduct u
  · have hqPrime :
        (canonicalLargestPrimeFactor (primeFaceProduct u)).Prime :=
      canonicalLargestPrimeFactor_prime huOne
    have hqDvd : canonicalLargestPrimeFactor (primeFaceProduct u) ∣
        primeFaceProduct u := canonicalLargestPrimeFactor_dvd huOne
    have hqDvdProd : canonicalLargestPrimeFactor (primeFaceProduct u) ∣
        u.prod id := by
      simpa [primeFaceProduct] using hqDvd
    rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqDvdProd with
      ⟨r, hru, hqr⟩
    have hrOld : r ∈ primesUpTo (p - 1) :=
      (Finset.mem_powerset.mp hu) hru
    have hrData := mem_primesUpTo.mp hrOld
    have hqrEq : canonicalLargestPrimeFactor (primeFaceProduct u) = r :=
      (Nat.prime_dvd_prime_iff_eq hqPrime hrData.1).mp hqr
    have hp2 : 2 ≤ p := hp.two_le
    calc
      canonicalLargestPrimeFactor (primeFaceProduct u) = r := hqrEq
      _ ≤ p - 1 := hrData.2
      _ < p := by omega
  · have hle : primeFaceProduct u ≤ 1 := Nat.le_of_not_gt huOne
    have hge : 1 ≤ primeFaceProduct u := huPos
    have hprodOne : primeFaceProduct u = 1 := Nat.le_antisymm hle hge
    rw [hprodOne]
    have hnot : ¬ (1 : ℕ) < 1 := by omega
    unfold canonicalLargestPrimeFactor
    rw [dif_neg hnot]
    exact hp.one_lt

/-- Inserting the fresh prime into an old face gives a face whose represented
integer has canonical largest prime factor exactly `p`. -/
theorem canonicalLargestPrimeFactor_insert_freshPrime
    {p : ℕ} (hp : p.Prime) {u : Finset ℕ}
    (hu : u ∈ (primesUpTo (p - 1)).powerset) :
    canonicalLargestPrimeFactor (primeFaceProduct (insert p u)) = p := by
  have hpNot : p ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem hu
      (freshPrime_not_mem_primesUpTo_pred hp)
  have huPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hrough :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp hu
  have hmul := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
    huPos hp hrough
  have hprod : primeFaceProduct (insert p u) = p * primeFaceProduct u := by
    simp [primeFaceProduct, hpNot]
  rw [hprod, Nat.mul_comm]
  exact hmul

/-- Every admissible fresh child is obtained from an old parent by inserting
`p`, and conversely. -/
theorem insert_freshPrime_mem_childFaces
    {B p : ℕ} (hp : p.Prime) {u : Finset ℕ}
    (hu : u ∈ lowPrimeFreshParentFaces B p) :
    insert p u ∈ lowPrimeFreshChildFaces B p := by
  rcases mem_lowPrimeFreshParentFaces.mp hu with ⟨huOld, hchildB⟩
  have huPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset huOld
  have hpB : p ≤ B := by
    exact (Nat.le_mul_of_pos_right p huPos).trans hchildB
  have hsub : insert p u ⊆ primesUpTo B := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqu
    · exact mem_primesUpTo.mpr ⟨hp, hpB⟩
    · have hqOld : q ∈ primesUpTo (p - 1) :=
        (Finset.mem_powerset.mp huOld) hqu
      rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqle⟩
      exact mem_primesUpTo.mpr ⟨hqPrime, hqle.trans (by omega)⟩
  have hpNot : p ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem huOld
      (freshPrime_not_mem_primesUpTo_pred hp)
  have hprod : primeFaceProduct (insert p u) =
      p * primeFaceProduct u := by
    simp [primeFaceProduct, hpNot]
  apply mem_lowPrimeFreshChildFaces.mpr
  refine ⟨mem_admissiblePrimeFaces.mpr ⟨hsub, ?_⟩, ?_⟩
  · simpa [hprod] using hchildB
  · exact canonicalLargestPrimeFactor_insert_freshPrime hp huOld

/-- Removing `p` from a fresh child recovers an old parent and reinserting it is
literally inverse to that removal. -/
theorem erase_freshPrime_mem_parentFaces
    {B p : ℕ} (hp : p.Prime) {v : Finset ℕ}
    (hv : v ∈ lowPrimeFreshChildFaces B p) :
    v.erase p ∈ lowPrimeFreshParentFaces B p ∧
      insert p (v.erase p) = v := by
  rcases mem_lowPrimeFreshChildFaces.mp hv with ⟨hvAdm, hvLpf⟩
  have hvPow : v ∈ (primesUpTo B).powerset :=
    Finset.mem_powerset.mpr (mem_admissiblePrimeFaces.mp hvAdm).1
  have hvPos : 0 < primeFaceProduct v :=
    primeFaceProduct_pos_of_mem_powerset hvPow
  have hvNotOne : primeFaceProduct v ≠ 1 := by
    intro hOne
    have hnot : ¬ (1 : ℕ) < 1 := by omega
    have hlpfOne : canonicalLargestPrimeFactor (primeFaceProduct v) = 1 := by
      rw [hOne]
      unfold canonicalLargestPrimeFactor
      rw [dif_neg hnot]
    rw [hvLpf] at hlpfOne
    exact hp.ne_one hlpfOne
  have hvOneLe : 1 ≤ primeFaceProduct v := hvPos
  have hvGt : 1 < primeFaceProduct v :=
    lt_of_le_of_ne hvOneLe (Ne.symm hvNotOne)
  have hpDvd : p ∣ primeFaceProduct v := by
    rw [← hvLpf]
    exact canonicalLargestPrimeFactor_dvd hvGt
  have hpDvdProd : p ∣ v.prod id := by
    simpa [primeFaceProduct] using hpDvd
  rcases (Prime.dvd_finset_prod_iff hp.prime id).mp hpDvdProd with
    ⟨r, hrv, hpr⟩
  have hrPrime : r.Prime :=
    (prime_of_mem_admissibleFace_primesUpTo
      (mem_admissiblePrimeFaces.mp hvAdm) hrv).1
  have hprEq : p = r :=
    (Nat.prime_dvd_prime_iff_eq hp hrPrime).mp hpr
  have hpMem : p ∈ v := by simpa [hprEq] using hrv
  have hOldSub : v.erase p ⊆ primesUpTo (p - 1) := by
    intro q hq
    have hqData := Finset.mem_erase.mp hq
    have hqPrime : q.Prime :=
      (prime_of_mem_admissibleFace_primesUpTo
        (mem_admissiblePrimeFaces.mp hvAdm) hqData.2).1
    have hqDvd : q ∣ primeFaceProduct v := by
      unfold primeFaceProduct
      exact Finset.dvd_prod_of_mem id hqData.2
    have hqLe : q ≤ canonicalLargestPrimeFactor (primeFaceProduct v) :=
      prime_le_canonicalLargestPrimeFactor_of_dvd hvGt hqPrime hqDvd
    have hqLeP : q ≤ p := by simpa [hvLpf] using hqLe
    have hqNeP : q ≠ p := hqData.1
    have hqLt : q < p := lt_of_le_of_ne hqLeP hqNeP
    exact mem_primesUpTo.mpr ⟨hqPrime, by omega⟩
  have hpNotErase : p ∉ v.erase p := Finset.notMem_erase p v
  have hprod : primeFaceProduct v =
      p * primeFaceProduct (v.erase p) := by
    calc
      primeFaceProduct v = primeFaceProduct (insert p (v.erase p)) := by
        rw [Finset.insert_erase hpMem]
      _ = p * primeFaceProduct (v.erase p) := by
        simp [primeFaceProduct, hpNotErase]
  have hchildB : p * primeFaceProduct (v.erase p) ≤ B := by
    rw [← hprod]
    exact (mem_admissiblePrimeFaces.mp hvAdm).2
  constructor
  · exact mem_lowPrimeFreshParentFaces.mpr
      ⟨Finset.mem_powerset.mpr hOldSub, hchildB⟩
  · exact Finset.insert_erase hpMem

/-- Weighted fresh-child mass for an arbitrary response field. -/
def lowPrimeFreshChildFaceMass
    (B p : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ v ∈ lowPrimeFreshChildFaces B p,
    (booleanCubeSign v : ℂ) * F (primeFaceProduct v)

/-- The same fresh-child mass, written on the old-parent coordinate. -/
def lowPrimeFreshParentIndexedChildMass
    (B p : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ u ∈ lowPrimeFreshParentFaces B p,
    (booleanCubeSign (insert p u) : ℂ) *
      F (primeFaceProduct (insert p u))

/-- The fresh child faces are exactly the `insert p` image of their old
parents. -/
theorem lowPrimeFreshChildFaceMass_eq_parentIndexed
    (B p : ℕ) (F : ℕ → ℂ) (hp : p.Prime) :
    lowPrimeFreshChildFaceMass B p F =
      lowPrimeFreshParentIndexedChildMass B p F := by
  classical
  unfold lowPrimeFreshChildFaceMass lowPrimeFreshParentIndexedChildMass
  symm
  refine Finset.sum_bij
    (fun u _hu => insert p u)
    (fun u hu => insert_freshPrime_mem_childFaces hp hu)
    ?_ ?_ ?_
  · intro u1 hu1 u2 hu2 hEq
    have h1Old := (mem_lowPrimeFreshParentFaces.mp hu1).1
    have h2Old := (mem_lowPrimeFreshParentFaces.mp hu2).1
    have hpNot1 : p ∉ u1 :=
      Finset.notMem_of_mem_powerset_of_notMem h1Old
        (freshPrime_not_mem_primesUpTo_pred hp)
    have hpNot2 : p ∉ u2 :=
      Finset.notMem_of_mem_powerset_of_notMem h2Old
        (freshPrime_not_mem_primesUpTo_pred hp)
    have hErase := congrArg (fun s : Finset ℕ => s.erase p) hEq
    simpa [hpNot1, hpNot2] using hErase
  · intro v hv
    rcases erase_freshPrime_mem_parentFaces hp hv with ⟨hu, hInv⟩
    exact ⟨v.erase p, hu, hInv⟩
  · intro u _hu
    rfl

/-- Indicator form used by `LowPrimeFreshLayerBridge` is exactly the filtered
fresh-child mass. -/
theorem lowPrimeFreshChildFaceMass_eq_indicator
    (B p : ℕ) (F : ℕ → ℂ) :
    lowPrimeFreshChildFaceMass B p F =
      ∑ v ∈ admissiblePrimeFaces B,
        if canonicalLargestPrimeFactor (primeFaceProduct v) = p then
          (booleanCubeSign v : ℂ) * F (primeFaceProduct v)
        else 0 := by
  classical
  unfold lowPrimeFreshChildFaceMass lowPrimeFreshChildFaces
  rw [Finset.sum_filter]

/-- Matching old-parent half of one fresh-prime coordinate. -/
def lowPrimeFreshMatchingParentMass
    (B p : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ u ∈ lowPrimeFreshParentFaces B p,
    (booleanCubeSign u : ℂ) * F (primeFaceProduct u)

/-- Parent/child finite difference on the same old Boolean coordinate. -/
def lowPrimeFreshPairedDifferenceMass
    (B p : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ u ∈ lowPrimeFreshParentFaces B p,
    (booleanCubeSign u : ℂ) *
      (F (primeFaceProduct u) - F (p * primeFaceProduct u))

/-- **Old parent + fresh child = signed finite difference.** -/
theorem lowPrimeFreshMatchingParent_add_child_eq_pairedDifference
    (B p : ℕ) (F : ℕ → ℂ) (hp : p.Prime) :
    lowPrimeFreshMatchingParentMass B p F +
        lowPrimeFreshChildFaceMass B p F =
      lowPrimeFreshPairedDifferenceMass B p F := by
  classical
  rw [lowPrimeFreshChildFaceMass_eq_parentIndexed B p F hp]
  unfold lowPrimeFreshMatchingParentMass
    lowPrimeFreshParentIndexedChildMass
    lowPrimeFreshPairedDifferenceMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have huOld := (mem_lowPrimeFreshParentFaces.mp hu).1
  have hpNot : p ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem huOld
      (freshPrime_not_mem_primesUpTo_pred hp)
  have hprod : primeFaceProduct (insert p u) =
      p * primeFaceProduct u := by
    simp [primeFaceProduct, hpNot]
  have hcard : (insert p u).card = u.card + 1 :=
    Finset.card_insert_of_notMem hpNot
  simp only [booleanCubeSign, hprod, hcard, pow_succ]
  push_cast
  ring

/-! ## Instantiate the parent/child split on the verified BornPostTail layer -/

/-- Matching old-parent half of the exact BornPostTail fresh Boolean layer. -/
def squareRootBornPostTailFreshMatchingParentLayer
    (R K j p : ℕ) : ℂ :=
  lowPrimeFreshMatchingParentMass (squareRootEndpoint R) p
      (fun c => (squareRootBornPartnerCount R c : ℂ)) +
    lowPrimeFreshMatchingParentMass (R - 1) p
      (fun c => (squareRootBornPostTailHighResponse R K j c : ℂ))

/-- The paired BornPostTail finite difference after restoring the matching old
parents. -/
def squareRootBornPostTailFreshPairedDifferenceLayer
    (R K j p : ℕ) : ℂ :=
  lowPrimeFreshPairedDifferenceMass (squareRootEndpoint R) p
      (fun c => (squareRootBornPartnerCount R c : ℂ)) +
    lowPrimeFreshPairedDifferenceMass (R - 1) p
      (fun c => (squareRootBornPostTailHighResponse R K j c : ℂ))

/-- The Boolean fresh layer is exactly the child half of the old-parent /
fresh-child finite difference. -/
theorem squareRootBornPostTailFreshMatchingParent_add_freshBooleanFaceLayer
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootBornPostTailFreshMatchingParentLayer R K j p +
        squareRootBornPostTailFreshBooleanFaceLayer R K j p =
      squareRootBornPostTailFreshPairedDifferenceLayer R K j p := by
  have hborn := lowPrimeFreshMatchingParent_add_child_eq_pairedDifference
    (squareRootEndpoint R) p
    (fun c => (squareRootBornPartnerCount R c : ℂ)) hp
  have hhigh := lowPrimeFreshMatchingParent_add_child_eq_pairedDifference
    (R - 1) p
    (fun c => (squareRootBornPostTailHighResponse R K j c : ℂ)) hp
  have hbornChild := lowPrimeFreshChildFaceMass_eq_indicator
    (squareRootEndpoint R) p
    (fun c => (squareRootBornPartnerCount R c : ℂ))
  have hhighChild := lowPrimeFreshChildFaceMass_eq_indicator
    (R - 1) p
    (fun c => (squareRootBornPostTailHighResponse R K j c : ℂ))
  unfold squareRootBornPostTailFreshMatchingParentLayer
    squareRootBornPostTailFreshPairedDifferenceLayer
    squareRootBornPostTailFreshBooleanFaceLayer
  rw [← hbornChild, ← hhighChild]
  linear_combination hborn + hhigh

/-- Combining BRIDGE with the parent/child split identifies the numerical prime
increment plus its matching pre-existing parent mass with the exact finite
difference layer. -/
theorem squareRootBornPostTailRunningStep_add_matchingParent_eq_pairedDifference
    (R K j p : ℕ) (hp : p.Prime) :
    (squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1)) +
      squareRootBornPostTailFreshMatchingParentLayer R K j p =
        squareRootBornPostTailFreshPairedDifferenceLayer R K j p := by
  rw [squareRootBornPostTailRunningLowPrimeResponse_step_eq_freshBooleanFaceLayer
    R K j p hp]
  rw [add_comm]
  exact squareRootBornPostTailFreshMatchingParent_add_freshBooleanFaceLayer
    R K j p hp

/-! ## The post-root finite difference is the reciprocal prime-dilate window -/

/-- Concrete prime-partner set represented by the post-root prefix response. -/
def squareRootPostRootPrimePartnerSet (R d : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun q =>
    q.Prime ∧ d * q ≤ squareRootEndpoint R

/-- The product-form partner set has exactly the cardinality used by the
existing post-root prefix response. -/
theorem card_squareRootPostRootPrimePartnerSet_eq_prefixCard
    {R d : ℕ} (hd : 0 < d) :
    (squareRootPostRootPrimePartnerSet R d).card =
      squareRootPostRootPrimePrefixCard R d := by
  classical
  unfold squareRootPostRootPrimePartnerSet squareRootPostRootPrimePrefixCard
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hRq, hqX⟩, hqPrime, hdq⟩
    have hqDiv : q ≤ squareRootEndpoint R / d := by
      apply (Nat.le_div_iff_mul_le hd).2
      simpa [Nat.mul_comm] using hdq
    exact ⟨⟨hRq, hqDiv.trans (le_max_right _ _)⟩, hqPrime⟩
  · rintro ⟨⟨hRq, hqMax⟩, hqPrime⟩
    have hqDiv : q ≤ squareRootEndpoint R / d := by
      by_cases hRD : R ≤ squareRootEndpoint R / d
      · simpa [max_eq_right hRD] using hqMax
      · have hDR : squareRootEndpoint R / d ≤ R := Nat.le_of_not_ge hRD
        have hmaxR : max R (squareRootEndpoint R / d) = R :=
          max_eq_left hDR
        rw [hmaxR] at hqMax
        omega
    have hdq : d * q ≤ squareRootEndpoint R := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hqDiv
    have hqX : q ≤ squareRootEndpoint R := by
      exact hqDiv.trans (Nat.div_le_self _ _)
    exact ⟨⟨hRq, hqX⟩, hqPrime, hdq⟩

/-- Prime sites in the exact reciprocal parent-inside/child-outside window. -/
def squareRootPrimeDilateWindowPrimeSet
    (p R a : ℕ) : Finset ℕ :=
  (primeDilateCofactorWindow p R (squareRootEndpoint R) a).filter Nat.Prime

/-- The parent post-root prime set is the disjoint union of the child set and
its reciprocal prime-dilate window. -/
theorem squareRootPostRootPrimePartnerSet_eq_child_union_window
    {p R a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    squareRootPostRootPrimePartnerSet R a =
      squareRootPostRootPrimePartnerSet R (p * a) ∪
        squareRootPrimeDilateWindowPrimeSet p R a := by
  classical
  ext q
  simp only [squareRootPostRootPrimePartnerSet,
    squareRootPrimeDilateWindowPrimeSet, Finset.mem_filter, Finset.mem_union]
  rw [mem_primeDilateCofactorWindow_iff_prefixBoundary hp ha]
  simp only [Finset.mem_Ioc]
  constructor
  · rintro ⟨hqI, hqPrime, hparent⟩
    by_cases hchild : (p * a) * q ≤ squareRootEndpoint R
    · exact Or.inl ⟨hqI, hqPrime, hchild⟩
    · exact Or.inr ⟨⟨hqI, ⟨hparent, Nat.lt_of_not_ge hchild⟩⟩, hqPrime⟩
  · rintro (⟨hqI, hqPrime, hchild⟩ | ⟨⟨hqI, hboundary⟩, hqPrime⟩)
    · have haLe : a ≤ p * a := Nat.le_mul_of_pos_left a hp.pos
      have hparent : a * q ≤ squareRootEndpoint R :=
        (Nat.mul_le_mul_right q haLe).trans hchild
      exact ⟨hqI, hqPrime, hparent⟩
    · exact ⟨hqI, hqPrime, hboundary.1⟩

/-- Child and reciprocal-window prime populations are disjoint. -/
theorem squareRootPostRootPrimePartnerSet_disjoint_window
    {p R a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    Disjoint (squareRootPostRootPrimePartnerSet R (p * a))
      (squareRootPrimeDilateWindowPrimeSet p R a) := by
  classical
  rw [Finset.disjoint_left]
  intro q hchild hwindow
  have hchildData := Finset.mem_filter.mp hchild
  have hwindowData := Finset.mem_filter.mp hwindow
  have hboundary :=
    (mem_primeDilateCofactorWindow_iff_prefixBoundary hp ha).mp hwindowData.1
  exact (Nat.not_lt_of_ge hchildData.2.2) hboundary.2.2

/-- Exact cardinality telescope for the post-root parent/child prime-prefix
response. -/
theorem squareRootPostRootPrimePrefixCard_eq_child_add_windowCard
    {p R a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    squareRootPostRootPrimePrefixCard R a =
      squareRootPostRootPrimePrefixCard R (p * a) +
        (squareRootPrimeDilateWindowPrimeSet p R a).card := by
  have hunion := squareRootPostRootPrimePartnerSet_eq_child_union_window
    (p := p) (R := R) (a := a) hp ha
  have hdisj := squareRootPostRootPrimePartnerSet_disjoint_window
    (p := p) (R := R) (a := a) hp ha
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hunion] at hcard
  rw [card_squareRootPostRootPrimePartnerSet_eq_prefixCard ha] at hcard
  have hpa : 0 < p * a := Nat.mul_pos hp.pos ha
  rw [card_squareRootPostRootPrimePartnerSet_eq_prefixCard hpa] at hcard
  exact hcard

/-- The existing complex-valued prime-dilate window count is literally the
cardinality of the concrete window prime set. -/
theorem primeDilateCofactorWindowPrimeCount_eq_windowPrimeSet_card
    (p R a : ℕ) :
    primeDilateCofactorWindowPrimeCount p R (squareRootEndpoint R) a =
      ((squareRootPrimeDilateWindowPrimeSet p R a).card : ℂ) := by
  classical
  unfold primeDilateCofactorWindowPrimeCount squareRootPrimeDilateWindowPrimeSet
    primeSievePrimeIndicator
  rw [← Finset.sum_filter]
  simp

/-- **Post-root parent minus fresh child = reciprocal-window prime count.** -/
theorem squareRootPostRootPrimePrefix_sub_child_eq_primeDilateWindow
    {p R a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    ((squareRootPostRootPrimePrefixCard R a : ℕ) : ℂ) -
        ((squareRootPostRootPrimePrefixCard R (p * a) : ℕ) : ℂ) =
      primeDilateCofactorWindowPrimeCount
        p R (squareRootEndpoint R) a := by
  have hcard := squareRootPostRootPrimePrefixCard_eq_child_add_windowCard
    (p := p) (R := R) (a := a) hp ha
  rw [primeDilateCofactorWindowPrimeCount_eq_windowPrimeSet_card]
  exact_mod_cast (show
    (squareRootPostRootPrimePrefixCard R a : ℤ) -
        (squareRootPostRootPrimePrefixCard R (p * a) : ℤ) =
      ((squareRootPrimeDilateWindowPrimeSet p R a).card : ℤ) by omega)

/-! ## Exact high-response trichotomy -/

/-- Crossing defect when an old parent is in the shallow `K` plateau but its
fresh child has crossed beyond it. -/
def squareRootBornPostTailHighTransitionDifference
    (R K j p a : ℕ) : ℂ :=
  ((squareRootBornPostTailHighResponse R K j a : ℕ) : ℂ) -
    ((squareRootBornPostTailHighResponse R K j (p * a) : ℕ) : ℂ)

/-- Below the shallow cutoff both parent and child see the same high response,
so the high-channel finite difference is exactly zero. -/
theorem squareRootBornPostTailHighResponse_sub_child_eq_zero_of_child_le_K
    {R K j p a : ℕ} (hp : p.Prime) (hchildK : p * a ≤ K) :
    ((squareRootBornPostTailHighResponse R K j a : ℕ) : ℂ) -
        ((squareRootBornPostTailHighResponse R K j (p * a) : ℕ) : ℂ) = 0 := by
  have haLe : a ≤ p * a := Nat.le_mul_of_pos_left a hp.pos
  have haK : a ≤ K := haLe.trans hchildK
  unfold squareRootBornPostTailHighResponse
  rw [if_pos haK, if_pos hchildK]
  ring

/-- Beyond `K`, the high-response parent/child finite difference is exactly the
reciprocal prime-dilate window. -/
theorem squareRootBornPostTailHighResponse_sub_child_eq_primeDilateWindow
    {R K j p a : ℕ} (hp : p.Prime) (ha : 0 < a) (hKa : K < a) :
    ((squareRootBornPostTailHighResponse R K j a : ℕ) : ℂ) -
        ((squareRootBornPostTailHighResponse R K j (p * a) : ℕ) : ℂ) =
      primeDilateCofactorWindowPrimeCount
        p R (squareRootEndpoint R) a := by
  have haNot : ¬ a ≤ K := by omega
  have haLe : a ≤ p * a := Nat.le_mul_of_pos_left a hp.pos
  have hchildNot : ¬ p * a ≤ K := by omega
  unfold squareRootBornPostTailHighResponse
  rw [if_neg haNot, if_neg hchildNot]
  exact squareRootPostRootPrimePrefix_sub_child_eq_primeDilateWindow
    (p := p) (R := R) (a := a) hp ha

/-- Complete pointwise trichotomy for the high-response finite difference.
Only the shallow transition `a <= K < p*a` is not already a pure reciprocal
window. -/
theorem squareRootBornPostTailHighResponse_sub_child_trichotomy
    {R K j p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    ((squareRootBornPostTailHighResponse R K j a : ℕ) : ℂ) -
        ((squareRootBornPostTailHighResponse R K j (p * a) : ℕ) : ℂ) =
      if p * a ≤ K then 0
      else if a ≤ K then
        squareRootBornPostTailHighTransitionDifference R K j p a
      else
        primeDilateCofactorWindowPrimeCount
          p R (squareRootEndpoint R) a := by
  by_cases hchildK : p * a ≤ K
  · rw [if_pos hchildK]
    exact squareRootBornPostTailHighResponse_sub_child_eq_zero_of_child_le_K
      hp hchildK
  · rw [if_neg hchildK]
    by_cases haK : a ≤ K
    · rw [if_pos haK]
      rfl
    · rw [if_neg haK]
      exact squareRootBornPostTailHighResponse_sub_child_eq_primeDilateWindow
        hp ha (by omega)

/-! ## Same window, literal `window - p·window` low-wheel cell -/

/-- The reciprocal window exposed by the BornPostTail high parent/child
difference is exactly the geometric window whose low-wheel mixed cell is the
undilated indicator minus its fresh-prime dilate. -/
theorem squareRootLowWheelMixedCell_eq_window_sub_pDilation
    {p R a q : ℕ} (hp : p.Prime) (ha : 0 < a) :
    lowWheelMixedPrimeCell p R (squareRootEndpoint R) q (a * q) =
      lowWheelPrimeDilateWindowIndicator
          p R (squareRootEndpoint R) a q -
        lowWheelPrimeDilateWindowIndicator
          p R (squareRootEndpoint R) a (p * q) := by
  exact lowWheelMixedPrimeCell_mul_eq_window_sub_dilate hp ha

end RHLean.Proof
