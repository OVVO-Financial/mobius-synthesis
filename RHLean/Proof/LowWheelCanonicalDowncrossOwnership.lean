import Mathlib
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Proof.LowWheelCanonicalDefectReduction

/-!
# Canonical ownership of the remaining low-wheel downcross ledger

The endpoint identity has already reduced the square prefix to

`M(R^2-1) = M(R) - lowWheelCanonicalDowncrossLedger R`.

This file does not estimate that ledger. It exposes the canonical parent
coordinate of every surviving first-failure state and splits the ledger before
any absolute value.

For a downcross state `(t,(c,k))`, let

`p = minFac(c*k)`

and

`a = P(t) * (k/p)`.

The defining geometry is exactly

`a <= R < p*a`,

while the square ceiling becomes

`c*p*a <= R^2-1`.

Thus every state has a literal root-side parent `a <= R`. We then split the
carrier according to whether that parent still has a prime factor at least the
pivot `p`. On the complementary oriented population all parent primes are
strictly below `p`; the canonical-pivot condition then forces `k = p`.
Consequently that population is the genuine monotone Euler first-crossing
shape: every face prime is below `p`, while every prime factor of the squarefree
cofactor `c` is above `p`.

No norm, PNT estimate, recursive `F_{r^-}` descent, or asymptotic input appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

namespace LowWheelCanonicalDowncrossOwnership

/-- Canonical prime attached to one cofactor/quotient state. -/
def lowWheelCanonicalDowncrossPivot
    (x : LowWheelCofactorQuotientState) : ℕ :=
  lowWheelCanonicalCofactorQuotientPivot x

/-- Root-side parent coordinate of one tagged downcross state. -/
def lowWheelCanonicalDowncrossParent
    (t : Finset ℕ) (x : LowWheelCofactorQuotientState) : ℕ :=
  primeFaceProduct t *
    (x.2 / lowWheelCanonicalDowncrossPivot x)

/-- The root-crossing child reconstructed from the parent and canonical pivot. -/
def lowWheelCanonicalDowncrossChild
    (t : Finset ℕ) (x : LowWheelCofactorQuotientState) : ℕ :=
  lowWheelCanonicalDowncrossPivot x * lowWheelCanonicalDowncrossParent t x

/-- Every surviving downcross state carries one exact adjacent first-failure
edge `a <= R < p*a`, and the complete physical product is `c*p*a`. -/
theorem lowWheelCanonicalDowncross_firstFailure_geometry
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossPart R t) :
    let p := lowWheelCanonicalDowncrossPivot (c, k)
    let a := lowWheelCanonicalDowncrossParent t (c, k)
    p.Prime ∧
      ¬ p ∣ c ∧
      p ∣ k ∧
      a ≤ R ∧
      R < p * a ∧
      c * (p * a) ≤ squareRootEndpoint R := by
  rcases lowWheelCanonicalDowncrossPart_adjacent_shell hx with
    ⟨hp, hpc, hpk, hparent, hchild⟩
  have hxF := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  have htop := hcarrier.2.2.2
  have hkCancel :
      lowWheelCanonicalCofactorQuotientPivot (c, k) *
          (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) = k :=
    Nat.mul_div_cancel' hpk
  dsimp [lowWheelCanonicalDowncrossPivot, lowWheelCanonicalDowncrossParent]
  refine ⟨hp, hpc, hpk, hparent, ?_, ?_⟩
  · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hchild
  · calc
      c * (lowWheelCanonicalCofactorQuotientPivot (c, k) *
          (primeFaceProduct t *
            (k / lowWheelCanonicalCofactorQuotientPivot (c, k)))) =
          (c * primeFaceProduct t) *
            (lowWheelCanonicalCofactorQuotientPivot (c, k) *
              (k / lowWheelCanonicalCofactorQuotientPivot (c, k))) := by ring
      _ = (c * primeFaceProduct t) * k := by rw [hkCancel]
      _ ≤ squareRootEndpoint R := htop

/-- The canonical root-side parent is positive. -/
theorem lowWheelCanonicalDowncrossParent_pos
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossPart R t) :
    0 < lowWheelCanonicalDowncrossParent t (c, k) := by
  have h := lowWheelCanonicalDowncross_firstFailure_geometry hx
  dsimp only at h
  have hcross := h.2.2.2.2.1
  by_contra hnot
  have hzero : lowWheelCanonicalDowncrossParent t (c, k) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hzero] at hcross
  simp at hcross

/-- Population whose root-side parent still contains a prime coordinate not
strictly below the canonical pivot. This is the face/quotient duplication
population which must earn an exact sign-reversing partner. -/
def lowWheelCanonicalDowncrossLateParentPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalDowncrossPart R t).filter fun x =>
    ∃ q ∈ (lowWheelCanonicalDowncrossParent t x).primeFactors,
      lowWheelCanonicalDowncrossPivot x ≤ q

/-- Complementary population: every prime factor of the root-side parent lies
strictly below the canonical pivot. -/
def lowWheelCanonicalDowncrossOrientedPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalDowncrossPart R t).filter fun x =>
    ∀ q ∈ (lowWheelCanonicalDowncrossParent t x).primeFactors,
      q < lowWheelCanonicalDowncrossPivot x

@[simp] theorem mem_lowWheelCanonicalDowncrossLateParentPart
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelCanonicalDowncrossLateParentPart R t ↔
      x ∈ lowWheelCanonicalDowncrossPart R t ∧
      ∃ q ∈ (lowWheelCanonicalDowncrossParent t x).primeFactors,
        lowWheelCanonicalDowncrossPivot x ≤ q := by
  simp [lowWheelCanonicalDowncrossLateParentPart]

@[simp] theorem mem_lowWheelCanonicalDowncrossOrientedPart
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelCanonicalDowncrossOrientedPart R t ↔
      x ∈ lowWheelCanonicalDowncrossPart R t ∧
      ∀ q ∈ (lowWheelCanonicalDowncrossParent t x).primeFactors,
        q < lowWheelCanonicalDowncrossPivot x := by
  simp [lowWheelCanonicalDowncrossOrientedPart]

/-- The two named first-failure populations partition the complete downcross
carrier for each Boolean face. -/
theorem lowWheelCanonicalDowncross_late_union_oriented
    (R : ℕ) (t : Finset ℕ) :
    lowWheelCanonicalDowncrossLateParentPart R t ∪
      lowWheelCanonicalDowncrossOrientedPart R t =
        lowWheelCanonicalDowncrossPart R t := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (mem_lowWheelCanonicalDowncrossLateParentPart.mp hx).1
    · exact (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  · intro hx
    by_cases hlate :
        ∃ q ∈ (lowWheelCanonicalDowncrossParent t x).primeFactors,
          lowWheelCanonicalDowncrossPivot x ≤ q
    · exact Finset.mem_union.mpr <| Or.inl <|
        mem_lowWheelCanonicalDowncrossLateParentPart.mpr ⟨hx, hlate⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        mem_lowWheelCanonicalDowncrossOrientedPart.mpr ⟨hx, by
          intro q hq
          have hnot : ¬ lowWheelCanonicalDowncrossPivot x ≤ q := by
            intro hpq
            exact hlate ⟨q, hq, hpq⟩
          omega⟩

/-- The two named populations are disjoint. -/
theorem lowWheelCanonicalDowncross_late_disjoint_oriented
    (R : ℕ) (t : Finset ℕ) :
    Disjoint
      (lowWheelCanonicalDowncrossLateParentPart R t)
      (lowWheelCanonicalDowncrossOrientedPart R t) := by
  classical
  rw [Finset.disjoint_left]
  intro x hlate horiented
  rcases (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).2 with
    ⟨q, hq, hpq⟩
  have hqp :=
    (mem_lowWheelCanonicalDowncrossOrientedPart.mp horiented).2 q hq
  omega

/-- Signed late-parent subledger. -/
def lowWheelCanonicalDowncrossLateParentLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelCanonicalDowncrossLateParentPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- Signed canonically oriented first-crossing subledger. -/
def lowWheelCanonicalDowncrossOrientedLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelCanonicalDowncrossOrientedPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- Exact signed decomposition of the global boundary. No magnitude has been
taken: the only two remaining obligations are the face/quotient late-parent
population and the genuinely ordered Euler first-crossing population. -/
theorem lowWheelCanonicalDowncrossLedger_eq_late_add_oriented
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      lowWheelCanonicalDowncrossLateParentLedger R +
        lowWheelCanonicalDowncrossOrientedLedger R := by
  unfold lowWheelCanonicalDowncrossLedger
    lowWheelCanonicalDowncrossLateParentLedger
    lowWheelCanonicalDowncrossOrientedLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [← Finset.sum_union
      (lowWheelCanonicalDowncross_late_disjoint_oriented R t),
    lowWheelCanonicalDowncross_late_union_oriented R t]

/-- On the oriented population the residual quotient contains no factor beyond
the canonical pivot: `k = p`. Any nontrivial `k/p` would contribute a prime
factor to the root parent which is at least the least prime `p`, contradicting
orientation. -/
theorem lowWheelCanonicalDowncrossOriented_quotient_eq_pivot
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedPart R t) :
    k = lowWheelCanonicalDowncrossPivot (c, k) := by
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have horiented := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).2
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  let p := lowWheelCanonicalDowncrossPivot (c, k)
  let u := k / p
  have hp : p.Prime := by simpa [p] using hgeom.1
  have hpk : p ∣ k := by simpa [p] using hgeom.2.2.1
  have hkCancel : p * u = k := by
    simpa [u, p] using Nat.mul_div_cancel' hpk
  by_cases hu : u = 1
  · have hpkEq : p = k := by simpa [hu] using hkCancel
    simpa [p] using hpkEq.symm
  · exfalso
    have hqPrime : (Nat.minFac u).Prime := Nat.minFac_prime hu
    have hqDvdU : Nat.minFac u ∣ u := Nat.minFac_dvd u
    have hqDvdK : Nat.minFac u ∣ k := by
      rw [← hkCancel]
      exact dvd_mul_of_dvd_right hqDvdU p
    have hqDvdProd : Nat.minFac u ∣ c * k :=
      dvd_mul_of_dvd_right hqDvdK c
    have hpLeQ : p ≤ Nat.minFac u := by
      change Nat.minFac (c * k) ≤ Nat.minFac u
      exact Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
    have hqDvdParent : Nat.minFac u ∣
        lowWheelCanonicalDowncrossParent t (c, k) := by
      unfold lowWheelCanonicalDowncrossParent lowWheelCanonicalDowncrossPivot
      exact dvd_mul_of_dvd_right hqDvdU (primeFaceProduct t)
    have hparentPos := lowWheelCanonicalDowncrossParent_pos hdown
    have hqMem : Nat.minFac u ∈
        (lowWheelCanonicalDowncrossParent t (c, k)).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hqPrime, hqDvdParent, Nat.ne_of_gt hparentPos⟩
    have hqLtP := horiented (Nat.minFac u) hqMem
    exact (not_lt_of_ge hpLeQ) hqLtP

/-- Hence the root-side parent of an oriented state is literally its face
product. -/
theorem lowWheelCanonicalDowncrossOriented_parent_eq_faceProduct
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedPart R t) :
    lowWheelCanonicalDowncrossParent t (c, k) = primeFaceProduct t := by
  have hq := lowWheelCanonicalDowncrossOriented_quotient_eq_pivot hx
  have hp :=
    (lowWheelCanonicalDowncross_firstFailure_geometry
      (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1).1
  have hk0 : k ≠ 0 := by
    rw [hq]
    exact hp.ne_zero
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  unfold lowWheelCanonicalDowncrossParent
  rw [hq.symm]
  rw [Nat.div_self hkpos, Nat.mul_one]

/-- Every Boolean-face prime in an oriented state is strictly below the fresh
crossing pivot. -/
theorem lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot
    {R c k q : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedPart R t)
    (hq : q ∈ t) :
    q < lowWheelCanonicalDowncrossPivot (c, k) := by
  have hparent := lowWheelCanonicalDowncrossOriented_parent_eq_faceProduct hx
  have hqPrime : q.Prime :=
    prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hq)
  have hqDvdFace : q ∣ primeFaceProduct t := by
    simpa [primeFaceProduct] using Finset.dvd_prod_of_mem id hq
  have hqDvdParent : q ∣ lowWheelCanonicalDowncrossParent t (c, k) := by
    rw [hparent]
    exact hqDvdFace
  have hparentPos :=
    lowWheelCanonicalDowncrossParent_pos
      (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have hqMem : q ∈
      (lowWheelCanonicalDowncrossParent t (c, k)).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hqPrime, hqDvdParent, Nat.ne_of_gt hparentPos⟩
  exact (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).2 q hqMem

/-- Prime factors of the squarefree cofactor lie strictly above the oriented
crossing pivot. -/
theorem lowWheelCanonicalDowncrossOriented_cofactor_roughAbove
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedPart R t) :
    RoughAbove (lowWheelCanonicalDowncrossPivot (c, k)) c := by
  intro q hq
  have hqData := Nat.mem_primeFactors.mp hq
  rcases hqData with ⟨hqPrime, hqDvd, _hc0⟩
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hpc := hgeom.2.1
  have hpLeQ : lowWheelCanonicalDowncrossPivot (c, k) ≤ q := by
    change Nat.minFac (c * k) ≤ q
    exact Nat.minFac_le_of_dvd hqPrime.two_le
      (dvd_mul_of_dvd_left hqDvd k)
  have hne : q ≠ lowWheelCanonicalDowncrossPivot (c, k) := by
    intro heq
    subst q
    exact hpc hqDvd
  omega

end LowWheelCanonicalDowncrossOwnership

end RHLean.Proof