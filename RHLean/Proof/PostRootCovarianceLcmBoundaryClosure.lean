import Mathlib
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-! ## The owner descent is literally an LCM-wall descent

The scalar and complete-interior layers are now supplied by an earlier merged layer.
This file keeps only the genuinely new structural continuation: stripping the
chronological first separating prime scales the pair LCM exactly by that owner,
which turns the super-endpoint carrier into a literal first-wall-crossing
problem.  The final section records the corresponding four-corner Boolean
finite difference before any norm or multiplicity estimate is taken.
-/

private theorem lcm_prime_mul_left_of_not_dvd
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm (p * a) b = p * Nat.lcm a b := by
  apply Nat.dvd_antisymm
  · apply (Nat.lcm_dvd_iff).2
    constructor
    · exact Nat.mul_dvd_mul_left p (Nat.dvd_lcm_left a b)
    · rcases Nat.dvd_lcm_right a b with ⟨k, hk⟩
      refine ⟨p * k, ?_⟩
      rw [hk]
      ac_rfl
  · have hpTarget : p ∣ Nat.lcm (p * a) b :=
      (show p ∣ p * a from ⟨a, rfl⟩).trans (Nat.dvd_lcm_left (p * a) b)
    have haTarget : a ∣ Nat.lcm (p * a) b :=
      (show a ∣ p * a from ⟨p, by simp [Nat.mul_comm]⟩).trans
        (Nat.dvd_lcm_left (p * a) b)
    have hbTarget : b ∣ Nat.lcm (p * a) b := Nat.dvd_lcm_right (p * a) b
    have hlcmTarget : Nat.lcm a b ∣ Nat.lcm (p * a) b :=
      (Nat.lcm_dvd_iff).2 ⟨haTarget, hbTarget⟩
    have hlcmMul : Nat.lcm a b ∣ a * b := by
      apply (Nat.lcm_dvd_iff).2
      exact ⟨⟨b, rfl⟩, ⟨a, by simp [Nat.mul_comm]⟩⟩
    have hpNotLcm : ¬ p ∣ Nat.lcm a b := by
      intro hpLcm
      have hpMul : p ∣ a * b := hpLcm.trans hlcmMul
      rcases hp.dvd_mul.mp hpMul with hpA | hpB
      · exact hpa hpA
      · exact hpb hpB
    have hcop : Nat.Coprime p (Nat.lcm a b) :=
      hp.coprime_iff_not_dvd.mpr hpNotLcm
    exact hcop.mul_dvd_of_dvd_of_dvd hpTarget hlcmTarget

/-- Stripping the chronological first separating prime divides the pair LCM by
exactly that prime. -/
theorem squarefreePairFreshPrimeOwner_lcm_eq_owner_mul_parentLcm
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (hmpos : 0 < m) (hnpos : 0 < n) :
    let p := squarefreePairFreshPrimeOwner m n
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    Nat.lcm m n = p * Nat.lcm um un := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  change Nat.lcm m n = p * Nat.lcm um un
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hm hn hmn
  have hcube := squarefreePairFreshPrimeOwner_parentCube hm hn hmn hmpos hnpos
  change (¬ p ∣ um) ∧ (¬ p ∣ un) ∧
      ((m = p * um ∧ n = un) ∨ (m = um ∧ n = p * un)) at hcube
  rcases hcube with ⟨hpm, hpn, h | h⟩
  · rw [h.1, h.2]
    exact lcm_prime_mul_left_of_not_dvd hp hpm hpn
  · rw [h.1, h.2]
    calc
      Nat.lcm um (p * un) = Nat.lcm (p * un) um := Nat.lcm_comm _ _
      _ = p * Nat.lcm un um := lcm_prime_mul_left_of_not_dvd hp hpn hpm
      _ = p * Nat.lcm um un := by rw [Nat.lcm_comm un um]

/-- Reorienting the stripped parent does not change its LCM. -/
theorem squarefreePairFreshPrimeOrderedParent_lcm (m n : ℕ) :
    Nat.lcm (squarefreePairFreshPrimeOrderedParent m n).1
        (squarefreePairFreshPrimeOrderedParent m n).2 =
      Nat.lcm
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m)
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n) := by
  unfold squarefreePairFreshPrimeOrderedParent
  by_cases h :
      squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m <
        squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n
  · simp [h]
  · simp [h, Nat.lcm_comm]

/-- Ordered-parent form of the exact LCM scaling law. -/
theorem squarefreePairFreshPrimeOwner_lcm_eq_owner_mul_orderedParentLcm
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (hmpos : 0 < m) (hnpos : 0 < n) :
    Nat.lcm m n =
      squarefreePairFreshPrimeOwner m n *
        Nat.lcm (squarefreePairFreshPrimeOrderedParent m n).1
          (squarefreePairFreshPrimeOrderedParent m n).2 := by
  rw [squarefreePairFreshPrimeOrderedParent_lcm]
  exact squarefreePairFreshPrimeOwner_lcm_eq_owner_mul_parentLcm
    hm hn hmn hmpos hnpos

/-- **First LCM-wall dichotomy.**  On a nonzero boundary pair, stripping the
chronological owner either stays on the super-endpoint side or crosses the wall
for the first time.  In the crossing case the child LCM is exactly the owner
prime times the admitted parent LCM. -/
theorem postRootCovarianceRemainderBoundary_owner_parent_lcm_dichotomy
    {W m n : ℕ}
    (hboundary : (m, n) ∈ postRootCovarianceRemainderBoundaryLcmCarrier W)
    (hweight : realMoebiusStep m * realMoebiusStep n ≠ 0) :
    let p := squarefreePairFreshPrimeOwner m n
    let parent := squarefreePairFreshPrimeOrderedParent m n
    (W < Nat.lcm parent.1 parent.2) ∨
      (Nat.lcm parent.1 parent.2 ≤ W ∧
        W < p * Nat.lcm parent.1 parent.2) := by
  rcases mem_postRootCovarianceRemainderBoundaryLcmCarrier.mp hboundary with
    ⟨hremainder, hchildWall⟩
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hremainder).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, _hmW, hn1, _hnW, hmnlt⟩
  have hmstep : realMoebiusStep m ≠ 0 := by
    intro hmzero
    exact hweight (by rw [hmzero, zero_mul])
  have hnstep : realMoebiusStep n ≠ 0 := by
    intro hnzero
    exact hweight (by rw [hnzero, mul_zero])
  have hm : Squarefree m := squarefree_of_realMoebiusStep_ne_zero hmstep
  have hn : Squarefree n := squarefree_of_realMoebiusStep_ne_zero hnstep
  have hscale :=
    squarefreePairFreshPrimeOwner_lcm_eq_owner_mul_orderedParentLcm
      hm hn (Nat.ne_of_lt hmnlt) (by omega) (by omega)
  let p := squarefreePairFreshPrimeOwner m n
  let parent := squarefreePairFreshPrimeOrderedParent m n
  change (W < Nat.lcm parent.1 parent.2) ∨
    (Nat.lcm parent.1 parent.2 ≤ W ∧
      W < p * Nat.lcm parent.1 parent.2)
  by_cases hparent : W < Nat.lcm parent.1 parent.2
  · exact Or.inl hparent
  · right
    have hle : Nat.lcm parent.1 parent.2 ≤ W := Nat.le_of_not_gt hparent
    refine ⟨hle, ?_⟩
    rw [← hscale]
    exact hchildWall

/-! ## Exact four-corner finite difference at the LCM wall -/

/-- Real indicator for the literal super-endpoint LCM wall. -/
def superLcmIndicator (W m n : ℕ) : ℝ :=
  if W < Nat.lcm m n then 1 else 0

private theorem lcm_prime_mul_right_of_not_dvd
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm a (p * b) = p * Nat.lcm a b := by
  calc
    Nat.lcm a (p * b) = Nat.lcm (p * b) a := Nat.lcm_comm _ _
    _ = p * Nat.lcm b a := lcm_prime_mul_left_of_not_dvd hp hpb hpa
    _ = p * Nat.lcm a b := by rw [Nat.lcm_comm b a]

/-- **Exact one-prime LCM wall stencil.**  For a prime fresh to both parent
coordinates, the three non-base corners have common LCM `p*lcm(a,b)`.  The
complete four-corner indicator derivative therefore vanishes everywhere except
at the literal first crossing `lcm(a,b) ≤ W < p*lcm(a,b)`, where it is `-1`. -/
theorem superLcmIndicator_fourCorner_eq_firstFailure
    {W p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    superLcmIndicator W a b -
        superLcmIndicator W (p * a) b -
        superLcmIndicator W a (p * b) +
        superLcmIndicator W (p * a) (p * b) =
      if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b then -1 else 0 := by
  have hleft := lcm_prime_mul_left_of_not_dvd hp hpa hpb
  have hright := lcm_prime_mul_right_of_not_dvd hp hpa hpb
  have hboth : Nat.lcm (p * a) (p * b) = p * Nat.lcm a b := by
    rw [Nat.lcm_mul_left]
  unfold superLcmIndicator
  rw [hleft, hright, hboth]
  have hle : Nat.lcm a b ≤ p * Nat.lcm a b := by
    calc
      Nat.lcm a b = 1 * Nat.lcm a b := by simp
      _ ≤ p * Nat.lcm a b := Nat.mul_le_mul_right _ hp.one_le
  by_cases hbase : W < Nat.lcm a b
  · have hupper : W < p * Nat.lcm a b := hbase.trans_le hle
    simp [hbase, hupper]
  · have hbaseLe : Nat.lcm a b ≤ W := Nat.le_of_not_gt hbase
    by_cases hupper : W < p * Nat.lcm a b
    · simp [hbase, hbaseLe, hupper]
    · simp [hbase, hupper]

/-- **Möbius-weighted first-failure stencil.**  Fresh-prime sign reversal turns
the four physical pair corners into the Boolean derivative above.  Thus a full
Euler square contributes exactly zero away from the first LCM wall and exactly
minus its old pair weight on that wall. -/
theorem realMoebiusSuperLcmFourCorner_eq_firstFailure
    {W p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    (realMoebiusStep a * realMoebiusStep b) * superLcmIndicator W a b +
      (realMoebiusStep (p * a) * realMoebiusStep b) *
        superLcmIndicator W (p * a) b +
      (realMoebiusStep a * realMoebiusStep (p * b)) *
        superLcmIndicator W a (p * b) +
      (realMoebiusStep (p * a) * realMoebiusStep (p * b)) *
        superLcmIndicator W (p * a) (p * b) =
      if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b then
        -(realMoebiusStep a * realMoebiusStep b)
      else 0 := by
  rw [realMoebiusStep_mul_prime_eq_neg hp hpa,
    realMoebiusStep_mul_prime_eq_neg hp hpb]
  have hwall := superLcmIndicator_fourCorner_eq_firstFailure
    (W := W) hp hpa hpb
  by_cases hcross : Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b
  · rw [if_pos hcross] at hwall ⊢
    linear_combination (realMoebiusStep a * realMoebiusStep b) * hwall
  · rw [if_neg hcross] at hwall ⊢
    linear_combination (realMoebiusStep a * realMoebiusStep b) * hwall

/-! ## Retain the physical endpoint when recombining the LCM wall

The uncut stencil above does not by itself describe a physical prefix: a
corner can lie beyond `W`.  Clipping the same symmetric LCM kernel leaves a
positive top escape as well as the negative first crossing.  Keeping both
terms is necessary before aggregating any owner cubes.
-/

/-- The super-LCM kernel with both physical endpoint cutoffs retained.  It is
symmetric, so a crossed pair is counted in its positive orientation. -/
def physicalSuperLcmIndicator (W m n : ℕ) : ℝ :=
  if m ≤ W ∧ n ≤ W then superLcmIndicator W m n else 0

/-- **Physical LCM stencil.**  After reorienting a fresh parent pair `a ≤ b`,
the exact residue is top escape minus admitted first LCM crossing. -/
theorem physicalSuperLcmIndicator_fourCorner_eq_walls
    {W p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) :
    physicalSuperLcmIndicator W a b -
        physicalSuperLcmIndicator W (p * a) b -
        physicalSuperLcmIndicator W a (p * b) +
        physicalSuperLcmIndicator W (p * a) (p * b) =
      (if W < Nat.lcm a b ∧ W < p * a then 1 else 0) -
        (if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
          then 1 else 0) := by
  have haW : a ≤ W := hab.trans hbW
  have hleft := lcm_prime_mul_left_of_not_dvd hp hpa hpb
  have hright := lcm_prime_mul_right_of_not_dvd hp hpa hpb
  have hboth : Nat.lcm (p * a) (p * b) = p * Nat.lcm a b :=
    by rw [Nat.lcm_mul_left]
  have hcancel : physicalSuperLcmIndicator W a (p * b) =
      physicalSuperLcmIndicator W (p * a) (p * b) := by
    unfold physicalSuperLcmIndicator superLcmIndicator
    rw [hright, hboth]
    by_cases hpbW : p * b ≤ W
    · have hpaW : p * a ≤ W := (Nat.mul_le_mul_left p hab).trans hpbW
      simp [haW, hpbW, hpaW]
    · simp [hpbW]
  have hreduce :
      physicalSuperLcmIndicator W a b -
          physicalSuperLcmIndicator W (p * a) b -
          physicalSuperLcmIndicator W a (p * b) +
          physicalSuperLcmIndicator W (p * a) (p * b) =
        superLcmIndicator W a b -
          (if p * a ≤ W then superLcmIndicator W (p * a) b else 0) := by
    rw [hcancel]
    simp [physicalSuperLcmIndicator, haW, hbW]
  rw [hreduce]
  have hL : Nat.lcm a b ≤ p * Nat.lcm a b := by
    simpa using Nat.mul_le_mul_right (Nat.lcm a b) hp.one_le
  by_cases hpaW : p * a ≤ W
  · have hnotTop : ¬ W < p * a := Nat.not_lt.mpr hpaW
    by_cases hbase : W < Nat.lcm a b
    · have hupper : W < p * Nat.lcm a b := hbase.trans_le hL
      simp [superLcmIndicator, hleft, hpaW, hnotTop, hbase, hupper]
    · have hbaseLe : Nat.lcm a b ≤ W := Nat.le_of_not_gt hbase
      by_cases hupper : W < p * Nat.lcm a b
      · simp [superLcmIndicator, hleft, hpaW, hnotTop, hbase, hbaseLe, hupper]
      · simp [superLcmIndicator, hleft, hpaW, hnotTop, hbase, hupper]
  · have htop : W < p * a := Nat.lt_of_not_ge hpaW
    simp [superLcmIndicator, hpaW, htop]

/-- Signed mass of one physical fresh-prime LCM cube, with each corner clipped
at the actual prefix endpoint. -/
def realMoebiusPhysicalSuperLcmFourCorner (W p a b : ℕ) : ℝ :=
  (realMoebiusStep a * realMoebiusStep b) * physicalSuperLcmIndicator W a b +
    (realMoebiusStep (p * a) * realMoebiusStep b) *
      physicalSuperLcmIndicator W (p * a) b +
    (realMoebiusStep a * realMoebiusStep (p * b)) *
      physicalSuperLcmIndicator W a (p * b) +
    (realMoebiusStep (p * a) * realMoebiusStep (p * b)) *
      physicalSuperLcmIndicator W (p * a) (p * b)

/-- Fresh-prime signs retain both physical walls on the same old pair weight. -/
theorem realMoebiusPhysicalSuperLcmFourCorner_eq_walls
    {W p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) :
    realMoebiusPhysicalSuperLcmFourCorner W p a b =
      (realMoebiusStep a * realMoebiusStep b) *
        ((if W < Nat.lcm a b ∧ W < p * a then 1 else 0) -
          (if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
            then 1 else 0)) := by
  unfold realMoebiusPhysicalSuperLcmFourCorner
  rw [realMoebiusStep_mul_prime_eq_neg hp hpa,
    realMoebiusStep_mul_prime_eq_neg hp hpb]
  have hwall := physicalSuperLcmIndicator_fourCorner_eq_walls hp hpa hpb hab hbW
  linear_combination (realMoebiusStep a * realMoebiusStep b) * hwall

/-- Finite signed recombination on any physical fresh-parent carrier.  The top
escape stays explicit; there is no conversion to a support count. -/
theorem sum_realMoebiusPhysicalSuperLcmFourCorner_eq_walls
    {W p : ℕ} (S : Finset (ℕ × ℕ)) (hp : p.Prime)
    (hS : ∀ mn ∈ S,
      mn.1 ≤ mn.2 ∧ mn.2 ≤ W ∧ ¬ p ∣ mn.1 ∧ ¬ p ∣ mn.2) :
    (∑ mn ∈ S, realMoebiusPhysicalSuperLcmFourCorner W p mn.1 mn.2) =
      (∑ mn ∈ S, (realMoebiusStep mn.1 * realMoebiusStep mn.2) *
        (if W < Nat.lcm mn.1 mn.2 ∧ W < p * mn.1 then 1 else 0)) -
      ∑ mn ∈ S, (realMoebiusStep mn.1 * realMoebiusStep mn.2) *
        (if Nat.lcm mn.1 mn.2 ≤ W ∧
            W < p * Nat.lcm mn.1 mn.2 ∧ p * mn.1 ≤ W then 1 else 0) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mn hmn
  rcases hS mn hmn with ⟨hab, hbW, hpa, hpb⟩
  rw [realMoebiusPhysicalSuperLcmFourCorner_eq_walls hp hpa hpb hab hbW, mul_sub]

/-- The physical top escape is real: the uncut stencil cancels at this cell,
but clipping leaves the base pair.  Thus the extra term cannot be discarded. -/
theorem physicalSuperLcmIndicator_topEscape_example :
    physicalSuperLcmIndicator 5 2 5 -
        physicalSuperLcmIndicator 5 (3 * 2) 5 -
        physicalSuperLcmIndicator 5 2 (3 * 5) +
        physicalSuperLcmIndicator 5 (3 * 2) (3 * 5) = 1 := by
  norm_num [physicalSuperLcmIndicator, superLcmIndicator, Nat.lcm]

/-! ## Complete post-root cubes have a nonpositive signed total -/

/-- The scalar boundary kernel is the literal physical super-LCM pair sum. -/
theorem fullLcmBoundaryKernel_eq_sum_superLcmIndicator (W : ℕ) :
    fullLcmBoundaryKernel W =
      ∑ mn ∈ mertensPositivePhysicalPairCarrier W,
        (realMoebiusStep mn.1 * realMoebiusStep mn.2) *
          superLcmIndicator W mn.1 mn.2 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (mertensPositivePhysicalPairCarrier W)
    (fun mn : ℕ × ℕ => Nat.lcm mn.1 mn.2 ≤ W)
    (fun mn : ℕ × ℕ => realMoebiusStep mn.1 * realMoebiusStep mn.2)
  rw [sum_mertensPositivePhysicalPairCarrier_eq_positiveLagPairSum] at hsplit
  have hinterior := moebiusLcmInteriorPositiveCarrier_eq_filter W
  rw [← hinterior] at hsplit
  have hboundary :
      (∑ mn ∈ (mertensPositivePhysicalPairCarrier W).filter
          (fun mn => ¬ Nat.lcm mn.1 mn.2 ≤ W),
        realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      ∑ mn ∈ mertensPositivePhysicalPairCarrier W,
        (realMoebiusStep mn.1 * realMoebiusStep mn.2) *
          superLcmIndicator W mn.1 mn.2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro mn _hmn
    simp [superLcmIndicator, mul_ite]
  rw [hboundary] at hsplit
  unfold fullLcmBoundaryKernel
  linarith

/-- **Boundary positivity from integrality.**  Its exact scalar value is
`M(W) * (M(W)-1) / 2`, which is nonnegative for every integer Mertens value.
No Mertens magnitude estimate is used. -/
theorem fullLcmBoundaryKernel_nonneg (W : ℕ) :
    0 ≤ fullLcmBoundaryKernel W := by
  let z : ℤ := ∑ n ∈ Finset.range (W + 1), μ n
  have hzcast : (z : ℝ) = realMertensLength (W + 1) := by
    simp [z, realMertensLength, realMoebiusStep]
  have hquad : 0 ≤ (z : ℝ) ^ 2 - (z : ℝ) := by
    have hz : z ≤ 0 ∨ 1 ≤ z := by omega
    rcases hz with hz | hz
    · have hzreal : (z : ℝ) ≤ 0 := by exact_mod_cast hz
      nlinarith [sq_nonneg (z : ℝ)]
    · have hzreal : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
      nlinarith [sq_nonneg ((z : ℝ) - 1)]
  rw [hzcast] at hquad
  have hid := two_mul_fullLcmBoundaryKernel_eq_length_sq_sub_length W
  linarith

/-- A complete post-root parent cube has no physical top escape.  Its first
LCM crossing is precisely the super-LCM kernel at the quotient endpoint. -/
theorem realMoebiusPhysicalSuperLcmFourCorner_postRoot_eq_neg_lower
    {W p a b : ℕ} (hp : p ∈ postRootPrimeFamilySet W)
    (hab : (a, b) ∈ mertensPositivePhysicalPairCarrier (W / p)) :
    realMoebiusPhysicalSuperLcmFourCorner W p a b =
      -((realMoebiusStep a * realMoebiusStep b) *
        superLcmIndicator (W / p) a b) := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  rcases mem_mertensPositivePhysicalPairCarrier.mp hab with
    ⟨ha1, haq, hb1, hbq, hablt⟩
  have hqLt : W / p < p :=
    (Nat.div_lt_iff_lt_mul hpPrime.pos).2 ((Nat.sqrt_lt).1 hpRoot)
  have hpa : ¬ p ∣ a := by
    intro hdiv
    exact (not_le.mpr (haq.trans_lt hqLt)) (Nat.le_of_dvd ha1 hdiv)
  have hpb : ¬ p ∣ b := by
    intro hdiv
    exact (not_le.mpr (hbq.trans_lt hqLt)) (Nat.le_of_dvd hb1 hdiv)
  have hqW : W / p ≤ W := Nat.div_le_self W p
  have hpaW : p * a ≤ W := by
    calc
      p * a ≤ p * (W / p) := Nat.mul_le_mul_left p haq
      _ ≤ W := by simpa [Nat.mul_comm] using Nat.div_mul_le_self W p
  have hlcmDvd : Nat.lcm a b ∣ a * b :=
    Nat.lcm_dvd_iff.mpr ⟨⟨b, rfl⟩, ⟨a, by ring⟩⟩
  have hL : Nat.lcm a b ≤ W := by
    calc
      Nat.lcm a b ≤ a * b := Nat.le_of_dvd (Nat.mul_pos ha1 hb1) hlcmDvd
      _ ≤ (W / p) * (W / p) := Nat.mul_le_mul haq hbq
      _ = (W / p) ^ 2 := by ring
      _ ≤ W := postRootPrimeFamily_quotient_sq_le hp
  have hcross : W < p * Nat.lcm a b ↔ W / p < Nat.lcm a b := by
    simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul hpPrime.pos :
        W / p < Nat.lcm a b ↔ W < Nat.lcm a b * p).symm
  rw [realMoebiusPhysicalSuperLcmFourCorner_eq_walls
    hpPrime hpa hpb hablt.le (hbq.trans hqW)]
  simp [Nat.not_lt.mpr hpaW, hL, hpaW, hcross, superLcmIndicator]

/-- **Complete post-root cube collapse on the physical carrier.**  The whole
signed family of parent cubes equals minus one lower boundary kernel. -/
theorem sum_realMoebiusPhysicalSuperLcmFourCorner_postRoot_eq_neg_lower
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
      realMoebiusPhysicalSuperLcmFourCorner W p mn.1 mn.2) =
        -fullLcmBoundaryKernel (W / p) := by
  rw [fullLcmBoundaryKernel_eq_sum_superLcmIndicator, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mn hmn
  exact realMoebiusPhysicalSuperLcmFourCorner_postRoot_eq_neg_lower hp hmn

/-- **Unconditional signed inequality.**  Complete post-root parent cubes
cannot contribute positively to the LCM boundary.  Cubes clipped outside this
lower parent carrier still retain the explicit physical top-escape term. -/
theorem sum_realMoebiusPhysicalSuperLcmFourCorner_postRoot_nonpos
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
      realMoebiusPhysicalSuperLcmFourCorner W p mn.1 mn.2) ≤ 0 := by
  rw [sum_realMoebiusPhysicalSuperLcmFourCorner_postRoot_eq_neg_lower hp]
  exact neg_nonpos.mpr (fullLcmBoundaryKernel_nonneg (W / p))

end RHLean.Proof
