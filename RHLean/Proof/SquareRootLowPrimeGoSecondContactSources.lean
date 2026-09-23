import Mathlib
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope

/-!
# Global second-contact source form of the Go square residual

The square-dilated Go residual at owner `q` is not an externally indexed error.
Its old cofactor `c` produces the actual arithmetic child

`m = q*c`.

Because `P+(c) < q`, the fresh prime is recovered from the child as
`P+(m) = q`, and the canonical cofactor is recovered as `c`.  Moreover the
Möbius sign flips.  Consequently

`F_{q^-}(X/q^2) = - sum_{m in C_q(X)} mu(m)`

on the native arithmetic child population `C_q(X)`.

The child populations for distinct prime owners are already pairwise disjoint.
Therefore summing the Go square residuals over any finite owner set recombines
*before taking a norm* into one Möbius sum over the disjoint union of actual
second-contact sources.  There is no residual multiplicity in the prime
coordinate: it is encoded by `P+(m)`.

The final section records the quantitative consequence of this exact
reassembly.  Every child satisfies `q*m <= X`, while every prime owner has
`q >= 2`; hence every child lies at the strict half-scale `m <= X/2`.
Because the owner fibres are already disjoint, the *whole* square-residual
cascade has support of cardinality at most `X/2` before any absolute value is
taken.  This is the discrete scale-flux contraction needed by the saturated
second-contact descent.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The arithmetic child set is exactly the image of the smooth cofactor set
under the fresh-prime extension `c ↦ q*c`. -/
theorem squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage
    {q X : ℕ} (hq : q.Prime) :
    squareRootLowPrimeGoWallSquareResidualChildren q X =
      (squareRootLowPrimeGoSmoothCofactors q (X / (q * q))).image
        (fun c => q * c) := by
  rw [← squareRootLowPrimeGoWallSquareResidualFaces_image_eq_smoothCofactors hq]
  unfold squareRootLowPrimeGoWallSquareResidualChildren
  rw [Finset.image_image]
  rfl

/-- The unique child retains both canonical coordinates of the Go extension. -/
theorem squareRootLowPrimeGoWallSquareResidualChild_coordinates
    {q X m : ℕ} (hq : q.Prime)
    (hm : m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X) :
    canonicalLargestPrimeFactor m = q ∧
      q * canonicalCofactor m = m := by
  have howner := squareRootLowPrimeGoWallSquareResidualChild_owner hq hm
  rcases mem_squareRootLowPrimeGoWallSquareResidualChildren.mp hm with
    ⟨u, hu, rfl⟩
  have huData := mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu
  have hcPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset huData.1
  have hrough :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hq huData.1
  have hcofactor : canonicalCofactor (q * primeFaceProduct u) = primeFaceProduct u := by
    simpa [Nat.mul_comm] using
      canonicalCofactor_mul_prime_eq_of_rough hcPos hq hrough
  constructor
  · simpa using howner
  · rw [hcofactor]

/-- **One-owner signed second-contact form.**  The frozen predecessor residual
is the negative Möbius mass of its actual arithmetic children. -/
theorem squareRootLowPrimeGoWallSquareResidual_cast_eq_neg_childMass
    {q X : ℕ} (hq : q.Prime) :
    (((squareRootLowPrimeGoWallSquareResidual q X : ℤ) : ℂ)) =
      -∑ m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X,
        canonicalMoebiusWeight m := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum hq,
    squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq]
  let S := squareRootLowPrimeGoSmoothCofactors q (X / (q * q))
  have himage :
      (∑ m ∈ S.image (fun c => q * c), canonicalMoebiusWeight m) =
        ∑ c ∈ S, canonicalMoebiusWeight (q * c) := by
    apply Finset.sum_image
    intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left hq.pos hab
  have hcast :
      (((∑ c ∈ S, μ c : ℤ) : ℂ)) =
        ∑ c ∈ S, canonicalMoebiusWeight c := by
    unfold canonicalMoebiusWeight
    push_cast
    rfl
  rw [show squareRootLowPrimeGoSmoothCofactors q (X / (q * q)) = S by rfl]
  rw [hcast, himage]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hcData := mem_squareRootLowPrimeGoSmoothCofactors.mp hc
  have hcPos : 0 < c := by omega
  have hflip :
      canonicalMoebiusWeight (q * c) = -canonicalMoebiusWeight c := by
    simpa [Nat.mul_comm] using
      canonicalMoebiusWeight_mul_prime_eq_neg_of_rough
        hcPos hq hcData.2.2.2
  rw [hflip]
  ring

/-- Any finite prime owner schedule may be recombined into one arithmetic
second-contact source population. -/
def squareRootLowPrimeGoSecondContactSources
    (Q : Finset ℕ) (X : ℕ) : Finset ℕ :=
  Q.biUnion fun q => squareRootLowPrimeGoWallSquareResidualChildren q X

/-- Signed sum of the square residuals over one finite owner schedule. -/
def squareRootLowPrimeGoWallSquareResidualTotal
    (Q : Finset ℕ) (X : ℕ) : ℤ :=
  ∑ q ∈ Q, squareRootLowPrimeGoWallSquareResidual q X

/-- **Global signed recombination.**  For a prime owner schedule, all square
residuals combine exactly into one Möbius sum over a disjoint arithmetic source
set.  In particular, no `sum_q |F_q|` triangle inequality is taken. -/
theorem squareRootLowPrimeGoWallSquareResidualTotal_cast_eq_neg_sourceMass
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    (((squareRootLowPrimeGoWallSquareResidualTotal Q X : ℤ) : ℂ)) =
      -∑ m ∈ squareRootLowPrimeGoSecondContactSources Q X,
        canonicalMoebiusWeight m := by
  have hdisj :=
    squareRootLowPrimeGoWallSquareResidualChildren_pairwiseDisjoint Q X hprime
  have hunion :
      (∑ m ∈ squareRootLowPrimeGoSecondContactSources Q X,
          canonicalMoebiusWeight m) =
        ∑ q ∈ Q,
          ∑ m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X,
            canonicalMoebiusWeight m := by
    unfold squareRootLowPrimeGoSecondContactSources
    exact Finset.sum_biUnion hdisj
  unfold squareRootLowPrimeGoWallSquareResidualTotal
  push_cast
  calc
    (∑ q ∈ Q, (((squareRootLowPrimeGoWallSquareResidual q X : ℤ) : ℂ))) =
        ∑ q ∈ Q,
          -∑ m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X,
            canonicalMoebiusWeight m := by
      apply Finset.sum_congr rfl
      intro q hqQ
      exact squareRootLowPrimeGoWallSquareResidual_cast_eq_neg_childMass
        (hprime q hqQ)
    _ = -∑ q ∈ Q,
          ∑ m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X,
            canonicalMoebiusWeight m := by
      rw [Finset.sum_neg_distrib]
    _ = -∑ m ∈ squareRootLowPrimeGoSecondContactSources Q X,
          canonicalMoebiusWeight m := by rw [hunion]

/-- Membership in the global source set remembers a unique prime owner. -/
theorem squareRootLowPrimeGoSecondContactSource_owner_exists
    {Q : Finset ℕ} {X m : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime)
    (hm : m ∈ squareRootLowPrimeGoSecondContactSources Q X) :
    canonicalLargestPrimeFactor m ∈ Q ∧
      canonicalLargestPrimeFactor m * m ≤ X := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hqPrime := hprime q hqQ
  have howner := squareRootLowPrimeGoWallSquareResidualChild_owner hqPrime hmq
  have hcontact :=
    squareRootLowPrimeGoWallSquareResidualChild_owner_mul_le hqPrime hmq
  constructor
  · simpa [howner] using hqQ
  · simpa [howner] using hcontact

/-! ## Half-scale flux contraction -/

/-- **Global half-scale support.**  Once all square-residual owner fibres have
been recombined, every surviving arithmetic child lies below `X/2`.  This is a
property of the whole signed carrier, not a sum of ownerwise bounds. -/
theorem squareRootLowPrimeGoSecondContactSources_subset_halfScale
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    squareRootLowPrimeGoSecondContactSources Q X ⊆ Finset.Icc 1 (X / 2) := by
  intro m hm
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hqPrime := hprime q hqQ
  have hcontact :=
    squareRootLowPrimeGoWallSquareResidualChild_owner_mul_le hqPrime hmq
  rcases mem_squareRootLowPrimeGoWallSquareResidualChildren.mp hmq with
    ⟨u, hu, hchild⟩
  have huPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset
      (mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu).1
  have hmPos : 0 < m := by
    rw [← hchild]
    exact Nat.mul_pos hqPrime.pos huPos
  have htwoqm : 2 * m ≤ q * m :=
    Nat.mul_le_mul_right m hqPrime.two_le
  have htwoX : 2 * m ≤ X := htwoqm.trans hcontact
  have hmHalf : m ≤ X / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
    simpa [Nat.mul_comm] using htwoX
  exact Finset.mem_Icc.mpr ⟨by omega, hmHalf⟩

/-- The disjoint global second-contact population has at most half as many
arithmetic sites as its parent scale. -/
theorem squareRootLowPrimeGoSecondContactSources_card_le_halfScale
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    (squareRootLowPrimeGoSecondContactSources Q X).card ≤ X / 2 := by
  calc
    (squareRootLowPrimeGoSecondContactSources Q X).card ≤
        (Finset.Icc 1 (X / 2)).card :=
      Finset.card_le_card
        (squareRootLowPrimeGoSecondContactSources_subset_halfScale hprime)
    _ = X / 2 := by simp

/-- Integer-valued form of the global signed recombination. -/
theorem squareRootLowPrimeGoWallSquareResidualTotal_eq_neg_sourceMobiusSum
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    squareRootLowPrimeGoWallSquareResidualTotal Q X =
      -∑ m ∈ squareRootLowPrimeGoSecondContactSources Q X, μ m := by
  have h :=
    squareRootLowPrimeGoWallSquareResidualTotal_cast_eq_neg_sourceMass (X := X) hprime
  have hcast :
      ((squareRootLowPrimeGoWallSquareResidualTotal Q X : ℤ) : ℂ) =
        (((-∑ m ∈ squareRootLowPrimeGoSecondContactSources Q X, μ m : ℤ) : ℤ) : ℂ) := by
    simpa [canonicalMoebiusWeight] using h
  exact_mod_cast hcast

/-- **Quantitative half-scale flux bound.**  After exact signed recombination,
the complete `q^2` Go residual cascade has absolute mass at most `X/2`. -/
theorem abs_squareRootLowPrimeGoWallSquareResidualTotal_le_halfScale
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    |squareRootLowPrimeGoWallSquareResidualTotal Q X| ≤ (X / 2 : ℤ) := by
  rw [squareRootLowPrimeGoWallSquareResidualTotal_eq_neg_sourceMobiusSum hprime,
    abs_neg]
  calc
    |∑ m ∈ squareRootLowPrimeGoSecondContactSources Q X, μ m| ≤
        ∑ m ∈ squareRootLowPrimeGoSecondContactSources Q X, |μ m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ squareRootLowPrimeGoSecondContactSources Q X, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro m _hm
      rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> simp [h]
    _ = ((squareRootLowPrimeGoSecondContactSources Q X).card : ℤ) := by simp
    _ ≤ (X / 2 : ℤ) := by
      exact_mod_cast
        squareRootLowPrimeGoSecondContactSources_card_le_halfScale hprime

/-! ## Canonical-parent flux: the second contraction -/

/-- Canonical parents of the globally reassembled second-contact source set. -/
def squareRootLowPrimeGoSecondContactParentCofactors
    (Q : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSecondContactSources Q X).image canonicalCofactor

/-- **Quarter-scale canonical-parent descent.**  Removing the unique largest
prime from a globally reassembled second-contact child gains a full factor
four: `q*m <= X`, `m=q*c`, and `q>=2` give `4*c <= X`. -/
theorem squareRootLowPrimeGoSecondContactSource_canonicalCofactor_le_quarterScale
    {Q : Finset ℕ} {X m : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime)
    (hm : m ∈ squareRootLowPrimeGoSecondContactSources Q X) :
    canonicalCofactor m ≤ X / 4 := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hqPrime := hprime q hqQ
  have hcoords :=
    squareRootLowPrimeGoWallSquareResidualChild_coordinates hqPrime hmq
  have hcontact :=
    squareRootLowPrimeGoWallSquareResidualChild_owner_mul_le hqPrime hmq
  have hq2 : q * (q * canonicalCofactor m) ≤ X := by
    rw [hcoords.2]
    exact hcontact
  have hfourqq : 4 ≤ q * q := by
    nlinarith [hqPrime.two_le]
  have hfour :
      4 * canonicalCofactor m ≤ q * (q * canonicalCofactor m) := by
    have h := Nat.mul_le_mul_right (canonicalCofactor m) hfourqq
    simpa [Nat.mul_assoc] using h
  have h4X : 4 * canonicalCofactor m ≤ X := hfour.trans hq2
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))).2
  simpa [Nat.mul_comm] using h4X

/-- A second-contact child has a positive canonical parent. -/
theorem squareRootLowPrimeGoSecondContactSource_canonicalCofactor_pos
    {Q : Finset ℕ} {X m : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime)
    (hm : m ∈ squareRootLowPrimeGoSecondContactSources Q X) :
    0 < canonicalCofactor m := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hqPrime := hprime q hqQ
  have hcoords :=
    squareRootLowPrimeGoWallSquareResidualChild_coordinates hqPrime hmq
  rcases mem_squareRootLowPrimeGoWallSquareResidualChildren.mp hmq with
    ⟨u, hu, hchild⟩
  have huPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset
      (mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu).1
  have hmPos : 0 < m := by
    rw [← hchild]
    exact Nat.mul_pos hqPrime.pos huPos
  by_contra hnot
  have hc0 : canonicalCofactor m = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hc0, Nat.mul_zero] at hcoords
  omega

/-- The whole canonical-parent image therefore lives in one quarter-scale
interval.  This is a support theorem on the globally reassembled carrier, not a
sum of bounds over old owners. -/
theorem squareRootLowPrimeGoSecondContactParentCofactors_subset_quarterScale
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    squareRootLowPrimeGoSecondContactParentCofactors Q X ⊆
      Finset.Icc 1 (X / 4) := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨m, hm, rfl⟩
  exact Finset.mem_Icc.mpr
    ⟨squareRootLowPrimeGoSecondContactSource_canonicalCofactor_pos hprime hm,
      squareRootLowPrimeGoSecondContactSource_canonicalCofactor_le_quarterScale
        hprime hm⟩

/-- There are at most `X/4` distinct canonical parents.  The parent map is not
asserted injective; its exact fresh-owner fibre is retained for the next signed
cancellation. -/
theorem squareRootLowPrimeGoSecondContactParentCofactors_card_le_quarterScale
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    (squareRootLowPrimeGoSecondContactParentCofactors Q X).card ≤ X / 4 := by
  calc
    (squareRootLowPrimeGoSecondContactParentCofactors Q X).card ≤
        (Finset.Icc 1 (X / 4)).card :=
      Finset.card_le_card
        (squareRootLowPrimeGoSecondContactParentCofactors_subset_quarterScale
          hprime)
    _ = X / 4 := by simp

/-! ## Canonical owner-free description of the full daughter union -/

/-- With the complete prime schedule through `X`, the global `q^2` daughter
carrier can be described without an owner index. -/
def squareRootLowPrimeCanonicalSecondContactSources (X : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (X / 2)).filter fun m =>
    Squarefree m ∧ canonicalLargestPrimeFactor m * m ≤ X

/-- Every globally reassembled second-contact child is squarefree. -/
theorem squareRootLowPrimeGoSecondContactSource_squarefree
    {Q : Finset ℕ} {X m : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime)
    (hm : m ∈ squareRootLowPrimeGoSecondContactSources Q X) :
    Squarefree m := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hq := hprime q hqQ
  rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq] at hmq
  rcases Finset.mem_image.mp hmq with ⟨c, hc, rfl⟩
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hc with
    ⟨hc1, _hcB, hcsq, hcrough⟩
  have hqNot : ¬ q ∣ c := by
    intro hqd
    by_cases hcEq : c = 1
    · subst c
      exact hq.not_dvd_one hqd
    · have hcgt : 1 < c := by omega
      have hle := prime_dvd_le_canonicalLargestPrimeFactor hcgt hq hqd
      omega
  have hcop : Nat.Coprime q c := (hq.coprime_iff_not_dvd).2 hqNot
  exact (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hcsq⟩

/-- **Exact canonical carrier identification.**  Summing over every prime owner
through `X`, the disjoint `q^2` daughter population is precisely the squarefree
integers whose canonical largest prime can make one further multiplicative
contact below `X`. -/
theorem squareRootLowPrimeGoSecondContactSources_primesUpTo_eq_canonical
    (X : ℕ) :
    squareRootLowPrimeGoSecondContactSources (primesUpTo X) X =
      squareRootLowPrimeCanonicalSecondContactSources X := by
  ext m
  constructor
  · intro hm
    have hprime : ∀ q ∈ primesUpTo X, q.Prime := by
      intro q hq
      exact (mem_primesUpTo.mp hq).1
    have hhalf := squareRootLowPrimeGoSecondContactSources_subset_halfScale
      (Q := primesUpTo X) (X := X) hprime hm
    have howner := squareRootLowPrimeGoSecondContactSource_owner_exists
      (Q := primesUpTo X) (X := X) hprime hm
    have hsq := squareRootLowPrimeGoSecondContactSource_squarefree hprime hm
    have hmTwo : 2 ≤ m := by
      rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
      have hq := (mem_primesUpTo.mp hqQ).1
      rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq] at hmq
      rcases Finset.mem_image.mp hmq with ⟨c, hc, hmc⟩
      have hc1 := (mem_squareRootLowPrimeGoSmoothCofactors.mp hc).1
      rw [← hmc]
      nlinarith [hq.two_le]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hmTwo, (Finset.mem_Icc.mp hhalf).2⟩,
      hsq, howner.2⟩
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hmIcc, hsq, hcontact⟩
    have hmTwo : 2 ≤ m := (Finset.mem_Icc.mp hmIcc).1
    have hmgt : 1 < m :=
      lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ)) hmTwo
    let q := canonicalLargestPrimeFactor m
    let c := canonicalCofactor m
    have hdata : CanonicalSourceData q c := by
      simpa [q, c] using canonicalSourceData_of_squarefree hsq hmgt
    rcases hdata with ⟨hq, hc1, hcsq, _hcop, hdom⟩
    have hprod : q * c = m := by
      simpa [q, c, Nat.mul_comm] using
        canonicalCofactor_mul_largestPrimeFactor hmgt
    have hqX : q ≤ X := by
      have hmOne : 1 ≤ m := Nat.le_of_lt hmgt
      have hqm : q ≤ q * m := by
        simpa using Nat.mul_le_mul_left q hmOne
      have hcontact' : q * m ≤ X := by
        simpa [q] using hcontact
      exact hqm.trans hcontact'
    have hqMem : q ∈ primesUpTo X := mem_primesUpTo.mpr ⟨hq, hqX⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hqMem, ?_⟩
    rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq]
    apply Finset.mem_image.mpr
    refine ⟨c, ?_, hprod⟩
    apply mem_squareRootLowPrimeGoSmoothCofactors.mpr
    refine ⟨hc1, ?_, hcsq, ?_⟩
    · apply (Nat.le_div_iff_mul_le (Nat.mul_pos hq.pos hq.pos)).2
      rw [show c * (q * q) = q * (q * c) by ring, hprod]
      exact hcontact
    · by_cases hcEq : c = 1
      · have hcEq' : canonicalCofactor m = 1 := by
          simpa [c] using hcEq
        simpa [c, hcEq', canonicalLargestPrimeFactor] using hq.one_lt
      · have hcgt : 1 < c := by omega
        exact hdom _ (canonicalLargestPrimeFactor_prime hcgt)
          (canonicalLargestPrimeFactor_dvd hcgt)

/-- The full square-residual cascade is therefore one signed Möbius sum on the
canonical triangular carrier. -/
theorem squareRootLowPrimeGoWallSquareResidualTotal_primesUpTo_eq_canonicalMobiusSum
    (X : ℕ) :
    squareRootLowPrimeGoWallSquareResidualTotal (primesUpTo X) X =
      -∑ m ∈ squareRootLowPrimeCanonicalSecondContactSources X, μ m := by
  have hprime : ∀ q ∈ primesUpTo X, q.Prime := by
    intro q hq
    exact (mem_primesUpTo.mp hq).1
  rw [squareRootLowPrimeGoWallSquareResidualTotal_eq_neg_sourceMobiusSum hprime,
    squareRootLowPrimeGoSecondContactSources_primesUpTo_eq_canonical]

end RHLean.Proof