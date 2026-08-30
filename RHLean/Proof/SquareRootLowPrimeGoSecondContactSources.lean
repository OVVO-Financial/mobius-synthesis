import Mathlib
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
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

No quantitative estimate is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

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

end RHLean.Proof
