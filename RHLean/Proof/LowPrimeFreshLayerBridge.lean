import Mathlib
import RHLean.Proof.LowWheelDoubleCubeTransport
import RHLean.Proof.SquareRootBornPostTailLowPrimeRemainder

/-!
# Fresh low-prime layer bridge for the BornPostTail response

This module isolates one exact statement only: the prime-by-prime trajectory
used in the `LowPrimeProcessedResponse` numerical diagnostic is the same finite
object as an alternating Boolean prime-face layer.

For a variable cutoff `p`, retain exactly those cofactor terms whose canonical
largest prime factor is at most `p`.  At a prime step, subtracting the state at
`p-1` leaves exactly the cofactors with `P+(c)=p`.  Reindexing the nonzero
Mobius support through the repository's squarefree prime-face bijection then
turns that fresh cofactor layer into an alternating Boolean-face sum.

No norm, inequality, dissipation claim, endpoint Mertens identity, PNT input,
or instantiated crossing depth appears here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Running version of the processed response from the fresh-layer bridge.  The final cutoff
`P_R = R - floor(sqrt R)` is deliberately replaced by a free coordinate `p`.
The two summands are exactly the born-partner and post-crossing high responses
from the existing definition. -/
def squareRootBornPostTailRunningLowPrimeResponse
    (R K j p : ℕ) : ℂ :=
  (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
      if canonicalLargestPrimeFactor c ≤ p then
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)
      else 0) +
  (∑ c ∈ Finset.Icc 1 (R - 1),
      if canonicalLargestPrimeFactor c ≤ p then
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)
      else 0)

/-- The running state at the fresh-layer cutoff is definitionally the already
kernel-checked `LowPrimeProcessedResponse`, modulo the standard filter/indicator
sum identity. -/
theorem squareRootBornPostTailRunningLowPrimeResponse_at_cutoff
    (R K j : ℕ) :
    squareRootBornPostTailRunningLowPrimeResponse R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootBornPostTailLowPrimeProcessedResponse R K j := by
  classical
  unfold squareRootBornPostTailRunningLowPrimeResponse
    squareRootBornPostTailLowPrimeProcessedResponse
  rw [Finset.sum_filter, Finset.sum_filter]

/-- Literal cofactor layer born at largest-prime coordinate `p`. -/
def squareRootBornPostTailFreshCofactorLayer
    (R K j p : ℕ) : ℂ :=
  (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
      if canonicalLargestPrimeFactor c = p then
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)
      else 0) +
  (∑ c ∈ Finset.Icc 1 (R - 1),
      if canonicalLargestPrimeFactor c = p then
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)
      else 0)

private theorem sum_lpf_le_sub_pred_eq_sum_lpf_eq
    (S : Finset ℕ) (F : ℕ → ℂ) (p : ℕ) (hp : 1 ≤ p) :
    (∑ c ∈ S,
        if canonicalLargestPrimeFactor c ≤ p then F c else 0) -
      (∑ c ∈ S,
        if canonicalLargestPrimeFactor c ≤ p - 1 then F c else 0) =
    ∑ c ∈ S,
      if canonicalLargestPrimeFactor c = p then F c else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases heq : canonicalLargestPrimeFactor c = p
  · rw [heq]
    have hnot : ¬ p ≤ p - 1 := by omega
    simp [hnot]
  · by_cases hle : canonicalLargestPrimeFactor c ≤ p
    · have hpred : canonicalLargestPrimeFactor c ≤ p - 1 := by omega
      simp [heq, hle, hpred]
    · have hpred : ¬ canonicalLargestPrimeFactor c ≤ p - 1 := by
        intro h
        exact hle (h.trans (Nat.sub_le p 1))
      simp [heq, hle, hpred]

/-- A fresh prime step of the running LPR state is exactly the literal
`P+(c)=p` cofactor layer.  This is the exact quantity bucketed by prime in the
sequential diagnostic. -/
theorem squareRootBornPostTailRunningLowPrimeResponse_step_eq_freshCofactorLayer
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) =
      squareRootBornPostTailFreshCofactorLayer R K j p := by
  unfold squareRootBornPostTailRunningLowPrimeResponse
    squareRootBornPostTailFreshCofactorLayer
  have hborn := sum_lpf_le_sub_pred_eq_sum_lpf_eq
    (Finset.Icc 1 (squareRootEndpoint R))
    (fun c => canonicalMoebiusWeight c *
      (squareRootBornPartnerCount R c : ℂ)) p hp.one_le
  have hhigh := sum_lpf_le_sub_pred_eq_sum_lpf_eq
    (Finset.Icc 1 (R - 1))
    (fun c => canonicalMoebiusWeight c *
      (squareRootBornPostTailHighResponse R K j c : ℂ)) p hp.one_le
  linear_combination hborn + hhigh

/-- Generic squarefree-face reindex on the closed interval `[1,B]`.  This is the
closed-interval form of the repository's existing admissible-face theorem and
is useful here because both response coordinates are naturally closed prefixes. -/
theorem canonicalMoebiusWeighted_Icc_eq_admissibleFaceSum
    (B : ℕ) (F : ℕ → ℂ) :
    (∑ c ∈ Finset.Icc 1 B, canonicalMoebiusWeight c * F c) =
      ∑ u ∈ admissiblePrimeFaces B,
        (booleanCubeSign u : ℂ) * F (primeFaceProduct u) := by
  have h := canonicalMoebiusWeighted_Ico_eq_admissibleFaceSum
    (B + 1) (by omega : 1 ≤ B + 1) F
  have hset : Finset.Ico 1 (B + 1) = Finset.Icc 1 B := by
    ext c
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hset] at h
  simpa using h

/-- Boolean-face form of the fresh LPR layer.  The condition `P+(P(u))=p`
selects exactly the squarefree faces born at prime coordinate `p`; the
coefficients are the native Boolean signs, while the born/high responses are
unchanged. -/
def squareRootBornPostTailFreshBooleanFaceLayer
    (R K j p : ℕ) : ℂ :=
  (∑ u ∈ admissiblePrimeFaces (squareRootEndpoint R),
      if canonicalLargestPrimeFactor (primeFaceProduct u) = p then
        (booleanCubeSign u : ℂ) *
          (squareRootBornPartnerCount R (primeFaceProduct u) : ℂ)
      else 0) +
  (∑ u ∈ admissiblePrimeFaces (R - 1),
      if canonicalLargestPrimeFactor (primeFaceProduct u) = p then
        (booleanCubeSign u : ℂ) *
          (squareRootBornPostTailHighResponse R K j
            (primeFaceProduct u) : ℂ)
      else 0)

private theorem freshCofactorBorn_eq_booleanFace
    (R p : ℕ) :
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
      if canonicalLargestPrimeFactor c = p then
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)
      else 0) =
    ∑ u ∈ admissiblePrimeFaces (squareRootEndpoint R),
      if canonicalLargestPrimeFactor (primeFaceProduct u) = p then
        (booleanCubeSign u : ℂ) *
          (squareRootBornPartnerCount R (primeFaceProduct u) : ℂ)
      else 0 := by
  let F : ℕ → ℂ := fun c =>
    if canonicalLargestPrimeFactor c = p then
      (squareRootBornPartnerCount R c : ℂ)
    else 0
  have h := canonicalMoebiusWeighted_Icc_eq_admissibleFaceSum
    (squareRootEndpoint R) F
  calc
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
      if canonicalLargestPrimeFactor c = p then
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)
      else 0) =
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          canonicalMoebiusWeight c * F c := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases heq : canonicalLargestPrimeFactor c = p <;> simp [F, heq]
    _ = ∑ u ∈ admissiblePrimeFaces (squareRootEndpoint R),
        (booleanCubeSign u : ℂ) * F (primeFaceProduct u) := h
    _ = ∑ u ∈ admissiblePrimeFaces (squareRootEndpoint R),
      if canonicalLargestPrimeFactor (primeFaceProduct u) = p then
        (booleanCubeSign u : ℂ) *
          (squareRootBornPartnerCount R (primeFaceProduct u) : ℂ)
      else 0 := by
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases heq : canonicalLargestPrimeFactor (primeFaceProduct u) = p <;>
        simp [F, heq]

private theorem freshCofactorHigh_eq_booleanFace
    (R K j p : ℕ) :
    (∑ c ∈ Finset.Icc 1 (R - 1),
      if canonicalLargestPrimeFactor c = p then
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)
      else 0) =
    ∑ u ∈ admissiblePrimeFaces (R - 1),
      if canonicalLargestPrimeFactor (primeFaceProduct u) = p then
        (booleanCubeSign u : ℂ) *
          (squareRootBornPostTailHighResponse R K j
            (primeFaceProduct u) : ℂ)
      else 0 := by
  let F : ℕ → ℂ := fun c =>
    if canonicalLargestPrimeFactor c = p then
      (squareRootBornPostTailHighResponse R K j c : ℂ)
    else 0
  have h := canonicalMoebiusWeighted_Icc_eq_admissibleFaceSum (R - 1) F
  calc
    (∑ c ∈ Finset.Icc 1 (R - 1),
      if canonicalLargestPrimeFactor c = p then
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)
      else 0) =
        ∑ c ∈ Finset.Icc 1 (R - 1), canonicalMoebiusWeight c * F c := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases heq : canonicalLargestPrimeFactor c = p <;> simp [F, heq]
    _ = ∑ u ∈ admissiblePrimeFaces (R - 1),
        (booleanCubeSign u : ℂ) * F (primeFaceProduct u) := h
    _ = ∑ u ∈ admissiblePrimeFaces (R - 1),
      if canonicalLargestPrimeFactor (primeFaceProduct u) = p then
        (booleanCubeSign u : ℂ) *
          (squareRootBornPostTailHighResponse R K j
            (primeFaceProduct u) : ℂ)
      else 0 := by
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases heq : canonicalLargestPrimeFactor (primeFaceProduct u) = p <;>
        simp [F, heq]

/-- The literal fresh cofactor layer and the Boolean prime-face layer are the
same finite signed object. -/
theorem squareRootBornPostTailFreshCofactorLayer_eq_freshBooleanFaceLayer
    (R K j p : ℕ) :
    squareRootBornPostTailFreshCofactorLayer R K j p =
      squareRootBornPostTailFreshBooleanFaceLayer R K j p := by
  unfold squareRootBornPostTailFreshCofactorLayer
    squareRootBornPostTailFreshBooleanFaceLayer
  rw [freshCofactorBorn_eq_booleanFace, freshCofactorHigh_eq_booleanFace]

/-- **BRIDGE.**  For every fresh prime `p`, the exact increment of the running
LowPrimeProcessedResponse is the alternating Boolean face layer born at that
prime.  This identifies the prime-by-prime numerical trajectory with the
repository's finite Boolean-cube coordinates before any estimate is taken. -/
theorem squareRootBornPostTailRunningLowPrimeResponse_step_eq_freshBooleanFaceLayer
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) =
      squareRootBornPostTailFreshBooleanFaceLayer R K j p := by
  rw [squareRootBornPostTailRunningLowPrimeResponse_step_eq_freshCofactorLayer
    R K j p hp,
    squareRootBornPostTailFreshCofactorLayer_eq_freshBooleanFaceLayer]

end RHLean.Proof
