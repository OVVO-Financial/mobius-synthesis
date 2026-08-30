import Mathlib
import RHLean.Proof.LowWheelHighPrimeSurvivor
import RHLean.Proof.LowWheelDoubleCubeTransport

/-!
# High transport on terminal face coordinates

The cofactor-first high transport is usually written as a signed sum over
integer cofactors `c < R` and high primes `p > R`.  The low-wheel development
already proves that every squarefree cofactor can be reindexed uniquely by its
prime face.  Nonsquarefree cofactors have zero Möbius weight.

Consequently the complete high transport admits the exact terminal coordinate
system

`(t,p)`,

where `t` is an admissible low-prime face with `P(t) < R` and `p` belongs to the
existing high-prime fibre of `P(t)`.  The signed weight is just the Boolean sign
of `t`.

This is the global version of the coordinate rotation used by the repeated
terminal boundary: the apparent repeated-parent multiplicity is precisely the
already-existing high-prime multiplicity of the face product.

No estimate, prime-density input, asymptotic argument, or recursion is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The complete high transport written on its squarefree Boolean-face
cofactor coordinate and its existing high-prime fibre. -/
def squareRootExternalTerminalFaceLedger (R : ℕ) : ℂ :=
  ∑ t ∈ admissiblePrimeFaces (R - 1),
    ∑ _p ∈ squareRootHighPrimeCofactorSet R (primeFaceProduct t),
      (booleanCubeSign t : ℂ)

/-- An admissible face at cutoff `R-1` has positive product strictly below `R`,
so it is a legitimate cofactor in the square-root transport. -/
theorem admissibleTerminalFace_product_mem_Ico
    {R : ℕ} (hR : 1 ≤ R) {t : Finset ℕ}
    (ht : t ∈ admissiblePrimeFaces (R - 1)) :
    primeFaceProduct t ∈ Finset.Ico 1 R := by
  have htAdm := mem_admissiblePrimeFaces.mp ht
  have htPow : t ∈ (primesUpTo (R - 1)).powerset :=
    Finset.mem_powerset.mpr htAdm.1
  have hpos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset htPow
  have hpredLt : R - 1 < R := by omega
  exact Finset.mem_Ico.mpr ⟨by omega, htAdm.2.trans_lt hpredLt⟩

/-- The low-wheel high-prime multiplicity at an admissible face product is
literally the cardinality of its native high-prime fibre. -/
theorem lowWheelHighPrimeMultiplicity_face_eq_highPrimeCard
    {R : ℕ} (hR : 2 ≤ R) {t : Finset ℕ}
    (ht : t ∈ admissiblePrimeFaces (R - 1)) :
    lowWheelHighPrimeMultiplicity R (primeFaceProduct t) =
      (squareRootHighPrimeCofactorSet R (primeFaceProduct t)).card := by
  have hc := admissibleTerminalFace_product_mem_Ico (by omega) ht
  have hset := squareRootHighPrimeCofactorSet_eq_lowWheelHighSurvivorSet
    hR hc
  unfold lowWheelHighPrimeMultiplicity
  rw [← hset]

/-- **High transport = terminal face/high-prime grid.**  This is an exact
reindexing of the whole cofactor-first transport, not merely of one terminal
subpopulation.  Every squarefree low cofactor is replaced by its unique prime
face, and its upper-prime multiplicity is left as the same finite high-prime
fibre. -/
theorem squareRootTransportCofactorFirst_eq_externalTerminalFaceLedger
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      squareRootExternalTerminalFaceLedger R := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelFrequency R hR]
  unfold squareRootTransportLowWheelFrequency
    squareRootExternalTerminalFaceLedger
  let F : ℕ → ℂ := fun c => (lowWheelHighPrimeMultiplicity R c : ℂ)
  have hreindex := canonicalMoebiusWeighted_Ico_eq_admissibleFaceSum
    R (by omega) F
  have hleft :
      (∑ c ∈ Finset.Ico 1 R,
          (lowWheelHighPrimeMultiplicity R c : ℂ) *
            canonicalMoebiusWeight c) =
        ∑ c ∈ Finset.Ico 1 R,
          canonicalMoebiusWeight c * F c := by
    apply Finset.sum_congr rfl
    intro c _hc
    simp [F, mul_comm]
  rw [hleft, hreindex]
  apply Finset.sum_congr rfl
  intro t ht
  change (booleanCubeSign t : ℂ) *
      (lowWheelHighPrimeMultiplicity R (primeFaceProduct t) : ℂ) =
    ∑ _p ∈ squareRootHighPrimeCofactorSet R (primeFaceProduct t),
      (booleanCubeSign t : ℂ)
  rw [lowWheelHighPrimeMultiplicity_face_eq_highPrimeCard hR ht]
  simp [mul_comm]

end RHLean.Proof
