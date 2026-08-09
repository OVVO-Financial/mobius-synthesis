import Mathlib

noncomputable section

namespace RHLean.Analysis

/-- Scalar two-vector energy `‖B - β P‖²` written from Gram data. -/
def twoVectorEnergy (baseEnergy predictionEnergy alignment beta : ℝ) : ℝ :=
  baseEnergy - 2 * beta * alignment + beta ^ 2 * predictionEnergy

/-- Determinant of the real symmetric two-vector Gram block. -/
def twoVectorGramDeterminant
    (baseEnergy predictionEnergy alignment : ℝ) : ℝ :=
  baseEnergy * predictionEnergy - alignment ^ 2

/-- The least-squares coefficient predicted by a nonzero Gram diagonal. -/
def twoVectorOptimalCoefficient
    (predictionEnergy alignment : ℝ) : ℝ :=
  alignment / predictionEnergy

/--
Exact coefficient-gap decomposition.  The energy at any coefficient equals the
minimum Gram-determinant energy plus the squared coefficient error times the
prediction energy.
-/
theorem twoVectorEnergy_eq_gramDeterminant_add_gap
    (baseEnergy predictionEnergy alignment beta : ℝ)
    (hprediction : predictionEnergy ≠ 0) :
    twoVectorEnergy baseEnergy predictionEnergy alignment beta =
      twoVectorGramDeterminant baseEnergy predictionEnergy alignment /
          predictionEnergy +
        (beta - twoVectorOptimalCoefficient predictionEnergy alignment) ^ 2 *
          predictionEnergy := by
  unfold twoVectorEnergy twoVectorGramDeterminant twoVectorOptimalCoefficient
  field_simp [hprediction]
  ring

/-- The optimal coefficient leaves exactly the normalized Gram determinant. -/
theorem twoVectorEnergy_optimal
    (baseEnergy predictionEnergy alignment : ℝ)
    (hprediction : predictionEnergy ≠ 0) :
    twoVectorEnergy baseEnergy predictionEnergy alignment
        (twoVectorOptimalCoefficient predictionEnergy alignment) =
      twoVectorGramDeterminant baseEnergy predictionEnergy alignment /
        predictionEnergy := by
  rw [twoVectorEnergy_eq_gramDeterminant_add_gap
    baseEnergy predictionEnergy alignment
      (twoVectorOptimalCoefficient predictionEnergy alignment) hprediction]
  ring

/--
The theorem-predicted coefficient `1` for the complementary-main subtraction.
Its excess over the orthogonal minimum is exactly the squared coefficient gap.
-/
theorem complementaryMain_coefficient_one_energy
    (baseEnergy predictionEnergy alignment : ℝ)
    (hprediction : predictionEnergy ≠ 0) :
    twoVectorEnergy baseEnergy predictionEnergy alignment 1 =
      twoVectorGramDeterminant baseEnergy predictionEnergy alignment /
          predictionEnergy +
        (1 - twoVectorOptimalCoefficient predictionEnergy alignment) ^ 2 *
          predictionEnergy := by
  exact twoVectorEnergy_eq_gramDeterminant_add_gap
    baseEnergy predictionEnergy alignment 1 hprediction

/--
A small normalized Gram determinant and a small coefficient gap are the exact
two scalar obligations controlling the theorem-predicted complementary main.
-/
theorem complementaryMain_energy_le
    (baseEnergy predictionEnergy alignment determinantBound gapBound : ℝ)
    (hprediction : 0 < predictionEnergy)
    (hdet :
      twoVectorGramDeterminant baseEnergy predictionEnergy alignment /
          predictionEnergy ≤ determinantBound)
    (hgap :
      (1 - twoVectorOptimalCoefficient predictionEnergy alignment) ^ 2 *
          predictionEnergy ≤ gapBound) :
    twoVectorEnergy baseEnergy predictionEnergy alignment 1 ≤
      determinantBound + gapBound := by
  rw [complementaryMain_coefficient_one_energy
    baseEnergy predictionEnergy alignment (ne_of_gt hprediction)]
  exact add_le_add hdet hgap

/--
Concrete naming for the numerically identified block: `base = L` and
`prediction = -Hhat_F`, with theorem coefficient exactly one.
-/
def complementaryMainEnergy
    (lEnergy hhatEnergy lAgainstNegHhat : ℝ) : ℝ :=
  twoVectorEnergy lEnergy hhatEnergy lAgainstNegHhat 1

/-- The complementary-main energy has the exact determinant-plus-gap form. -/
theorem complementaryMainEnergy_eq
    (lEnergy hhatEnergy lAgainstNegHhat : ℝ)
    (hhhat : hhatEnergy ≠ 0) :
    complementaryMainEnergy lEnergy hhatEnergy lAgainstNegHhat =
      twoVectorGramDeterminant lEnergy hhatEnergy lAgainstNegHhat /
          hhatEnergy +
        (1 - twoVectorOptimalCoefficient hhatEnergy lAgainstNegHhat) ^ 2 *
          hhatEnergy := by
  exact complementaryMain_coefficient_one_energy
    lEnergy hhatEnergy lAgainstNegHhat hhhat

end RHLean.Analysis
