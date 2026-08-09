import Mathlib
import RHLean.Proof.ActualResidualDecomposition
import RHLean.Proof.NormalizedCofactorExpansion

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Interpret an ordered factor pair as the cofactor-channel type used by the
actual residual interface. -/
def actualChannelOfPair (p : ℕ × ℕ) :
    RHLean.Analysis.ActualCofactorChannel where
  lowerCofactor := p.1
  upperFactor := p.2

@[simp] theorem actualChannelOfPair_lowerCofactor (p : ℕ × ℕ) :
    (actualChannelOfPair p).lowerCofactor = p.1 := by
  rfl

@[simp] theorem actualChannelOfPair_upperFactor (p : ℕ × ℕ) :
    (actualChannelOfPair p).upperFactor = p.2 := by
  rfl

/-- The channel amplitude omits the lower-cofactor Möbius factor because
`actualResidualEntry` already applies it explicitly. -/
def normalizedChannelAmplitudeRat
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℚ :=
  alphaWeightRat (channel.lowerCofactor * channel.upperFactor) *
    (((μ channel.upperFactor : ℤ) : ℚ))

/-- Complex cast of the normalized channel amplitude for later packet synthesis. -/
def normalizedChannelAmplitude
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  (normalizedChannelAmplitudeRat channel : ℂ)

/-- Reintroducing the explicit lower-cofactor Möbius factor recovers exactly the
normalized ordered cofactor coefficient. -/
theorem lowerMoebius_mul_normalizedChannelAmplitudeRat
    (c q : ℕ) :
    (((μ c : ℤ) : ℚ)) *
        normalizedChannelAmplitudeRat
          { lowerCofactor := c, upperFactor := q } =
      normalizedCofactorWeightRat c q := by
  simp only [normalizedChannelAmplitudeRat, normalizedCofactorWeightRat]
  ring

/-- Pair-indexed form of the exact coefficient compatibility theorem. -/
theorem pairLowerMoebius_mul_normalizedChannelAmplitudeRat
    (p : ℕ × ℕ) :
    (((μ p.1 : ℤ) : ℚ)) *
        normalizedChannelAmplitudeRat (actualChannelOfPair p) =
      normalizedCofactorWeightRat p.1 p.2 := by
  rcases p with ⟨c, q⟩
  exact lowerMoebius_mul_normalizedChannelAmplitudeRat c q

/-- The exact ordered-cofactor realization at the manuscript square-prefix
endpoint, still valued in `ℚ`. -/
def squarePrefixCofactorExpansionRat (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (RHLean.Analysis.squarePrefixEndpoint n + 1),
    ∑ p ∈ orderedCoprimeFactorPairs m,
      (((μ p.1 : ℤ) : ℚ)) *
        normalizedChannelAmplitudeRat (actualChannelOfPair p)

/-- The concrete channel expansion is definitionally the normalized fiber
expansion at the exact square-prefix endpoint. -/
theorem squarePrefixCofactorExpansionRat_eq_normalizedFiberExpansionRat
    (n : ℕ) :
    squarePrefixCofactorExpansionRat n =
      normalizedFiberExpansionRat
        (RHLean.Analysis.squarePrefixEndpoint n) := by
  unfold squarePrefixCofactorExpansionRat normalizedFiberExpansionRat
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro p _
  exact pairLowerMoebius_mul_normalizedChannelAmplitudeRat p

/-- Exact concrete realization of the square-prefix Mertens value by normalized
ordered cofactor channels. -/
theorem squarePrefixCofactorExpansion_cast_eq_squarePrefixMertens
    (n : ℕ) :
    ((squarePrefixCofactorExpansionRat n : ℚ) : ℂ) =
      RHLean.Analysis.squarePrefixMertens n := by
  rw [squarePrefixCofactorExpansionRat_eq_normalizedFiberExpansionRat]
  rw [RHLean.Analysis.squarePrefixMertens]
  exact normalizedFiberExpansion_cast_eq_mertens
    (RHLean.Analysis.squarePrefixEndpoint n)

/-- Expanded finite-sum form of the concrete square-prefix cofactor
realization. -/
theorem squarePrefixMertens_eq_normalizedChannelSum
    (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      ∑ m ∈ Finset.range (RHLean.Analysis.squarePrefixEndpoint n + 1),
        ∑ p ∈ orderedCoprimeFactorPairs m,
          (((μ p.1 : ℤ) : ℂ)) *
            normalizedChannelAmplitude (actualChannelOfPair p) := by
  rw [← squarePrefixCofactorExpansion_cast_eq_squarePrefixMertens]
  unfold squarePrefixCofactorExpansionRat normalizedChannelAmplitude
  push_cast
  rfl

end RHLean.Proof
