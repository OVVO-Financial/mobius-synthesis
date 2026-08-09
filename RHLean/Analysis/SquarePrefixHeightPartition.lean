import Mathlib
import RHLean.Proof.ConcreteSquarePrefixCofactorRealization

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The manuscript's scale-dependent low-height cutoff `Λ n`. -/
def squarePrefixHeightCutoff (Λ : ℝ) (n : ℕ) : ℝ :=
  Λ * (n : ℝ)

/-- A normalized ordered cofactor channel is low height at square scale `n`
when its exact squared-complex ordinate has absolute value at most `Λ n`. -/
def IsLowHeightChannel
    (Λ : ℝ) (n : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel) : Prop :=
  abs (RHLean.Analysis.actualCofactorSquareY channel) ≤
    squarePrefixHeightCutoff Λ n

/-- Pair-indexed form of the exact low-height predicate. -/
def IsLowHeightPair (Λ : ℝ) (n : ℕ) (p : ℕ × ℕ) : Prop :=
  IsLowHeightChannel Λ n (actualChannelOfPair p)

/-- All normalized ordered coprime factor pairs occurring in the complete
square prefix `X_n = (n+1)^2 - 1`. -/
noncomputable def squarePrefixCofactorPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    (Finset.range (RHLean.Analysis.squarePrefixEndpoint n + 1)).biUnion
      orderedCoprimeFactorPairs

/-- The exact low-height normalized ordered pair support. -/
noncomputable def squarePrefixLowHeightPairs (Λ : ℝ) (n : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (squarePrefixCofactorPairs n).filter (IsLowHeightPair Λ n)

/-- The exact high-height normalized ordered pair support. -/
noncomputable def squarePrefixHighHeightPairs (Λ : ℝ) (n : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (squarePrefixCofactorPairs n).filter fun p => ¬ IsLowHeightPair Λ n p

/-- The complete cofactor-channel support available to a later concrete
`ActualResidualData` constructor. -/
noncomputable def squarePrefixCofactorChannels (n : ℕ) :
    Finset RHLean.Analysis.ActualCofactorChannel := by
  classical
  exact (squarePrefixCofactorPairs n).image actualChannelOfPair

/-- The low-height cofactor-channel support. -/
noncomputable def squarePrefixLowHeightChannels (Λ : ℝ) (n : ℕ) :
    Finset RHLean.Analysis.ActualCofactorChannel := by
  classical
  exact (squarePrefixLowHeightPairs Λ n).image actualChannelOfPair

/-- The high-height cofactor-channel support. -/
noncomputable def squarePrefixHighHeightChannels (Λ : ℝ) (n : ℕ) :
    Finset RHLean.Analysis.ActualCofactorChannel := by
  classical
  exact (squarePrefixHighHeightPairs Λ n).image actualChannelOfPair

/-- The pair-to-channel realization loses no information. -/
theorem actualChannelOfPair_injective : Function.Injective actualChannelOfPair := by
  intro p q h
  apply Prod.ext
  · simpa using
      congrArg RHLean.Analysis.ActualCofactorChannel.lowerCofactor h
  · simpa using
      congrArg RHLean.Analysis.ActualCofactorChannel.upperFactor h

/-- Every pair in an individual product fiber belongs to the complete square-prefix
pair support whenever the product lies below the exact endpoint. -/
theorem mem_squarePrefixCofactorPairs_of_mem_fiber
    {n m : ℕ} {p : ℕ × ℕ}
    (hm : m < RHLean.Analysis.squarePrefixEndpoint n + 1)
    (hp : p ∈ orderedCoprimeFactorPairs m) :
    p ∈ squarePrefixCofactorPairs n := by
  classical
  exact Finset.mem_biUnion.mpr
    ⟨m, Finset.mem_range.mpr hm, hp⟩

/-- Low and high pair supports cover the complete normalized ordered support. -/
theorem squarePrefixLowHeightPairs_union_highHeightPairs
    (Λ : ℝ) (n : ℕ) :
    squarePrefixLowHeightPairs Λ n ∪
        squarePrefixHighHeightPairs Λ n =
      squarePrefixCofactorPairs n := by
  classical
  ext p
  by_cases h : IsLowHeightPair Λ n p
  · simp [squarePrefixLowHeightPairs, squarePrefixHighHeightPairs, h]
  · simp [squarePrefixLowHeightPairs, squarePrefixHighHeightPairs, h]

/-- The low- and high-height pair supports are disjoint. -/
theorem squarePrefixLowHeightPairs_disjoint_highHeightPairs
    (Λ : ℝ) (n : ℕ) :
    Disjoint (squarePrefixLowHeightPairs Λ n)
      (squarePrefixHighHeightPairs Λ n) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro p hpLow hpHigh
  have hLow : IsLowHeightPair Λ n p :=
    (Finset.mem_filter.mp hpLow).2
  have hHigh : ¬ IsLowHeightPair Λ n p :=
    (Finset.mem_filter.mp hpHigh).2
  exact hHigh hLow

/-- Low and high channel supports cover the complete concrete channel support. -/
theorem squarePrefixLowHeightChannels_union_highHeightChannels
    (Λ : ℝ) (n : ℕ) :
    squarePrefixLowHeightChannels Λ n ∪
        squarePrefixHighHeightChannels Λ n =
      squarePrefixCofactorChannels n := by
  classical
  unfold squarePrefixLowHeightChannels squarePrefixHighHeightChannels
    squarePrefixCofactorChannels
  rw [← Finset.image_union]
  rw [squarePrefixLowHeightPairs_union_highHeightPairs]

/-- The low- and high-height concrete channel supports are disjoint. -/
theorem squarePrefixLowHeightChannels_disjoint_highHeightChannels
    (Λ : ℝ) (n : ℕ) :
    Disjoint (squarePrefixLowHeightChannels Λ n)
      (squarePrefixHighHeightChannels Λ n) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro channel hLow hHigh
  rcases Finset.mem_image.mp hLow with ⟨p, hpLow, hpChannel⟩
  rcases Finset.mem_image.mp hHigh with ⟨q, hqHigh, hqChannel⟩
  have hpq : p = q :=
    actualChannelOfPair_injective (hpChannel.trans hqChannel.symm)
  subst q
  exact
    (Finset.disjoint_left.mp
      (squarePrefixLowHeightPairs_disjoint_highHeightPairs Λ n))
      hpLow hqHigh

/-- Exact low-height part of the normalized square-prefix channel expansion. -/
noncomputable def squarePrefixLowHeightExpansionRat (Λ : ℝ) (n : ℕ) : ℚ := by
  classical
  exact
    ∑ m ∈ Finset.range (RHLean.Analysis.squarePrefixEndpoint n + 1),
      ∑ p ∈ orderedCoprimeFactorPairs m,
        if IsLowHeightPair Λ n p then
          (((μ p.1 : ℤ) : ℚ)) *
            normalizedChannelAmplitudeRat (actualChannelOfPair p)
        else 0

/-- Exact high-height part of the normalized square-prefix channel expansion. -/
noncomputable def squarePrefixHighHeightExpansionRat (Λ : ℝ) (n : ℕ) : ℚ := by
  classical
  exact
    ∑ m ∈ Finset.range (RHLean.Analysis.squarePrefixEndpoint n + 1),
      ∑ p ∈ orderedCoprimeFactorPairs m,
        if IsLowHeightPair Λ n p then 0
        else
          (((μ p.1 : ℤ) : ℚ)) *
            normalizedChannelAmplitudeRat (actualChannelOfPair p)

/-- The normalized ordered expansion splits exactly into its low- and high-height
parts, with the original product-fiber indexing unchanged. -/
theorem squarePrefixCofactorExpansionRat_eq_low_add_high
    (Λ : ℝ) (n : ℕ) :
    squarePrefixCofactorExpansionRat n =
      squarePrefixLowHeightExpansionRat Λ n +
        squarePrefixHighHeightExpansionRat Λ n := by
  classical
  unfold squarePrefixCofactorExpansionRat squarePrefixLowHeightExpansionRat
    squarePrefixHighHeightExpansionRat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : IsLowHeightPair Λ n p
  · simp [h]
  · simp [h]

/-- Complex low-height square-prefix contribution. -/
def squarePrefixLowHeightExpansion (Λ : ℝ) (n : ℕ) : ℂ :=
  (squarePrefixLowHeightExpansionRat Λ n : ℂ)

/-- Complex high-height square-prefix contribution. -/
def squarePrefixHighHeightExpansion (Λ : ℝ) (n : ℕ) : ℂ :=
  (squarePrefixHighHeightExpansionRat Λ n : ℂ)

/-- Exact signal-level recombination of the concrete square-prefix Mertens value
into low- and high-height normalized channel contributions. -/
theorem squarePrefixMertens_eq_lowHeight_add_highHeight
    (Λ : ℝ) (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      squarePrefixLowHeightExpansion Λ n +
        squarePrefixHighHeightExpansion Λ n := by
  have hrat := squarePrefixCofactorExpansionRat_eq_low_add_high Λ n
  have hcast := congrArg (fun x : ℚ => (x : ℂ)) hrat
  rw [← squarePrefixCofactorExpansion_cast_eq_squarePrefixMertens]
  simpa [squarePrefixLowHeightExpansion, squarePrefixHighHeightExpansion] using hcast

end RHLean.Proof
