import Mathlib
import RHLean.Proof.CanonicalHighSectorCovariance

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The canonical square-block contribution from values whose largest prime
factor does not exceed the square-root block scale. -/
noncomputable def squareBlockSmoothIncrement (k : ℕ) : ℂ := by
  classical
  exact
    ∑ m ∈ canonicalSquareBlock k,
      if canonicalLargestPrimeFactor m ≤ k then canonicalMoebiusWeight m else 0

/-- The sign-reversed complementary square-block contribution from values whose
largest prime factor exceeds the square-root block scale. With this convention
the complete block increment is `smooth - transport`. -/
noncomputable def squareBlockTransportIncrement (k : ℕ) : ℂ := by
  classical
  exact
    - ∑ m ∈ canonicalSquareBlock k,
        if k < canonicalLargestPrimeFactor m then canonicalMoebiusWeight m else 0

/-- Exact deterministic smooth-minus-transport identity on every canonical
square block. -/
theorem canonicalTotalIncrement_eq_smooth_sub_transport (k : ℕ) :
    canonicalTotalIncrement k =
      squareBlockSmoothIncrement k - squareBlockTransportIncrement k := by
  classical
  unfold canonicalTotalIncrement squareBlockSmoothIncrement squareBlockTransportIncrement
  rw [sub_neg_eq_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : canonicalLargestPrimeFactor m ≤ k
  · simp [h, Nat.not_lt.mpr h]
  · have hk : k < canonicalLargestPrimeFactor m := Nat.lt_of_not_ge h
    simp [h, hk]

/-- Cumulative smooth contribution from the common-origin square blocks
`0,1,...,n`. -/
def squareBlockSmoothPrefix (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), squareBlockSmoothIncrement k

/-- Cumulative transport contribution from the common-origin square blocks
`0,1,...,n`. -/
def squareBlockTransportPrefix (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), squareBlockTransportIncrement k

/-- The theorem-predicted cumulative smooth-minus-transport residual. -/
def squareBlockSmoothTransportResidual (n : ℕ) : ℂ :=
  squareBlockSmoothPrefix n - squareBlockTransportPrefix n

/-- Exact cumulative smooth-minus-transport recombination. -/
theorem canonicalTotalPrefix_eq_smooth_sub_transport (n : ℕ) :
    canonicalTotalPrefix n = squareBlockSmoothTransportResidual n := by
  unfold canonicalTotalPrefix squareBlockSmoothTransportResidual
    squareBlockSmoothPrefix squareBlockTransportPrefix
  calc
    (∑ j ∈ Finset.range (n + 1), canonicalTotalIncrement j) =
        ∑ k ∈ Finset.range (n + 1),
          (squareBlockSmoothIncrement k - squareBlockTransportIncrement k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact canonicalTotalIncrement_eq_smooth_sub_transport k
    _ = (∑ k ∈ Finset.range (n + 1), squareBlockSmoothIncrement k) -
          ∑ k ∈ Finset.range (n + 1), squareBlockTransportIncrement k := by
      rw [Finset.sum_sub_distrib]

/-- The cumulative smooth-minus-transport residual is exactly the concrete
square-prefix Mertens sequence. -/
theorem squareBlockSmoothTransportResidual_eq_squarePrefixMertens (n : ℕ) :
    squareBlockSmoothTransportResidual n = RHLean.Analysis.squarePrefixMertens n := by
  rw [← canonicalTotalPrefix_eq_smooth_sub_transport n]
  exact canonicalTotalPrefix_eq_squarePrefixMertens n

/-- Local smooth energy on `[N,N+H)`. -/
def squareBlockLocalSmoothEnergy (N H : ℕ) : ℝ :=
  RHLean.Analysis.localSequenceEnergy squareBlockSmoothPrefix N H

/-- Local transport energy on `[N,N+H)`. -/
def squareBlockLocalTransportEnergy (N H : ℕ) : ℝ :=
  RHLean.Analysis.localSequenceEnergy squareBlockTransportPrefix N H

/-- The complete signed smooth/transport interaction. It is defined as the
exact difference between the residual energy and the two diagonal energies, so
no cross term is discarded or assigned a sign assumption. -/
def squareBlockLocalSmoothTransportInteraction (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H,
    (‖squareBlockSmoothPrefix (N + h) - squareBlockTransportPrefix (N + h)‖ ^ 2 -
      ‖squareBlockSmoothPrefix (N + h)‖ ^ 2 -
      ‖squareBlockTransportPrefix (N + h)‖ ^ 2)

/-- The full signed joint Gram energy of the theorem-predicted subtraction. -/
def squareBlockSmoothTransportJointEnergy (N H : ℕ) : ℝ :=
  squareBlockLocalSmoothEnergy N H + squareBlockLocalTransportEnergy N H +
    squareBlockLocalSmoothTransportInteraction N H

/-- Exact signed Gram expansion with both diagonal energies and the complete
smooth/transport interaction retained. -/
theorem squareBlockSmoothTransportJointEnergy_eq_localResidualEnergy
    (N H : ℕ) :
    squareBlockSmoothTransportJointEnergy N H =
      RHLean.Analysis.localSequenceEnergy squareBlockSmoothTransportResidual N H := by
  unfold squareBlockSmoothTransportJointEnergy squareBlockLocalSmoothEnergy
    squareBlockLocalTransportEnergy squareBlockLocalSmoothTransportInteraction
    RHLean.Analysis.localSequenceEnergy squareBlockSmoothTransportResidual
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- The joint smooth/transport energy is exactly the concrete square-prefix
Mertens local energy. -/
theorem squareBlockSmoothTransportJointEnergy_eq_squarePrefixLocalEnergy
    (N H : ℕ) :
    squareBlockSmoothTransportJointEnergy N H =
      RHLean.Analysis.localSequenceEnergy RHLean.Analysis.squarePrefixMertens N H := by
  rw [squareBlockSmoothTransportJointEnergy_eq_localResidualEnergy]
  apply Finset.sum_congr rfl
  intro h hh
  rw [squareBlockSmoothTransportResidual_eq_squarePrefixMertens]

/-- Exact coherent-mean plus centered-covariance decomposition of the complete
signed smooth/transport Gram energy. -/
theorem squareBlockSmoothTransportJointEnergy_eq_coherentMean_add_centeredCovariance
    (N H : ℕ) (hH : 1 ≤ H) :
    squareBlockSmoothTransportJointEnergy N H =
      localCoherentMeanEnergy squareBlockSmoothTransportResidual N H +
        localCenteredCovarianceEnergy squareBlockSmoothTransportResidual N H := by
  rw [squareBlockSmoothTransportJointEnergy_eq_localResidualEnergy]
  exact localSequenceEnergy_eq_coherentMean_add_centeredCovariance
    squareBlockSmoothTransportResidual N H hH

/-- The single unresolved analytic premise for uniform local control of the
full signed square-block smooth/transport Gram form. -/
def SquareBlockSmoothTransportGramBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        squareBlockSmoothTransportJointEnergy N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The typed Gram premise is exactly the repository's concrete square-prefix
uniform local criterion. -/
theorem squareBlockSmoothTransportGramBound_iff_squarePrefixUniformLocalBounded :
    SquareBlockSmoothTransportGramBound ↔
      RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rw [← squareBlockSmoothTransportJointEnergy_eq_squarePrefixLocalEnergy]
    exact hbound N H hH hHN
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rw [squareBlockSmoothTransportJointEnergy_eq_squarePrefixLocalEnergy]
    exact hbound N H hH hHN

/-- Conditional RH bridge for the full signed square-block smooth/transport
Gram premise. This theorem proves no analytic estimate and assumes only the
existing classical Mertens-energy equivalence as an ordinary theorem argument. -/
theorem squareBlockSmoothTransportGramBound_iff_riemannHypothesis
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    SquareBlockSmoothTransportGramBound ↔
      RHLean.Analysis.RiemannHypothesisStatement := by
  calc
    SquareBlockSmoothTransportGramBound ↔
        RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement :=
      squareBlockSmoothTransportGramBound_iff_squarePrefixUniformLocalBounded
    _ ↔ RHLean.Analysis.MertensEnergyBoundedStatement :=
      RHLean.Analysis.squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded
    _ ↔ RHLean.Analysis.RiemannHypothesisStatement := criterion.iff_riemannHypothesis

end RHLean.Proof
