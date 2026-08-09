import Mathlib
import RHLean.Proof.SquareBlockSmoothTransportGram

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Strong global second-moment control of the exact square-block increments
`squareBlockSmoothIncrement k - squareBlockTransportIncrement k`.

This is an explicit unresolved arithmetic premise. It is strictly stronger than
the repository's cumulative uniform-local criterion and is not asserted here. -/
def SquareBlockIncrementEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ K : ℕ, 1 ≤ K →
        ∑ k ∈ Finset.range (K + 1),
            ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖ ^ 2 ≤
          C * Real.rpow (K : ℝ) (1 + ε)

/-- The cumulative smooth-minus-transport residual is the finite sum of the
exact block increments from the common origin. -/
theorem squareBlockSmoothTransportResidual_eq_sum_increment (n : ℕ) :
    squareBlockSmoothTransportResidual n =
      ∑ k ∈ Finset.range (n + 1),
        (squareBlockSmoothIncrement k - squareBlockTransportIncrement k) := by
  unfold squareBlockSmoothTransportResidual squareBlockSmoothPrefix
    squareBlockTransportPrefix
  rw [Finset.sum_sub_distrib]

/-- Strong increment-energy control gives the RH-scale pointwise energy bound
for the cumulative smooth-minus-transport residual. -/
theorem norm_squareBlockSmoothTransportResidual_sq_le_of_incrementEnergy
    (hinc : SquareBlockIncrementEnergyBoundedStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℕ, 1 ≤ n →
          ‖squareBlockSmoothTransportResidual n‖ ^ 2 ≤
            C * Real.rpow (n : ℝ) (2 + ε) := by
  intro ε hε
  rcases hinc (ε / 2) (by linarith) with ⟨C, hC, henergy⟩
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro n hn
  have hrepresentation := squareBlockSmoothTransportResidual_eq_sum_increment n
  have hnorm :
      ‖squareBlockSmoothTransportResidual n‖ ≤
        ∑ k ∈ Finset.range (n + 1),
          ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖ := by
    rw [hrepresentation]
    exact norm_sum_le _ _
  have hsum_nonneg :
      0 ≤ ∑ k ∈ Finset.range (n + 1),
        ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖ := by
    positivity
  have hnorm_sq :
      ‖squareBlockSmoothTransportResidual n‖ ^ 2 ≤
        (∑ k ∈ Finset.range (n + 1),
          ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum_nonneg).2 hnorm
  have hcauchy :
      (∑ k ∈ Finset.range (n + 1),
          ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖) ^ 2 ≤
        (n + 1 : ℝ) *
          ∑ k ∈ Finset.range (n + 1),
            ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.range (n + 1))
        (f := fun k : ℕ =>
          ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖))
  have henergy_n := henergy n hn
  have hcard_nat : n + 1 ≤ 2 * n := by omega
  have hcard : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hcard_nat
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hbase : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hrpow_nonneg :
      0 ≤ Real.rpow (n : ℝ) (1 + ε / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have henergy_rhs_nonneg :
      0 ≤ C * Real.rpow (n : ℝ) (1 + ε / 2) :=
    mul_nonneg hC hrpow_nonneg
  have hrpow_mul :
      (n : ℝ) * Real.rpow (n : ℝ) (1 + ε / 2) =
        Real.rpow (n : ℝ) (2 + ε / 2) := by
    calc
      (n : ℝ) * Real.rpow (n : ℝ) (1 + ε / 2) =
          Real.rpow (n : ℝ) 1 * Real.rpow (n : ℝ) (1 + ε / 2) := by
        exact congrArg
          (fun x : ℝ => x * Real.rpow (n : ℝ) (1 + ε / 2))
          (Real.rpow_one (n : ℝ)).symm
      _ = Real.rpow (n : ℝ) (1 + (1 + ε / 2)) :=
        (Real.rpow_add hn_pos 1 (1 + ε / 2)).symm
      _ = Real.rpow (n : ℝ) (2 + ε / 2) := by
        congr 1
        ring
  have hrpow_mono :
      Real.rpow (n : ℝ) (2 + ε / 2) ≤
        Real.rpow (n : ℝ) (2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  calc
    ‖squareBlockSmoothTransportResidual n‖ ^ 2 ≤
        (∑ k ∈ Finset.range (n + 1),
          ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖) ^ 2 :=
      hnorm_sq
    _ ≤ (n + 1 : ℝ) *
          ∑ k ∈ Finset.range (n + 1),
            ‖squareBlockSmoothIncrement k - squareBlockTransportIncrement k‖ ^ 2 :=
      hcauchy
    _ ≤ (n + 1 : ℝ) *
          (C * Real.rpow (n : ℝ) (1 + ε / 2)) :=
      mul_le_mul_of_nonneg_left henergy_n (by positivity)
    _ ≤ (2 * (n : ℝ)) *
          (C * Real.rpow (n : ℝ) (1 + ε / 2)) :=
      mul_le_mul_of_nonneg_right hcard henergy_rhs_nonneg
    _ = (2 * C) *
          ((n : ℝ) * Real.rpow (n : ℝ) (1 + ε / 2)) := by
      ring
    _ = (2 * C) * Real.rpow (n : ℝ) (2 + ε / 2) := by
      rw [hrpow_mul]
    _ ≤ (2 * C) * Real.rpow (n : ℝ) (2 + ε) :=
      mul_le_mul_of_nonneg_left hrpow_mono (mul_nonneg (by norm_num) hC)

/-- Strong increment-energy control gives the repository's existing pointwise
square-prefix criterion. -/
theorem squarePrefixCurrentPointwiseBounded_of_incrementEnergy
    (hinc : SquareBlockIncrementEnergyBoundedStatement) :
    RHLean.Analysis.SquarePrefixCurrentPointwiseBoundedStatement := by
  intro ε hε
  rcases norm_squareBlockSmoothTransportResidual_sq_le_of_incrementEnergy hinc ε hε with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N hN
  rw [← squareBlockSmoothTransportResidual_eq_squarePrefixMertens]
  exact hbound N hN

/-- Strong global increment-energy control implies the repository's existing
uniform-local cumulative square-prefix criterion. -/
theorem squarePrefixUniformLocalBounded_of_incrementEnergy
    (hinc : SquareBlockIncrementEnergyBoundedStatement) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement :=
  RHLean.Analysis.squarePrefix_uniformLocalBounded_of_currentPointwise
    (squarePrefixCurrentPointwiseBounded_of_incrementEnergy hinc)

/-- Strong global increment-energy control implies the complete signed
smooth/transport Gram premise from the preceding layer. -/
theorem squareBlockSmoothTransportGramBound_of_incrementEnergy
    (hinc : SquareBlockIncrementEnergyBoundedStatement) :
    SquareBlockSmoothTransportGramBound :=
  squareBlockSmoothTransportGramBound_iff_squarePrefixUniformLocalBounded.mpr
    (squarePrefixUniformLocalBounded_of_incrementEnergy hinc)

/-- Conditional RH implication from the strong square-block increment-energy
premise and the ordinary classical Mertens-energy equivalence argument. -/
theorem riemannHypothesis_of_squareBlockIncrementEnergy
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hinc : SquareBlockIncrementEnergyBoundedStatement) :
    RHLean.Analysis.RiemannHypothesisStatement :=
  (squareBlockSmoothTransportGramBound_iff_riemannHypothesis criterion).mp
    (squareBlockSmoothTransportGramBound_of_incrementEnergy hinc)

end RHLean.Proof
