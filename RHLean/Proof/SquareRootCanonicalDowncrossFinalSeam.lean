import Mathlib
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Analysis.MertensEnergyRHForward

/-!
# Canonical root-downcross final seam

The orientation-split route exposes an ancestral Mertens transform, but that
quantity is not the primitive obstruction.  In the unsplit `S = A - T`
coordinates the complete smooth population `A_R` is already removed exactly by
the canonical low-wheel involution.  What survives is one signed adjacent
multiplicative root-downcross ledger:

`M(R^2 - 1) = M(R) - D_R`.

The same endpoint also has the compiled three-section description

`M(R^2 - 1) = A_R - Middle_R - Top_R`,

where the top block is deterministic and the middle block is the only
nontrivial post-root fresh-prime evolution.  Combining the two descriptions
therefore gives one simultaneous-coordinate seam for the same signed mass.

This file names the only new quantitative proposition needed at this seam:

`||D_R|| <= C * R`.

No estimate for `D_R` is proved here.  The rest of the file proves that this
single linear bound implies the square-prefix energy criterion and then the
repository's native formal Riemann hypothesis theorem.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- **Primitive final quantitative seam.**  The canonical adjacent root-downcross
ledger has uniformly linear signed mass.  This is deliberately stated on the
unsplit `S = A - T` residual rather than on either smooth orientation. -/
def SquareRootCanonicalDowncrossLinearBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖lowWheelCanonicalDowncrossLedger R‖ ≤ C * (R : ℝ)

/-- The square-prefix jump from the lower Mertens state is exactly the negative
canonical downcross ledger. -/
theorem squarePrefixMertens_sub_mertens_eq_neg_canonicalDowncross
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) - mertensSummatory R =
      -lowWheelCanonicalDowncrossLedger R := by
  rw [squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR]
  ring

/-- Norm form of the primitive seam: no inequality or asymptotic input is used. -/
theorem norm_squarePrefixMertens_sub_mertens_eq_canonicalDowncross
    (R : ℕ) (hR : 3 ≤ R) :
    ‖squarePrefixMertens (R - 1) - mertensSummatory R‖ =
      ‖lowWheelCanonicalDowncrossLedger R‖ := by
  rw [squarePrefixMertens_sub_mertens_eq_neg_canonicalDowncross R hR]
  simp

/-- **Simultaneous-coordinate identity.**  The same downcross ledger is what is
left when the middle fresh-prime evolution and deterministic top block are read
against the complete smooth stopping state. -/
theorem canonicalDowncross_eq_lower_sub_smooth_add_middle_add_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalDowncrossLedger R =
      mertensSummatory R - squareRootSmoothMass (R - 1) +
        squareRootMiddleMertensTail R +
          ((squareRootTopFibrePrimes R).card : ℂ) := by
  have hdown := squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR
  have hmiddle := squarePrefixMertens_eq_smooth_sub_middle_sub_topCard R hR
  calc
    lowWheelCanonicalDowncrossLedger R =
        mertensSummatory R - squarePrefixMertens (R - 1) := by
      rw [hdown]
      ring
    _ = mertensSummatory R -
          (squareRootSmoothMass (R - 1) -
            squareRootMiddleMertensTail R -
              ((squareRootTopFibrePrimes R).card : ℂ)) := by
      rw [hmiddle]
    _ = mertensSummatory R - squareRootSmoothMass (R - 1) +
          squareRootMiddleMertensTail R +
            ((squareRootTopFibrePrimes R).card : ℂ) := by
      ring

/-- A linear downcross bound immediately gives a linear square-prefix Mertens
bound, using only the trivial interval bound `|M(R)| <= R`. -/
theorem norm_squarePrefixMertens_le_of_canonicalDowncrossLinear
    {C : ℝ} (_hC : 0 ≤ C)
    (hdown : ∀ R : ℕ, 3 ≤ R →
      ‖lowWheelCanonicalDowncrossLedger R‖ ≤ C * (R : ℝ))
    {R : ℕ} (hR : 3 ≤ R) :
    ‖squarePrefixMertens (R - 1)‖ ≤ (C + 1) * (R : ℝ) := by
  have hMstep := norm_mertensSummatory_sub_le 0 R (Nat.zero_le R)
  have hM : ‖mertensSummatory R‖ ≤ (R : ℝ) := by
    simpa using hMstep
  rw [squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR]
  calc
    ‖mertensSummatory R - lowWheelCanonicalDowncrossLedger R‖ ≤
        ‖mertensSummatory R‖ + ‖lowWheelCanonicalDowncrossLedger R‖ :=
      norm_sub_le _ _
    _ ≤ (R : ℝ) + C * (R : ℝ) := add_le_add hM (hdown R hR)
    _ = (C + 1) * (R : ℝ) := by ring

/-- The primitive linear downcross seam supplies the repository's current
square-prefix pointwise energy criterion. -/
theorem squarePrefixCurrentPointwiseBounded_of_canonicalDowncrossLinear
    (hdown : SquareRootCanonicalDowncrossLinearBound) :
    SquarePrefixCurrentPointwiseBoundedStatement := by
  obtain ⟨C, hC, hD⟩ := hdown
  intro ε hε
  refine ⟨4 * (C + 1) ^ 2 + 9, by positivity, ?_⟩
  intro N hN
  by_cases hN1 : N = 1
  · subst N
    have hinterval :=
      norm_mertensSummatory_sub_le 0 (squarePrefixEndpoint 1)
        (Nat.zero_le (squarePrefixEndpoint 1))
    have hnorm : ‖squarePrefixMertens 1‖ ≤ 3 := by
      simpa [squarePrefixMertens, squarePrefixEndpoint] using hinterval
    have hsq : ‖squarePrefixMertens 1‖ ^ 2 ≤ 9 := by
      nlinarith [norm_nonneg (squarePrefixMertens 1)]
    have hcoef : 9 ≤ 4 * (C + 1) ^ 2 + 9 := by
      nlinarith [sq_nonneg (C + 1)]
    simpa using hsq.trans hcoef
  · have hN2 : 2 ≤ N := by omega
    have hR : 3 ≤ N + 1 := by omega
    have hlin :=
      norm_squarePrefixMertens_le_of_canonicalDowncrossLinear
        hC hD (R := N + 1) hR
    have hlinN :
        ‖squarePrefixMertens N‖ ≤
          (C + 1) * (((N + 1 : ℕ) : ℝ)) := by
      simpa using hlin
    have hC1 : 0 ≤ C + 1 := by linarith
    have hNplus : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
      exact_mod_cast (by omega : N + 1 ≤ 2 * N)
    have hlin2 :
        ‖squarePrefixMertens N‖ ≤ 2 * (C + 1) * (N : ℝ) := by
      calc
        ‖squarePrefixMertens N‖ ≤
            (C + 1) * (((N + 1 : ℕ) : ℝ)) := hlinN
        _ ≤ (C + 1) * (2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hNplus hC1
        _ = 2 * (C + 1) * (N : ℝ) := by ring
    have hright : 0 ≤ 2 * (C + 1) * (N : ℝ) := by positivity
    have hsq :
        ‖squarePrefixMertens N‖ ^ 2 ≤
          (2 * (C + 1) * (N : ℝ)) ^ 2 := by
      nlinarith [norm_nonneg (squarePrefixMertens N)]
    have hsq' :
        ‖squarePrefixMertens N‖ ^ 2 ≤
          4 * (C + 1) ^ 2 * (N : ℝ) ^ 2 := by
      calc
        ‖squarePrefixMertens N‖ ^ 2 ≤
            (2 * (C + 1) * (N : ℝ)) ^ 2 := hsq
        _ = 4 * (C + 1) ^ 2 * (N : ℝ) ^ 2 := by ring
    have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hrpow :
        (N : ℝ) ^ 2 ≤ Real.rpow (N : ℝ) (2 + ε) := by
      have hmono :=
        Real.rpow_le_rpow_of_exponent_le hbase
          (by linarith : (2 : ℝ) ≤ 2 + ε)
      -- `Real.rpow_natCast` states the exponent as `((2 : ℕ) : ℝ)`, which is not
      -- syntactically the literal `(2 : ℝ)` produced by the monotonicity lemma,
      -- so bridge the two rather than rewriting one into the other.
      have h2 : Real.rpow (N : ℝ) (2 : ℝ) = (N : ℝ) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
        exact Real.rpow_natCast (N : ℝ) 2
      calc
        (N : ℝ) ^ 2 = Real.rpow (N : ℝ) (2 : ℝ) := h2.symm
        _ ≤ Real.rpow (N : ℝ) (2 + ε) := hmono
    have hsmallCoeff : 0 ≤ 4 * (C + 1) ^ 2 := by positivity
    have hcoeff :
        4 * (C + 1) ^ 2 ≤ 4 * (C + 1) ^ 2 + 9 := by linarith
    calc
      ‖squarePrefixMertens N‖ ^ 2 ≤
          4 * (C + 1) ^ 2 * (N : ℝ) ^ 2 := hsq'
      _ ≤ 4 * (C + 1) ^ 2 * Real.rpow (N : ℝ) (2 + ε) :=
        mul_le_mul_of_nonneg_left hrpow hsmallCoeff
      _ ≤ (4 * (C + 1) ^ 2 + 9) *
          Real.rpow (N : ℝ) (2 + ε) :=
        mul_le_mul_of_nonneg_right hcoeff
          (Real.rpow_nonneg (by positivity) _)

/-- The primitive downcross bound therefore gives the exact square-prefix energy
criterion already consumed by the analytic bridge. -/
theorem squarePrefixEnergyBounded_of_canonicalDowncrossLinear
    (hdown : SquareRootCanonicalDowncrossLinearBound) :
    SquarePrefixEnergyBoundedStatement := by
  exact (squarePrefixEnergyBounded_iff_currentPointwise).2
    (squarePrefixCurrentPointwiseBounded_of_canonicalDowncrossLinear hdown)

/-- **Formal closure.**  A uniform linear bound on the one canonical root-downcross
ledger implies the repository's native formal Riemann hypothesis theorem. -/
theorem riemannHypothesis_of_canonicalDowncrossLinear
    (hdown : SquareRootCanonicalDowncrossLinearBound) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  apply mertensEnergyBounded_of_squarePrefixEnergyBounded
  exact squarePrefixEnergyBounded_of_canonicalDowncrossLinear hdown

end RHLean.Proof
