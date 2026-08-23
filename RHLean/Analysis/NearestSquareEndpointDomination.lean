import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Nearest-square endpoint domination

This module makes the square-endpoint reduction pointwise and two-sided.
Inside the complete square block between `R^2 - 1` and `(R+1)^2 - 1`, every
integer lies within distance `R` of one of the two completed-square endpoints.
Since the Mertens summatory function changes by at most the length of an integer
interval, the full interior excursion is bounded by the larger adjacent endpoint
plus exactly one root-scale term.

The squared consequence shows that arbitrary interior points contribute only an
explicit `2 * R^2` baseline beyond adjacent endpoint energy.  The final theorem
re-exports the already-proved square-prefix-to-full-Mertens energy implication,
so future analytic work may focus on the completed-square sequence without
introducing a separate arbitrary-point obligation.
-/

noncomputable section

namespace RHLean.Analysis

private theorem squarePrefixEndpoint_pred_add_one
    (R : ℕ) (hR : 1 ≤ R) :
    squarePrefixEndpoint (R - 1) + 1 = R ^ 2 := by
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  simpa [hpred] using squarePrefixEndpoint_add_one (R - 1)

private theorem squarePrefixEndpoint_eq_pred_add_two_mul_add_one
    (R : ℕ) (hR : 1 ≤ R) :
    squarePrefixEndpoint R =
      squarePrefixEndpoint (R - 1) + 2 * R + 1 := by
  have hlow := squarePrefixEndpoint_pred_add_one R hR
  have hupp := squarePrefixEndpoint_add_one R
  have hsq : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  rw [hsq] at hupp
  omega

/-- Every point in a complete square block is controlled by the larger of the
two adjacent completed-square Mertens values plus exactly one root-scale term.
No asymptotic notation is used. -/
theorem norm_mertensSummatory_le_max_nearestSquareEndpoint_add_root
    (R x : ℕ)
    (hR : 1 ≤ R)
    (hlower : squarePrefixEndpoint (R - 1) ≤ x)
    (hupper : x ≤ squarePrefixEndpoint R) :
    ‖mertensSummatory x‖ ≤
      max ‖squarePrefixMertens (R - 1)‖ ‖squarePrefixMertens R‖ +
        (R : ℝ) := by
  have hblock :=
    squarePrefixEndpoint_eq_pred_add_two_mul_add_one R hR
  by_cases hnear : x - squarePrefixEndpoint (R - 1) ≤ R
  · have hgap :=
      norm_mertensSummatory_sub_le
        (squarePrefixEndpoint (R - 1)) x hlower
    have hgap' :
        ‖mertensSummatory x - squarePrefixMertens (R - 1)‖ ≤
          ((x - squarePrefixEndpoint (R - 1) : ℕ) : ℝ) := by
      simpa [squarePrefixMertens] using hgap
    have hnearR :
        ((x - squarePrefixEndpoint (R - 1) : ℕ) : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast hnear
    calc
      ‖mertensSummatory x‖ =
          ‖squarePrefixMertens (R - 1) +
            (mertensSummatory x - squarePrefixMertens (R - 1))‖ := by
        congr 1
        ring
      _ ≤ ‖squarePrefixMertens (R - 1)‖ +
            ‖mertensSummatory x - squarePrefixMertens (R - 1)‖ :=
        norm_add_le _ _
      _ ≤ ‖squarePrefixMertens (R - 1)‖ +
            ((x - squarePrefixEndpoint (R - 1) : ℕ) : ℝ) :=
        add_le_add_left hgap' _
      _ ≤ max ‖squarePrefixMertens (R - 1)‖ ‖squarePrefixMertens R‖ +
            (R : ℝ) :=
        add_le_add (le_max_left _ _) hnearR
  · have hfar : R < x - squarePrefixEndpoint (R - 1) := by omega
    have hnearUpper : squarePrefixEndpoint R - x ≤ R := by omega
    have hgap := norm_mertensSummatory_sub_le x (squarePrefixEndpoint R) hupper
    have hgap' :
        ‖mertensSummatory x - squarePrefixMertens R‖ ≤
          ((squarePrefixEndpoint R - x : ℕ) : ℝ) := by
      rw [squarePrefixMertens]
      calc
        ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint R)‖ =
            ‖-(mertensSummatory (squarePrefixEndpoint R) - mertensSummatory x)‖ := by
          congr 1
          ring
        _ = ‖mertensSummatory (squarePrefixEndpoint R) - mertensSummatory x‖ :=
          norm_neg _
        _ ≤ ((squarePrefixEndpoint R - x : ℕ) : ℝ) := hgap
    have hnearUpperR :
        ((squarePrefixEndpoint R - x : ℕ) : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast hnearUpper
    calc
      ‖mertensSummatory x‖ =
          ‖squarePrefixMertens R +
            (mertensSummatory x - squarePrefixMertens R)‖ := by
        congr 1
        ring
      _ ≤ ‖squarePrefixMertens R‖ +
            ‖mertensSummatory x - squarePrefixMertens R‖ :=
        norm_add_le _ _
      _ ≤ ‖squarePrefixMertens R‖ +
            ((squarePrefixEndpoint R - x : ℕ) : ℝ) :=
        add_le_add_left hgap' _
      _ ≤ max ‖squarePrefixMertens (R - 1)‖ ‖squarePrefixMertens R‖ +
            (R : ℝ) :=
        add_le_add (le_max_right _ _) hnearUpperR

private theorem sq_le_two_max_sq_add_two_sq
    {z a b r : ℝ}
    (hz : 0 ≤ z) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : z ≤ max a b + r) :
    z ^ 2 ≤ 2 * max (a ^ 2) (b ^ 2) + 2 * r ^ 2 := by
  rcases le_total a b with hab | hba
  · have habsq : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha hb).2 hab
    rw [max_eq_right hab] at h
    rw [max_eq_right habsq]
    have hzsq : z ^ 2 ≤ (b + r) ^ 2 :=
      (sq_le_sq₀ hz (add_nonneg hb hr)).2 h
    nlinarith [sq_nonneg (b - r)]
  · have hbasq : b ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hb ha).2 hba
    rw [max_eq_left hba] at h
    rw [max_eq_left hbasq]
    have hzsq : z ^ 2 ≤ (a + r) ^ 2 :=
      (sq_le_sq₀ hz (add_nonneg ha hr)).2 h
    nlinarith [sq_nonneg (a - r)]

/-- Squared nearest-endpoint domination.  Interior energy differs from the
larger adjacent completed-square endpoint energy by at most an explicit
`2 * R^2` root-scale baseline. -/
theorem norm_mertensSummatory_sq_le_two_max_nearestSquareEndpoint_sq_add_root_sq
    (R x : ℕ)
    (hR : 1 ≤ R)
    (hlower : squarePrefixEndpoint (R - 1) ≤ x)
    (hupper : x ≤ squarePrefixEndpoint R) :
    ‖mertensSummatory x‖ ^ 2 ≤
      2 * max (‖squarePrefixMertens (R - 1)‖ ^ 2)
          (‖squarePrefixMertens R‖ ^ 2) +
        2 * (R : ℝ) ^ 2 := by
  have h :=
    norm_mertensSummatory_le_max_nearestSquareEndpoint_add_root
      R x hR hlower hupper
  exact sq_le_two_max_sq_add_two_sq
    (norm_nonneg _)
    (norm_nonneg _)
    (norm_nonneg _)
    (Nat.cast_nonneg R)
    h

/-- Frontier certificate: completed-square energy control already implies the
full arbitrary-point Mertens energy criterion.  The analytic content is the
existing square-prefix theorem; the two results above make its finite
nearest-endpoint geometry explicit. -/
theorem arbitraryPointMertensEnergyBounded_of_squarePrefixEnergyBounded
    (hS : SquarePrefixEnergyBoundedStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_squarePrefixEnergyBounded hS

end RHLean.Analysis
