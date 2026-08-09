import Mathlib
import RHLean.Analysis.ConcreteSquarePrefixGeometry

/-!
# Canonical high-sector arithmetic core

This analysis module contains the exact largest-prime-factor canonical geometry,
its square-block low/high decomposition, and the abstract low-increment control
interface. Analytic criterion and RH implication theorems remain in
`RHLean.Analysis.CanonicalHighSectorBridge`.

The namespace is retained as `RHLean.Proof` for API compatibility with the
existing repository theorem names while the dependency-carrying source file is
placed in the analysis layer.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The largest prime factor of `m`, with the harmless convention `P⁺(0)=P⁺(1)=1`. -/
noncomputable def canonicalLargestPrimeFactor (m : ℕ) : ℕ :=
  if h : 1 < m then
    m.primeFactors.max' (Nat.nonempty_primeFactors.mpr h)
  else
    1

/-- The canonical cofactor `c_m = m / P⁺(m)`. -/
def canonicalCofactor (m : ℕ) : ℕ :=
  m / canonicalLargestPrimeFactor m

/-- Twice the manuscript's signed canonical height:
`2 Y_m = q_m^2 - c_m^2`.

Using the doubled height avoids introducing division by `2` into the cutoff
predicate while retaining the exact signed geometry.
-/
def canonicalHeightTwice (m : ℕ) : ℝ :=
  (canonicalLargestPrimeFactor m : ℝ) ^ 2 -
    (canonicalCofactor m : ℝ) ^ 2

/-- The exact integer block `[j^2,(j+1)^2)`. -/
def canonicalSquareBlock (j : ℕ) : Finset ℕ :=
  Finset.Ico (j ^ 2) ((j + 1) ^ 2)

/-- The native canonical low-height predicate `|Y_m| ≤ Λ j`, written using
`2Y_m` as `|2Y_m| ≤ 2Λj`. -/
def IsCanonicalLowHeight (Λ : ℝ) (j m : ℕ) : Prop :=
  abs (canonicalHeightTwice m) ≤ 2 * Λ * (j : ℝ)

/-- The native canonical high-height predicate. -/
def IsCanonicalHighHeight (Λ : ℝ) (j m : ℕ) : Prop :=
  ¬ IsCanonicalLowHeight Λ j m

/-- Möbius weight as a complex scalar. -/
def canonicalMoebiusWeight (m : ℕ) : ℂ :=
  (((μ m : ℤ) : ℂ))

/-- Native canonical low-height increment in square block `j`. -/
noncomputable def canonicalLowIncrement (Λ : ℝ) (j : ℕ) : ℂ := by
  classical
  exact
    ∑ m ∈ canonicalSquareBlock j,
      if IsCanonicalLowHeight Λ j m then canonicalMoebiusWeight m else 0

/-- Native canonical high-height increment in square block `j`. -/
noncomputable def canonicalHighIncrement (Λ : ℝ) (j : ℕ) : ℂ := by
  classical
  exact
    ∑ m ∈ canonicalSquareBlock j,
      if IsCanonicalHighHeight Λ j m then canonicalMoebiusWeight m else 0

/-- Complete Möbius increment in square block `j`. -/
def canonicalTotalIncrement (j : ℕ) : ℂ :=
  ∑ m ∈ canonicalSquareBlock j, canonicalMoebiusWeight m

/-- Cumulative native low-height square-prefix value. -/
def canonicalLowPrefix (Λ : ℝ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), canonicalLowIncrement Λ j

/-- Cumulative native high-height square-prefix value `S_n^high(Λ)`. -/
def canonicalHighPrefix (Λ : ℝ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), canonicalHighIncrement Λ j

/-- Cumulative complete square-block sum. -/
def canonicalTotalPrefix (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), canonicalTotalIncrement j

/-- Every square block is partitioned exactly into its native canonical low and
high contributions. -/
theorem canonicalTotalIncrement_eq_low_add_high
    (Λ : ℝ) (j : ℕ) :
    canonicalTotalIncrement j =
      canonicalLowIncrement Λ j + canonicalHighIncrement Λ j := by
  classical
  unfold canonicalTotalIncrement canonicalLowIncrement canonicalHighIncrement
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : IsCanonicalLowHeight Λ j m
  · simp [IsCanonicalHighHeight, h]
  · simp [IsCanonicalHighHeight, h]

/-- Exact cumulative low/high recombination. -/
theorem canonicalTotalPrefix_eq_low_add_high
    (Λ : ℝ) (n : ℕ) :
    canonicalTotalPrefix n =
      canonicalLowPrefix Λ n + canonicalHighPrefix Λ n := by
  unfold canonicalTotalPrefix canonicalLowPrefix canonicalHighPrefix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact canonicalTotalIncrement_eq_low_add_high Λ j

/-- The complete square-block prefix is exactly the repository's concrete
square-prefix Mertens value at `X_n=(n+1)^2-1`. -/
theorem canonicalTotalPrefix_eq_squarePrefixMertens (n : ℕ) :
    canonicalTotalPrefix n = RHLean.Analysis.squarePrefixMertens n := by
  induction n with
  | zero =>
      simp [canonicalTotalPrefix, canonicalTotalIncrement, canonicalSquareBlock,
        canonicalMoebiusWeight, RHLean.Analysis.squarePrefixMertens,
        RHLean.Analysis.mertensSummatory, RHLean.Analysis.squarePrefixEndpoint]
  | succ n ih =>
      rw [canonicalTotalPrefix, Finset.sum_range_succ]
      change canonicalTotalPrefix n + canonicalTotalIncrement (n + 1) = _
      rw [ih]
      unfold canonicalTotalIncrement canonicalSquareBlock
      unfold RHLean.Analysis.squarePrefixMertens RHLean.Analysis.mertensSummatory
      rw [RHLean.Analysis.squarePrefixEndpoint_add_one]
      rw [RHLean.Analysis.squarePrefixEndpoint_add_one]
      have hle : (n + 1) ^ 2 ≤ (n + 2) ^ 2 := by
        exact Nat.pow_le_pow_left (by omega) 2
      simpa [canonicalMoebiusWeight, Nat.add_assoc] using
        (Finset.sum_range_add_sum_Ico
          (fun m : ℕ => canonicalMoebiusWeight m) hle)

/-- Exact signal-level realization of the paper's native canonical low/high
decomposition. -/
theorem squarePrefixMertens_eq_canonicalLow_add_high
    (Λ : ℝ) (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      canonicalLowPrefix Λ n + canonicalHighPrefix Λ n := by
  rw [← canonicalTotalPrefix_eq_squarePrefixMertens n]
  exact canonicalTotalPrefix_eq_low_add_high Λ n

/-- Typed uniform control interface for the native canonical low increment.

`RHLean.Analysis.CanonicalLowOccupancy` constructs this object unconditionally
with bound `floor Λ + 1`, where the extra one is precisely the isolated `m=1`
endpoint. -/
structure CanonicalLowIncrementControl (Λ : ℝ) where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_increment_le : ∀ j, ‖canonicalLowIncrement Λ j‖ ≤ bound

/-- A uniform block-increment bound gives the expected linear pointwise bound
for the cumulative canonical low sector. -/
theorem norm_canonicalLowPrefix_le
    {Λ : ℝ} (control : CanonicalLowIncrementControl Λ) (n : ℕ) :
    ‖canonicalLowPrefix Λ n‖ ≤ (n + 1 : ℝ) * control.bound := by
  unfold canonicalLowPrefix
  calc
    ‖∑ j ∈ Finset.range (n + 1), canonicalLowIncrement Λ j‖ ≤
        ∑ j ∈ Finset.range (n + 1), ‖canonicalLowIncrement Λ j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (n + 1), control.bound := by
      exact Finset.sum_le_sum fun j _ => control.norm_increment_le j
    _ = (n + 1 : ℝ) * control.bound := by simp

/-- The cumulative canonical low sector satisfies a quadratic pointwise energy
bound, including the `n=0` endpoint. -/
theorem canonicalLowPrefix_energy_le
    {Λ : ℝ} (control : CanonicalLowIncrementControl Λ) (n : ℕ) :
    ‖canonicalLowPrefix Λ n‖ ^ 2 ≤
      (4 * control.bound ^ 2) * (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [canonicalLowPrefix, canonicalLowIncrement, canonicalSquareBlock,
      canonicalMoebiusWeight]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnorm := norm_canonicalLowPrefix_le control n
    have hindexNat : n + 1 ≤ 2 * n := by omega
    have hindex : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hindexNat
    have hnorm_nonneg : 0 ≤ ‖canonicalLowPrefix Λ n‖ := norm_nonneg _
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hupper :
        ‖canonicalLowPrefix Λ n‖ ≤
          (2 * (n : ℝ)) * control.bound := by
      calc
        ‖canonicalLowPrefix Λ n‖ ≤ (n + 1 : ℝ) * control.bound := hnorm
        _ ≤ (2 * (n : ℝ)) * control.bound :=
          mul_le_mul_of_nonneg_right hindex control.bound_nonneg
    have hupper_nonneg : 0 ≤ (2 * (n : ℝ)) * control.bound :=
      mul_nonneg (mul_nonneg (by norm_num) hn_nonneg) control.bound_nonneg
    calc
      ‖canonicalLowPrefix Λ n‖ ^ 2 ≤
          ((2 * (n : ℝ)) * control.bound) ^ 2 :=
        (sq_le_sq₀ hnorm_nonneg hupper_nonneg).2 hupper
      _ = (4 * control.bound ^ 2) * (n : ℝ) ^ 2 := by ring

end RHLean.Proof
