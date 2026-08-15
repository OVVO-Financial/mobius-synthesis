import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery
import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Analysis.SquarePrefixMertensBridge

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-!
# Recovered square-root wheel as the exact Mertens criterion

The arithmetic layer proves that a square-root-covered prime wheel recovers the
joint signed quantity `raw - 2 * smooth` exactly as the Möbius prefix.  This
module packages the canonical minimal square-root wheel and shows that a
critical energy estimate for that single signed quantity is exactly the existing
Mertens-energy criterion, hence exactly the square-prefix criterion already used
by the square-block route.

No quantitative estimate is asserted here.  The open theorem is isolated as the
boundedness statement below.
-/

/-- The canonical minimal square-root wheel prefix at physical cutoff `X`.
Only prime coordinates through `sqrt X` are used, and the smooth-core correction
is retained inside the signed object. -/
def sqrtWheelRecoveredPrefix (X : ℕ) : ℤ :=
  primeWheelRawPositivePrefix (primesUpTo (Nat.sqrt X)) X -
    2 * primeWheelSmoothPositivePrefix (primesUpTo (Nat.sqrt X)) X X

/-- The canonical prime set through `sqrt X` has exactly the coverage required
by the pointwise prime-wheel recovery theorem. -/
theorem primesUpTo_sqrtCoverage (X : ℕ) :
    PrimeWheelSqrtCoverage (primesUpTo (Nat.sqrt X)) X := by
  intro p hp hple
  exact mem_primesUpTo.mpr ⟨hp, hple⟩

/-- Exact arithmetic recovery for the canonical minimal square-root wheel. -/
theorem sqrtWheelRecoveredPrefix_eq_moebiusPositivePrefix (X : ℕ) :
    sqrtWheelRecoveredPrefix X = moebiusPositivePrefix X := by
  unfold sqrtWheelRecoveredPrefix
  exact primeWheelRaw_sub_two_smooth_eq_moebiusPositivePrefix
    (primesUpTo (Nat.sqrt X)) X X
    (by
      intro p hp
      exact prime_of_mem_primesUpTo hp)
    (primesUpTo_sqrtCoverage X) le_rfl

/-- The canonical recovered wheel is exactly the repository's standard integer
Möbius prefix. -/
theorem sqrtWheelRecoveredPrefix_eq_moebiusPrefix (X : ℕ) :
    sqrtWheelRecoveredPrefix X =
      ∑ n ∈ Finset.range (X + 1), μ n := by
  rw [sqrtWheelRecoveredPrefix_eq_moebiusPositivePrefix,
    moebiusPositivePrefix_eq_moebiusPrefix]

/-- After the harmless integer-to-complex cast, the recovered wheel prefix is
literally the analytic Mertens summatory function used downstream. -/
theorem sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory (X : ℕ) :
    ((sqrtWheelRecoveredPrefix X : ℤ) : ℂ) = mertensSummatory X := by
  rw [sqrtWheelRecoveredPrefix_eq_moebiusPrefix]
  simp [mertensSummatory]

/-- The exact quantitative target for the canonical square-root wheel.  This is
the squared form of the desired `X^(1/2+ε)` cancellation, expressed without
splitting raw and smooth mass. -/
def SqrtWheelRecoveredEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ,
        ‖((sqrtWheelRecoveredPrefix X : ℤ) : ℂ)‖ ^ 2 ≤
          C * Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)

/-- The recovered square-root wheel estimate is exactly the protected global
Mertens-energy criterion.  Thus proving the former loses no cancellation and
requires no additional analytic transfer theorem. -/
theorem sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded :
    SqrtWheelRecoveredEnergyBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro X
    have hx := hbound X
    rw [sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory X] at hx
    exact hx
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro X
    rw [sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory X]
    exact hbound X

/-- The same target is therefore exactly equivalent to the repository's
square-prefix energy criterion.  This is the formal square-block compatibility
statement for the recovered prime-wheel quantity. -/
theorem sqrtWheelRecoveredEnergyBounded_iff_squarePrefixEnergyBounded :
    SqrtWheelRecoveredEnergyBoundedStatement ↔
      SquarePrefixEnergyBoundedStatement := by
  exact sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded.trans
    mertensEnergyBounded_iff_squarePrefixEnergyBounded

/-- The existing Mertens continuation and completed-zeta reflection route turns
a proof of the recovered square-root wheel bound directly into RH. -/
theorem riemannHypothesis_of_sqrtWheelRecoveredEnergy
    (h : SqrtWheelRecoveredEnergyBoundedStatement) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  exact sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded.mp h

end RHLean.Analysis
