import Mathlib
import RHLean.Proof.ResonantProjection

namespace RHLean.Analysis

/-- A state with separately typed resonant and nonresonant components. -/
structure ResonantNonresonantState (R N : Type*) where
  resonant : R
  nonresonant : N

/--
The explicit scale-dependent block recurrence. The four linear maps are kept as
separate fields so neither leakage direction can be hidden inside an opaque
operator. Low-height, endpoint, and boundary forcing are also separate fields.
No contraction, triangularity, or zero-leakage property is assumed.
-/
structure ResonantLeakageOperator (𝕜 R N : Type*)
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N] where
  A_M : ℕ → R →ₗ[𝕜] R
  B_M : ℕ → N →ₗ[𝕜] R
  C_M : ℕ → R →ₗ[𝕜] N
  D_M : ℕ → N →ₗ[𝕜] N
  lowHeightResonant : ℕ → R
  lowHeightNonresonant : ℕ → N
  endpointResonant : ℕ → R
  endpointNonresonant : ℕ → N
  boundaryResonant : ℕ → R
  boundaryNonresonant : ℕ → N

/-- The total resonant forcing, with all three sources displayed explicitly. -/
def resonantForcing
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N) (M : ℕ) : R :=
  operator.lowHeightResonant M +
    operator.endpointResonant M +
      operator.boundaryResonant M

/-- The total nonresonant forcing, with all three sources displayed explicitly. -/
def nonresonantForcing
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N) (M : ℕ) : N :=
  operator.lowHeightNonresonant M +
    operator.endpointNonresonant M +
      operator.boundaryNonresonant M

/-- The resonant state propagated through the resonant block `A_M`. -/
def resonantPropagation
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) : R :=
  operator.A_M M parent.resonant

/-- Leakage from the nonresonant state into the resonant state through `B_M`. -/
def nonresonantToResonantLeakage
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) : R :=
  operator.B_M M parent.nonresonant

/-- Leakage from the resonant state into the nonresonant state through `C_M`. -/
def resonantToNonresonantLeakage
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) : N :=
  operator.C_M M parent.resonant

/-- The nonresonant state propagated through the nonresonant block `D_M`. -/
def nonresonantPropagation
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) : N :=
  operator.D_M M parent.nonresonant

/-- The resonant component of the exact affine block update. -/
def resonantUpdate
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) : R :=
  resonantPropagation operator M parent +
    nonresonantToResonantLeakage operator M parent +
      resonantForcing operator M

/-- The nonresonant component of the exact affine block update. -/
def nonresonantUpdate
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) : N :=
  resonantToNonresonantLeakage operator M parent +
    nonresonantPropagation operator M parent +
      nonresonantForcing operator M

/-- The full exact affine block update at scale `M`. -/
def leakageUpdate
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) :
    ResonantNonresonantState R N where
  resonant := resonantUpdate operator M parent
  nonresonant := nonresonantUpdate operator M parent

/-- Exact resonant row of the affine block recurrence. -/
theorem leakageUpdate_resonant
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) :
    (leakageUpdate operator M parent).resonant =
      operator.A_M M parent.resonant +
        operator.B_M M parent.nonresonant +
          (operator.lowHeightResonant M +
            operator.endpointResonant M +
              operator.boundaryResonant M) := by
  rfl

/-- Exact nonresonant row of the affine block recurrence. -/
theorem leakageUpdate_nonresonant
    {𝕜 R N : Type*}
    [Semiring 𝕜]
    [AddCommMonoid R] [Module 𝕜 R]
    [AddCommMonoid N] [Module 𝕜 N]
    (operator : ResonantLeakageOperator 𝕜 R N)
    (M : ℕ) (parent : ResonantNonresonantState R N) :
    (leakageUpdate operator M parent).nonresonant =
      operator.C_M M parent.resonant +
        operator.D_M M parent.nonresonant +
          (operator.lowHeightNonresonant M +
            operator.endpointNonresonant M +
              operator.boundaryNonresonant M) := by
  rfl

end RHLean.Analysis
