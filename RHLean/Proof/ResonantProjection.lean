import Mathlib
import RHLean.Analysis.ComplexQuadraticPhase

noncomputable section

namespace RHLean.Analysis

/--
An exact scale-`M` resonant mode index. The denominator is positive and lies
below the chosen scale-dependent cutoff. No coprimality, dominance, or
cancellation assumption is built into the index.
-/
structure ResonantModeIndex (cutoff : ℕ → ℕ) (M : ℕ) where
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_le_cutoff : denominator ≤ cutoff M

/-- The canonical quadratic-phase modulus attached to a resonant mode is `2r`. -/
def resonantModeModulus {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : ResonantModeIndex cutoff M) : ℤ :=
  2 * (mode.denominator : ℤ)

/-- The exact quadratic phase carried by a scale-dependent resonant mode. -/
def resonantQuadraticMode {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : ResonantModeIndex cutoff M) (u : ℤ) : ℂ :=
  RHLean.QuadraticPrimePhase.quadraticPhase
    mode.numerator (mode.denominator : ℤ) u

/-- Every resonant quadratic mode has the exact canonical period `2r`. -/
theorem resonantQuadraticMode_shift_modulus
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : ResonantModeIndex cutoff M) (u : ℤ) :
    resonantQuadraticMode mode (u + resonantModeModulus mode) =
      resonantQuadraticMode mode u := by
  simpa [resonantQuadraticMode, resonantModeModulus] using
    RHLean.QuadraticPrimePhase.quadraticPhase_shift_two_mul_r
      mode.numerator (mode.denominator : ℤ) u

/--
A scale-dependent resonant projection skeleton. The extraction map is required
only to land in the span of the declared resonant modes. This structure does not
assert idempotence, self-adjointness, orthogonality, or a Pythagorean identity.
-/
structure ResonantProjectionSkeleton (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  cutoff : ℕ → ℕ
  modeVector : (M : ℕ) → ResonantModeIndex cutoff M → E
  extraction : ℕ → E →ₗ[𝕜] E
  extraction_mem_span :
    ∀ M x, extraction M x ∈
      Submodule.span 𝕜 (Set.range (modeVector M))

/-- The span of the declared resonant modes at scale `M`. -/
def resonantSubspace {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (skeleton : ResonantProjectionSkeleton 𝕜 E) (M : ℕ) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (skeleton.modeVector M))

/-- The scale-`M` resonant component supplied by the extraction skeleton. -/
def resonantComponent {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (skeleton : ResonantProjectionSkeleton 𝕜 E) (M : ℕ) (x : E) : E :=
  skeleton.extraction M x

/-- The algebraic complement of the scale-`M` resonant component. -/
def nonresonantComponent {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (skeleton : ResonantProjectionSkeleton 𝕜 E) (M : ℕ) (x : E) : E :=
  x - resonantComponent skeleton M x

/-- The extracted resonant component lies in the declared resonant span. -/
theorem resonantComponent_mem_resonantSubspace
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (skeleton : ResonantProjectionSkeleton 𝕜 E) (M : ℕ) (x : E) :
    resonantComponent skeleton M x ∈ resonantSubspace skeleton M := by
  simpa [resonantComponent, resonantSubspace] using
    skeleton.extraction_mem_span M x

/--
The resonant and nonresonant components recombine exactly. This is purely an
algebraic decomposition and makes no orthogonality claim.
-/
theorem resonantComponent_add_nonresonantComponent
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (skeleton : ResonantProjectionSkeleton 𝕜 E) (M : ℕ) (x : E) :
    resonantComponent skeleton M x + nonresonantComponent skeleton M x = x := by
  unfold nonresonantComponent
  abel

end RHLean.Analysis
