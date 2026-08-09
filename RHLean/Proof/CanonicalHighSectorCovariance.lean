import Mathlib
import RHLean.Analysis.CanonicalHighSectorBridge

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Sum of a complex-valued sequence on the translated window `[N,N+H)`. -/
def localWindowSum (f : ℕ → ℂ) (N H : ℕ) : ℂ :=
  ∑ h ∈ Finset.range H, f (N + h)

/-- Arithmetic mean of a complex-valued sequence on `[N,N+H)`.

The real and imaginary coordinates are averaged separately. This agrees with
`localWindowSum f N H / H` when `H > 0`, while remaining total at `H = 0`.
-/
def localWindowMean (f : ℕ → ℂ) (N H : ℕ) : ℂ :=
  ⟨(∑ h ∈ Finset.range H, (f (N + h)).re) / (H : ℝ),
    (∑ h ∈ Finset.range H, (f (N + h)).im) / (H : ℝ)⟩

/-- The coherent window-mean contribution `H * |mean|²`. -/
def localCoherentMeanEnergy (f : ℕ → ℂ) (N H : ℕ) : ℝ :=
  (H : ℝ) * ‖localWindowMean f N H‖ ^ 2

/-- The centered covariance energy on `[N,N+H)`. -/
def localCenteredCovarianceEnergy (f : ℕ → ℂ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ‖f (N + h) - localWindowMean f N H‖ ^ 2

private theorem real_sum_sq_eq_mean_add_centered
    (g : ℕ → ℝ) (H : ℕ) (hH : 0 < H) :
    (∑ h ∈ Finset.range H, g h ^ 2) =
      (H : ℝ) * ((∑ h ∈ Finset.range H, g h) / (H : ℝ)) ^ 2 +
        ∑ h ∈ Finset.range H,
          (g h - (∑ k ∈ Finset.range H, g k) / (H : ℝ)) ^ 2 := by
  let S : ℝ := ∑ h ∈ Finset.range H, g h
  let μ : ℝ := S / (H : ℝ)
  have hHne : (H : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hH)
  have hmean : (H : ℝ) * μ = S := by
    dsimp [μ]
    field_simp
  have hexpand :
      (∑ h ∈ Finset.range H, (g h - μ) ^ 2) =
        (∑ h ∈ Finset.range H, g h ^ 2) - 2 * μ * S + (H : ℝ) * μ ^ 2 := by
    calc
      (∑ h ∈ Finset.range H, (g h - μ) ^ 2) =
          ∑ h ∈ Finset.range H, (g h ^ 2 - 2 * μ * g h + μ ^ 2) := by
        apply Finset.sum_congr rfl
        intro h hh
        ring
      _ = (∑ h ∈ Finset.range H, g h ^ 2) - 2 * μ * S +
            (H : ℝ) * μ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
        simp [S, nsmul_eq_mul]
  change (∑ h ∈ Finset.range H, g h ^ 2) =
    (H : ℝ) * μ ^ 2 + ∑ h ∈ Finset.range H, (g h - μ) ^ 2
  rw [hexpand, ← hmean]
  ring

/-- Exact finite-window decomposition into coherent mean energy and centered
covariance energy. -/
theorem localSequenceEnergy_eq_coherentMean_add_centeredCovariance
    (f : ℕ → ℂ) (N H : ℕ) (hH : 1 ≤ H) :
    RHLean.Analysis.localSequenceEnergy f N H =
      localCoherentMeanEnergy f N H + localCenteredCovarianceEnergy f N H := by
  have hre := real_sum_sq_eq_mean_add_centered
    (fun h => (f (N + h)).re) H (Nat.zero_lt_of_lt hH)
  have him := real_sum_sq_eq_mean_add_centered
    (fun h => (f (N + h)).im) H (Nat.zero_lt_of_lt hH)
  simp only [pow_two] at hre him
  unfold RHLean.Analysis.localSequenceEnergy localCoherentMeanEnergy
    localCenteredCovarianceEnergy localWindowMean
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  rw [hre, him]
  ring

/-- Coherent mean energy is nonnegative. -/
theorem localCoherentMeanEnergy_nonneg
    (f : ℕ → ℂ) (N H : ℕ) :
    0 ≤ localCoherentMeanEnergy f N H := by
  unfold localCoherentMeanEnergy
  positivity

/-- Centered covariance energy is nonnegative. -/
theorem localCenteredCovarianceEnergy_nonneg
    (f : ℕ → ℂ) (N H : ℕ) :
    0 ≤ localCenteredCovarianceEnergy f N H := by
  unfold localCenteredCovarianceEnergy
  positivity

/-- On a one-point window the centered covariance term vanishes identically. -/
@[simp] theorem localCenteredCovarianceEnergy_one
    (f : ℕ → ℂ) (N : ℕ) :
    localCenteredCovarianceEnergy f N 1 = 0 := by
  simp [localCenteredCovarianceEnergy, localWindowMean]

/-- On a one-point window all energy is coherent mean energy. -/
@[simp] theorem localCoherentMeanEnergy_one
    (f : ℕ → ℂ) (N : ℕ) :
    localCoherentMeanEnergy f N 1 = ‖f N‖ ^ 2 := by
  simp [localCoherentMeanEnergy, localWindowMean]

/-- Generic uniform local bound for a complex-valued sequence. -/
def SequenceUniformLocalBoundedStatement (f : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy f N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- Uniform local control of the coherent window-mean energy. -/
def CoherentMeanUniformLocalBoundedStatement (f : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        localCoherentMeanEnergy f N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- Uniform local control of the centered covariance energy. -/
def CenteredCovarianceUniformLocalBoundedStatement (f : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        localCenteredCovarianceEnergy f N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The uncentered local-energy criterion is exactly equivalent to simultaneous
control of the coherent mean and centered covariance pieces. -/
theorem sequenceUniformLocalBounded_iff_coherentMean_and_centeredCovariance
    (f : ℕ → ℂ) :
    SequenceUniformLocalBoundedStatement f ↔
      CoherentMeanUniformLocalBoundedStatement f ∧
        CenteredCovarianceUniformLocalBoundedStatement f := by
  constructor
  · intro htotal
    constructor
    · intro ε hε
      rcases htotal ε hε with ⟨C, hC, hbound⟩
      refine ⟨C, hC, ?_⟩
      intro N H hH hHN
      have hsplit :=
        localSequenceEnergy_eq_coherentMean_add_centeredCovariance f N H hH
      have hcov_nonneg := localCenteredCovarianceEnergy_nonneg f N H
      have hmean_le :
          localCoherentMeanEnergy f N H ≤
            RHLean.Analysis.localSequenceEnergy f N H := by
        nlinarith
      exact hmean_le.trans (hbound N H hH hHN)
    · intro ε hε
      rcases htotal ε hε with ⟨C, hC, hbound⟩
      refine ⟨C, hC, ?_⟩
      intro N H hH hHN
      have hsplit :=
        localSequenceEnergy_eq_coherentMean_add_centeredCovariance f N H hH
      have hmean_nonneg := localCoherentMeanEnergy_nonneg f N H
      have hcov_le :
          localCenteredCovarianceEnergy f N H ≤
            RHLean.Analysis.localSequenceEnergy f N H := by
        nlinarith
      exact hcov_le.trans (hbound N H hH hHN)
  · rintro ⟨hmean, hcov⟩ ε hε
    rcases hmean ε hε with ⟨Cmean, hCmean, hmeanBound⟩
    rcases hcov ε hε with ⟨Ccov, hCcov, hcovBound⟩
    refine ⟨Cmean + Ccov, add_nonneg hCmean hCcov, ?_⟩
    intro N H hH hHN
    rw [localSequenceEnergy_eq_coherentMean_add_centeredCovariance f N H hH]
    have hm := hmeanBound N H hH hHN
    have hc := hcovBound N H hH hHN
    calc
      localCoherentMeanEnergy f N H + localCenteredCovarianceEnergy f N H ≤
          Cmean * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) +
            Ccov * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) :=
        add_le_add hm hc
      _ = (Cmean + Ccov) * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by
        ring

/-- Canonical coherent-level half of `(HS)`. -/
def CanonicalHighCoherentMeanUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  CoherentMeanUniformLocalBoundedStatement (canonicalHighPrefix Λ)

/-- Canonical centered-covariance half of `(HS)`. -/
def CanonicalHighCenteredCovarianceUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  CenteredCovarianceUniformLocalBoundedStatement (canonicalHighPrefix Λ)

/-- Canonical `(HS)` is exactly the conjunction of coherent-level control and
centered covariance control. -/
theorem canonicalHighUniformLocalBounded_iff_coherentMean_and_centeredCovariance
    (Λ : ℝ) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      CanonicalHighCoherentMeanUniformLocalBoundedStatement Λ ∧
        CanonicalHighCenteredCovarianceUniformLocalBoundedStatement Λ := by
  simpa [CanonicalHighUniformLocalBoundedStatement,
    CanonicalHighCoherentMeanUniformLocalBoundedStatement,
    CanonicalHighCenteredCovarianceUniformLocalBoundedStatement,
    SequenceUniformLocalBoundedStatement] using
      sequenceUniformLocalBounded_iff_coherentMean_and_centeredCovariance
        (canonicalHighPrefix Λ)

/-- Exact conditional bridge from the two covariance pieces to RH. This does
not prove either analytic estimate; it only replaces the single `(HS)` premise
by its exact coherent/centered decomposition. -/
theorem canonicalHighCoherentMean_and_centeredCovariance_iff_riemannHypothesis
    (Λ : ℝ) (control : CanonicalLowIncrementControl Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    (CanonicalHighCoherentMeanUniformLocalBoundedStatement Λ ∧
      CanonicalHighCenteredCovarianceUniformLocalBoundedStatement Λ) ↔
        RHLean.Analysis.RiemannHypothesisStatement := by
  calc
    (CanonicalHighCoherentMeanUniformLocalBoundedStatement Λ ∧
      CanonicalHighCenteredCovarianceUniformLocalBoundedStatement Λ) ↔
        CanonicalHighUniformLocalBoundedStatement Λ :=
      (canonicalHighUniformLocalBounded_iff_coherentMean_and_centeredCovariance Λ).symm
    _ ↔ RHLean.Analysis.RiemannHypothesisStatement :=
      canonicalHighUniformLocalBounded_iff_riemannHypothesis Λ control criterion

end RHLean.Proof
