import Mathlib
import RHLean.Analysis.PrimeWheelFourierReduction
import RHLean.Analysis.PrimeWheelTorusRealization
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity

open scoped BigOperators
open AddChar

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

private def finNatCastEquivZMod' (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun i := (i.val : ZMod n)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv z := ZMod.natCast_zmod_val z

/-- Finite Dirichlet response at frequency `r`, with the interval translated to
start at zero. -/
def primeWheelDirichletKernel
    (W : PrimeWheelFiniteSystem) (N : ℕ) (r : ZMod W.modulus) : ℂ :=
  ∑ j ∈ Finset.range N, ZMod.stdAddChar ((j : ZMod W.modulus) * r)

/-- Phase imposed by the pinned arithmetic start `lower + 1`. -/
def primeWheelPinnedPhase
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) : ℂ :=
  ZMod.stdAddChar (((W.lower + 1 : ℕ) : ZMod W.modulus) * r)

/-- The DFT of the pinned interval window is exactly the synchronized start
phase times a finite Dirichlet kernel. -/
theorem prefixWindowSpectrum_neg_eq_phase_mul_dirichlet
    (W : PrimeWheelFiniteSystem) (N : ℕ) (r : ZMod W.modulus)
    (hupper : W.lower + N ≤ W.upper) :
    W.prefixWindowSpectrum (W.lower + N) (-r) =
      primeWheelPinnedPhase W r * primeWheelDirichletKernel W N r := by
  classical
  have hxmod : W.lower + N < W.modulus :=
    lt_of_le_of_lt hupper W.upper_lt_modulus
  let F : ZMod W.modulus → ℂ := fun z =>
    ZMod.stdAddChar (z * r) *
      (if W.lower < z.val ∧ z.val ≤ W.lower + N then 1 else 0)
  unfold PrimeWheelFiniteSystem.prefixWindowSpectrum
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, mul_neg, neg_neg]
  change (∑ z : ZMod W.modulus, F z) = _
  calc
    (∑ z : ZMod W.modulus, F z) =
        ∑ i : Fin W.modulus, F ((finNatCastEquivZMod' W.modulus) i) := by
      exact ((finNatCastEquivZMod' W.modulus).sum_comp F).symm
    _ = ∑ n ∈ Finset.range W.modulus,
        if W.lower < n ∧ n ≤ W.lower + N then
          ZMod.stdAddChar ((n : ZMod W.modulus) * r) else 0 := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      change F (i.val : ZMod W.modulus) = _
      have hval : ((i.val : ZMod W.modulus).val) = i.val :=
        ZMod.val_natCast_of_lt i.isLt
      by_cases hwin : W.lower < i.val ∧ i.val ≤ W.lower + N
      · simp [F, hval, hwin]
      · simp [F, hval, hwin]
    _ = ∑ n ∈ Finset.Ioc W.lower (W.lower + N),
        ZMod.stdAddChar ((n : ZMod W.modulus) * r) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
        constructor
        · intro hn
          exact hn.2
        · intro hn
          exact ⟨lt_of_le_of_lt hn.2 hxmod, hn⟩
      · intro n hn
        rfl
    _ = ∑ n ∈ Finset.Ico (W.lower + 1) (W.lower + N + 1),
        ZMod.stdAddChar ((n : ZMod W.modulus) * r) := by
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_Ioc, Finset.mem_Ico]
        omega
      · intro n hn
        rfl
    _ = ∑ j ∈ Finset.range N,
        ZMod.stdAddChar ((((W.lower + 1) + j : ℕ) : ZMod W.modulus) * r) := by
      rw [Finset.sum_Ico_eq_sum_range]
      rw [show W.lower + N + 1 - (W.lower + 1) = N by omega]
    _ = primeWheelPinnedPhase W r * primeWheelDirichletKernel W N r := by
      unfold primeWheelPinnedPhase primeWheelDirichletKernel
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← map_add_eq_mul]
      congr 1
      push_cast
      ring

/-- Phase-adjusted arithmetic coefficient in the exact pinned-prefix formula. -/
def primeWheelPinnedCoefficient
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) : ℂ :=
  ((W.modulus : ℂ)⁻¹) * W.jointSpectrum r * primeWheelPinnedPhase W r

/-- Exact finite phase/Dirichlet representation of a prefix of length `N`. -/
def primeWheelDirichletPrefix
    (W : PrimeWheelFiniteSystem) (N : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    primeWheelPinnedCoefficient W r * primeWheelDirichletKernel W N r

/-- The generic spectral prefix is exactly the phase-adjusted arithmetic vector
paired with the finite Dirichlet response. -/
theorem spectralPrefix_lower_add_eq_dirichletPrefix
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (hupper : W.lower + N ≤ W.upper) :
    W.spectralPrefix (W.lower + N) = primeWheelDirichletPrefix W N := by
  unfold PrimeWheelFiniteSystem.spectralPrefix primeWheelDirichletPrefix
    primeWheelPinnedCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [prefixWindowSpectrum_neg_eq_phase_mul_dirichlet W N r hupper]
  ring

/-- Concrete primorial specialization: the explicit Dirichlet sum is exactly
the corresponding Mertens increment. -/
theorem primorialWheel_dirichletPrefix_eq_mertens_sub
    (k N : ℕ)
    (hNpos : 0 < N)
    (hupper : primorialBlockLower k + N ≤ primorialBlockUpper k) :
    primeWheelDirichletPrefix (primorialWheelSystem k) N =
      mertensSummatory (primorialBlockLower k + N) -
        mertensSummatory (primorialBlockLower k) := by
  rw [← spectralPrefix_lower_add_eq_dirichletPrefix
    (primorialWheelSystem k) N hupper]
  have hlower : primorialBlockLower k < primorialBlockLower k + N :=
    Nat.lt_add_of_pos_right hNpos
  have hlowerSys :
      (primorialWheelSystem k).lower < (primorialWheelSystem k).lower + N := by
    simpa [primorialWheelSystem] using hlower
  have hupperSys :
      (primorialWheelSystem k).lower + N ≤ (primorialWheelSystem k).upper := by
    change primorialBlockLower k + N ≤ primorialBlockUpper k
    exact hupper
  rw [(primorialWheelSystem k).spectralPrefix_eq_residual
    (primorialWheelSystem k).canonicalTorusRealizationCertificate
    hlowerSys hupperSys]
  exact primorialWheel_residual_cast_eq_mertens_sub k hlower hupper

end RHLean.Analysis
