import Mathlib.Analysis.Fourier.ZMod

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- The ordinary bilinear pairing on the finite additive torus `ZMod N`. -/
def finiteTorusPairing {N : ℕ} [NeZero N]
    (f g : ZMod N → ℂ) : ℂ :=
  ∑ x : ZMod N, f x * g x

/-- The Fourier-side bilinear pairing.  The second transform is evaluated at
`-r`, matching the sign convention in `ZMod.dft_apply`. -/
def finiteTorusSpectralPairing {N : ℕ} [NeZero N]
    (f g : ZMod N → ℂ) : ℂ :=
  ((N : ℂ)⁻¹) * ∑ r : ZMod N, ZMod.dft f r * ZMod.dft g (-r)

/-- Exact finite Fourier pairing identity on `ZMod N`.

This is the bilinear (not sesquilinear) form needed for the interval-prefix
reduction: one factor is the arithmetic field and the other is the indicator
of the pinned interval. -/
theorem finiteTorusPairing_eq_spectral
    {N : ℕ} [NeZero N]
    (f g : ZMod N → ℂ) :
    finiteTorusPairing f g = finiteTorusSpectralPairing f g := by
  classical
  unfold finiteTorusPairing finiteTorusSpectralPairing
  have hInv : ZMod.dft.symm (ZMod.dft f) = f :=
    ZMod.dft.symm_apply_apply f
  calc
    (∑ x : ZMod N, f x * g x) =
        ∑ x : ZMod N,
          (((N : ℂ)⁻¹) *
              ∑ r : ZMod N,
                (ZMod.stdAddChar (r * x) * ZMod.dft f r)) *
            g x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← congrFun hInv x, ZMod.invDFT_apply]
      simp only [smul_eq_mul]
    _ = ((N : ℂ)⁻¹) *
        ∑ x : ZMod N,
          (∑ r : ZMod N,
            (ZMod.stdAddChar (r * x) * ZMod.dft f r)) *
            g x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ((N : ℂ)⁻¹) *
        ∑ x : ZMod N,
          ∑ r : ZMod N,
            (ZMod.stdAddChar (r * x) * ZMod.dft f r) * g x := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ((N : ℂ)⁻¹) *
        ∑ r : ZMod N,
          ∑ x : ZMod N,
            (ZMod.stdAddChar (r * x) * ZMod.dft f r) * g x := by
      congr 1
      exact Finset.sum_comm
    _ = ((N : ℂ)⁻¹) *
        ∑ r : ZMod N,
          ZMod.dft f r *
            ∑ x : ZMod N,
              (ZMod.stdAddChar (r * x) * g x) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ((N : ℂ)⁻¹) *
        ∑ r : ZMod N, ZMod.dft f r * ZMod.dft g (-r) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      apply congrArg (fun z : ℂ => ZMod.dft f r * z)
      rw [ZMod.dft_apply]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [smul_eq_mul]
      congr 1
      congr 1
      ring

end RHLean.Analysis
