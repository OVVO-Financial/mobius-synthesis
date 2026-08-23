import Mathlib
import RHLean.Analysis.StrongMertensZetaKernel

/-!
# Small-height reciprocal-zeta control for the shared Mertens corridor

The literal reciprocal zeta is not continuous at Mathlib's junk value at one,
so compactness is applied to the regularized reciprocal from
`StrongMertensZetaKernel`.  Every actual shifted-contour point has real part
strictly below one, hence the regularized and literal reciprocals agree there.
-/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology

namespace RHLean.Analysis

local notation "zetaC" => riemannZeta

-- `StrongPNT.PNT1_ComplexAnalysis` declares a root-level `def I := Complex.I`,
-- so with `Complex` open the bare token `I` resolves two ways.
local notation "I" => Complex.I

/-- Uniform reciprocal-zeta bound on the bounded-height part of every shifted
line belonging to one shared corridor. -/
theorem strongMertens_inv_zeta_small_height_bdd
    (corridor : StrongMertensLogNineCorridor) :
    ∃ M ≥ 0, ∀ (T : ℝ), 3 ≤ T → ∀ (t : ℝ), |t| ≤ 3 →
      1 / ‖zetaC (strongMertensLogNineShift corridor.A T + t * I)‖ ≤ M := by
  let K : Set ℂ :=
    Set.Icc corridor.smallSigma 1 ×ℂ Set.Icc (-3 : ℝ) 3
  have hKcompact : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcontReg : ContinuousOn nativeInvZetaRegularized K := by
    apply nativeInvZetaRegularized_continuousOn
    intro s hs _hs1
    rw [← Complex.re_add_im s]
    exact corridor.small_zero s.im
      (abs_le.mpr ⟨hs.2.1, hs.2.2⟩) s.re hs.1.1
  have hcontNorm : ContinuousOn (fun s : ℂ => ‖nativeInvZetaRegularized s‖) K :=
    hcontReg.norm
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hcontNorm
  let M : ℝ := max B 0
  have hMnonneg : 0 ≤ M := le_max_right _ _
  refine ⟨M, hMnonneg, ?_⟩
  intro T hT t ht
  let sigma : ℝ := strongMertensLogNineShift corridor.A T
  let s : ℂ := (sigma : ℂ) + t * I
  have hsK : s ∈ K := by
    constructor
    · simpa [s, sigma] using
        ⟨corridor.shift_ge_small T hT,
          (corridor.shift_lt_one T hT).le⟩
    · have htlr := abs_le.mp ht
      simpa [s] using htlr
  have hsne : s ≠ 1 := by
    intro hs1
    have hre := congrArg Complex.re hs1
    simp only [s, sigma, add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, one_re] at hre
    exact (corridor.shift_lt_one T hT).ne hre
  have hreg : nativeInvZetaRegularized s = (zetaC s)⁻¹ := by
    simp [nativeInvZetaRegularized, hsne]
  have hb : ‖nativeInvZetaRegularized s‖ ≤ B := hB ⟨s, hsK, rfl⟩
  calc
    1 / ‖zetaC (strongMertensLogNineShift corridor.A T + t * I)‖
        = ‖nativeInvZetaRegularized s‖ := by
          rw [hreg, norm_inv, one_div]
    _ ≤ B := hb
    _ ≤ M := le_max_left _ _

end RHLean.Analysis
