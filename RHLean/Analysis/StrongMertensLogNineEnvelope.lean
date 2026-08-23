import Mathlib
import RHLean.Analysis.StrongMertensLogNineBounds

/-!
# Five-leg envelope for the shared log-nine Mertens contour

This file contains no new analytic estimate.  It packages the two right tails,
two horizontal cuts, and shifted vertical cut into three scalar envelopes and
then applies the residue-free contour identity.  One corridor object is passed
through every theorem.
-/

noncomputable section

open Filter Finset Topology Asymptotics Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

/-- Combined scale for the two far tails. -/
def strongMertensFarEnvelope (eps X T : ℝ) : ℝ :=
  X * Real.log X / (eps * Real.sqrt T)

/-- Combined scale for the two horizontal cuts. -/
def strongMertensHorizontalEnvelope (eps X T : ℝ) : ℝ :=
  X * (1 + (Real.log T) ^ 10) / (eps * T ^ 2)

/-- Scale for the shifted vertical cut. -/
def strongMertensVerticalEnvelope
    (corridor : StrongMertensLogNineCorridor) (eps X T : ℝ) : ℝ :=
  X * Real.exp (-corridor.A * Real.log X / (Real.log T) ^ 9) *
    (1 + (Real.log T) ^ 7) / eps

/-- The five contour legs are bounded by the three shared scalar envelopes. -/
theorem nativeMertensFiveLeg_logNine_bound_for
    (corridor : StrongMertensLogNineCorridor)
    {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T →
      let sigmaLeft := strongMertensLogNineShift corridor.A T
      ‖nativeMertensContourM1 f eps X T‖ +
          ‖nativeMertensContourM2 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM3 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM4 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM5 f eps X T‖ ≤
        C * (strongMertensFarEnvelope eps X T +
          strongMertensHorizontalEnvelope eps X T +
          strongMertensVerticalEnvelope corridor eps X T) := by
  obtain ⟨C1, hC1, hM1⟩ := nativeMertensM1_logNine_bound hsupp hdiff
  obtain ⟨C5, hC5, hM5⟩ := nativeMertensM5_logNine_bound hsupp hdiff
  obtain ⟨Ch, hCh, hHorizontal⟩ :=
    nativeMertensHorizontal_logNine_bound_for corridor hsupp hnonneg hmass hdiff
  obtain ⟨C3, hC3, hM3⟩ :=
    nativeMertensM3_logNine_bound_for corridor hsupp hnonneg hmass hdiff
  let C : ℝ := C1 + C5 + Ch + C3 + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro eps X T heps hX hT
  simp only []
  let sigmaLeft : ℝ := strongMertensLogNineShift corridor.A T
  have h1 := hM1 heps hX hT
  have h5 := hM5 heps hX hT
  have hh := hHorizontal heps hX hT
  have h3 := hM3 heps hX hT
  dsimp [sigmaLeft] at hh h3 ⊢
  have hXnonneg : 0 ≤ X := by linarith
  have hlogXnonneg : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogTnonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hfar_nonneg : 0 ≤ strongMertensFarEnvelope eps X T := by
    unfold strongMertensFarEnvelope
    exact div_nonneg
      (mul_nonneg hXnonneg hlogXnonneg)
      (mul_nonneg heps.1.le (Real.sqrt_nonneg T))
  have hhor_nonneg : 0 ≤ strongMertensHorizontalEnvelope eps X T := by
    unfold strongMertensHorizontalEnvelope
    exact div_nonneg
      (mul_nonneg hXnonneg (add_nonneg zero_le_one (pow_nonneg hlogTnonneg 10)))
      (mul_nonneg heps.1.le (sq_nonneg T))
  have hvert_nonneg : 0 ≤ strongMertensVerticalEnvelope corridor eps X T := by
    unfold strongMertensVerticalEnvelope
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg hXnonneg (Real.exp_pos _).le)
        (add_nonneg zero_le_one (pow_nonneg hlogTnonneg 7)))
      heps.1.le
  have h1' : ‖nativeMertensContourM1 f eps X T‖ ≤
      C1 * strongMertensFarEnvelope eps X T := by
    simpa [strongMertensFarEnvelope] using h1
  have h5' : ‖nativeMertensContourM5 f eps X T‖ ≤
      C5 * strongMertensFarEnvelope eps X T := by
    simpa [strongMertensFarEnvelope] using h5
  have hh' :
      ‖nativeMertensContourM2 f eps X T
          (strongMertensLogNineShift corridor.A T)‖ +
        ‖nativeMertensContourM4 f eps X T
          (strongMertensLogNineShift corridor.A T)‖ ≤
      Ch * strongMertensHorizontalEnvelope eps X T := by
    unfold strongMertensHorizontalEnvelope
    convert hh using 1
    ring
  have h3' :
      ‖nativeMertensContourM3 f eps X T
          (strongMertensLogNineShift corridor.A T)‖ ≤
      C3 * strongMertensVerticalEnvelope corridor eps X T := by
    unfold strongMertensVerticalEnvelope
    convert h3 using 1
    ring
  calc
    ‖nativeMertensContourM1 f eps X T‖ +
          ‖nativeMertensContourM2 f eps X T
            (strongMertensLogNineShift corridor.A T)‖ +
          ‖nativeMertensContourM3 f eps X T
            (strongMertensLogNineShift corridor.A T)‖ +
          ‖nativeMertensContourM4 f eps X T
            (strongMertensLogNineShift corridor.A T)‖ +
          ‖nativeMertensContourM5 f eps X T‖
      = (‖nativeMertensContourM1 f eps X T‖ +
          ‖nativeMertensContourM5 f eps X T‖) +
        (‖nativeMertensContourM2 f eps X T
            (strongMertensLogNineShift corridor.A T)‖ +
          ‖nativeMertensContourM4 f eps X T
            (strongMertensLogNineShift corridor.A T)‖) +
        ‖nativeMertensContourM3 f eps X T
          (strongMertensLogNineShift corridor.A T)‖ := by ring
    _ ≤ (C1 + C5) * strongMertensFarEnvelope eps X T +
        Ch * strongMertensHorizontalEnvelope eps X T +
        C3 * strongMertensVerticalEnvelope corridor eps X T := by
      have h15 :
          ‖nativeMertensContourM1 f eps X T‖ +
              ‖nativeMertensContourM5 f eps X T‖ ≤
            (C1 + C5) * strongMertensFarEnvelope eps X T := by
        calc
          _ ≤ C1 * strongMertensFarEnvelope eps X T +
              C5 * strongMertensFarEnvelope eps X T := add_le_add h1' h5'
          _ = _ := by ring
      exact add_le_add (add_le_add h15 hh') h3'
    _ ≤ C * strongMertensFarEnvelope eps X T +
        C * strongMertensHorizontalEnvelope eps X T +
        C * strongMertensVerticalEnvelope corridor eps X T := by
      have h15C : C1 + C5 ≤ C := by dsimp [C]; linarith [hCh, hC3]
      have hChC : Ch ≤ C := by dsimp [C]; linarith [hC1, hC5, hC3]
      have hC3C : C3 ≤ C := by dsimp [C]; linarith [hC1, hC5, hCh]
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_right h15C hfar_nonneg)
          (mul_le_mul_of_nonneg_right hChC hhor_nonneg))
        (mul_le_mul_of_nonneg_right hC3C hvert_nonneg)
    _ = C * (strongMertensFarEnvelope eps X T +
          strongMertensHorizontalEnvelope eps X T +
          strongMertensVerticalEnvelope corridor eps X T) := by ring

/-- The residue-free pull together with the five-leg estimate bounds the whole
smoothed Mobius transform by the three shared envelopes. -/
theorem nativeSmoothedMobius_logNine_envelope_for
    (corridor : StrongMertensLogNineCorridor)
    {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T →
      ‖nativeSmoothedMobius f eps X‖ ≤
        C * (strongMertensFarEnvelope eps X T +
          strongMertensHorizontalEnvelope eps X T +
          strongMertensVerticalEnvelope corridor eps X T) := by
  obtain ⟨C, hC, hFive⟩ :=
    nativeMertensFiveLeg_logNine_bound_for corridor hsupp hnonneg hmass hdiff
  refine ⟨C, hC, ?_⟩
  intro eps X T heps hX hT
  let sigmaLeft : ℝ := strongMertensLogNineShift corridor.A T
  have hHolo := strongMertensSmoothedIntegrand_holomorphicOn_punctured_box
    corridor heps.1 heps.2 hsupp hnonneg hmass hdiff
    (X := X) (T := T) (by linarith : 0 < X) hT.le
  have hInt := strongMertensSmoothedIntegrand_integrable_right_line
    heps.1 heps.2 hX hsupp hnonneg hmass hdiff
  have hpull := nativeMertensContourPull_holds
    heps.1 heps.2 hX (by linarith : 0 < T)
    (corridor.shift_pos T hT.le) (corridor.shift_lt_one T hT.le)
    hsupp hnonneg hmass hdiff hHolo hInt
  have htri :
      ‖nativeSmoothedMobius f eps X‖ ≤
        ‖nativeMertensContourM1 f eps X T‖ +
          ‖nativeMertensContourM2 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM3 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM4 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM5 f eps X T‖ := by
    rw [hpull]
    calc
      ‖nativeMertensContourM1 f eps X T -
            nativeMertensContourM2 f eps X T sigmaLeft +
            nativeMertensContourM3 f eps X T sigmaLeft +
            nativeMertensContourM4 f eps X T sigmaLeft +
            nativeMertensContourM5 f eps X T‖
        ≤ ‖nativeMertensContourM1 f eps X T -
              nativeMertensContourM2 f eps X T sigmaLeft +
              nativeMertensContourM3 f eps X T sigmaLeft +
              nativeMertensContourM4 f eps X T sigmaLeft‖ +
            ‖nativeMertensContourM5 f eps X T‖ := norm_add_le _ _
      _ ≤ (‖nativeMertensContourM1 f eps X T -
              nativeMertensContourM2 f eps X T sigmaLeft +
              nativeMertensContourM3 f eps X T sigmaLeft‖ +
            ‖nativeMertensContourM4 f eps X T sigmaLeft‖) +
            ‖nativeMertensContourM5 f eps X T‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ((‖nativeMertensContourM1 f eps X T -
              nativeMertensContourM2 f eps X T sigmaLeft‖ +
            ‖nativeMertensContourM3 f eps X T sigmaLeft‖) +
            ‖nativeMertensContourM4 f eps X T sigmaLeft‖) +
            ‖nativeMertensContourM5 f eps X T‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ((‖nativeMertensContourM1 f eps X T‖ +
              ‖nativeMertensContourM2 f eps X T sigmaLeft‖ +
            ‖nativeMertensContourM3 f eps X T sigmaLeft‖) +
            ‖nativeMertensContourM4 f eps X T sigmaLeft‖) +
            ‖nativeMertensContourM5 f eps X T‖ := by
          gcongr
          exact norm_sub_le _ _
      _ = ‖nativeMertensContourM1 f eps X T‖ +
          ‖nativeMertensContourM2 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM3 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM4 f eps X T sigmaLeft‖ +
          ‖nativeMertensContourM5 f eps X T‖ := by ring
  exact htri.trans (by
    dsimp [sigmaLeft]
    exact hFive heps hX hT)

end RHLean.Analysis