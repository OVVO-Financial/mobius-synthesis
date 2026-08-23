import RHLean.Analysis.StrongMertensLogNineBalanceCore

noncomputable section

open Filter Asymptotics Set

namespace RHLean.Analysis

/-! Final sharp-endpoint closure of the log-nine Strong Mertens chain. -/

/-- Balanced smoothed Mobius transform with subexponential decay. -/
theorem nativeSmoothedMobius_logNine_subexp_eventually
    (corridor : StrongMertensLogNineCorridor)
    {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      ‖nativeSmoothedMobius f (strongMertensBalanceEps corridor X) X‖ ≤
        C * X * Real.exp (-strongMertensFinalDecay corridor * strongMertensScale X) := by
  obtain ⟨C0, hC0, henv⟩ :=
    nativeSmoothedMobius_logNine_envelope_for corridor hsupp hnonneg hmass hdiff
  refine ⟨5 * C0, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (3 : ℝ),
    strongMertensScale_tendsto_atTop.eventually_gt_atTop (Real.log 3),
    strongMertens_balanced_envelopes_eventually corridor] with X hX hr3 hbal
  have heps : strongMertensBalanceEps corridor X ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨strongMertensBalanceEps_pos corridor X,
      strongMertensBalanceEps_lt_one corridor (by linarith)⟩
  have hT : 3 < strongMertensBalanceHeight X := by
    rw [strongMertensBalanceHeight, ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_lt_exp.mpr hr3
  have h := henv heps hX hT
  exact h.trans <| by
    have hC0nn : 0 ≤ C0 := hC0.le
    calc
      C0 * (strongMertensFarEnvelope (strongMertensBalanceEps corridor X) X
              (strongMertensBalanceHeight X) +
            strongMertensHorizontalEnvelope (strongMertensBalanceEps corridor X) X
              (strongMertensBalanceHeight X) +
            strongMertensVerticalEnvelope corridor (strongMertensBalanceEps corridor X) X
              (strongMertensBalanceHeight X))
        ≤ C0 * (5 * X * Real.exp
            (-strongMertensFinalDecay corridor * strongMertensScale X)) :=
          mul_le_mul_of_nonneg_left hbal hC0nn
      _ = 5 * C0 * X * Real.exp
          (-strongMertensFinalDecay corridor * strongMertensScale X) := by ring

/-- Transfer the balanced smoothed estimate to the sharp real Mertens sum. -/
theorem nativeMertensSharpReal_logNine_subexp_eventually_for
    (corridor : StrongMertensLogNineCorridor)
    {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      |nativeMertensSharpReal X| ≤
        C * X * Real.exp (-strongMertensFinalDecay corridor * strongMertensScale X) := by
  obtain ⟨Cs, hCs, hsmooth⟩ :=
    nativeSmoothedMobius_logNine_subexp_eventually corridor hsupp hnonneg hmass hdiff
  obtain ⟨Cc, hCc, hclose⟩ := strongMertens_smoothed_close_eps hdiff hsupp hnonneg hmass
  refine ⟨Cc + Cs, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (3 : ℝ),
    strongMertensScale_tendsto_atTop.eventually_ge_atTop (0 : ℝ),
    strongMertens_two_lt_X_mul_balanceEps corridor,
    hsmooth] with X hX hr0 hXeps hs
  let eps := strongMertensBalanceEps corridor X
  have heps0 : 0 < eps := strongMertensBalanceEps_pos corridor X
  have heps1 : eps < 1 := strongMertensBalanceEps_lt_one corridor (by linarith)
  have hc := hclose X hX eps heps0 heps1 hXeps
  let c := strongMertensFinalDecay corridor
  have hcA : c ≤ corridor.A / 8 := by
    dsimp [c, strongMertensFinalDecay]
    exact min_le_left _ _
  have heps_le : eps ≤ Real.exp (-c * strongMertensScale X) := by
    dsimp [eps, strongMertensBalanceEps]
    apply Real.exp_le_exp.mpr
    have hA := corridor.A_mem.1
    nlinarith
  have hclose' :
      ‖nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)‖ ≤
        Cc * X * Real.exp (-c * strongMertensScale X) := by
    calc
      _ ≤ Cc * eps * X := hc
      _ ≤ Cc * Real.exp (-c * strongMertensScale X) * X := by gcongr
      _ = Cc * X * Real.exp (-c * strongMertensScale X) := by ring
  have htri : ‖(nativeMertensSharpReal X : ℂ)‖ ≤
      ‖nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)‖ +
        ‖nativeSmoothedMobius f eps X‖ := by
    calc
      ‖(nativeMertensSharpReal X : ℂ)‖ =
          ‖nativeSmoothedMobius f eps X -
            (nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ))‖ := by
              congr 1
              ring
      _ ≤ ‖nativeSmoothedMobius f eps X‖ +
          ‖nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)‖ :=
        norm_sub_le (nativeSmoothedMobius f eps X)
          (nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ))
      _ = ‖nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)‖ +
          ‖nativeSmoothedMobius f eps X‖ := by ring
  have hfinal : ‖(nativeMertensSharpReal X : ℂ)‖ ≤
      (Cc + Cs) * X * Real.exp (-c * strongMertensScale X) :=
    htri.trans <| by
      calc
        ‖nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)‖ +
            ‖nativeSmoothedMobius f eps X‖
          ≤ Cc * X * Real.exp (-c * strongMertensScale X) +
            Cs * X * Real.exp (-c * strongMertensScale X) := add_le_add hclose' hs
        _ = (Cc + Cs) * X * Real.exp (-c * strongMertensScale X) := by ring
  simpa [c, Complex.norm_real, Real.norm_eq_abs] using hfinal

/-- The sharp real estimate transfers exactly to natural Mertens endpoints. -/
theorem nativeMertensSummatory_logNine_subexp_eventually
    (corridor : StrongMertensLogNineCorridor) :
    ∃ C > 0, ∀ᶠ N : ℕ in atTop,
      |nativeMertensSummatory N| ≤
        C * (N : ℝ) *
          Real.exp (-strongMertensFinalDecay corridor *
            strongMertensScale (N : ℝ)) := by
  obtain ⟨ν, hνdiff, hνnonneg, hνsupp, hνmass⟩ := SmoothExistence
  have hdiff : ContDiff ℝ 1 ν := hνdiff.of_le (by simp)
  have hnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ => hνnonneg x
  have hmass : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1 := by
    rwa [← MeasureTheory.integral_Ici_eq_integral_Ioi]
  obtain ⟨C, hC, hreal⟩ :=
    nativeMertensSharpReal_logNine_subexp_eventually_for
      corridor hνsupp hnonneg hmass hdiff
  refine ⟨C, hC, ?_⟩
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with N hN
  simpa using hN

/-- The global natural-endpoint target follows from the canonical log-nine
corridor and finite-prefix absorption. -/
theorem strongNativeMertensSubexp : StrongNativeMertensSubexp := by
  unfold StrongNativeMertensSubexp
  let corridor := strongMertensLogNineCorridor
  let c := strongMertensFinalDecay corridor
  have hc : 0 < c := by
    dsimp [c]
    exact strongMertensFinalDecay_pos corridor
  obtain ⟨C0, hC0, hlarge⟩ :=
    nativeMertensSummatory_logNine_subexp_eventually corridor
  rcases eventually_atTop.1 hlarge with ⟨M, hM⟩
  let D : ℕ → ℝ := fun n =>
    (n : ℝ) * Real.exp (-c * strongMertensScale (n : ℝ))
  let S : ℝ :=
    ∑ n ∈ Finset.range M, |nativeMertensSummatory n| / D n
  have hDnonneg (n : ℕ) : 0 ≤ D n := by
    dsimp [D]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun n _ =>
      div_nonneg (abs_nonneg _) (hDnonneg n)
  refine ⟨c, C0 + S, hc, by positivity, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hDpos : 0 < D N := by
    dsimp [D]
    exact mul_pos hNpos (Real.exp_pos _)
  by_cases hMN : M ≤ N
  · have htail := hM N hMN
    have htailD : |nativeMertensSummatory N| ≤ C0 * D N := by
      simpa [D, c, mul_assoc] using htail
    calc
      |nativeMertensSummatory N| ≤ C0 * D N := htailD
      _ ≤ (C0 + S) * D N := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS) hDpos.le
      _ = (C0 + S) * (N : ℝ) *
          Real.exp (-c * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 10)) := by
        dsimp [D, strongMertensScale]
        ring
  · have hNM : N < M := Nat.lt_of_not_ge hMN
    have hsingle : |nativeMertensSummatory N| / D N ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (fun n _ => div_nonneg (abs_nonneg _) (hDnonneg n))
        (Finset.mem_range.2 hNM)
    have hprefix : |nativeMertensSummatory N| ≤ S * D N :=
      (div_le_iff₀ hDpos).1 hsingle
    calc
      |nativeMertensSummatory N| ≤ S * D N := hprefix
      _ ≤ (C0 + S) * D N := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC0.le) hDpos.le
      _ = (C0 + S) * (N : ℝ) *
          Real.exp (-c * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 10)) := by
        dsimp [D, strongMertensScale]
        ring

end RHLean.Analysis