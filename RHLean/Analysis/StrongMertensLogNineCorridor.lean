import Mathlib
import Mathlib.NumberTheory.LSeries.Dirichlet
import PrimeNumberTheoremAnd.ZetaBounds
import StrongPNT.PNT4_ZeroFreeRegion
import StrongPNT.ZetaZeroFree

/-!
# Shared log-nine corridor for the unconditional strong Mertens bridge

This file reconciles, once and for all, the existential constants coming from
PNT+'s reciprocal-zeta estimate, StrongPNT's zero-free region, and StrongPNT's
bounded-height zero-free box.  Downstream contour code sees one positive constant
`A`, one left boundary

  `sigma_A(T) = 1 - A / (log T)^9`,

and does not destruct any of the underlying existential theorems again.

No wide-strip reciprocal-zeta hypothesis is introduced here.  In particular, this
file does not use the certificate-dependent de la Vallee Poussin consumer bound
from external developments.
-/

noncomputable section

open Complex Filter Set
open scoped ArithmeticFunction.Moebius LSeries.notation Topology

namespace RHLean.Analysis

local notation "zeta" => riemannZeta
local notation "I" => Complex.I

/-- The fixed left boundary used by the Mobius contour pull. -/
def strongMertensLogNineShift (A T : ℝ) : ℝ :=
  1 - A / (Real.log T) ^ 9

/-- One coherent analytic corridor.  The small-height theorem is retained in its
strong form because it is useful for compactness bounds near the pole. -/
structure StrongMertensLogNineCorridor where
  A : ℝ
  A_mem : A ∈ Set.Ioc (0 : ℝ) (1 / 2)
  invConst : ℝ
  invConst_pos : 0 < invConst
  smallSigma : ℝ
  smallSigma_lt_one : smallSigma < 1
  small_zero :
    ∀ (t : ℝ), |t| ≤ 3 → ∀ (sigma : ℝ), smallSigma ≤ sigma →
      zeta (sigma + t * I) ≠ 0
  shift_ge_small :
    ∀ (T : ℝ), 3 ≤ T → smallSigma ≤ strongMertensLogNineShift A T
  shift_pos :
    ∀ (T : ℝ), 3 ≤ T → 0 < strongMertensLogNineShift A T
  shift_lt_one :
    ∀ (T : ℝ), 3 ≤ T → strongMertensLogNineShift A T < 1
  zero_free_box :
    ∀ (T : ℝ), 3 ≤ T →
      ∀ s ∈ (((Set.Icc (strongMertensLogNineShift A T) 2) ×ℂ
          (Set.Icc (-T) T)) \ {(1 : ℂ)}),
        zeta s ≠ 0
  inv_window_large :
    ∀ (sigma t : ℝ), 3 < |t| →
      sigma ∈ Set.Ico
        (1 - A / (Real.log |t|) ^ 9)
        (1 + A / (Real.log |t|) ^ 9) →
      1 / ‖zeta (sigma + t * I)‖ ≤
        invConst * (Real.log |t|) ^ (7 : ℝ)
  inv_shift_large :
    ∀ (T t : ℝ), 3 < T → 3 < |t| → |t| ≤ T →
      1 / ‖zeta (strongMertensLogNineShift A T + t * I)‖ ≤
        invConst * (Real.log |t|) ^ (7 : ℝ)

private lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
  apply Real.log_lt_log (Real.exp_pos 1)
  exact Real.exp_one_lt_d9.trans (by norm_num)

private lemma log_mono_of_three_le {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    Real.log x ≤ Real.log y := by
  exact Real.log_le_log (by linarith) hxy

private lemma log_pow_nine_mono {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    (Real.log x) ^ 9 ≤ (Real.log y) ^ 9 := by
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog := log_mono_of_three_le hx hxy
  exact pow_le_pow_left₀ hxlog hlog 9

private lemma log_le_log_pow_nine {x : ℝ} (hx : 3 ≤ x) :
    Real.log x ≤ (Real.log x) ^ 9 := by
  have hlog : 1 < Real.log x :=
    lt_of_lt_of_le log_three_gt_one (log_mono_of_three_le (by norm_num) hx)
  have hpos : (0 : ℝ) < Real.log x := lt_trans zero_lt_one hlog
  have h8 : (1 : ℝ) ≤ (Real.log x) ^ 8 := one_le_pow₀ hlog.le
  nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr h8)]

private lemma shift_lt_one {A T : ℝ} (hA : 0 < A) (hT : 3 ≤ T) :
    strongMertensLogNineShift A T < 1 := by
  unfold strongMertensLogNineShift
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have : 0 < A / (Real.log T) ^ 9 := by positivity
  linarith

/-- The canonical shared corridor.  Its `A` is the minimum of:

* the `ZetaInvBnd` log-nine constant;
* the StrongPNT zero-free constant;
* the bounded-height allowance `(1-smallSigma) * (log 3)^9`.

Shrinking is proved explicitly, so no downstream theorem relies on unrelated
existential witnesses being definitionally equal.

`StrongMertensLogNineCorridor` bundles real data, so it lives in `Type`, while
every analytic input below (`ZetaInvBnd`, `ZetaZeroFree_p`, `ZetaNoZerosInBox'`)
is a `Prop`-valued existential whose witnesses may not be eliminated into
`Type`.  Existence is therefore proved as the `Prop` statement `Nonempty
StrongMertensLogNineCorridor`, and the corridor term used downstream is the
choice of a witness. -/
theorem nonempty_strongMertensLogNineCorridor :
    Nonempty StrongMertensLogNineCorridor := by
  obtain ⟨Ainv, hAinv, Cinv, hCinv, hInv⟩ := ZetaInvBnd
  obtain ⟨Azf, hAzf, hZF⟩ := ZetaZeroFree_p
  obtain ⟨sigma0, hsigma0, hSmall⟩ := ZetaNoZerosInBox' 3

  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set Acorner : ℝ := (1 - sigma0) * (Real.log 3) ^ 9 with hAcorner
  have hAcornerpos : 0 < Acorner := by
    rw [hAcorner]
    exact mul_pos (sub_pos.mpr hsigma0) (pow_pos hlog3pos 9)

  set A : ℝ := min Ainv (min Azf Acorner) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    exact lt_min hAinv.1 (lt_min hAzf.1 hAcornerpos)
  have hA_le_inv : A ≤ Ainv := by
    rw [hAdef]
    exact min_le_left _ _
  have hA_le_zf : A ≤ Azf := by
    rw [hAdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hA_le_corner : A ≤ Acorner := by
    rw [hAdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hAle : A ≤ (1 : ℝ) / 2 := hA_le_inv.trans hAinv.2
  have hAmem : A ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨hApos, hAle⟩

  have hshift_ge_small : ∀ T : ℝ, 3 ≤ T →
      sigma0 ≤ strongMertensLogNineShift A T := by
    intro T hT
    have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
    have hlog3powpos : 0 < (Real.log 3) ^ 9 := pow_pos hlog3pos 9
    have hlogTpowpos : 0 < (Real.log T) ^ 9 := pow_pos hlogTpos 9
    have hpow : (Real.log 3) ^ 9 ≤ (Real.log T) ^ 9 :=
      log_pow_nine_mono (by norm_num) hT
    have h1 : A / (Real.log T) ^ 9 ≤ Acorner / (Real.log T) ^ 9 := by
      exact (div_le_div_iff_of_pos_right hlogTpowpos).2 hA_le_corner
    have h2 : Acorner / (Real.log T) ^ 9 ≤ Acorner / (Real.log 3) ^ 9 := by
      rw [div_le_div_iff₀ hlogTpowpos hlog3powpos]
      exact mul_le_mul_of_nonneg_left hpow hAcornerpos.le
    have hcorner_eval : Acorner / (Real.log 3) ^ 9 = 1 - sigma0 := by
      rw [hAcorner]
      field_simp
    have h12 := h1.trans h2
    rw [hcorner_eval] at h12
    unfold strongMertensLogNineShift
    linarith

  have hshift_pos : ∀ T : ℝ, 3 ≤ T → 0 < strongMertensLogNineShift A T := by
    intro T hT
    have hlogT : 1 < Real.log T :=
      lt_of_lt_of_le log_three_gt_one (log_mono_of_three_le (by norm_num) hT)
    have hpow1 : (1 : ℝ) ≤ (Real.log T) ^ 9 := by
      exact one_le_pow₀ hlogT.le
    have hdiv : A / (Real.log T) ^ 9 ≤ (1 : ℝ) / 2 := by
      have hlogpowpos : 0 < (Real.log T) ^ 9 := by positivity
      calc
        A / (Real.log T) ^ 9 ≤ A / 1 := by
          rw [div_le_div_iff₀ hlogpowpos (by norm_num)]
          exact mul_le_mul_of_nonneg_left hpow1 hApos.le
        _ = A := by ring
        _ ≤ (1 : ℝ) / 2 := hAle
    unfold strongMertensLogNineShift
    linarith

  have hlarge_width_inv : ∀ {T t : ℝ}, 3 < |t| → |t| ≤ T →
      A / (Real.log T) ^ 9 ≤ Ainv / (Real.log |t|) ^ 9 := by
    intro T t ht htle
    have ht3 : (3 : ℝ) ≤ |t| := ht.le
    have hT3 : (3 : ℝ) ≤ T := ht3.trans htle
    have hlogtpos : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
    have hpwtpos : 0 < (Real.log |t|) ^ 9 := pow_pos hlogtpos 9
    have hpwTpos : 0 < (Real.log T) ^ 9 := pow_pos hlogTpos 9
    have hpw : (Real.log |t|) ^ 9 ≤ (Real.log T) ^ 9 :=
      log_pow_nine_mono ht3 htle
    rw [div_le_div_iff₀ hpwTpos hpwtpos]
    calc
      A * (Real.log |t|) ^ 9 ≤ Ainv * (Real.log |t|) ^ 9 :=
        mul_le_mul_of_nonneg_right hA_le_inv hpwtpos.le
      _ ≤ Ainv * (Real.log T) ^ 9 :=
        mul_le_mul_of_nonneg_left hpw hAinv.1.le

  have hlarge_width_zf : ∀ {T t : ℝ}, 3 < |t| → |t| ≤ T →
      A / (Real.log T) ^ 9 ≤ Azf / Real.log |t| := by
    intro T t ht htle
    have ht3 : (3 : ℝ) ≤ |t| := ht.le
    have hT3 : (3 : ℝ) ≤ T := ht3.trans htle
    have hlogtpos : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
    have hpwTpos : 0 < (Real.log T) ^ 9 := pow_pos hlogTpos 9
    have hlogle : Real.log |t| ≤ Real.log T :=
      log_mono_of_three_le ht3 htle
    have hlogTpow : Real.log T ≤ (Real.log T) ^ 9 :=
      log_le_log_pow_nine hT3
    have hden : Real.log |t| ≤ (Real.log T) ^ 9 := hlogle.trans hlogTpow
    rw [div_le_div_iff₀ hpwTpos hlogtpos]
    calc
      A * Real.log |t| ≤ Azf * Real.log |t| :=
        mul_le_mul_of_nonneg_right hA_le_zf hlogtpos.le
      _ ≤ Azf * (Real.log T) ^ 9 :=
        mul_le_mul_of_nonneg_left hden hAzf.1.le

  have hbox : ∀ (T : ℝ), 3 ≤ T →
      ∀ s ∈ (((Set.Icc (strongMertensLogNineShift A T) 2) ×ℂ
          (Set.Icc (-T) T)) \ {(1 : ℂ)}),
        zeta s ≠ 0 := by
    intro T hT s hs
    have hsbox := hs.1
    rw [Complex.mem_reProdIm] at hsbox
    obtain ⟨hre, him⟩ := hsbox
    have himabs : |s.im| ≤ T := abs_le.mpr ⟨him.1, him.2⟩
    rcases le_or_gt 1 s.re with hre1 | hrelt
    · exact riemannZeta_ne_zero_of_one_le_re hre1
    · rcases le_or_gt |s.im| 3 with hsmall | hlarge
      · have hsig : sigma0 ≤ s.re :=
          (hshift_ge_small T hT).trans hre.1
        rw [← re_add_im s]
        exact hSmall s.im hsmall s.re hsig
      · have hwidth := hlarge_width_zf hlarge himabs
        have hleft : 1 - Azf / Real.log |s.im| ^ 1 ≤ s.re := by
          simp only [pow_one]
          have hshift : 1 - Azf / Real.log |s.im| ≤
              strongMertensLogNineShift A T := by
            unfold strongMertensLogNineShift
            linarith
          exact hshift.trans hre.1
        have hmem : s.re ∈ Set.Ico (1 - Azf / Real.log |s.im| ^ 1) 1 :=
          ⟨hleft, hrelt⟩
        rw [← re_add_im s]
        exact hZF s.re s.im hlarge hmem

  have hinvwindow : ∀ (sigma t : ℝ), 3 < |t| →
      sigma ∈ Set.Ico
        (1 - A / (Real.log |t|) ^ 9)
        (1 + A / (Real.log |t|) ^ 9) →
      1 / ‖zeta (sigma + t * I)‖ ≤
        Cinv * (Real.log |t|) ^ (7 : ℝ) := by
    intro sigma t ht hsigma
    have hlogtpos : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hden : 0 < (Real.log |t|) ^ 9 := pow_pos hlogtpos 9
    have hfrac : A / (Real.log |t|) ^ 9 ≤
        Ainv / (Real.log |t|) ^ 9 :=
      (div_le_div_iff_of_pos_right hden).2 hA_le_inv
    have hlower : 1 - Ainv / (Real.log |t|) ^ 9 ≤ sigma := by
      linarith [hsigma.1, hfrac]
    have hupper : sigma < 1 + Ainv / (Real.log |t|) ^ 9 := by
      linarith [hsigma.2, hfrac]
    exact hInv sigma t ht ⟨hlower, hupper⟩

  have hinvshift : ∀ (T t : ℝ), 3 < T → 3 < |t| → |t| ≤ T →
      1 / ‖zeta (strongMertensLogNineShift A T + t * I)‖ ≤
        Cinv * (Real.log |t|) ^ (7 : ℝ) := by
    intro T t hT ht htle
    have hwidth := hlarge_width_inv ht htle
    have hlower : 1 - Ainv / (Real.log |t|) ^ 9 ≤
        strongMertensLogNineShift A T := by
      unfold strongMertensLogNineShift
      linarith
    have hupper : strongMertensLogNineShift A T <
        1 + Ainv / (Real.log |t|) ^ 9 := by
      have hshiftlt : strongMertensLogNineShift A T < 1 :=
        shift_lt_one hApos hT.le
      have hplus : 1 < 1 + Ainv / (Real.log |t|) ^ 9 := by
        have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
        -- `positivity` cannot see `0 < Ainv`: the corridor only carries
        -- `Ainv ∈ Ioc 0 (1/2)`, so give the division its two factors directly.
        have : 0 < Ainv / (Real.log |t|) ^ 9 := div_pos hAinv.1 (pow_pos hlog 9)
        linarith
      exact hshiftlt.trans hplus
    exact hInv (strongMertensLogNineShift A T) t ht ⟨hlower, hupper⟩

  exact
    ⟨{ A := A
       A_mem := hAmem
       invConst := Cinv
       invConst_pos := hCinv
       smallSigma := sigma0
       smallSigma_lt_one := hsigma0
       small_zero := hSmall
       shift_ge_small := hshift_ge_small
       shift_pos := hshift_pos
       shift_lt_one := fun T hT => shift_lt_one hApos hT
       zero_free_box := hbox
       inv_window_large := hinvwindow
       inv_shift_large := hinvshift }⟩

/-- The single corridor object threaded through the whole contour stack.  Every
downstream module takes a `StrongMertensLogNineCorridor` as an argument, so this
choice is made exactly once, here. -/
def strongMertensLogNineCorridor : StrongMertensLogNineCorridor :=
  Classical.choice nonempty_strongMertensLogNineCorridor

end RHLean.Analysis
