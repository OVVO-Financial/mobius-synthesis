#!/usr/bin/env python3
"""Apply compatibility repairs discovered after the main StrongPNT 4.24 patch.

This stays separate from apply.py while the terminal modules are being driven through
GitHub Actions. Every replacement is exact and therefore fails closed on upstream drift.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STRONGPNT = ROOT / ".lake" / "packages" / "StrongPNT" / "StrongPNT"


def replace_exact(path: Path, label: str, old: str, new: str) -> None:
    text = path.read_text()
    old_count = text.count(old)
    new_count = text.count(new)
    if old_count == 1:
        path.write_text(text.replace(old, new, 1))
        print(f"applied {path.name}: {label}")
    elif old_count == 0 and new_count == 1:
        print(f"already applied {path.name}: {label}")
    else:
        raise SystemExit(
            f"compatibility patch mismatch in {path.name} for {label!r}: "
            f"old_count={old_count}, new_count={new_count}"
        )


def remove_exact(path: Path, label: str, old: str) -> None:
    text = path.read_text()
    old_count = text.count(old)
    if old_count == 1:
        path.write_text(text.replace(old, "", 1))
        print(f"removed {path.name}: {label}")
    elif old_count == 0:
        print(f"already removed {path.name}: {label}")
    else:
        raise SystemExit(
            f"compatibility patch mismatch in {path.name} for {label!r}: "
            f"old_count={old_count}"
        )


def main() -> None:
    target = STRONGPNT / "ZetaZeroFree.lean"
    replace_exact(
        target,
        "use direct zeta continuity at the punctured-limit center",
        """      use h (isClosed_singleton.isSeqClosed this (.comp (cont.continuousAt.comp (eventually_ne_nhds (by field_simp [ht₀])).mono fun and=>.intro ⟨⟩) (ToOneT0.trans (inf_le_left))))
""",
        """      have hcenter_ne : (1 : ℂ) + Complex.I * t₀ ≠ 1 := by
        intro hcenter
        apply ht₀
        have him := congrArg Complex.im hcenter
        simpa using him
      have hcont : ContinuousAt ζ (1 + Complex.I * t₀) := by
        apply DifferentiableAt.continuousAt (𝕜 := ℂ)
        convert differentiableAt_riemannZeta hcenter_ne
      have hz_tendsto :
          Tendsto (fun n ↦ ζ (↑(σ' (subseq n)) + I * ↑(t (subseq n)))) atTop
            (𝓝 (ζ (1 + I * ↑t₀))) :=
        hcont.tendsto.comp (ToOneT0.trans inf_le_left)
      exact h (isClosed_singleton.isSeqClosed this hz_tendsto)
""",
    )

    target = STRONGPNT / "PNT5_Strong.lean"
    replace_exact(
        target,
        "import the 4.24 Mellin and smoothing interfaces explicitly",
        """import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.ZetaConj
""",
        """import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.ZetaConj
import PrimeNumberTheoremAnd.SmoothExistence
import Mathlib.Analysis.MellinInversion
""",
    )
    replace_exact(
        target,
        "Mellin transform API rename",
        'local notation (name := mellintransform2) "𝓜" => MellinTransform\n',
        'local notation (name := mellintransform2) "𝓜" => mellin\n',
    )
    replace_exact(
        target,
        "make the smoothing Mellin integrand complex-valued",
        """  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 ((Smooth1 SmoothingF ε) ·) s * (X : ℂ) ^ s
""",
        """  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s
""",
    )
    replace_exact(
        target,
        "unfold the Mathlib 4.24 Mellin definition",
        "  · unfold MellinTransform\n",
        "  · unfold mellin\n",
    )
    remove_exact(
        target,
        "obsolete MellinTransform_eq bridge",
        "  rw [MellinTransform_eq]\n",
    )
    replace_exact(
        target,
        "make MellinOfSmooth1cExplicit use a complex-valued function",
        "    ∀ ε ∈ Ioo 0 ε₀, ‖𝓜 ((Smooth1 ν ε) ·) 1 - 1‖ ≤ c * ε := by\n",
        "    ∀ ε ∈ Ioo 0 ε₀, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1‖ ≤ c * ε := by\n",
    )
    replace_exact(
        target,
        "normalize scalar multiplication in Mellin conjugation",
        """    intro x xpos
    simp only [map_mul, Complex.conj_ofReal]
    congr
""",
        """    intro x xpos
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    congr
""",
    )
    replace_exact(
        target,
        "make Mellin continuity explicitly complex-valued",
        """  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
""",
        """  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
""",
    )
    replace_exact(
        target,
        "scope integral_tsum side conditions as in 4.24 MediumPNT",
        """  rw [MeasureTheory.integral_tsum]
  have x_neq_zero : X ≠ 0 := by linarith
  . intro i
    by_cases i_eq_zero : i = 0
    . simpa [i_eq_zero] using aestronglyMeasurable_const
    . apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  . rw [← lt_top_iff_ne_top]
""",
        """  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
""",
    )
    replace_exact(
        target,
        "use direct 4.24 tsum-integral theorem without obsolete Mellin bridge",
        """  · congr
    rw [← MellinTransform_eq]
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
""",
        """  · congr
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
""",
    )
    replace_exact(
        target,
        "port cpow quotient rewrite from 4.24 MediumPNT",
        """    have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + t * I) ?_ ?_
    push_cast at this ⊢
    rw [← this, div_mul_cancel₀]
    · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
    · apply div_nonneg (by linarith : 0 ≤ X); simp
    · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, not_and, not_not]
      intro hn; exfalso; exact n_ne_zero hn
""",
        """    have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
    · push_cast at this ⊢
      rw [← this, div_mul_cancel₀]
      · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
    · apply div_nonneg (by linarith : 0 ≤ X); simp
    · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
""",
    )
    replace_exact(
        target,
        "follow 4.24 conv path for inverse cpow",
        "    conv => rhs; rhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]\n",
        "    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]\n",
    )
    replace_exact(
        target,
        "port Mellin inversion API to 4.24",
        """    rw [(by rw [div_mul]; simp : 1 / (2 * π) = 1 / (2 * π * I) * I), mul_assoc]
    conv => lhs; rhs; rhs; rhs; intro t; rw [mul_comm]; norm_cast
    have := MellinInversion σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [MellinInverseTransform, VerticalIntegral] at this
      rw [← MellinTransform_eq, this]
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      rw [← MellinTransform_eq]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
""",
        """    have := mellin_inversion σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
""",
    )


if __name__ == "__main__":
    main()
