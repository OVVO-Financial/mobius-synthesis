import Mathlib
import RHLean.Analysis.MertensZetaIdentityContinuation

/-!
# The forward Mertens-energy implication to the Riemann hypothesis

The preceding Mertens layers construct a holomorphic continuation `F` on
`Re(s) > 1/2` and prove

`riemannZeta s * F s = 1`

there away from the pole `s = 1`.  Hence zeta is zero-free strictly to the
right of the critical line.

To exclude a nontrivial zero strictly to the left, this file uses the completed
Riemann zeta function.  Mathlib's exact zero set for `Gammaℝ` says that the
Archimedean factor vanishes only at nonpositive even integers.  The zero at
`s = 0` is excluded by `zeta(0) = -1/2`, while the negative even points are
exactly the trivial-zero locus already excluded by Mathlib's definition of RH.
Thus a nontrivial zeta zero gives a completed-zeta zero; the completed functional
equation reflects it to `1-s`, contradicting right-half-plane zero-freeness.

This proves only the forward implication needed by
`Proof.TerminalMertensReduction`.  No reverse RH-to-Mertens theorem is asserted.
-/

noncomputable section

namespace RHLean.Analysis

open Complex

/-- The propagated reciprocal identity immediately rules out zeta zeros
strictly to the right of the critical line. -/
theorem riemannZeta_ne_zero_of_half_lt_re
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : (1 : ℝ) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hprod :=
    riemannZeta_mul_mertensMellinContinuation_eq_one_of_half_lt_re
      hM hs hs1
  rw [hz, zero_mul] at hprod
  exact zero_ne_one hprod

/-- At a nontrivial candidate zero, the completed-zeta Archimedean factor is
nonzero.  Mathlib identifies its zero set exactly with the nonpositive even
integers. -/
private theorem GammaR_ne_zero_of_not_trivial
    {s : ℂ} (hs0 : s ≠ 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    Gammaℝ s ≠ 0 := by
  intro hGamma
  rcases Gammaℝ_eq_zero_iff.mp hGamma with ⟨n, hn⟩
  cases n with
  | zero =>
      apply hs0
      simpa using hn
  | succ n =>
      apply htriv
      refine ⟨n, ?_⟩
      simpa [Nat.cast_succ] using hn

/-- The repository's squared Mertens-energy criterion implies Mathlib's formal
Riemann hypothesis, with no caller-supplied classical Mertens/RH criterion. -/
theorem riemannHypothesis_of_mertensEnergy
    (hM : MertensEnergyBoundedStatement) :
    RiemannHypothesis := by
  intro s hz hnontriv hs1
  by_cases hcrit : s.re = (1 : ℝ) / 2
  · exact hcrit
  have hnotRight : ¬(1 : ℝ) / 2 < s.re := by
    intro hright
    exact (riemannZeta_ne_zero_of_half_lt_re hM hright hs1) hz
  have hleft : s.re < (1 : ℝ) / 2 := by
    exact lt_of_le_of_ne (le_of_not_gt hnotRight) hcrit
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hGamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_trivial hs0 hnontriv
  have hcompleted : completedRiemannZeta s = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    have hdiv : completedRiemannZeta s / Gammaℝ s = 0 := by
      rw [← hdef, hz]
    simpa [hGamma] using hdiv
  have hrefCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub s, hcompleted]
  have href0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    exact (sub_eq_zero.mp h).symm
  have hrefZeta : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero href0, hrefCompleted]
    simp
  have hrefRe : (1 : ℝ) / 2 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have href1 : 1 - s ≠ 1 := by
    intro h
    exact hs0 (sub_eq_self.mp h)
  exfalso
  exact (riemannZeta_ne_zero_of_half_lt_re hM hrefRe href1) hrefZeta

end RHLean.Analysis
