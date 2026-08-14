import Mathlib
import RHLean.Proof.DeathShellSubpolynomial
import RHLean.Proof.LifetimeActiveSet

/-!
# Lifetime overlap Gram criterion for the surviving high population

The death-shell route leaves one live object: the current birth-high survivor
mass.  The existing lifetime kernel already expands a fixed finite atom universe
into a pair Gram form, but its canonical specialization had only been identified
with the survivor amplitude when the terminal universe and observation stage
were equal.

This module freezes one terminal universe across an entire translated window.
Future-born atoms contribute zero before birth, so the canonical lifetime
amplitude with terminal stage `T` equals the current survivor mass at every
`t <= T`.  Taking `T = N + H` therefore identifies the complete translated
survivor energy exactly with one lifetime-overlap Gram matrix.

Consequently the remaining lifetime/death-shell analytic premise can be stated
as a concrete pair-correlation estimate for the overlap kernel.  No analytic
estimate is asserted here.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace RHLean.Proof

/-- Restricting a later birth-high universe to atoms already active at stage
`t` gives exactly the stage-`t` lifetime-active set. -/
theorem birthCanonicalHighAtomSet_filter_lifetimeActive_eq
    {Λ : ℝ} {t T : ℕ} (htT : t ≤ T) :
    (birthCanonicalHighAtomSet Λ T).filter
        (fun p => IsLifetimeActive Λ p t) =
      lifetimeActiveAtomSet Λ t := by
  classical
  unfold lifetimeActiveAtomSet
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpT, hpActive⟩
    have hpBirth : p ∈ birthCanonicalHighAtomSet Λ t := by
      unfold birthCanonicalHighAtomSet at hpT ⊢
      rcases Finset.mem_sigma.mp hpT with ⟨_hpRangeT, hpBlock⟩
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_range.mpr ?_, hpBlock⟩
      exact Nat.lt_succ_of_le hpActive.1
    exact ⟨hpBirth, hpActive⟩
  · rintro ⟨hpBirth, hpActive⟩
    have hpT : p ∈ birthCanonicalHighAtomSet Λ T := by
      unfold birthCanonicalHighAtomSet at hpBirth ⊢
      rcases Finset.mem_sigma.mp hpBirth with ⟨hpRange, hpBlock⟩
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_range.mpr ?_, hpBlock⟩
      have hpt : p.1 ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hpRange)
      exact Nat.lt_succ_of_le (hpt.trans htT)
    exact ⟨hpT, hpActive⟩

/-- A fixed terminal canonical lifetime universe gives the exact current
survivor amplitude at every earlier observation stage. -/
theorem canonicalLifetimeAmplitude_eq_activeMass_of_le
    {Λ : ℝ} {t T : ℕ} (htT : t ≤ T) :
    canonicalLifetimeAmplitude Λ T t = lifetimeActiveAtomMass Λ t := by
  classical
  unfold canonicalLifetimeAmplitude canonicalLifetimeUniverse lifetimeAmplitude
  rw [← Finset.sum_filter]
  rw [birthCanonicalHighAtomSet_filter_lifetimeActive_eq htT]
  simp [lifetimeActiveAtomMass, canonicalAtomMass, canonicalHighAtomWeight]

/-- The real translated local energy of the survivor sequence, cast to `ℂ`, is
exactly the canonical conjugate energy of one fixed terminal lifetime universe. -/
theorem lifetimeActive_localSequenceEnergy_cast_eq_canonicalLifetimeWindowEnergy
    (Λ : ℝ) (N H : ℕ) :
    ((RHLean.Analysis.localSequenceEnergy
        (lifetimeActiveAtomMass Λ) N H : ℝ) : ℂ) =
      canonicalLifetimeWindowEnergy Λ (N + H) N H := by
  classical
  unfold RHLean.Analysis.localSequenceEnergy canonicalLifetimeWindowEnergy
    lifetimeWindowEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro h hh
  have hhLt : h < H := Finset.mem_range.mp hh
  have ht : N + h ≤ N + H := by omega
  have hamp := canonicalLifetimeAmplitude_eq_activeMass_of_le
    (Λ := Λ) (t := N + h) (T := N + H) ht
  unfold canonicalLifetimeAmplitude at hamp
  rw [hamp]
  let A : ℂ := lifetimeActiveAtomMass Λ (N + h)
  change (‖A‖ : ℂ) ^ 2 = conj A * A
  calc
    (‖A‖ : ℂ) ^ 2 = (((‖A‖ ^ 2 : ℝ) : ℂ)) := by norm_num
    _ = (Complex.normSq A : ℂ) := by rw [Complex.normSq_eq_norm_sq]
    _ = conj A * A := Complex.normSq_eq_conj_mul_self

/-- Exact pair-correlation form of the complete translated survivor energy. -/
theorem lifetimeActive_localSequenceEnergy_cast_eq_overlapGram
    (Λ : ℝ) (N H : ℕ) :
    ((RHLean.Analysis.localSequenceEnergy
        (lifetimeActiveAtomMass Λ) N H : ℝ) : ℂ) =
      lifetimeOverlapGram (canonicalLifetimeUniverse Λ (N + H))
        canonicalHighAtomWeight Λ N H := by
  rw [lifetimeActive_localSequenceEnergy_cast_eq_canonicalLifetimeWindowEnergy]
  exact canonicalLifetimeWindowEnergy_eq_overlapGram Λ (N + H) N H

private theorem lifetimeActive_localSequenceEnergy_nonneg
    (Λ : ℝ) (N H : ℕ) :
    0 ≤ RHLean.Analysis.localSequenceEnergy
      (lifetimeActiveAtomMass Λ) N H := by
  unfold RHLean.Analysis.localSequenceEnergy
  positivity

/-- Since the overlap Gram is exactly a nonnegative real energy, its complex
norm is the survivor local energy itself. -/
theorem norm_lifetimeOverlapGram_eq_lifetimeActive_localSequenceEnergy
    (Λ : ℝ) (N H : ℕ) :
    ‖lifetimeOverlapGram (canonicalLifetimeUniverse Λ (N + H))
        canonicalHighAtomWeight Λ N H‖ =
      RHLean.Analysis.localSequenceEnergy
        (lifetimeActiveAtomMass Λ) N H := by
  rw [← lifetimeActive_localSequenceEnergy_cast_eq_overlapGram]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (lifetimeActive_localSequenceEnergy_nonneg Λ N H)]

/-- Critical translated-window pair-correlation estimate for the canonical
lifetime overlap kernel. -/
def LifetimeOverlapGramUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N H : ℕ),
        1 ≤ H → H ≤ N →
        ‖lifetimeOverlapGram (canonicalLifetimeUniverse Λ (N + H))
            canonicalHighAtomWeight Λ N H‖ ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The pair-correlation overlap-Gram criterion is exactly the remaining
birth-minus-death survivor-discrepancy criterion. -/
theorem lifetimeOverlapGramUniformLocalBounded_iff_endpointDiscrepancy
    (Λ : ℝ) :
    LifetimeOverlapGramUniformLocalBoundedStatement Λ ↔
      LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  constructor
  · intro hG ε hε
    obtain ⟨C, hC, hGb⟩ := hG ε hε
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rw [← lifetimeActive_localEnergy_eq_birth_sub_death]
    rw [← norm_lifetimeOverlapGram_eq_lifetimeActive_localSequenceEnergy]
    exact hGb N H hH hHN
  · intro hD ε hε
    obtain ⟨C, hC, hDb⟩ := hD ε hε
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rw [norm_lifetimeOverlapGram_eq_lifetimeActive_localSequenceEnergy]
    rw [lifetimeActive_localEnergy_eq_birth_sub_death]
    exact hDb N H hH hHN

/-- The overlap-Gram estimate therefore feeds the protected square-prefix
uniform-local criterion once the unconditional death-shell theorem is used. -/
theorem lifetimeOverlapGramUniformLocalBounded_implies_squarePrefixUniformLocal
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hG : LifetimeOverlapGramUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  apply lifetimeEndpointDiscrepancy_implies_squarePrefixUniformLocal hΛ
  exact (lifetimeOverlapGramUniformLocalBounded_iff_endpointDiscrepancy Λ).1 hG

/-- Conditional RH terminal in the explicit lifetime pair-correlation
coordinate. -/
theorem lifetimeOverlapGramUniformLocalBounded_implies_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 < Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hG : LifetimeOverlapGramUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  apply lifetimeEndpointDiscrepancy_implies_riemannHypothesis hΛ criterion
  exact (lifetimeOverlapGramUniformLocalBounded_iff_endpointDiscrepancy Λ).1 hG

end RHLean.Proof
