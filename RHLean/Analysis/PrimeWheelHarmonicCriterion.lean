import Mathlib
import RHLean.Analysis.PrimeWheelFourierReduction
import RHLean.Analysis.PrimeWheelTorusRealization

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- A family of finite synchronized prime-wheel systems. -/
abbrev PrimeWheelFamily := ℕ → PrimeWheelFiniteSystem

/-- The RH-scale arithmetic target for the complete raw-minus-twice-smooth
residual on every pinned wheel prefix. -/
def PrimeWheelResidualBoundedStatement
    (W : PrimeWheelFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k x : ℕ,
        (W k).lower < x → x ≤ (W k).upper →
        ‖(((W k).residual x : ℤ) : ℂ)‖ ^ 2 ≤
          C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)

/-- The same RH-scale target written entirely as a finite DFT/window
nonconcentration estimate. -/
def PrimeWheelHarmonicNonconcentration
    (W : PrimeWheelFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k x : ℕ,
        (W k).lower < x → x ≤ (W k).upper →
        ‖(W k).spectralPrefix x‖ ^ 2 ≤
          C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)

/-- A family of finite lossless torus embeddings. -/
def PrimeWheelTorusCertificates (W : PrimeWheelFamily) : Prop :=
  ∀ k : ℕ, (W k).TorusRealizationCertificate

/-- Canonical lossless torus certificates for every finite wheel family. -/
def canonicalPrimeWheelTorusCertificates
    (W : PrimeWheelFamily) : PrimeWheelTorusCertificates W :=
  fun k => (W k).canonicalTorusRealizationCertificate

/-- The finite harmonic nonconcentration statement is exactly the arithmetic
residual bound once the zero-padding realization is proved. -/
theorem primeWheelHarmonicNonconcentration_iff_residualBounded
    (W : PrimeWheelFamily)
    (torusCert : PrimeWheelTorusCertificates W) :
    PrimeWheelHarmonicNonconcentration W ↔
      PrimeWheelResidualBoundedStatement W := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro k x hlower hupper
    rw [← (W k).spectralPrefix_eq_residual (torusCert k) hlower hupper]
    exact hbound k x hlower hupper
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro k x hlower hupper
    rw [(W k).spectralPrefix_eq_residual (torusCert k) hlower hupper]
    exact hbound k x hlower hupper

/-- Conductor of an additive frequency after reducing the fraction `r/modulus`.
The zero frequency is assigned conductor one. -/
def reducedAdditiveConductor
    {N : ℕ} [NeZero N] (r : ZMod N) : ℕ :=
  if r = 0 then 1 else N / Nat.gcd r.val N

/-- Joint spectral energy at a fixed reduced additive conductor. -/
def jointConductorEnergy
    (W : PrimeWheelFiniteSystem) (q : ℕ) : ℝ :=
  ∑ r : ZMod W.modulus,
    if q = reducedAdditiveConductor r then ‖W.jointSpectrum r‖ ^ 2 else 0

/-- Exact conductor partition of total joint spectral energy.  This is only a
finite regrouping identity; it asserts no decay estimate. -/
theorem jointSpectrumEnergy_eq_sum_conductors
    (W : PrimeWheelFiniteSystem) :
    (∑ r : ZMod W.modulus, ‖W.jointSpectrum r‖ ^ 2) =
      ∑ q ∈ Finset.range (W.modulus + 1), jointConductorEnergy W q := by
  classical
  unfold jointConductorEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hcond : reducedAdditiveConductor r ≤ W.modulus := by
    unfold reducedAdditiveConductor
    split_ifs
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt W.modulus_pos)
    · exact Nat.div_le_self _ _
  have hmem : reducedAdditiveConductor r ∈ Finset.range (W.modulus + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcond)
  simp [hmem]

end RHLean.Analysis
