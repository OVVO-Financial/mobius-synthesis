import Mathlib
import RHLean.Analysis.PrimeDilateCofactorPrimeWindows
import RHLean.Proof.LowWheelSequentialGeometricSavings

/-!
# Sequential low-wheel cells as reciprocal prime-dilate windows

The multiplicative shell formula for one fresh low-wheel coordinate has an even
more useful geometric reading.  Fix a positive cofactor-face product `a`.  The
outer shell

`R < q`, `a*q <= X < p*a*q`

is exactly the reciprocal prime-dilate window

`q ∈ primeDilateCofactorWindow p R X a`.

The inner shell is the same window after the fresh-prime dilation `q ↦ p*q`.
Consequently the complete mixed four-corner cell is

`1_W(q) - 1_W(p*q)`.

This is the form needed for sequential savings: after summing over a residual
multiplier, the second term is literally the `p`-dilate of the first and can be
paired against the `p`-divisible part of the parent multiplier population.

All statements here are exact finite identities.  No norm or estimate appears.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Membership in the reciprocal cofactor window is exactly the first
multiplicative shell for the physical product `a*q`. -/
theorem mem_primeDilateCofactorWindow_iff_lowWheelShell
    {p R X a q : ℕ} (hp : p.Prime) (ha : 0 < a) :
    q ∈ primeDilateCofactorWindow p R X a ↔
      R < q ∧ a * q ≤ X ∧ X < p * (a * q) := by
  rw [mem_primeDilateCofactorWindow]
  unfold primeDilateCofactorWindowLower primeDilateCofactorWindowUpper
  have hpa : 0 < p * a := Nat.mul_pos hp.pos ha
  constructor
  · rintro ⟨hlower, hupper⟩
    have hRq : R < q :=
      lt_of_le_of_lt (le_max_left R (X / (p * a))) hlower
    have hdiv : X / (p * a) < q :=
      lt_of_le_of_lt (le_max_right R (X / (p * a))) hlower
    have hparent : a * q ≤ X := by
      have h := (Nat.le_div_iff_mul_le ha).1 hupper
      simpa [Nat.mul_comm] using h
    have hchild : X < p * (a * q) := by
      have h := (Nat.div_lt_iff_lt_mul hpa).1 hdiv
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    exact ⟨hRq, hparent, hchild⟩
  · rintro ⟨hRq, hparent, hchild⟩
    have hupper : q ≤ X / a := by
      apply (Nat.le_div_iff_mul_le ha).2
      simpa [Nat.mul_comm] using hparent
    have hdiv : X / (p * a) < q := by
      apply (Nat.div_lt_iff_lt_mul hpa).2
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hchild
    exact ⟨max_lt hRq hdiv, hupper⟩

/-- The second shell is exactly the same reciprocal window after the fresh-prime
coordinate dilates `q` by `p`. -/
theorem mul_mem_primeDilateCofactorWindow_iff_lowWheelSecondShell
    {p R X a q : ℕ} (hp : p.Prime) (ha : 0 < a) :
    p * q ∈ primeDilateCofactorWindow p R X a ↔
      R < p * q ∧ p * (a * q) ≤ X ∧ X < p * p * (a * q) := by
  have h := mem_primeDilateCofactorWindow_iff_lowWheelShell
    (p := p) (R := R) (X := X) (a := a) (q := p * q) hp ha
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- Integer indicator of one reciprocal prime-dilate window. -/
def lowWheelPrimeDilateWindowIndicator
    (p R X a q : ℕ) : ℤ :=
  if q ∈ primeDilateCofactorWindow p R X a then 1 else 0

/-- **Fresh-prime cell = window minus its prime dilation.**  When the endpoint
variable is the physical product `a*q`, the complete two-copy low-wheel
four-corner cell is exactly a first multiplicative difference of one reciprocal
window. -/
theorem lowWheelMixedPrimeCell_mul_eq_window_sub_dilate
    {p R X a q : ℕ} (hp : p.Prime) (ha : 0 < a) :
    lowWheelMixedPrimeCell p R X q (a * q) =
      lowWheelPrimeDilateWindowIndicator p R X a q -
        lowWheelPrimeDilateWindowIndicator p R X a (p * q) := by
  rw [lowWheelMixedPrimeCell_eq_sequentialShellDifference hp.one_le]
  have hfirst := mem_primeDilateCofactorWindow_iff_lowWheelShell
    (p := p) (R := R) (X := X) (a := a) (q := q) hp ha
  have hsecond := mul_mem_primeDilateCofactorWindow_iff_lowWheelSecondShell
    (p := p) (R := R) (X := X) (a := a) (q := q) hp ha
  unfold lowWheelPrimeDilateWindowIndicator
  by_cases h1 : R < q ∧ a * q ≤ X ∧ X < p * (a * q) <;>
    by_cases h2 : R < p * q ∧ p * (a * q) ≤ X ∧ X < p * p * (a * q) <;>
    simp [h1, h2, hfirst, hsecond]

/-- Support consequence in window language: a nonzero fresh-prime cell lies in
the reciprocal window either before or after the prime dilation. -/
theorem lowWheelMixedPrimeCell_mul_ne_zero_imp_window_or_dilate
    {p R X a q : ℕ} (hp : p.Prime) (ha : 0 < a)
    (h : lowWheelMixedPrimeCell p R X q (a * q) ≠ 0) :
    q ∈ primeDilateCofactorWindow p R X a ∨
      p * q ∈ primeDilateCofactorWindow p R X a := by
  rw [lowWheelMixedPrimeCell_mul_eq_window_sub_dilate hp ha] at h
  unfold lowWheelPrimeDilateWindowIndicator at h
  by_cases hq : q ∈ primeDilateCofactorWindow p R X a
  · exact Or.inl hq
  · by_cases hpq : p * q ∈ primeDilateCofactorWindow p R X a
    · exact Or.inr hpq
    · simp [hq, hpq] at h

end RHLean.Proof
