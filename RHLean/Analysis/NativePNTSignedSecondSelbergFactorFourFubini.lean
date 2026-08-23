import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourBridge

/-!
# Physical-product Fubini coordinate for the factor-four signed K2 shell

The harmonic factor-four shell is expanded one step further into the exact
physical-product coordinate

`N / 4 < d * k <= N`.

This is the coordinate in which a fresh prime can move between the Möbius
divisor and the reciprocal quotient without changing the physical product.
Consequently the leading `log^2` mode cancels before any absolute value is
taken.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Reciprocal mass on a half-open integer interval is the corresponding
harmonic difference. -/
theorem nativeRecipIoc_eq_harmonic_sub
    (A B : ℕ) (hAB : A ≤ B) :
    (∑ k ∈ Finset.Ioc A B, 1 / (k : ℝ)) =
      (harmonic B : ℝ) - (harmonic A : ℝ) := by
  have hsub : Finset.Icc 1 A ⊆ Finset.Icc 1 B := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkA⟩
    exact Finset.mem_Icc.mpr ⟨hk1, hkA.trans hAB⟩
  have hset : Finset.Icc 1 B \ Finset.Icc 1 A = Finset.Ioc A B := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hs := Finset.sum_sdiff hsub (f := fun k : ℕ => 1 / (k : ℝ))
  rw [hset, nativeRecipIcc_eq_harmonic, nativeRecipIcc_eq_harmonic] at hs
  linarith

/-- Exact double-Fubini shell.  Every summand has physical product `d*k` in
`(N/4,N]`. -/
def nativePNTSignedK2RecipDoubleShell (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    ∑ k ∈ Finset.Ioc ((N / 4) / d) (N / d),
      nativePNTSignedK2RecipFubiniAtom d k

/-- The factor-four signed K2 reciprocal interval is exactly the physical
product double shell. -/
theorem nativePNTSignedK2RecipInterval_four_eq_doubleShell
    (N : ℕ) :
    nativePNTSignedK2RecipInterval N 4 =
      nativePNTSignedK2RecipDoubleShell N := by
  rw [nativePNTSignedK2RecipInterval_four_eq_mobius_harmonic_shell]
  unfold nativePNTSignedK2RecipDoubleShell
  apply Finset.sum_congr rfl
  intro d hd
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  have hAB : (N / 4) / d ≤ N / d :=
    Nat.div_le_div_right (Nat.div_le_self N 4)
  unfold nativePNTDepthFourHarmonicShell
  rw [← nativeRecipIoc_eq_harmonic_sub ((N / 4) / d) (N / d) hAB]
  unfold nativeMobiusLogSquareRecipWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkI := Finset.mem_Ioc.mp hk
  have hkpos : 0 < k :=
    Nat.lt_of_le_of_lt (Nat.zero_le ((N / 4) / d)) hkI.1
  have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have hkR0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
  unfold nativePNTSignedK2RecipFubiniAtom
  rw [Nat.cast_mul]
  field_simp [hdR0, hkR0]

/-- Prime-two specialization of the same-product fresh-prime cancellation.
This is the exact local cell used by the dyadic fold. -/
theorem nativePNTSignedK2RecipFubiniAtom_two_sameProduct
    (m k : ℕ) (hm : Odd m) (hk : 1 ≤ k) :
    nativePNTSignedK2RecipFubiniAtom (m * 2) k +
        nativePNTSignedK2RecipFubiniAtom m (2 * k) =
      -(μ : ArithmeticFunction ℝ) m *
        ((Real.log (2 : ℝ)) ^ 2 +
          2 * Real.log (2 : ℝ) * Real.log (m : ℝ)) /
        (((m * 2) * k : ℕ) : ℝ) := by
  have hcop : Nat.Coprime m 2 := (hm.coprime_two_left).symm
  have hm1 : 1 ≤ m := by
    rcases hm with ⟨j, hj⟩
    omega
  exact nativePNTSignedK2RecipFubiniAtom_freshPrime_sameProduct
    m 2 k hm1 hk Nat.prime_two hcop

end RHLean.Analysis
