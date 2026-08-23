import Mathlib
import RHLean.Analysis.NativePNTSelberg

/-!
# Fixed-ratio reciprocal von-Mangoldt mass

The depth-four signed frontier repeatedly produces prime and prime-power sums
inside a fixed multiplicative annulus.  Mertens' first theorem in bounded-error
form makes the full reciprocal von-Mangoldt mass on such an annulus uniformly
bounded.  Keeping the full positive `Lambda` measure gives a convenient
majorant for every prime-only subfamily used later.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Reciprocal von-Mangoldt mass in the half-open multiplicative interval
`(A,B]`. -/
def nativeLambdaRecipInterval (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc A B, Λ n / (n : ℝ)

/-- Interval mass is the difference of reciprocal prefixes. -/
theorem nativeLambdaRecipInterval_eq_sub
    (A B : ℕ) (hAB : A ≤ B) :
    nativeLambdaRecipInterval A B = nativeLambdaRecip B - nativeLambdaRecip A := by
  unfold nativeLambdaRecipInterval nativeLambdaRecip
  have hsub : Finset.Icc 1 A ⊆ Finset.Icc 1 B := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnA⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hnA.trans hAB⟩
  have hset : Finset.Icc 1 B \ Finset.Icc 1 A = Finset.Ioc A B := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hs := Finset.sum_sdiff hsub (f := fun n => Λ n / (n : ℝ))
  rw [hset] at hs
  linarith

/-- Reciprocal von-Mangoldt interval mass is nonnegative. -/
theorem nativeLambdaRecipInterval_nonneg (A B : ℕ) :
    0 ≤ nativeLambdaRecipInterval A B := by
  unfold nativeLambdaRecipInterval
  apply Finset.sum_nonneg
  intro n _hn
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- Uniform factor-four annular mass.  The constant is deliberately crude;
independence of the physical endpoint is the point. -/
theorem nativeLambdaRecipInterval_le_factor_four
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB4 : B ≤ 4 * A) :
    nativeLambdaRecipInterval A B ≤ 2 * Real.log 4 + 3 := by
  have hB : 1 ≤ B := hA.trans hAB
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hlowA := (nativeLambdaRecip_sub_log_bounds A hA).1
  have hupB := (nativeLambdaRecip_sub_log_bounds B hB).2
  have hlogB4A : Real.log (B : ℝ) ≤ Real.log ((4 * A : ℕ) : ℝ) := by
    exact Real.log_le_log hBpos (by exact_mod_cast hB4)
  have hlog4A : Real.log ((4 * A : ℕ) : ℝ) = Real.log 4 + Real.log (A : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hApos)]
  rw [hlog4A] at hlogB4A
  rw [nativeLambdaRecipInterval_eq_sub A B hAB]
  linarith

end RHLean.Analysis
