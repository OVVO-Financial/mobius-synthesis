import Mathlib
import RHLean.Analysis.NativePNTErdosContraction
import RHLean.Analysis.NativePNTInterceptOnsetCore

noncomputable section

namespace RHLean.Analysis

def nativePNTFinitePrefixCoeff : Real := Real.log 4 + 3

lemma nativePNTFinitePrefixCoeff_nonneg :
    0 <= nativePNTFinitePrefixCoeff := by
  unfold nativePNTFinitePrefixCoeff
  have hlog : 0 <= Real.log (4 : Real) := Real.log_nonneg (by norm_num)
  linarith

theorem nativePNTAffineEnvelopeAt_of_tail_cutoff
    (M : Nat) (alpha : Real) (halpha : 0 <= alpha)
    (htail : forall N : Nat, M <= N ->
      |nativePNTError N| <= alpha * (N : Real)) :
    NativePNTAffineEnvelopeAt alpha
      (nativePNTFinitePrefixCoeff * (M : Real)) := by
  have hB := nativePNTFinitePrefixCoeff_nonneg
  have hD : 0 <= nativePNTFinitePrefixCoeff * (M : Real) :=
    mul_nonneg hB (by positivity)
  refine ⟨hD, ?_⟩
  intro N
  by_cases hMN : M <= N
  · exact (htail N hMN).trans (le_add_of_nonneg_right hD)
  · have hNM : N <= M := Nat.le_of_lt (lt_of_not_ge hMN)
    have hNMR : (N : Real) <= (M : Real) := by exact_mod_cast hNM
    have hglobal := nativePNTError_abs_le_const_mul N
    have hprefix :
        nativePNTFinitePrefixCoeff * (N : Real) <=
          nativePNTFinitePrefixCoeff * (M : Real) :=
      mul_le_mul_of_nonneg_left hNMR hB
    have haN : 0 <= alpha * (N : Real) := mul_nonneg halpha (by positivity)
    calc
      |nativePNTError N| <= nativePNTFinitePrefixCoeff * (N : Real) := by
        simpa [nativePNTFinitePrefixCoeff] using hglobal
      _ <= nativePNTFinitePrefixCoeff * (M : Real) := hprefix
      _ <= alpha * (N : Real) + nativePNTFinitePrefixCoeff * (M : Real) :=
        le_add_of_nonneg_left haN

end RHLean.Analysis
