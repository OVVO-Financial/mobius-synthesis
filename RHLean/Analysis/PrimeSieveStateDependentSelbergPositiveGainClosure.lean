import Mathlib
import RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainCore

noncomputable section

namespace RHLean.Analysis

theorem primeSieveStateDependentSelberg_slopeUpdate_le
    (N M : Nat) (alpha beta c : Real) (p : Nat)
    (hN : 2 <= N)
    (hgain : PrimeSieveStateDependentSelbergStateHasPowerGain
      c p N M alpha beta) :
    nativePNTEvolvingTailSlopeUpdate
        nativePNTFirstRemainder N M alpha beta <=
      alpha - c * alpha ^ p := by
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hden : 0 < (N : Real) * (Real.log (N : Real)) ^ 2 :=
    mul_pos hNR (sq_pos_of_pos hlog)
  have hdiv :
      c * alpha ^ p <=
        primeSieveStateDependentSelbergNetGain N M alpha beta /
          ((N : Real) * (Real.log (N : Real)) ^ 2) := by
    apply (le_div_iff₀ hden).2
    unfold PrimeSieveStateDependentSelbergStateHasPowerGain at hgain
    simpa [mul_assoc] using hgain
  unfold nativePNTEvolvingTailSlopeUpdate nativePNTEvolvingTailSlopeGain
  linarith

theorem primeSieveStateDependentSelberg_error_le_power_contraction
    (N M : Nat) (alpha beta c : Real) (p : Nat)
    (hadm : PrimeSieveStateDependentSelbergAdmissible N M alpha beta)
    (hgain : PrimeSieveStateDependentSelbergStateHasPowerGain
      c p N M alpha beta) :
    |nativePNTError N| <=
      (alpha - c * alpha ^ p) * (N : Real) := by
  rcases hadm with ⟨⟨hN, _hM1, _hMN, halpha, htail⟩, _hbeta0, _hba⟩
  unfold PrimeSieveStateDependentSelbergStateHasPowerGain at hgain
  exact nativePNTError_tail_pointwise_improve_evolving
    nativePNTFirstRemainder nativePNTFirstRemainder_profile
    N M alpha beta (c * alpha ^ p)
    hN halpha.le htail hgain

theorem primeSieveStateDependentSelberg_positiveGainLaw_closure
    (c : Real) (p : Nat)
    (hlaw : PrimeSieveStateDependentSelbergPositiveGainLaw c p)
    (N : Nat) (alpha : Real)
    (htail : PrimeSieveStateDependentSelbergHasTailState N alpha) :
    ∃ M : Nat, ∃ beta : Real,
      PrimeSieveStateDependentSelbergAdmissible N M alpha beta ∧
      nativePNTEvolvingTailSlopeUpdate
          nativePNTFirstRemainder N M alpha beta <=
        alpha - c * alpha ^ p ∧
      |nativePNTError N| <=
        (alpha - c * alpha ^ p) * (N : Real) := by
  rcases hlaw with ⟨_hc, _hp, hselect⟩
  rcases hselect N alpha htail with ⟨M, beta, hadm, hgain⟩
  refine ⟨M, beta, hadm, ?_, ?_⟩
  · exact primeSieveStateDependentSelberg_slopeUpdate_le
      N M alpha beta c p hadm.1.1 hgain
  · exact primeSieveStateDependentSelberg_error_le_power_contraction
      N M alpha beta c p hadm hgain

end RHLean.Analysis
