import Mathlib
import RHLean.Analysis.NativePNTTailOptimalIntercept

noncomputable section

namespace RHLean.Analysis

def NativePNTReciprocalInterceptLaw (K : Real) : Prop :=
  0 < K ∧ forall alpha : Real, 0 < alpha ->
    NativePNTAffineEnvelopeAt alpha (K / alpha)

def NativePNTReciprocalTailCutoffLaw (K : Real) : Prop :=
  0 < K ∧ forall alpha : Real, 0 < alpha ->
    ∃ M : Nat,
      nativePNTFinitePrefixCoeff * (M : Real) <= K / alpha ∧
      (forall N : Nat, M <= N ->
        |nativePNTError N| <= alpha * (N : Real))

theorem nativePNTReciprocalInterceptLaw_of_tailCutoffLaw
    (K : Real) (hlaw : NativePNTReciprocalTailCutoffLaw K) :
    NativePNTReciprocalInterceptLaw K := by
  rcases hlaw with ⟨hK, hlaw⟩
  refine ⟨hK, ?_⟩
  intro alpha halpha
  rcases hlaw alpha halpha with ⟨M, hMcost, htail⟩
  have henv := nativePNTAffineEnvelopeAt_of_tail_cutoff
    M alpha halpha.le htail
  constructor
  · exact div_nonneg hK.le halpha.le
  · intro N
    exact (henv.2 N).trans
      (add_le_add_left hMcost (alpha * (N : Real)))

theorem nativePNTError_abs_le_two_sqrt_of_reciprocalInterceptLaw
    (K : Real) (hlaw : NativePNTReciprocalInterceptLaw K)
    (N : Nat) (hN : 1 <= N) :
    |nativePNTError N| <=
      2 * Real.sqrt (K * (N : Real)) := by
  rcases hlaw with ⟨hK, hlaw⟩
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  let alpha : Real := Real.sqrt (K / (N : Real))
  have hratio : 0 < K / (N : Real) := div_pos hK hNR
  have halpha : 0 < alpha := by
    dsimp [alpha]
    exact Real.sqrt_pos.2 hratio
  have halpha_sq : alpha ^ 2 = K / (N : Real) := by
    dsimp [alpha]
    exact Real.sq_sqrt hratio.le
  have hmul : alpha * alpha * (N : Real) = K := by
    calc
      alpha * alpha * (N : Real) = alpha ^ 2 * (N : Real) := by ring
      _ = (K / (N : Real)) * (N : Real) := by rw [halpha_sq]
      _ = K := by field_simp [ne_of_gt hNR]
  have hdiv : K / alpha = alpha * (N : Real) := by
    apply (div_eq_iff (ne_of_gt halpha)).2
    calc
      K = alpha * alpha * (N : Real) := hmul.symm
      _ = (alpha * (N : Real)) * alpha := by ring
  have hscaled_nonneg : 0 <= alpha * (N : Real) :=
    mul_nonneg halpha.le hNR.le
  have hscaled_sq :
      (alpha * (N : Real)) ^ 2 = K * (N : Real) := by
    calc
      (alpha * (N : Real)) ^ 2 = alpha ^ 2 * (N : Real) ^ 2 := by ring
      _ = (K / (N : Real)) * (N : Real) ^ 2 := by rw [halpha_sq]
      _ = K * (N : Real) := by field_simp [ne_of_gt hNR]
  have hscaled_sqrt :
      alpha * (N : Real) = Real.sqrt (K * (N : Real)) := by
    calc
      alpha * (N : Real) = Real.sqrt ((alpha * (N : Real)) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hscaled_nonneg]
      _ = Real.sqrt (K * (N : Real)) := by rw [hscaled_sq]
  have hbound := (hlaw alpha halpha).2 N
  calc
    |nativePNTError N| <= alpha * (N : Real) + K / alpha := hbound
    _ = 2 * (alpha * (N : Real)) := by rw [hdiv]; ring
    _ = 2 * Real.sqrt (K * (N : Real)) := by rw [hscaled_sqrt]

theorem nativePNTError_abs_le_two_sqrt_of_reciprocalTailCutoffLaw
    (K : Real) (hlaw : NativePNTReciprocalTailCutoffLaw K)
    (N : Nat) (hN : 1 <= N) :
    |nativePNTError N| <=
      2 * Real.sqrt (K * (N : Real)) := by
  exact nativePNTError_abs_le_two_sqrt_of_reciprocalInterceptLaw
    K (nativePNTReciprocalInterceptLaw_of_tailCutoffLaw K hlaw) N hN

end RHLean.Analysis
