import Mathlib
import RHLean.Analysis.NativePNTErdosContraction
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

/-- A single affine envelope at slope `eta` generates reciprocal-intercept
envelopes on every prescribed finite slope window `[eta,A]`.

The point is purely finite.  If `|R(N)| <= eta*N + D`, set
`K = A*(D+1)`.  For `eta <= alpha <= A`, the original intercept satisfies
`D <= K/alpha`, so the same global envelope is admissible with slope `alpha`
and reciprocal intercept `K/alpha`. -/
theorem nativePNTAffineEnvelopeAt_reciprocal_window_of_base
    (eta A D : Real) (heta : 0 < eta) (hetaA : eta <= A) (hA : 0 < A)
    (henv : NativePNTAffineEnvelopeAt eta D) :
    forall alpha : Real, eta <= alpha -> alpha <= A ->
      NativePNTAffineEnvelopeAt alpha (A * (D + 1) / alpha) := by
  rcases henv with ⟨hD, hpoint⟩
  intro alpha hetaAlpha hAlphaA
  have halpha : 0 < alpha := lt_of_lt_of_le heta hetaAlpha
  have hK : 0 < A * (D + 1) := by
    exact mul_pos hA (by linarith)
  constructor
  · exact div_nonneg hK.le halpha.le
  · intro N
    have hNR : 0 <= (N : Real) := by positivity
    have hslope : eta * (N : Real) <= alpha * (N : Real) :=
      mul_le_mul_of_nonneg_right hetaAlpha hNR
    have hDalpha : D * alpha <= D * A :=
      mul_le_mul_of_nonneg_left hAlphaA hD
    have hDA : D * A <= A * (D + 1) := by
      nlinarith [hA.le]
    have hintercept : D <= A * (D + 1) / alpha := by
      rw [le_div_iff₀ halpha]
      exact hDalpha.trans hDA
    exact (hpoint N).trans (add_le_add hslope hintercept)

/-- Local optimizer for one reciprocal-intercept affine envelope.  Unlike the
global reciprocal-intercept law above, this needs the envelope only at the
single optimizing slope `alpha`, characterized by `alpha^2 = K/N`. -/
theorem nativePNTError_abs_le_two_sqrt_of_reciprocalEnvelopeAt
    (K alpha : Real) (hK : 0 < K) (halpha : 0 < alpha)
    (N : Nat) (hN : 1 <= N)
    (halpha_sq : alpha ^ 2 = K / (N : Real))
    (henv : NativePNTAffineEnvelopeAt alpha (K / alpha)) :
    |nativePNTError N| <= 2 * Real.sqrt (K * (N : Real)) := by
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
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
  have hbound := henv.2 N
  calc
    |nativePNTError N| <= alpha * (N : Real) + K / alpha := hbound
    _ = 2 * (alpha * (N : Real)) := by rw [hdiv]; ring
    _ = 2 * Real.sqrt (K * (N : Real)) := by rw [hscaled_sqrt]

/-- **Unconditional finite-window square-root bound.**

For every finite slope window `0 < eta <= A`, the proved native PNT supplies a
finite constant `K` such that every endpoint whose optimizing slope
`sqrt(K/N)` lies in that window satisfies the genuine square-root estimate

`|psi(N)-N| <= 2*sqrt(K*N)`.

This does not assert a tail bound: `K` depends on the chosen window.  The
remaining global problem is to control these constants as the lower slope
`eta` tends to zero strongly enough that the finite windows cover the tail. -/
theorem exists_nativePNTError_abs_le_two_sqrt_on_finite_window
    (eta A : Real) (heta : 0 < eta) (hetaA : eta <= A) (hA : 0 < A) :
    ∃ K : Real, 0 < K ∧
      forall N : Nat, 1 <= N ->
        eta <= Real.sqrt (K / (N : Real)) ->
        Real.sqrt (K / (N : Real)) <= A ->
        |nativePNTError N| <= 2 * Real.sqrt (K * (N : Real)) := by
  rcases nativePNTHasAffineEnvelope_arbitrarily_small eta heta with
    ⟨D, hD, hpoint⟩
  let K : Real := A * (D + 1)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos hA (by linarith)
  refine ⟨K, hK, ?_⟩
  intro N hN hlow hhigh
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
  have henvAlpha := nativePNTAffineEnvelopeAt_reciprocal_window_of_base
    eta A D heta hetaA hA ⟨hD, hpoint⟩ alpha
    (by simpa [alpha] using hlow) (by simpa [alpha] using hhigh)
  have henvAlpha' : NativePNTAffineEnvelopeAt alpha (K / alpha) := by
    simpa [K] using henvAlpha
  exact nativePNTError_abs_le_two_sqrt_of_reciprocalEnvelopeAt
    K alpha hK halpha N hN halpha_sq henvAlpha'

/-- Algebraic form of the finite window.  The two inequalities say exactly that
`N` lies in the finite annulus `K/A^2 <= N <= K/eta^2`, without introducing
new asymptotic notation. -/
theorem exists_nativePNTError_abs_le_two_sqrt_on_finite_annulus
    (eta A : Real) (heta : 0 < eta) (hetaA : eta <= A) (hA : 0 < A) :
    ∃ K : Real, 0 < K ∧
      forall N : Nat, 1 <= N ->
        K <= A ^ 2 * (N : Real) ->
        eta ^ 2 * (N : Real) <= K ->
        |nativePNTError N| <= 2 * Real.sqrt (K * (N : Real)) := by
  rcases exists_nativePNTError_abs_le_two_sqrt_on_finite_window
      eta A heta hetaA hA with ⟨K, hK, hwindow⟩
  refine ⟨K, hK, ?_⟩
  intro N hN hlower hupper
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hratio : 0 < K / (N : Real) := div_pos hK hNR
  have hsqrt0 : 0 <= Real.sqrt (K / (N : Real)) := Real.sqrt_nonneg _
  have hsqrtSq :
      (Real.sqrt (K / (N : Real))) ^ 2 = K / (N : Real) :=
    Real.sq_sqrt hratio.le
  have hetaSq : eta ^ 2 <= K / (N : Real) := by
    rw [le_div_iff₀ hNR]
    exact hupper
  have hASq : K / (N : Real) <= A ^ 2 := by
    rw [div_le_iff₀ hNR]
    exact hlower
  have hlow : eta <= Real.sqrt (K / (N : Real)) := by
    nlinarith
  have hhigh : Real.sqrt (K / (N : Real)) <= A := by
    nlinarith [hA.le]
  exact hwindow N hN hlow hhigh

end RHLean.Analysis
