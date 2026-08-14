import Mathlib
import RHLean.Analysis.NativePNTEvolvingTailState

noncomputable section

namespace RHLean.Analysis

/-- Exact net contraction resource at the current state: the full good-tail
deficit minus every evolving finite-scale cost. -/
def nativePNTEvolvingTailNetGain
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real) : Real :=
  (alpha - beta) * (N : Real) *
      nativeLambdaTwoGoodTailRecipMass N M beta -
    nativePNTEvolvingTailCost R N M alpha

/-- The exact state-dependent slope drop furnished by the current endpoint. -/
def nativePNTEvolvingTailSlopeGain
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real) : Real :=
  nativePNTEvolvingTailNetGain R N M alpha beta /
    ((N : Real) * (Real.log (N : Real)) ^ 2)

/-- The slope after applying the full currently available net gain. -/
def nativePNTEvolvingTailSlopeUpdate
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real) : Real :=
  alpha - nativePNTEvolvingTailSlopeGain R N M alpha beta

/-- Fully generalized one-step PNT contraction.  Any requested slope drop
`delta` is valid exactly when the current net gain pays for
`delta * N * log(N)^2`. -/
theorem nativePNTError_tail_pointwise_improve_evolving
    (R : Nat -> Real) (hR : NativePNTOneLogRemainderProfile R)
    (N M : Nat) (alpha beta delta : Real)
    (hN : 2 <= N)
    (halpha : 0 <= alpha)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))
    (hgain :
      delta * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        nativePNTEvolvingTailNetGain R N M alpha beta) :
    |nativePNTError N| <= (alpha - delta) * (N : Real) := by
  let L : Real := Real.log (N : Real)
  have hrec := nativePNTError_abs_log_sq_le_evolving_tail
    R hR N M (by omega) alpha beta halpha htail
  have hgain' :
      delta * (N : Real) * L ^ 2 <=
        (alpha - beta) * (N : Real) *
            nativeLambdaTwoGoodTailRecipMass N M beta -
          nativePNTEvolvingTailCost R N M alpha := by
    simpa [nativePNTEvolvingTailNetGain, L] using hgain
  have hbound :
      |nativePNTError N| * L ^ 2 <=
        (alpha - delta) * (N : Real) * L ^ 2 := by
    have hrec' :
        |nativePNTError N| * L ^ 2 <=
          alpha * (N : Real) * L ^ 2 -
            (alpha - beta) * (N : Real) *
              nativeLambdaTwoGoodTailRecipMass N M beta +
            nativePNTEvolvingTailCost R N M alpha := by
      simpa [L] using hrec
    calc
      |nativePNTError N| * L ^ 2 <=
          alpha * (N : Real) * L ^ 2 -
            (alpha - beta) * (N : Real) *
              nativeLambdaTwoGoodTailRecipMass N M beta +
            nativePNTEvolvingTailCost R N M alpha := hrec'
      _ <= alpha * (N : Real) * L ^ 2 -
            delta * (N : Real) * L ^ 2 := by
        linarith [hgain']
      _ = (alpha - delta) * (N : Real) * L ^ 2 := by ring
  have hL : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  have hcancel := (mul_le_mul_iff_left₀ hLsq).mp
    (show |nativePNTError N| * L ^ 2 <=
      ((alpha - delta) * (N : Real)) * L ^ 2 by
        simpa [mul_assoc] using hbound)
  exact hcancel

/-- The exact state itself determines a valid next slope. -/
theorem nativePNTError_tail_pointwise_le_evolvingSlopeUpdate
    (R : Nat -> Real) (hR : NativePNTOneLogRemainderProfile R)
    (N M : Nat) (alpha beta : Real)
    (hN : 2 <= N)
    (halpha : 0 <= alpha)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real)) :
    |nativePNTError N| <=
      nativePNTEvolvingTailSlopeUpdate R N M alpha beta * (N : Real) := by
  unfold nativePNTEvolvingTailSlopeUpdate
  apply nativePNTError_tail_pointwise_improve_evolving
    R hR N M alpha beta
      (nativePNTEvolvingTailSlopeGain R N M alpha beta)
      hN halpha htail
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hden :
      (N : Real) * (Real.log (N : Real)) ^ 2 ≠ 0 :=
    ne_of_gt (mul_pos hNR (sq_pos_of_pos hlog))
  unfold nativePNTEvolvingTailSlopeGain
  calc
    (nativePNTEvolvingTailNetGain R N M alpha beta /
        ((N : Real) * (Real.log (N : Real)) ^ 2)) *
        (N : Real) * (Real.log (N : Real)) ^ 2 =
      (nativePNTEvolvingTailNetGain R N M alpha beta /
        ((N : Real) * (Real.log (N : Real)) ^ 2)) *
        ((N : Real) * (Real.log (N : Real)) ^ 2) := by ring
    _ = nativePNTEvolvingTailNetGain R N M alpha beta := by
      field_simp [hden]
    _ <= nativePNTEvolvingTailNetGain R N M alpha beta := le_rfl

/-- Positive exact net gain makes the state-dependent slope update strict. -/
theorem nativePNTEvolvingTailSlopeUpdate_lt
    (R : Nat -> Real) (N M : Nat) (alpha beta : Real)
    (hN : 2 <= N)
    (hgain : 0 < nativePNTEvolvingTailNetGain R N M alpha beta) :
    nativePNTEvolvingTailSlopeUpdate R N M alpha beta < alpha := by
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hden :
      0 < (N : Real) * (Real.log (N : Real)) ^ 2 :=
    mul_pos hNR (sq_pos_of_pos hlog)
  have hslope :
      0 < nativePNTEvolvingTailSlopeGain R N M alpha beta := by
    unfold nativePNTEvolvingTailSlopeGain
    exact div_pos hgain hden
  unfold nativePNTEvolvingTailSlopeUpdate
  linarith

/-- Positive requested net-gain budget gives a genuinely strict contraction. -/
theorem nativePNTError_tail_pointwise_strict_improve_evolving
    (R : Nat -> Real) (hR : NativePNTOneLogRemainderProfile R)
    (N M : Nat) (alpha beta delta : Real)
    (hN : 2 <= N)
    (halpha : 0 <= alpha) (hdelta : 0 < delta)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))
    (hgain :
      delta * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        nativePNTEvolvingTailNetGain R N M alpha beta) :
    alpha - delta < alpha ∧
      |nativePNTError N| <= (alpha - delta) * (N : Real) := by
  constructor
  · linarith
  · exact nativePNTError_tail_pointwise_improve_evolving
      R hR N M alpha beta delta hN halpha htail hgain

/-- Canonical specialization using the exact first Selberg remainder profile. -/
theorem nativePNTError_tail_pointwise_improve_canonical
    (N M : Nat) (alpha beta delta : Real)
    (hN : 2 <= N)
    (halpha : 0 <= alpha)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))
    (hgain :
      delta * (N : Real) * (Real.log (N : Real)) ^ 2 <=
        nativePNTEvolvingTailNetGain
          nativePNTFirstRemainder N M alpha beta) :
    |nativePNTError N| <= (alpha - delta) * (N : Real) := by
  exact nativePNTError_tail_pointwise_improve_evolving
    nativePNTFirstRemainder nativePNTFirstRemainder_profile
    N M alpha beta delta hN halpha htail hgain

end RHLean.Analysis
