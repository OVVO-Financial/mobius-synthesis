import Mathlib
import RHLean.Analysis.NativePNTEvolvingTailStep

noncomputable section

namespace RHLean.Analysis

def PrimeSieveStateDependentSelbergTailState
    (N M : Nat) (alpha : Real) : Prop :=
  2 <= N ∧ 1 <= M ∧ M <= N ∧ 0 < alpha ∧
    (forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real))

def PrimeSieveStateDependentSelbergHasTailState
    (N : Nat) (alpha : Real) : Prop :=
  ∃ M : Nat, PrimeSieveStateDependentSelbergTailState N M alpha

def PrimeSieveStateDependentSelbergAdmissible
    (N M : Nat) (alpha beta : Real) : Prop :=
  PrimeSieveStateDependentSelbergTailState N M alpha ∧
    0 <= beta ∧ beta < alpha

abbrev primeSieveStateDependentSelbergNetGain
    (N M : Nat) (alpha beta : Real) : Real :=
  nativePNTEvolvingTailNetGain
    nativePNTFirstRemainder N M alpha beta

theorem primeSieveStateDependentSelbergNetGain_eq
    (N M : Nat) (alpha beta : Real) :
    primeSieveStateDependentSelbergNetGain N M alpha beta =
      (alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta -
        nativePNTEvolvingTailCost
          nativePNTFirstRemainder N M alpha := rfl

def PrimeSieveStateDependentSelbergStateHasPowerGain
    (c : Real) (p : Nat)
    (N M : Nat) (alpha beta : Real) : Prop :=
  c * alpha ^ p * (N : Real) * (Real.log (N : Real)) ^ 2 <=
    primeSieveStateDependentSelbergNetGain N M alpha beta

/-- The arithmetic law selects a valid cutoff and threshold.  Quantifying over
arbitrary remainder majorants, cutoffs, or all `beta < alpha` would make a
uniform positive lower bound false. -/
def PrimeSieveStateDependentSelbergPositiveGainLaw
    (c : Real) (p : Nat) : Prop :=
  0 < c ∧ 0 < p ∧
    forall (N : Nat) (alpha : Real),
      PrimeSieveStateDependentSelbergHasTailState N alpha ->
      ∃ M : Nat, ∃ beta : Real,
        PrimeSieveStateDependentSelbergAdmissible N M alpha beta ∧
          PrimeSieveStateDependentSelbergStateHasPowerGain
            c p N M alpha beta

def PrimeSieveStateDependentSelbergHasPositiveGain : Prop :=
  ∃ c : Real, ∃ p : Nat,
    PrimeSieveStateDependentSelbergPositiveGainLaw c p

theorem primeSieveStateDependentSelberg_gain_of_component_budget
    (N M : Nat) (alpha beta c : Real) (p : Nat)
    (hbudget :
      c * alpha ^ p * (N : Real) * (Real.log (N : Real)) ^ 2 +
          nativePNTEvolvingTailCost
            nativePNTFirstRemainder N M alpha <=
        (alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta) :
    PrimeSieveStateDependentSelbergStateHasPowerGain
      c p N M alpha beta := by
  unfold PrimeSieveStateDependentSelbergStateHasPowerGain
    primeSieveStateDependentSelbergNetGain
    nativePNTEvolvingTailNetGain
  linarith

end RHLean.Analysis
