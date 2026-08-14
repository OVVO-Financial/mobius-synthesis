import Mathlib
import RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainClosure

noncomputable section

namespace RHLean.Analysis

def PrimeSieveStateDependentSelbergTrajectory
    (N M : Nat -> Nat) (alpha beta : Nat -> Real) : Prop :=
  forall n : Nat,
    PrimeSieveStateDependentSelbergAdmissible
        (N n) (M n) (alpha n) (beta n) ∧
      alpha (n + 1) =
        nativePNTEvolvingTailSlopeUpdate nativePNTFirstRemainder
          (N n) (M n) (alpha n) (beta n)

theorem primeSieveStateDependentSelberg_trajectory_power_contraction
    (N M : Nat -> Nat) (alpha beta : Nat -> Real)
    (c : Real) (p : Nat)
    (htraj : PrimeSieveStateDependentSelbergTrajectory N M alpha beta)
    (hgain : forall n : Nat,
      PrimeSieveStateDependentSelbergStateHasPowerGain
        c p (N n) (M n) (alpha n) (beta n)) :
    forall n : Nat,
      alpha (n + 1) <= alpha n - c * (alpha n) ^ p := by
  intro n
  rcases htraj n with ⟨hadm, hnext⟩
  rw [hnext]
  exact primeSieveStateDependentSelberg_slopeUpdate_le
    (N n) (M n) (alpha n) (beta n) c p hadm.1.1 (hgain n)

end RHLean.Analysis
