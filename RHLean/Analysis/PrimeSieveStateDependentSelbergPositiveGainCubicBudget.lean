import Mathlib
import RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainTrajectoryCore
import RHLean.Analysis.NativePNTCubicContractionInequality

noncomputable section

namespace RHLean.Analysis

theorem primeSieveStateDependentSelberg_cubic_trajectory_inv_sq_rate
    (N M : Nat -> Nat) (alpha beta : Nat -> Real)
    (c : Real) (hc : 0 <= c)
    (hpos : forall n, 0 < alpha n)
    (htraj : PrimeSieveStateDependentSelbergTrajectory N M alpha beta)
    (hgain : forall n : Nat,
      PrimeSieveStateDependentSelbergStateHasPowerGain
        c 3 (N n) (M n) (alpha n) (beta n)) :
    forall n : Nat,
      1 / (alpha 0) ^ 2 + 2 * c * (n : Real) <=
        1 / (alpha n) ^ 2 := by
  apply inv_sq_rate_of_cubic_contraction_inequality alpha c hc hpos
  exact primeSieveStateDependentSelberg_trajectory_power_contraction
    N M alpha beta c 3 htraj hgain

theorem primeSieveStateDependentSelberg_cubic_trajectory_le_eta_of_budget
    (N M : Nat -> Nat) (alpha beta : Nat -> Real)
    (c eta : Real) (hc : 0 <= c) (heta : 0 < eta)
    (hpos : forall n, 0 < alpha n)
    (htraj : PrimeSieveStateDependentSelbergTrajectory N M alpha beta)
    (hgain : forall n : Nat,
      PrimeSieveStateDependentSelbergStateHasPowerGain
        c 3 (N n) (M n) (alpha n) (beta n))
    (n : Nat)
    (hbudget : 1 < 2 * c * (n : Real) * eta ^ 2) :
    alpha n <= eta := by
  apply cubic_contraction_inequality_le_eta_of_budget
    alpha c eta hc heta hpos
  · exact primeSieveStateDependentSelberg_trajectory_power_contraction
      N M alpha beta c 3 htraj hgain
  · exact hbudget

end RHLean.Analysis
