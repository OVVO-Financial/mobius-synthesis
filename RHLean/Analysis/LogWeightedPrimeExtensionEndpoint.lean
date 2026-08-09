import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionFiber

/-!
# Endpoint form of the log-weighted child-fiber identity

This module packages the local squarefree child-fiber theorem into an exact
finite block identity.  It deliberately separates the endpoint-fiber theorem
from the remaining rectangular product-fiber reindexing.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- The squarefree endpoint child fiber.  Non-squarefree endpoints contribute
zero, matching their Möbius weight. -/
def logWeightedEndpointFiber (n : ℕ) : ℝ :=
  if Squarefree n then
    ∑ p ∈ n.primeFactors, moebiusReal (n / p) * Real.log p
  else
    0

/-- Exact value of one endpoint child fiber. -/
theorem logWeightedEndpointFiber_eq (n : ℕ) :
    logWeightedEndpointFiber n = -moebiusReal n * Real.log n := by
  by_cases hs : Squarefree n
  · simp only [logWeightedEndpointFiber, if_pos hs]
    exact sum_log_p_mu_parent_eq_neg_mu_log n hs
  · simp only [logWeightedEndpointFiber, if_neg hs]
    have hmu : μ n = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
    simp [moebiusReal, hmu]

/-- Endpoint-first fresh child mass on the doubling block. -/
def logWeightedEndpointFiberMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N), logWeightedEndpointFiber n

/-- The endpoint-first child mass is exactly the negative log-weighted Möbius
block. -/
theorem logWeightedEndpointFiberMass_eq_neg_logWeightedBlock (N : ℕ) :
    logWeightedEndpointFiberMass N = -logWeightedBlock N := by
  unfold logWeightedEndpointFiberMass logWeightedBlock
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [logWeightedEndpointFiber_eq]
  ring

end RHLean.Analysis
