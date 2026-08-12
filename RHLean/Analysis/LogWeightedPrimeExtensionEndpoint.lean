import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionFiber

/-!
# Endpoint form of the log-weighted child-fiber identity

This module packages the local squarefree child-fiber theorem into an exact
finite block identity.  It deliberately separates the endpoint-fiber theorem
from the remaining rectangular product-fiber reindexing.

The final section begins the architecture-native prime-number-theorem route.
Its first objects are finite von Mangoldt and logarithmic masses together with
the logarithmic derivation on the Dirichlet ring.  No theorem asserting PNT is
imported or used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

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

/-! ## Native PNT: finite von Mangoldt layer -/

/-- Finite Chebyshev `psi` mass through the integer endpoint `x`, defined
without any asymptotic theorem. -/
def nativePsi (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, Λ n

/-- Finite logarithmic mass through `x`. -/
def nativeLogMass (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, Real.log n

/-- Divisor-first form of the same logarithmic mass.  This is the first exact
multiplicative reindexing in the native Selberg route: every `log n` is the sum
of von Mangoldt weights over the divisor fibre of `n`. -/
def nativeDivisorVonMangoldtMass (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, Λ d

/-- Exact finite divisor identity underlying the architecture-native PNT route. -/
theorem nativeLogMass_eq_divisorVonMangoldtMass (x : ℕ) :
    nativeLogMass x = nativeDivisorVonMangoldtMass x := by
  unfold nativeLogMass nativeDivisorVonMangoldtMass
  apply Finset.sum_congr rfl
  intro n _hn
  exact ArithmeticFunction.vonMangoldt_sum.symm

/-! ## The logarithmic derivation on Dirichlet convolution -/

/-- Multiply an arithmetic-function coefficient by `log n`. -/
def arithmeticLogWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * Real.log n, by simp⟩

@[simp] theorem arithmeticLogWeight_apply
    (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticLogWeight f n = f n * Real.log n := rfl

/-- Multiplication by `log n` is a derivation for Dirichlet convolution.  This
is the exact multiplicative analogue of the product rule and is the algebraic
kernel of Selberg's symmetry formula. -/
theorem arithmeticLogWeight_mul
    (f g : ArithmeticFunction ℝ) :
    arithmeticLogWeight (f * g) =
      arithmeticLogWeight f * g + f * arithmeticLogWeight g := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [arithmeticLogWeight]
  simp only [arithmeticLogWeight_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.add_apply]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ab hab
  have hprod : ab.1 * ab.2 = n :=
    (Nat.mem_divisorsAntidiagonal.mp hab).1
  have ha0 : ab.1 ≠ 0 :=
    Nat.left_ne_zero_of_mem_divisorsAntidiagonal hab
  have hb0 : ab.2 ≠ 0 :=
    Nat.right_ne_zero_of_mem_divisorsAntidiagonal hab
  have hlog :
      Real.log (n : ℝ) = Real.log (ab.1 : ℝ) + Real.log (ab.2 : ℝ) := by
    calc
      Real.log (n : ℝ) =
          Real.log (((ab.1 * ab.2 : ℕ) : ℝ)) := by rw [hprod]
      _ = Real.log ((ab.1 : ℝ) * (ab.2 : ℝ)) := by rw [Nat.cast_mul]
      _ = Real.log (ab.1 : ℝ) + Real.log (ab.2 : ℝ) := by
        rw [Real.log_mul (by exact_mod_cast ha0) (by exact_mod_cast hb0)]
  rw [hlog]
  ring

/-- The pointwise square of the logarithm, bundled as an arithmetic function. -/
def arithmeticLogSquare : ArithmeticFunction ℝ :=
  ⟨fun n => (Real.log n) ^ 2, by simp⟩

/-- Applying the logarithmic derivation to the arithmetic logarithm gives
`log^2` pointwise. -/
theorem arithmeticLogWeight_log :
    arithmeticLogWeight ArithmeticFunction.log = arithmeticLogSquare := by
  ext n
  change Real.log n * Real.log n = (Real.log n) ^ 2
  ring

/-- The logarithmic derivative of the zeta arithmetic function is the
arithmetic logarithm itself. -/
theorem arithmeticLogWeight_zeta :
    arithmeticLogWeight
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) =
      ArithmeticFunction.log := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [arithmeticLogWeight]
  change
    (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) n) *
        Real.log n = Real.log n
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn]
  simp

/-- Selberg's second von Mangoldt function in the Dirichlet-ring form
`Lambda_2 = mu * log^2`. -/
def nativeLambdaTwo : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ) * arithmeticLogSquare

/-- **Exact Selberg symmetry kernel.**  The second von Mangoldt function is the
sum of the log-weighted von Mangoldt function and its Dirichlet self-convolution:

`Lambda_2 = D Lambda + Lambda * Lambda`.

This is a finite ring identity.  It uses no asymptotic prime-distribution input. -/
theorem nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution :
    nativeLambdaTwo = arithmeticLogWeight Λ + Λ * Λ := by
  have hDlog :
      arithmeticLogSquare =
        ArithmeticFunction.log * Λ +
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
            arithmeticLogWeight Λ := by
    calc
      arithmeticLogSquare = arithmeticLogWeight ArithmeticFunction.log :=
        arithmeticLogWeight_log.symm
      _ = arithmeticLogWeight
          (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * Λ) := by
            rw [ArithmeticFunction.zeta_mul_vonMangoldt]
      _ = arithmeticLogWeight
            ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * Λ +
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
            arithmeticLogWeight Λ :=
              arithmeticLogWeight_mul _ _
      _ = ArithmeticFunction.log * Λ +
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
            arithmeticLogWeight Λ := by
              rw [arithmeticLogWeight_zeta]
  unfold nativeLambdaTwo
  rw [hDlog]
  simp [mul_add, ← mul_assoc, add_comm]

end RHLean.Analysis
