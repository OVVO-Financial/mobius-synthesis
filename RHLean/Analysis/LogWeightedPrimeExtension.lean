import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Analysis.TwoABPrimeDilation

/-!
# Log-weighted prime extension identities

This module introduces the exact finite objects for the logarithmic
prime-extension renewal route and proves the pinned-API-safe finite algebraic
layer: fresh-prime sign reversal, pointwise fresh/square splitting, and exact
cofactor-first/prime-first Fubini reindexing.

The child-fiber identification with the log-weighted Möbius block and the sharp
finite square-correction bound are exposed as typed arithmetic statements for
the next module.  No asymptotic prime estimate or contraction claim appears
here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Real-valued cast of the Möbius function, fixed once at the definition
boundary. -/
def moebiusReal (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ)

/-- The exact Möbius increment on the prime-scaled doubling interval
`(N / p, (2N) / p]`. -/
def primeScaleIncrement (N p : ℕ) : ℝ :=
  ∑ c ∈ Finset.Ioc (N / p) ((2 * N) / p), moebiusReal c

/-- The logarithmically weighted Möbius mass in the doubling block
`(N, 2N]`. -/
def logWeightedBlock (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N), moebiusReal n * Real.log n

/-- Fresh prime divisors of `n`: prime factors whose removal leaves a cofactor
not divisible by the same prime. -/
def freshPrimeDivisors (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => ¬ p ∣ n / p

/-- Unrestricted logarithmic prime-extension contribution of one cofactor/prime
pair in the doubling block. -/
def logPrimeExtensionTerm (N c p : ℕ) : ℝ :=
  if p.Prime ∧ N < c * p ∧ c * p ≤ 2 * N then
    moebiusReal c * Real.log p
  else 0

/-- Fresh part of one logarithmic prime-extension contribution. -/
def logFreshPrimeExtensionTerm (N c p : ℕ) : ℝ :=
  if p.Prime ∧ N < c * p ∧ c * p ≤ 2 * N ∧ ¬ p ∣ c then
    moebiusReal c * Real.log p
  else 0

/-- Square-producing part of one logarithmic prime-extension contribution. -/
def logSquarePrimeExtensionTerm (N c p : ℕ) : ℝ :=
  if p.Prime ∧ N < c * p ∧ c * p ≤ 2 * N ∧ p ∣ c then
    moebiusReal c * Real.log p
  else 0

/-- Logarithmic fresh-prime extension mass available to a cofactor `c`. -/
def logFreshPrimeExtension (N c : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 (2 * N), logFreshPrimeExtensionTerm N c p

/-- Complete rectangular cofactor-first unrestricted extension mass. -/
def logPrimeExtensionCofactorFirst (N : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 (2 * N),
    ∑ p ∈ Finset.Icc 2 (2 * N), logPrimeExtensionTerm N c p

/-- The same unrestricted mass read prime first. -/
def logPrimeExtensionPrimeFirst (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 (2 * N),
    ∑ c ∈ Finset.Icc 1 (2 * N), logPrimeExtensionTerm N c p

/-- Complete fresh extension mass. -/
def logFreshPrimeExtensionMass (N : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 (2 * N),
    ∑ p ∈ Finset.Icc 2 (2 * N), logFreshPrimeExtensionTerm N c p

/-- Complete square-producing correction in the same rectangular support. -/
def squareCorrection (N : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 (2 * N),
    ∑ p ∈ Finset.Icc 2 (2 * N), logSquarePrimeExtensionTerm N c p

/-- Elementary finite majorant target for the square correction. -/
def squareCorrectionMajorant (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 (Nat.sqrt (2 * N)),
    if p.Prime then Real.log p * (((N / (p ^ 2) + 1 : ℕ) : ℝ)) else 0

@[simp] theorem moebiusReal_zero : moebiusReal 0 = 0 := by
  simp [moebiusReal]

/-- Möbius sign flip under multiplication by a genuinely fresh prime. -/
theorem moebiusReal_prime_mul
    {p c : ℕ} (hp : p.Prime) (hpc : ¬ p ∣ c) :
    moebiusReal (p * c) = -moebiusReal c := by
  unfold moebiusReal
  rw [RHLean.Arithmetic.moebius_prime_mul hp hpc]
  push_cast
  ring

/-- Every unrestricted pair is exactly either fresh or square-producing. -/
theorem logPrimeExtensionTerm_eq_fresh_add_square
    (N c p : ℕ) :
    logPrimeExtensionTerm N c p =
      logFreshPrimeExtensionTerm N c p +
        logSquarePrimeExtensionTerm N c p := by
  unfold logPrimeExtensionTerm logFreshPrimeExtensionTerm
    logSquarePrimeExtensionTerm
  by_cases hp : p.Prime
  · by_cases hlower : N < c * p
    · by_cases hupper : c * p ≤ 2 * N
      · by_cases hdvd : p ∣ c <;> simp [hp, hlower, hupper, hdvd]
      · simp [hp, hlower, hupper]
    · simp [hp, hlower]
  · simp [hp]

/-- Exact finite Fubini reindexing for the complete logarithmic extension
family. -/
theorem logPrimeExtensionCofactorFirst_eq_primeFirst (N : ℕ) :
    logPrimeExtensionCofactorFirst N = logPrimeExtensionPrimeFirst N := by
  unfold logPrimeExtensionCofactorFirst logPrimeExtensionPrimeFirst
  rw [Finset.sum_comm]

/-- Exact finite decomposition of the unrestricted extension mass into fresh
and square-producing parts. -/
theorem logPrimeExtensionCofactorFirst_eq_fresh_add_squareCorrection
    (N : ℕ) :
    logPrimeExtensionCofactorFirst N =
      logFreshPrimeExtensionMass N + squareCorrection N := by
  unfold logPrimeExtensionCofactorFirst logFreshPrimeExtensionMass
    squareCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact logPrimeExtensionTerm_eq_fresh_add_square N c p

/-- Exact child-fiber identity still to be discharged from the existing finite
product-fiber APIs.  Keeping it typed prevents any analytic assumption from
entering the arithmetic layer. -/
def LogWeightedChildFiberIdentityStatement : Prop :=
  ∀ N : ℕ, logFreshPrimeExtensionMass N = -logWeightedBlock N

/-- Exact prime-first renewal identity obtained once the child-fiber statement
is combined with the finite Fubini and fresh/square decomposition above. -/
def LogWeightedPrimeRenewalIdentityStatement : Prop :=
  ∀ N : ℕ,
    logWeightedBlock N +
      (∑ p ∈ Finset.Icc 2 (2 * N),
        if p.Prime then Real.log p * primeScaleIncrement N p else 0) =
      squareCorrection N

/-- Finite square-correction estimate, deliberately separated from its later
real-analysis normalization. -/
def LogWeightedSquareCorrectionBoundStatement : Prop :=
  ∀ N : ℕ, |squareCorrection N| ≤ squareCorrectionMajorant N

end RHLean.Analysis
