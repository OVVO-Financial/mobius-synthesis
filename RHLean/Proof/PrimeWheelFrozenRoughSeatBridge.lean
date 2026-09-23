import RHLean.Proof.PrimeWheelRoughSeatCorrelation
import RHLean.Proof.PrimeCombVisualizationDynamics

/-!
# The rough-seat kernel is the existing frozen prime universe

The signed truncated prime-wheel kernel exposed by the rough-seat Fubini
collapse is exactly the chronological frozen prime cube already used by the
first-owner and Go machinery.  This file promotes that coordinate bridge from
the focused research check to the production proof graph.

No norm, estimate, asymptotic input, or change of carrier is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **Kernel/frozen-cube identification.**  On every finite prime universe, the
truncated divisor Mobius kernel is exactly the chronological frozen prime
universe mass. -/
theorem primeWheelTruncatedMoebiusKernel_eq_frozenPrimeUniverseMass
    (S : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    primeWheelTruncatedMoebiusKernel S X =
      frozenPrimeUniverseMass S X := by
  classical
  induction S using Finset.induction_on generalizing X with
  | empty =>
      simp [primeWheelTruncatedMoebiusKernel,
        RHLean.Arithmetic.primorial,
        frozenPrimeUniverseMass,
        truncatedCubeAlternatingSum,
        primeProductAdmissible,
        primeFaceProduct,
        booleanCubeSign]
  | @insert p S hpS ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p S)
      have hS : ∀ q ∈ S, q.Prime := fun q hq =>
        hprime q (Finset.mem_insert_of_mem hq)
      rw [primeWheelTruncatedMoebiusKernel_insert S p X hp hpS hS]
      rw [frozenPrimeUniverseMass_insert hpS hp]
      rw [ih X hS, ih (X / p) hS]

/-- The rough-seat correlation written directly with the existing frozen prime
universe mass as its reciprocal response field. -/
def primeWheelFrozenRoughSeatCorrelation (S : Finset ℕ) (B : ℕ) : ℤ :=
  ∑ n ∈ roughWheelInterval (RHLean.Arithmetic.primorial S)
      (B / RHLean.Arithmetic.primorial S) B,
    (μ n : ℤ) * frozenPrimeUniverseMass S (B / n)

/-- Exact equality of the rough-seat kernel coordinate and the frozen-cube
coordinate. -/
theorem primeWheelRoughSeatCorrelation_eq_frozen
    (S : Finset ℕ) (B : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    primeWheelRoughSeatCorrelation S B =
      primeWheelFrozenRoughSeatCorrelation S B := by
  unfold primeWheelRoughSeatCorrelation primeWheelFrozenRoughSeatCorrelation
  apply Finset.sum_congr rfl
  intro n _hn
  rw [primeWheelTruncatedMoebiusKernel_eq_frozenPrimeUniverseMass
    S (B / n) hprime]

/-- For any nontrivial finite prime wheel, ordinary Mertens is exactly one
Mobius/frozen-cube correlation on the physical rough seats above the complete
wheel anchor. -/
theorem roughMertens_one_eq_primeWheel_frozenRoughSeatCorrelation
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hWne : RHLean.Arithmetic.primorial S ≠ 1) (B : ℕ) :
    roughMertens 1 B = primeWheelFrozenRoughSeatCorrelation S B := by
  rw [roughMertens_one_eq_primeWheel_roughSeatCorrelation S hprime hWne B,
    primeWheelRoughSeatCorrelation_eq_frozen S B hprime]

/-- Full positive rough carrier, requiring no nontrivial-wheel hypothesis. -/
def primeWheelFrozenFullRoughSeatCorrelation (S : Finset ℕ) (B : ℕ) : ℤ :=
  ∑ n ∈ roughWheelInterval (RHLean.Arithmetic.primorial S) 0 B,
    (μ n : ℤ) * frozenPrimeUniverseMass S (B / n)

/-- **Frozen full rough-seat Mertens identity.**  Every finite prime set gives
an exact signed Mertens correlation.  Stopping before the square root therefore
retains the outer Mobius parity field without changing the represented value. -/
theorem roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) (B : ℕ) :
    roughMertens 1 B =
      primeWheelFrozenFullRoughSeatCorrelation S B := by
  rw [roughMertens_one_eq_primeWheel_fullRoughSeatCorrelation S hprime B]
  unfold primeWheelFrozenFullRoughSeatCorrelation
  apply Finset.sum_congr rfl
  intro n _hn
  rw [primeWheelTruncatedMoebiusKernel_eq_frozenPrimeUniverseMass
    S (B / n) hprime]

/-- Named square-endpoint proper-subwheel target. -/
def squareRootProperSubwheelFrozenCorrelation (R Y : ℕ) : ℤ :=
  primeWheelFrozenFullRoughSeatCorrelation (primesUpTo Y)
    (squareRootEndpoint R)

/-- **Wheel depth is a coordinate parameter.**  For every `Y`, including a
proper subwheel `Y < R`, the frozen rough-seat correlation is exactly the same
square-endpoint Mertens value. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_roughMertens
    (R Y : ℕ) :
    squareRootProperSubwheelFrozenCorrelation R Y =
      roughMertens 1 (squareRootEndpoint R) := by
  symm
  apply roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
  intro p hp
  exact prime_of_mem_primesUpTo hp

end RHLean.Proof
