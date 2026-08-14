import Mathlib
import RHLean.Analysis.NativePNTSignedWheelRemainder

/-!
# Signed local surplus in reciprocal Möbius coordinates

The absolute evolving-tail state destroys signed cancellation before
self-composition.  This module starts the replacement arithmetic directly in
the signed Möbius/wheel coordinate.

The existing signed transform is first localized to an arbitrary finite
cofactor packet, with the wheel/residual split kept exact on that packet.  The
actual reciprocal atoms are then paired under one fresh-prime extension.  For
fixed inner quotient `k`, the atoms at `(m,p*k)` and `(m*p,k)` share the same
Chebyshev endpoint, so Möbius sign reversal removes the duplicated `log k`
contribution exactly.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Signed Möbius reciprocal mass restricted to an arbitrary cofactor packet. -/
def nativePNTMobiusSignedCofactorMassOn
    (N : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ m ∈ s,
    (μ : ArithmeticFunction ℝ) m *
      nativePNTMobiusLogReciprocalFiber N m
        (fun d => nativePNTError (N / d))

/-- The full signed Möbius error mass is the packet mass on the complete
positive prefix. -/
theorem nativePNTMobiusReciprocalSignedErrorMass_eq_cofactorMassOn
    (N : ℕ) :
    nativePNTMobiusReciprocalSignedErrorMass N =
      nativePNTMobiusSignedCofactorMassOn N (Finset.Icc 1 N) := by
  rfl

/-- Local resolved wheel mass on an arbitrary cofactor packet. -/
def nativePNTWheelResolvedSignedMassOn
    (y N : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ m ∈ s,
    (RHLean.Arithmetic.partialPrimeWheelSite y N m : ℝ) *
      nativePNTMobiusLogReciprocalFiber N m
        (fun d => nativePNTError (N / d))

/-- Local unresolved wheel residual on an arbitrary cofactor packet. -/
def nativePNTWheelResidualSignedMassOn
    (y N : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ m ∈ s,
    (((μ : ArithmeticFunction ℝ) m -
        (RHLean.Arithmetic.partialPrimeWheelSite y N m : ℝ)) *
      nativePNTMobiusLogReciprocalFiber N m
        (fun d => nativePNTError (N / d)))

/-- Exact signed wheel/residual splitting holds packet by packet. -/
theorem nativePNTMobiusSignedCofactorMassOn_eq_wheel_add_residual
    (y N : ℕ) (s : Finset ℕ) :
    nativePNTMobiusSignedCofactorMassOn N s =
      nativePNTWheelResolvedSignedMassOn y N s +
        nativePNTWheelResidualSignedMassOn y N s := by
  unfold nativePNTMobiusSignedCofactorMassOn
    nativePNTWheelResolvedSignedMassOn nativePNTWheelResidualSignedMassOn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- Local cofactor masses add exactly across disjoint packets. -/
theorem nativePNTMobiusSignedCofactorMassOn_union
    (N : ℕ) (s t : Finset ℕ) (hdisj : Disjoint s t) :
    nativePNTMobiusSignedCofactorMassOn N (s ∪ t) =
      nativePNTMobiusSignedCofactorMassOn N s +
        nativePNTMobiusSignedCofactorMassOn N t := by
  unfold nativePNTMobiusSignedCofactorMassOn
  rw [Finset.sum_union hdisj]

/-- One signed reciprocal Möbius atom in the PNT error transform. -/
def nativePNTMobiusSignedAtom (N m k : ℕ) : ℝ :=
  ((μ m : ℤ) : ℝ) * Real.log (k : ℝ) *
    nativePNTError (N / (m * k))

/-- **Fresh-prime signed atom identity.**  The two reciprocal atoms indexed by
`(m,p*k)` and `(m*p,k)` share the same Chebyshev endpoint.  Möbius sign reversal
removes the inner `log k` contribution and leaves only `log p`. -/
theorem nativePNTMobiusSignedAtom_pair_adjoin_prime
    (N m p k : ℕ) (hk : 1 ≤ k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTMobiusSignedAtom N m (p * k) +
        nativePNTMobiusSignedAtom N (m * p) k =
      ((μ m : ℤ) : ℝ) * Real.log (p : ℝ) *
        nativePNTError (N / ((m * p) * k)) := by
  have hpair := nativeMobiusLogFiber_pair_adjoin_prime m p k hk hp hcop
  have hmul : m * (p * k) = (m * p) * k := by ring
  unfold nativePNTMobiusSignedAtom
  rw [hmul]
  calc
    ((μ m : ℤ) : ℝ) * Real.log ((p * k : ℕ) : ℝ) *
          nativePNTError (N / ((m * p) * k)) +
        ((μ (m * p) : ℤ) : ℝ) * Real.log (k : ℝ) *
          nativePNTError (N / ((m * p) * k)) =
      (((μ m : ℤ) : ℝ) * Real.log ((p * k : ℕ) : ℝ) +
        ((μ (m * p) : ℤ) : ℝ) * Real.log (k : ℝ)) *
          nativePNTError (N / ((m * p) * k)) := by ring
    _ = ((μ m : ℤ) : ℝ) * Real.log (p : ℝ) *
          nativePNTError (N / ((m * p) * k)) := by
      rw [hpair]

/-- **Exact local signed surplus.**  The drop from the sum of the two absolute
atom masses to the absolute mass after fresh-prime pairing is exactly twice the
duplicated `log k` mass. -/
theorem nativePNTMobiusSignedAtom_pair_abs_surplus_eq
    (N m p k : ℕ) (hk : 1 ≤ k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    |nativePNTMobiusSignedAtom N m (p * k)| +
        |nativePNTMobiusSignedAtom N (m * p) k| -
        |nativePNTMobiusSignedAtom N m (p * k) +
          nativePNTMobiusSignedAtom N (m * p) k| =
      2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ) *
        |nativePNTError (N / ((m * p) * k))| := by
  rw [nativePNTMobiusSignedAtom_pair_adjoin_prime N m p k hk hp hcop]
  unfold nativePNTMobiusSignedAtom
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  have hmul : m * (p * k) = (m * p) * k := by ring
  rw [hmul]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by omega)
  have hpLog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hkLog0 : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  rw [Real.log_mul hp0 hk0]
  simp only [abs_mul, abs_neg, abs_of_nonneg hpLog0,
    abs_of_nonneg hkLog0, abs_of_nonneg (add_nonneg hpLog0 hkLog0)]
  ring

/-- A large common endpoint error turns the exact fresh-prime cancellation into
an explicit lower bound for the local surplus. -/
theorem nativePNTMobiusSignedAtom_pair_abs_surplus_ge_of_error
    (N m p k : ℕ) (beta : ℝ)
    (hk : 1 ≤ k) (hp : p.Prime) (hcop : Nat.Coprime m p)
    (herror :
      beta * ((N / ((m * p) * k) : ℕ) : ℝ) ≤
        |nativePNTError (N / ((m * p) * k))|) :
    (2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ)) *
        (beta * ((N / ((m * p) * k) : ℕ) : ℝ)) ≤
      |nativePNTMobiusSignedAtom N m (p * k)| +
        |nativePNTMobiusSignedAtom N (m * p) k| -
        |nativePNTMobiusSignedAtom N m (p * k) +
          nativePNTMobiusSignedAtom N (m * p) k| := by
  have hkLog0 : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  have hcoef :
      0 ≤ 2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hkLog0
  calc
    (2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ)) *
        (beta * ((N / ((m * p) * k) : ℕ) : ℝ)) ≤
      (2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ)) *
        |nativePNTError (N / ((m * p) * k))| :=
      mul_le_mul_of_nonneg_left herror hcoef
    _ = 2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ) *
        |nativePNTError (N / ((m * p) * k))| := by ring
    _ = |nativePNTMobiusSignedAtom N m (p * k)| +
        |nativePNTMobiusSignedAtom N (m * p) k| -
        |nativePNTMobiusSignedAtom N m (p * k) +
          nativePNTMobiusSignedAtom N (m * p) k| :=
      (nativePNTMobiusSignedAtom_pair_abs_surplus_eq
        N m p k hk hp hcop).symm

end RHLean.Analysis
