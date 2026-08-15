import Mathlib
import Mathlib.Data.Finset.NatDivisors

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# Canonical finite Möbius difference operator

The multi-prime finite-difference operator is defined directly as a Möbius-
weighted divisor sum over the product of the selected prime coordinates.  The
definition does not choose an ordering of the finite prime set and does not use
Dirichlet convolution: it acts on an arbitrary sequence by floor shifts.
-/

/-- Product of a finite set of prime coordinates.  The definition itself does
not require primality; prime-set hypotheses enter only in structural lemmas. -/
def primorial (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

/-- Floor shift by an arithmetic dilation. -/
def shift {R : Type*} (d : ℕ) (f : ℕ → R) : ℕ → R :=
  fun x => f (x / d)

/-- Canonical finite Möbius difference operator attached to a finite prime set.
For a genuine prime set `S`, `primorial S` is squarefree, so its divisors are
precisely the Boolean prime faces. -/
def finiteDifferenceOperator
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (f : ℕ → R) : ℕ → R :=
  fun x =>
    ∑ d ∈ (primorial S).divisors,
      (((μ d : ℤ) : R)) * shift d f x

@[simp] theorem primorial_empty : primorial ∅ = 1 := by
  simp [primorial]

@[simp] theorem primorial_insert
    (S : Finset ℕ) (p : ℕ) (hpS : p ∉ S) :
    primorial (insert p S) = p * primorial S := by
  simp [primorial, hpS]

@[simp] theorem shift_one
    {R : Type*} (f : ℕ → R) :
    shift 1 f = f := by
  funext x
  simp [shift]

/-- Floor shifts compose exactly by multiplying their dilation parameters. -/
theorem shift_comp
    {R : Type*} (d e : ℕ) (f : ℕ → R) :
    shift d (shift e f) = shift (d * e) f := by
  funext x
  simp [shift, Nat.div_div_eq_div_mul]

/-- Floor shifts commute. -/
theorem shift_comm
    {R : Type*} (d e : ℕ) (f : ℕ → R) :
    shift d (shift e f) = shift e (shift d f) := by
  rw [shift_comp, shift_comp, Nat.mul_comm]

@[simp] theorem finiteDifferenceOperator_empty
    {R : Type*} [CommRing R] (f : ℕ → R) :
    finiteDifferenceOperator ∅ f = f := by
  funext x
  simp [finiteDifferenceOperator, shift]

/-- Pointwise expansion of the canonical operator. -/
theorem finiteDifferenceOperator_apply
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (f : ℕ → R) (x : ℕ) :
    finiteDifferenceOperator S f x =
      ∑ d ∈ (primorial S).divisors,
        (((μ d : ℤ) : R)) * f (x / d) := by
  rfl

end RHLean.Arithmetic
