import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifference
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime
import RHLean.Arithmetic.PrimesUpToFrontier

/-!
# Full-prefix identification of the finite Möbius difference operator

For any function `f` with `f 0 = 0` and any prime set `S` saturated through
the cutoff (`primesUpTo X ⊆ S`), the ordinary Möbius-weighted reciprocal
prefix `Σ_{n ≤ X} μ(n)·f(⌊X/n⌋)` is exactly the canonical finite-difference
operator `D_S f` evaluated at `X`: divisors of the primorial exceeding `X`
contribute `f 0 = 0`, squarefree `n ≤ X` divide the saturated primorial, and
non-squarefree `n` carry Möbius weight zero.

The module also records the two support identities for the primorial divisor
lattice (`2^{|S|}` faces; Euler reciprocal sum `Π (1 + 1/p)`) and the
truncated operator `finiteDifferenceOperatorUpTo` with its exact tail split.
These are bookkeeping identities: no estimate is asserted anywhere.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- The primorial of a genuine prime set is positive. -/
theorem primorial_ne_zero (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    primorial S ≠ 0 := by
  unfold primorial
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact (hprime p hp).ne_zero

/-- The primorial divisor lattice of a prime set has exactly `2^|S|` faces. -/
theorem card_divisors_primorial (S : Finset ℕ) :
    (∀ p ∈ S, Nat.Prime p) →
    (primorial S).divisors.card = 2 ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => intro _; simp [primorial]
  | @insert p S hpS ih =>
      intro hprime
      have hp : Nat.Prime p := hprime p (Finset.mem_insert_self p S)
      have hS : ∀ q ∈ S, Nat.Prime q := fun q hq =>
        hprime q (Finset.mem_insert_of_mem hq)
      rw [divisors_primorial_insert S p hp hpS,
        Finset.card_union_of_disjoint
          (disjoint_divisors_primorial_mul_image S p hp hpS hS),
        Finset.card_image_of_injective _
          (fun a b hab => Nat.eq_of_mul_eq_mul_left hp.pos hab),
        ih hS, Finset.card_insert_of_notMem hpS, pow_succ]
      ring

/-- Euler reciprocal sum over the primorial divisor lattice. -/
theorem sum_inv_divisors_primorial (S : Finset ℕ) :
    (∀ p ∈ S, Nat.Prime p) →
    (∑ d ∈ (primorial S).divisors, ((d : ℝ))⁻¹) =
      ∏ p ∈ S, (1 + ((p : ℝ))⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro _; simp [primorial]
  | @insert p S hpS ih =>
      intro hprime
      have hp : Nat.Prime p := hprime p (Finset.mem_insert_self p S)
      have hS : ∀ q ∈ S, Nat.Prime q := fun q hq =>
        hprime q (Finset.mem_insert_of_mem hq)
      rw [divisors_primorial_insert S p hp hpS,
        Finset.sum_union
          (disjoint_divisors_primorial_mul_image S p hp hpS hS),
        Finset.sum_image
          (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp.pos hab)]
      have hcast : ∀ d ∈ (primorial S).divisors,
          (((p * d : ℕ) : ℝ))⁻¹ = ((p : ℝ))⁻¹ * ((d : ℝ))⁻¹ := by
        intro d _
        push_cast
        rw [mul_inv]
      rw [Finset.sum_congr rfl hcast, ← Finset.mul_sum, ih hS,
        Finset.prod_insert hpS]
      ring

/-- **Exact full-prefix identification, saturated form.**  For a prime set
containing every prime up to `X` and any `f` vanishing at `0`, the ordinary
Möbius reciprocal prefix at `X` is the canonical finite-difference operator. -/
theorem sum_Icc_moebius_mul_eq_finiteDifferenceOperator_of_primesUpTo_subset
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (f : ℕ → R) (X : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : primesUpTo X ⊆ S)
    (hf0 : f 0 = 0) :
    (∑ n ∈ Finset.Icc 1 X, (((μ n : ℤ) : R)) * f (X / n)) =
      finiteDifferenceOperator S f X := by
  classical
  have hP0 : primorial S ≠ 0 := primorial_ne_zero S hprime
  rw [finiteDifferenceOperator_apply]
  have hvan1 : ∀ d ∈ (primorial S).divisors,
      d ∉ (primorial S).divisors.filter (fun d => d ≤ X) →
      (((μ d : ℤ) : R)) * f (X / d) = 0 := by
    intro d hd hnot
    have hdX : ¬ d ≤ X := by
      simp only [Finset.mem_filter, hd, true_and] at hnot
      exact hnot
    rw [Nat.div_eq_of_lt (by omega), hf0, mul_zero]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hvan1]
  have hsub : (primorial S).divisors.filter (fun d => d ≤ X) ⊆
      Finset.Icc 1 X := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have h1 : 0 < d := Nat.pos_of_mem_divisors hd.1
    rw [Finset.mem_Icc]
    omega
  have hvan2 : ∀ d ∈ Finset.Icc 1 X,
      d ∉ (primorial S).divisors.filter (fun d => d ≤ X) →
      (((μ d : ℤ) : R)) * f (X / d) = 0 := by
    intro d hd hnot
    rw [Finset.mem_Icc] at hd
    by_cases hsq : Squarefree d
    · exfalso
      apply hnot
      rw [Finset.mem_filter]
      refine ⟨Nat.mem_divisors.mpr ⟨?_, hP0⟩, hd.2⟩
      have hfac : d.primeFactors ⊆ S := by
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
        have hpX : p ≤ X :=
          le_trans (Nat.le_of_dvd (by omega) hpd) hd.2
        exact hcover (mem_primesUpTo_of_prime_le hpp hpX)
      calc d = ∏ p ∈ d.primeFactors, p :=
            (Nat.prod_primeFactors_of_squarefree hsq).symm
        _ ∣ ∏ p ∈ S, p := Finset.prod_dvd_prod_of_subset _ _ _ hfac
        _ = primorial S := rfl
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      simp
  exact (Finset.sum_subset hsub hvan2).symm

/-- Canonical corollary at the full ambient prime set.  `primesUpTo X` is a
proof-level object here, not an evaluation strategy. -/
theorem sum_Icc_moebius_mul_eq_finiteDifferenceOperator_primesUpTo
    {R : Type*} [CommRing R]
    (f : ℕ → R) (X : ℕ) (hf0 : f 0 = 0) :
    (∑ n ∈ Finset.Icc 1 X, (((μ n : ℤ) : R)) * f (X / n)) =
      finiteDifferenceOperator (primesUpTo X) f X :=
  sum_Icc_moebius_mul_eq_finiteDifferenceOperator_of_primesUpTo_subset
    (primesUpTo X) f X (fun _ hp => prime_of_mem_primesUpTo hp)
    (Finset.Subset.refl _) hf0

/-- The `K`-truncated finite Möbius difference operator: only divisor fibers
at truncation level at most `K` are retained. -/
def finiteDifferenceOperatorUpTo
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (K : ℕ) (f : ℕ → R) : ℕ → R :=
  fun x =>
    ∑ d ∈ (primorial S).divisors.filter (fun d => d ≤ K),
      (((μ d : ℤ) : R)) * f (x / d)

/-- Exact tail split of the canonical operator at any truncation level. -/
theorem finiteDifferenceOperator_eq_upTo_add_tail
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (K : ℕ) (f : ℕ → R) (x : ℕ) :
    finiteDifferenceOperator S f x =
      finiteDifferenceOperatorUpTo S K f x +
        ∑ d ∈ (primorial S).divisors.filter (fun d => K < d),
          (((μ d : ℤ) : R)) * f (x / d) := by
  classical
  rw [finiteDifferenceOperator_apply]
  simp only [finiteDifferenceOperatorUpTo]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((primorial S).divisors) (fun d => d ≤ K)
    (fun d => (((μ d : ℤ) : R)) * f (x / d))]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun d _ => ?_) fun _ _ => rfl
  simp [not_le]

end RHLean.Arithmetic

end
