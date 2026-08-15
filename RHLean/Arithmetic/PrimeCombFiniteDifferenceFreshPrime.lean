import Mathlib
import Mathlib.Data.Finset.NatDivisors
import RHLean.Arithmetic.PrimeCombFiniteDifference

open scoped ArithmeticFunction.Moebius BigOperators Pointwise

noncomputable section

namespace RHLean.Arithmetic

/-- A prime outside a finite prime set is coprime to the product of that set. -/
theorem prime_coprime_primorial
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    Nat.Coprime p (primorial S) := by
  rw [hp.coprime_iff_not_dvd]
  intro hpdiv
  have hpdiv' : p ∣ S.prod id := by
    simpa [primorial] using hpdiv
  rcases (Prime.dvd_finset_prod_iff hp.prime id).mp hpdiv' with
    ⟨q, hqS, hpq⟩
  rcases (hprime q hqS).eq_one_or_self_of_dvd p hpq with hpOne | hpqEq
  · exact hp.ne_one hpOne
  · exact hpS (hpqEq ▸ hqS)

/-- For a fresh prime, divisors of the enlarged primorial split into the old
divisors and their `p`-multiples.  This is the unordered divisor decomposition
underlying the exact finite-difference recurrence. -/
theorem divisors_primorial_insert
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S) :
    (primorial (insert p S)).divisors =
      (primorial S).divisors ∪
        (primorial S).divisors.image (fun d => p * d) := by
  classical
  rw [primorial_insert S p hpS, Nat.divisors_mul, hp.divisors]
  ext n
  constructor
  · intro hn
    rcases Finset.mem_mul.mp hn with ⟨a, ha, b, hb, hab⟩
    have ha' : a = 1 ∨ a = p := by
      simpa using ha
    rcases ha' with rfl | rfl
    · have hbn : b = n := by simpa using hab
      exact Finset.mem_union.mpr (Or.inl (hbn ▸ hb))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨b, hb, hab⟩))
  · intro hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact Finset.mem_mul.mpr ⟨1, by simp, n, hn, by simp⟩
    · rcases Finset.mem_image.mp hn with ⟨b, hb, hbn⟩
      exact Finset.mem_mul.mpr ⟨p, by simp, b, hb, hbn⟩

/-- The two divisor branches in `divisors_primorial_insert` are disjoint. -/
theorem disjoint_divisors_primorial_mul_image
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    Disjoint (primorial S).divisors
      ((primorial S).divisors.image (fun d => p * d)) := by
  classical
  have hcop : Nat.Coprime p (primorial S) :=
    prime_coprime_primorial S p hp hpS hprime
  have hpNot : ¬ p ∣ primorial S :=
    (hp.coprime_iff_not_dvd.mp hcop)
  rw [Finset.disjoint_left]
  intro n hnD hnImage
  rcases Finset.mem_image.mp hnImage with ⟨d, hdD, hdn⟩
  have hpdD : p * d ∣ primorial S := by
    apply Nat.dvd_of_mem_divisors
    rw [hdn]
    exact hnD
  apply hpNot
  exact dvd_trans ⟨d, rfl⟩ hpdD

/-- Exact fresh-prime recurrence for the canonical finite Möbius divisor-sum
operator.  No ordering of `S` and no complete CRT period enters the statement. -/
theorem finiteDifferenceOperator_insert
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q)
    (f : ℕ → R) :
    finiteDifferenceOperator (insert p S) f =
      finiteDifferenceOperator S f -
        finiteDifferenceOperator S (shift p f) := by
  classical
  funext x
  have hcop : Nat.Coprime p (primorial S) :=
    prime_coprime_primorial S p hp hpS hprime
  have hdisj :=
    disjoint_divisors_primorial_mul_image S p hp hpS hprime
  unfold finiteDifferenceOperator
  rw [divisors_primorial_insert S p hp hpS]
  rw [Finset.sum_union hdisj]
  have hinj : Set.InjOn (fun d : ℕ => p * d) (primorial S).divisors := by
    intro a ha b hb hab
    exact Nat.mul_left_cancel hp.pos hab
  have himage :
      (∑ d ∈ (primorial S).divisors.image (fun d => p * d),
          (((μ d : ℤ) : R)) * shift d f x) =
        -(∑ d ∈ (primorial S).divisors,
          (((μ d : ℤ) : R)) * shift d (shift p f) x) := by
    rw [Finset.sum_image hinj]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdP : d ∣ primorial S := Nat.dvd_of_mem_divisors hd
    have hcopd : Nat.Coprime p d := hcop.of_dvd_right hdP
    have hmu : μ (p * d) = -μ d := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopd]
      rw [ArithmeticFunction.moebius_apply_prime hp]
      ring
    rw [hmu]
    simp [shift, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [himage]
  simp only [Pi.sub_apply, sub_eq_add_neg]

/-- Singleton specialization: the canonical divisor operator is exactly one
multiplicative finite difference. -/
theorem finiteDifferenceOperator_singleton
    {R : Type*} [CommRing R]
    (p : ℕ) (hp : Nat.Prime p) (f : ℕ → R) :
    finiteDifferenceOperator {p} f =
      f - shift p f := by
  have h := finiteDifferenceOperator_insert
    (R := R) ∅ p hp (by simp) (by simp) f
  simpa using h

end RHLean.Arithmetic
