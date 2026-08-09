import Mathlib

/-!
# Least-prime factor-depth hierarchy and the terminal semiprime fringe

Elementary, unconditional facts underlying the frontier's depth stratification
(companion to the omega-parity / N-over-2 diagnostics).

If a squarefree `n ≤ X` has its least prime factor so large that
`(minFac n)^(r+1) > X`, then `n` cannot carry `r+1` distinct primes, so
`ω(n) ≤ r`.  Writing the threshold as `(minFac n)^(r+1) > X` avoids real
`(r+1)`-th roots entirely: it is exactly `minFac n > X^{1/(r+1)}` in integer form.

The `r = 2` case is the terminal semiprime fringe: a squarefree composite with
`(minFac n)^3 > X` is a semiprime `n = pq`, hence `μ(n) = +1`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- **Factor-depth hierarchy.**  A squarefree `n ≤ X` whose least prime factor
satisfies `(minFac n)^(r+1) > X` has at most `r` distinct prime factors. -/
theorem card_primeFactors_le_of_lt_minFac_pow
    {n X r : ℕ} (hsq : Squarefree n) (hnX : n ≤ X)
    (hlt : X < n.minFac ^ (r + 1)) :
    n.primeFactors.card ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  -- Every prime factor is at least the least prime factor.
  have hle : ∀ p ∈ n.primeFactors, n.minFac ≤ p := by
    intro p hp
    have hpp := Nat.mem_primeFactors.mp hp
    exact Nat.minFac_le_of_dvd hpp.1.two_le hpp.2.1
  have hmpos : 1 ≤ n.minFac := n.minFac_pos
  have hprod : ∏ p ∈ n.primeFactors, p = n :=
    Nat.prod_primeFactors_of_squarefree hsq
  -- `minFac^{card} ≤ ∏ primeFactors = n`.
  have hpow_le : n.minFac ^ n.primeFactors.card ≤ n := by
    calc
      n.minFac ^ n.primeFactors.card
          = ∏ _p ∈ n.primeFactors, n.minFac := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hle
      _ = n := hprod
  -- and `minFac^{r+1} ≤ minFac^{card}` because `r+1 ≤ card`.
  have hstep : n.minFac ^ (r + 1) ≤ n.minFac ^ n.primeFactors.card :=
    Nat.pow_le_pow_right hmpos hcon
  omega

/-- A squarefree `n > 1` that is not prime has at least two distinct prime
factors. -/
theorem two_le_card_primeFactors_of_not_prime
    {n : ℕ} (hsq : Squarefree n) (hn1 : 1 < n) (hcomp : ¬ n.Prime) :
    2 ≤ n.primeFactors.card := by
  classical
  rcases Nat.lt_or_ge n.primeFactors.card 2 with h | h
  · exfalso
    have hprod : ∏ p ∈ n.primeFactors, p = n :=
      Nat.prod_primeFactors_of_squarefree hsq
    rcases Nat.lt_or_ge n.primeFactors.card 1 with h0 | h1
    · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [hempty, Finset.prod_empty] at hprod
      omega
    · have hc1 : n.primeFactors.card = 1 := by omega
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc1
      have hpmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
      have hpprime : p.Prime := (Nat.mem_primeFactors.mp hpmem).1
      have hnp : n = p := by
        rw [hp, Finset.prod_singleton] at hprod; exact hprod.symm
      rw [hnp] at hcomp
      exact hcomp hpprime
  · exact h

/-- **Terminal semiprime fringe.**  A squarefree composite `n ≤ X` with
`(minFac n)^3 > X` has exactly two distinct prime factors. -/
theorem card_primeFactors_eq_two_of_composite_lt_minFac_cube
    {n X : ℕ} (hsq : Squarefree n) (hn1 : 1 < n) (hcomp : ¬ n.Prime)
    (hnX : n ≤ X) (hlt : X < n.minFac ^ 3) :
    n.primeFactors.card = 2 := by
  have hle : n.primeFactors.card ≤ 2 :=
    card_primeFactors_le_of_lt_minFac_pow hsq hnX (by simpa using hlt)
  have hge : 2 ≤ n.primeFactors.card :=
    two_le_card_primeFactors_of_not_prime hsq hn1 hcomp
  omega

/-- The fringe is entirely positive: such a semiprime has Möbius value `+1`. -/
theorem moebius_eq_one_of_composite_lt_minFac_cube
    {n X : ℕ} (hsq : Squarefree n) (hn1 : 1 < n) (hcomp : ¬ n.Prime)
    (hnX : n ≤ X) (hlt : X < n.minFac ^ 3) :
    μ n = 1 := by
  classical
  have hcard : n.primeFactors.card = 2 :=
    card_primeFactors_eq_two_of_composite_lt_minFac_cube hsq hn1 hcomp hnX hlt
  obtain ⟨p, q, hpq, hpf⟩ := Finset.card_eq_two.mp hcard
  have hprod : ∏ r ∈ n.primeFactors, r = n :=
    Nat.prod_primeFactors_of_squarefree hsq
  have hpmem : p ∈ n.primeFactors := by rw [hpf]; exact Finset.mem_insert_self p {q}
  have hqmem : q ∈ n.primeFactors := by
    rw [hpf]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hpmem).1
  have hqprime : q.Prime := (Nat.mem_primeFactors.mp hqmem).1
  have hn_eq : n = p * q := by
    rw [hpf, Finset.prod_pair hpq] at hprod; exact hprod.symm
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpprime hqprime).mpr hpq
  rw [hn_eq, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hpprime,
    ArithmeticFunction.moebius_apply_prime hqprime]
  norm_num

end RHLean.Arithmetic
