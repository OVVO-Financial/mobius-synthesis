import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy
import RHLean.Proof.NormalizedCofactorExpansion

/-!
# Low-ω sources are pure high-orientation mass

Elementary, unconditional fact recorded from the omega-parity / orientation
diagnostic (`research/OMEGA_PARITY_ORIENTATION.md`).

A squarefree `m > 1` with at most two distinct prime factors always has its
largest prime factor above the square root of `m`.  Equivalently, its canonical
cofactor is strictly below its largest prime, i.e. the canonical height is
strictly positive, i.e. the source is pure `q > c` (high) orientation:

* `canonicalCofactor m < canonicalLargestPrimeFactor m`   (the core inequality);
* `m < (canonicalLargestPrimeFactor m) ^ 2`               (`P⁺(m) > √m`);
* `0 < canonicalHeightTwice m`                            (positive canonical
  height).

Here `m.primeFactors.card` is `ω(m)`, the number of distinct prime factors — the
same count the death-shell decomposition tracks on the canonical cofactor
(`RHLean.Proof.deathShellCofactorOmega`).  The statement is independent of any
conjecture; it only says the `ω ≤ 2` classes carry no low-orientation mass and so
never need the smooth/transport interaction to be split.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- For squarefree `m > 1` with at most two distinct prime factors, the canonical
cofactor is strictly smaller than the largest prime factor. -/
theorem canonicalCofactor_lt_largestPrimeFactor
    {m : ℕ} (hsq : Squarefree m) (hm : 1 < m)
    (hω : m.primeFactors.card ≤ 2) :
    canonicalCofactor m < canonicalLargestPrimeFactor m := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hPprime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hm
  have hPmem : canonicalLargestPrimeFactor m ∈ m.primeFactors :=
    canonicalLargestPrimeFactor_mem_primeFactors hm
  have hcP : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm
  have hcdvd : canonicalCofactor m ∣ m := ⟨_, hcP.symm⟩
  have hscf : Squarefree (canonicalCofactor m) := hsq.squarefree_of_dvd hcdvd
  -- The cofactor is coprime to the largest prime, so the prime does not divide it.
  have hcop : Nat.Coprime (canonicalCofactor m) (canonicalLargestPrimeFactor m) :=
    coprime_factors_of_squarefree hsq hcP
  have hPnc : ¬ canonicalLargestPrimeFactor m ∣ canonicalCofactor m :=
    hPprime.coprime_iff_not_dvd.mp hcop.symm
  -- Every prime factor of the cofactor is a prime factor of `m`.
  have hsub : (canonicalCofactor m).primeFactors ⊆ m.primeFactors := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, dvd_trans hp.2.1 hcdvd, hm0⟩
  have hPnmem :
      canonicalLargestPrimeFactor m ∉ (canonicalCofactor m).primeFactors :=
    fun hmem => hPnc (Nat.dvd_of_mem_primeFactors hmem)
  -- Hence at most one distinct prime factor survives in the cofactor.
  have hcardc : (canonicalCofactor m).primeFactors.card ≤ 1 := by
    have hss : (canonicalCofactor m).primeFactors ⊆
        m.primeFactors.erase (canonicalLargestPrimeFactor m) :=
      Finset.subset_erase.mpr ⟨hsub, hPnmem⟩
    have hle := Finset.card_le_card hss
    rw [Finset.card_erase_of_mem hPmem] at hle
    omega
  -- The squarefree cofactor is the product of its prime factors, over a set of
  -- size ≤ 1, hence `1` or a single prime strictly below the largest prime.
  have hprod : ∏ p ∈ (canonicalCofactor m).primeFactors, p = canonicalCofactor m :=
    Nat.prod_primeFactors_of_squarefree hscf
  rcases Nat.lt_or_ge (canonicalCofactor m).primeFactors.card 1 with h0 | h1
  · have hcard0 : (canonicalCofactor m).primeFactors.card = 0 := by omega
    have hempty : (canonicalCofactor m).primeFactors = ∅ :=
      Finset.card_eq_zero.mp hcard0
    have hc1 : canonicalCofactor m = 1 := by
      rw [hempty, Finset.prod_empty] at hprod
      exact hprod.symm
    rw [hc1]
    exact hPprime.one_lt
  · have hcard1 : (canonicalCofactor m).primeFactors.card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
    have hca : canonicalCofactor m = a := by
      rw [ha, Finset.prod_singleton] at hprod
      exact hprod.symm
    have hamem : a ∈ (canonicalCofactor m).primeFactors := by
      rw [ha]; exact Finset.mem_singleton_self a
    have haM : a ∈ m.primeFactors := hsub hamem
    have hale : a ≤ canonicalLargestPrimeFactor m := by
      unfold canonicalLargestPrimeFactor
      rw [dif_pos hm]
      exact Finset.le_max' _ a haM
    have hane : a ≠ canonicalLargestPrimeFactor m := fun h => hPnmem (h ▸ hamem)
    rw [hca]
    exact lt_of_le_of_ne hale hane

/-- Squarefree `m > 1` with at most two distinct prime factors has its largest
prime factor above `√m`: `m < (P⁺ m) ^ 2`. -/
theorem lt_largestPrimeFactor_sq
    {m : ℕ} (hsq : Squarefree m) (hm : 1 < m)
    (hω : m.primeFactors.card ≤ 2) :
    m < (canonicalLargestPrimeFactor m) ^ 2 := by
  have hlt := canonicalCofactor_lt_largestPrimeFactor hsq hm hω
  have hcP : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm
  have hPpos : 0 < canonicalLargestPrimeFactor m :=
    (canonicalLargestPrimeFactor_prime hm).pos
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hcP.symm
    _ < canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m :=
        mul_lt_mul_of_pos_right hlt hPpos
    _ = (canonicalLargestPrimeFactor m) ^ 2 := (pow_two _).symm

/-- Equivalently, the canonical height is strictly positive: the `ω ≤ 2` sources
are pure high-orientation (`q > c`) mass and need no smooth/transport splitting. -/
theorem canonicalHeightTwice_pos_of_card_primeFactors_le_two
    {m : ℕ} (hsq : Squarefree m) (hm : 1 < m)
    (hω : m.primeFactors.card ≤ 2) :
    0 < canonicalHeightTwice m := by
  have hlt := canonicalCofactor_lt_largestPrimeFactor hsq hm hω
  have hcast :
      (canonicalCofactor m : ℝ) < (canonicalLargestPrimeFactor m : ℝ) := by
    exact_mod_cast hlt
  have hcnn : (0 : ℝ) ≤ (canonicalCofactor m : ℝ) := by positivity
  unfold canonicalHeightTwice
  nlinarith [hcast, hcnn,
    mul_pos (sub_pos.mpr hcast)
      (by linarith : (0 : ℝ) <
        (canonicalLargestPrimeFactor m : ℝ) + (canonicalCofactor m : ℝ))]

end RHLean.Proof
