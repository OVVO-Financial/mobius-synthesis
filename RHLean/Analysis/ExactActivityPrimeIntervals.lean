import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm

/-!
# Exact active-prime intervals for compressed dyadic packets

This module replaces the midpoint-lifetime approximation used in the first
prime-density experiment with the exact finite activity interval.

For a retained odd cofactor `c`, prime factor `q`, and stage `t`, the compressed
boundary packet is active precisely when

```text
max (t+2) (ceil ((t+1)^2 / (2c))) <= q
q <= floor (((t+1)^2-1) / c).
```

The proof is elementary: the two square-root packet inequalities become the two
product inequalities around `(t+1)^2`, and the transition condition becomes
`t+2 <= q`.

All statements here are exact finite identities. No prime-density estimate,
short-interval variance bound, or RH implication is asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Lower endpoint of the exact prime interval active at stage `t` for cofactor
`c`. Ceiling division is used only with the explicit positivity hypothesis in
subsequent theorems. -/
def exactActivityPrimeLower (t c : ℕ) : ℕ :=
  max (t + 2) ((t + 1) ^ 2 ⌈/⌉ (2 * c))

/-- Upper endpoint of the exact prime interval active at stage `t` for cofactor
`c`. -/
def exactActivityPrimeUpper (t c : ℕ) : ℕ :=
  ((t + 1) ^ 2 - 1) / c

/-- Finite set of primes in the exact activity interval. -/
def exactActivityPrimeInterval (t c : ℕ) : Finset ℕ :=
  (Finset.Icc (exactActivityPrimeLower t c) (exactActivityPrimeUpper t c)).filter
    Nat.Prime

@[simp] theorem mem_exactActivityPrimeInterval {t c q : ℕ} :
    q ∈ exactActivityPrimeInterval t c ↔
      q.Prime ∧ exactActivityPrimeLower t c ≤ q ∧ q ≤ exactActivityPrimeUpper t c := by
  simp [exactActivityPrimeInterval, and_comm]

/-- The compressed packet activity predicate is exactly the three elementary
product inequalities, provided `t` lies inside the finite horizon. -/
theorem isDyadicBoundaryActive_iff_product_bounds
    {N c q t : ℕ} (htN : t ≤ N) :
    IsDyadicBoundaryActive N c q t ↔
      t + 2 ≤ q ∧
        (t + 1) ^ 2 ≤ 2 * (c * q) ∧
          c * q < (t + 1) ^ 2 := by
  constructor
  · intro h
    rcases h with ⟨hentry, hupper⟩
    have hupper' :
        t < Nat.sqrt (dyadicChildCofactor c * q) ∧
          t < finiteTransportUpper N q := by
      simpa [dyadicBoundaryUpper] using (lt_min_iff.mp hupper)
    have hfinite : t < q - 1 ∧ t < N + 1 := by
      simpa [finiteTransportUpper] using (lt_min_iff.mp hupper'.2)
    have hq : t + 2 ≤ q := by omega
    have hchildSucc : t + 1 ≤ Nat.sqrt (dyadicChildCofactor c * q) := by
      omega
    have hchildSquare : (t + 1) ^ 2 ≤ dyadicChildCofactor c * q :=
      (Nat.le_sqrt').1 hchildSucc
    have hlower : (t + 1) ^ 2 ≤ 2 * (c * q) := by
      simpa [dyadicChildCofactor, Nat.mul_assoc] using hchildSquare
    have hentryLt : Nat.sqrt (c * q) < t + 1 := by omega
    have hupperProduct : c * q < (t + 1) ^ 2 :=
      (Nat.sqrt_lt').1 hentryLt
    exact ⟨hq, hlower, hupperProduct⟩
  · rintro ⟨hq, hlower, hupperProduct⟩
    have hentryLt : Nat.sqrt (c * q) < t + 1 :=
      (Nat.sqrt_lt').2 hupperProduct
    have hentry : Nat.sqrt (c * q) ≤ t := by omega
    have hchildSquare :
        (t + 1) ^ 2 ≤ dyadicChildCofactor c * q := by
      simpa [dyadicChildCofactor, Nat.mul_assoc] using hlower
    have hchildSucc : t + 1 ≤ Nat.sqrt (dyadicChildCofactor c * q) :=
      (Nat.le_sqrt').2 hchildSquare
    have hchild : t < Nat.sqrt (dyadicChildCofactor c * q) := by omega
    have htransition : t < q - 1 := by omega
    have hhorizon : t < N + 1 := by omega
    refine ⟨hentry, ?_⟩
    unfold dyadicBoundaryUpper finiteTransportUpper
    exact lt_min hchild (lt_min htransition hhorizon)

/-- Membership in the explicit integer interval is exactly the same three
product inequalities. -/
theorem exactActivityPrimeBounds_iff_product_bounds
    {t c q : ℕ} (hc : 0 < c) :
    exactActivityPrimeLower t c ≤ q ∧ q ≤ exactActivityPrimeUpper t c ↔
      t + 2 ≤ q ∧
        (t + 1) ^ 2 ≤ 2 * (c * q) ∧
          c * q < (t + 1) ^ 2 := by
  have h2c : 0 < 2 * c := by omega
  constructor
  · rintro ⟨hlower, hupper⟩
    have hlower' :
        max (t + 2) ((t + 1) ^ 2 ⌈/⌉ (2 * c)) ≤ q := by
      simpa [exactActivityPrimeLower] using hlower
    have hparts := max_le_iff.mp hlower'
    have hceil : (t + 1) ^ 2 ≤ (2 * c) * q :=
      (ceilDiv_le_iff_le_mul h2c).1 hparts.2
    have hmiddle : (t + 1) ^ 2 ≤ 2 * (c * q) := by
      simpa [Nat.mul_assoc] using hceil
    have hdiv : q * c ≤ (t + 1) ^ 2 - 1 := by
      exact (Nat.le_div_iff_mul_le hc).1 hupper
    have hproductLe : c * q ≤ (t + 1) ^ 2 - 1 := by
      simpa [Nat.mul_comm] using hdiv
    have hsquarePos : 0 < (t + 1) ^ 2 := by positivity
    have hproductLt : c * q < (t + 1) ^ 2 := by omega
    exact ⟨hparts.1, hmiddle, hproductLt⟩
  · rintro ⟨hq, hmiddle, hproductLt⟩
    have hceil : ((t + 1) ^ 2 ⌈/⌉ (2 * c)) ≤ q := by
      apply (ceilDiv_le_iff_le_mul h2c).2
      simpa [Nat.mul_assoc] using hmiddle
    have hlowerMax :
        max (t + 2) ((t + 1) ^ 2 ⌈/⌉ (2 * c)) ≤ q :=
      max_le hq hceil
    have hlower : exactActivityPrimeLower t c ≤ q := by
      simpa [exactActivityPrimeLower] using hlowerMax
    have hqcLt : q * c < (t + 1) ^ 2 := by
      simpa [Nat.mul_comm] using hproductLt
    have hqcLe : q * c ≤ (t + 1) ^ 2 - 1 :=
      Nat.le_pred_of_lt hqcLt
    have hupper : q ≤ exactActivityPrimeUpper t c := by
      unfold exactActivityPrimeUpper
      exact (Nat.le_div_iff_mul_le hc).2 hqcLe
    exact ⟨hlower, hupper⟩

/-- Exact equivalence between compressed packet activity and the explicit prime
interval. -/
theorem isDyadicBoundaryActive_iff_exactActivityPrimeBounds
    {N c q t : ℕ} (hc : 0 < c) (htN : t ≤ N) :
    IsDyadicBoundaryActive N c q t ↔
      exactActivityPrimeLower t c ≤ q ∧ q ≤ exactActivityPrimeUpper t c := by
  rw [isDyadicBoundaryActive_iff_product_bounds htN,
    exactActivityPrimeBounds_iff_product_bounds hc]

/-- Prime membership in the exact interval is equivalent to prime packet
activity. -/
theorem mem_exactActivityPrimeInterval_iff
    {N c q t : ℕ} (hc : 0 < c) (htN : t ≤ N) :
    q ∈ exactActivityPrimeInterval t c ↔
      q.Prime ∧ IsDyadicBoundaryActive N c q t := by
  rw [mem_exactActivityPrimeInterval]
  constructor
  · rintro ⟨hqPrime, hbounds⟩
    exact ⟨hqPrime,
      (isDyadicBoundaryActive_iff_exactActivityPrimeBounds hc htN).2 hbounds⟩
  · rintro ⟨hqPrime, hactive⟩
    exact ⟨hqPrime,
      (isDyadicBoundaryActive_iff_exactActivityPrimeBounds hc htN).1 hactive⟩

/-- Exact finite cofactor fiber obtained by summing the compressed boundary
contribution over the active-prime interval. -/
def exactActivityPrimeSourceMass (N c t : ℕ) : ℂ :=
  ∑ q ∈ exactActivityPrimeInterval t c, dyadicBoundaryContribution N c q t

/-- Every prime in the exact interval contributes the same source sign when the
cofactor has already entered by time `t`. The complete fiber is therefore its
prime count times `-mu(c)`. -/
theorem exactActivityPrimeSourceMass_eq_card_nsmul
    {N c t : ℕ} (hc : 0 < c) (hct : c ≤ t) (htN : t ≤ N) :
    exactActivityPrimeSourceMass N c t =
      (exactActivityPrimeInterval t c).card • (-canonicalMoebiusWeight c) := by
  unfold exactActivityPrimeSourceMass
  calc
    (∑ q ∈ exactActivityPrimeInterval t c,
        dyadicBoundaryContribution N c q t) =
      ∑ q ∈ exactActivityPrimeInterval t c, -canonicalMoebiusWeight c := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqData := (mem_exactActivityPrimeInterval).1 hq
        have hactive :=
          (mem_exactActivityPrimeInterval_iff hc htN).1 hq |>.2
        have hlower := hqData.2.1
        change max (t + 2) ((t + 1) ^ 2 ⌈/⌉ (2 * c)) ≤ q at hlower
        have htq : t + 2 ≤ q := (max_le_iff.mp hlower).1
        have hcq : c < q := by omega
        rw [dyadicBoundaryContribution, if_pos hactive,
          canonicalMoebiusWeight_mul_prime_eq_neg hc hcq hqData.1]
    _ = (exactActivityPrimeInterval t c).card • (-canonicalMoebiusWeight c) := by
      simp

end RHLean.Proof
