import Mathlib
import RHLean.Analysis.PrimeWheelRawConductorCoefficient
import RHLean.Arithmetic.PrimeProductLowerBound

/-!
# Exact weight calculus for the raw conductor coefficient

The arithmetic coefficient from `PrimeWheelRawConductorCoefficient` is indexed
by exponent choices `0,1,2` at every square-sensitive prime.  On the natural raw
period, its normalized value factors into independent local conductor weights.

This is finite algebra only.  The exact weights are useful for support and
recombination diagnostics, but no analytic estimate follows from their `l1`
mass alone.  In particular, later arguments must continue to preserve the
signed interaction between raw, smooth, and zero-mode pieces before norms.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Natural complete square-sensitive modulus associated with a finite prime
set, written as a product over the coordinate subtype. -/
def primeWheelRawNaturalModulus (S : Finset ℕ) : ℕ :=
  ∏ p : {p // p ∈ S}, p.val ^ 2

/-- Signed normalized local conductor weight. -/
def localPrimeRawSignedConductorWeight (p : ℕ) (c : Fin 3) : ℝ :=
  if c.val = 0 then
    ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2
  else if c.val = 1 then
    (1 - 2 * (p : ℝ)) / (p : ℝ) ^ 2
  else
    1 / (p : ℝ) ^ 2

/-- Absolute normalized local conductor weight. -/
def localPrimeRawAbsoluteConductorWeight (p : ℕ) (c : Fin 3) : ℝ :=
  if c.val = 0 then
    ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2
  else if c.val = 1 then
    (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2
  else
    1 / (p : ℝ) ^ 2

/-- Simple pointwise envelope displaying conductor suppression. -/
def localPrimeRawConductorDecayEnvelope (p : ℕ) (c : Fin 3) : ℝ :=
  if c.val = 0 then 1
  else if c.val = 1 then 2 / (p : ℝ)
  else 1 / (p : ℝ) ^ 2

/-- Product absolute weight of one full conductor exponent pattern. -/
def primeWheelRawConductorPatternAbsoluteWeight
    (S : Finset ℕ) (c : PrimeWheelRawExpansionPoint S) : ℝ :=
  ∏ p : {p // p ∈ S},
    localPrimeRawAbsoluteConductorWeight p.val (c p)

/-- Product decay envelope of one full conductor exponent pattern. -/
def primeWheelRawConductorPatternDecayEnvelope
    (S : Finset ℕ) (c : PrimeWheelRawExpansionPoint S) : ℝ :=
  ∏ p : {p // p ∈ S},
    localPrimeRawConductorDecayEnvelope p.val (c p)

/-- Multiplicative marker for nonzero conductor coordinates in a chosen prime
subset. -/
def primeWheelRawConductorPatternMarker
    (S T : Finset ℕ) (t : ℝ)
    (c : PrimeWheelRawExpansionPoint S) : ℝ :=
  ∏ p : {p // p ∈ S},
    if p.val ∈ T ∧ (c p).val ≠ 0 then t else 1

/-- Marked absolute mass of the full exponent-pattern conductor family. -/
def primeWheelRawConductorPatternGeneratingMass
    (S T : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ c : PrimeWheelRawExpansionPoint S,
    primeWheelRawConductorPatternAbsoluteWeight S c *
      primeWheelRawConductorPatternMarker S T t c

private def localPrimeRawNormalizedExpansionTerm
    (p : ℕ) (e : Fin 3) : ℂ :=
  localPrimeCombExpansionWeight e * (((p : ℂ) ^ e.val)⁻¹)

private theorem rawExpansionDivisor_ne_zero
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S) :
    primeWheelRawExpansionDivisor S e ≠ 0 := by
  have hpos : 0 < primeWheelRawExpansionDivisor S e := by
    unfold primeWheelRawExpansionDivisor
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hprime p.val p.property).pos _
  exact Nat.ne_of_gt hpos

private theorem rawExpansionDivisor_factorization
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S) :
    (primeWheelRawExpansionDivisor S e).factorization =
      ∑ p : {p // p ∈ S}, Finsupp.single p.val (e p).val := by
  unfold primeWheelRawExpansionDivisor
  rw [Nat.factorization_prod]
  · apply Fintype.sum_congr
    intro p
    exact (hprime p.val p.property).factorization_pow
  · intro p hp
    exact pow_ne_zero _ (hprime p.val p.property).ne_zero

private theorem rawExpansionDivisor_factorization_apply
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S)
    (p : {p // p ∈ S}) :
    (primeWheelRawExpansionDivisor S e).factorization p.val = (e p).val := by
  classical
  rw [rawExpansionDivisor_factorization S hprime e]
  simp [Finsupp.single_apply]
  calc
    (∑ x ∈ S.attach, if x.val = p.val then (e x).val else 0) =
        (if p.val = p.val then (e p).val else 0) := by
          apply Finset.sum_eq_single_of_mem p
          · simp
          · intro q _ hqp
            rw [if_neg]
            intro hval
            exact hqp (Subtype.ext hval)
    _ = (e p).val := by
      rw [if_pos rfl]

private theorem rawExpansionDivisor_dvd_iff_pointwise
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (c e : PrimeWheelRawExpansionPoint S) :
    primeWheelRawExpansionDivisor S c ∣
        primeWheelRawExpansionDivisor S e ↔
      ∀ p : {p // p ∈ S}, (c p).val ≤ (e p).val := by
  classical
  have hc0 := rawExpansionDivisor_ne_zero S hprime c
  have he0 := rawExpansionDivisor_ne_zero S hprime e
  rw [← Nat.factorization_le_iff_dvd hc0 he0]
  constructor
  · intro h p
    have hp := h p.val
    change
      (primeWheelRawExpansionDivisor S c).factorization p.val ≤
        (primeWheelRawExpansionDivisor S e).factorization p.val at hp
    rw [rawExpansionDivisor_factorization_apply S hprime c p,
      rawExpansionDivisor_factorization_apply S hprime e p] at hp
    exact hp
  · intro h
    rw [rawExpansionDivisor_factorization S hprime c,
      rawExpansionDivisor_factorization S hprime e]
    apply Finset.sum_le_sum
    intro p hp
    exact Finsupp.single_le_single.mpr (h p)

private def primeWheelRawTopExpansionPoint
    (S : Finset ℕ) : PrimeWheelRawExpansionPoint S :=
  fun _p => ⟨2, by omega⟩

private theorem rawExpansionDivisor_top_eq_naturalModulus
    (S : Finset ℕ) :
    primeWheelRawExpansionDivisor S
        (primeWheelRawTopExpansionPoint S) =
      primeWheelRawNaturalModulus S := by
  unfold primeWheelRawExpansionDivisor primeWheelRawTopExpansionPoint
    primeWheelRawNaturalModulus
  rfl

private theorem rawExpansionDivisor_dvd_naturalModulus
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S) :
    primeWheelRawExpansionDivisor S e ∣
      primeWheelRawNaturalModulus S := by
  rw [← rawExpansionDivisor_top_eq_naturalModulus S]
  apply (rawExpansionDivisor_dvd_iff_pointwise S hprime e
    (primeWheelRawTopExpansionPoint S)).2
  intro p
  exact Nat.le_of_lt_succ (e p).isLt

private theorem natQuotient_cast_mul_inv_eq_inv
    {N d : ℕ} (hN : 0 < N) (hd : d ∣ N) :
    (((N / d : ℕ) : ℂ)) * ((N : ℂ)⁻¹) = ((d : ℂ)⁻¹) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hN
  have hNne : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hdne : (d : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdpos)
  have hprod : d * (N / d) = N := Nat.mul_div_cancel' hd
  field_simp [hNne, hdne]
  exact_mod_cast (by simpa [Nat.mul_comm] using hprod)

private theorem rawExpansionWeight_mul_invDivisor_eq_prod
    (S : Finset ℕ)
    (e : PrimeWheelRawExpansionPoint S) :
    primeWheelRawExpansionWeight S e *
        ((((primeWheelRawExpansionDivisor S e : ℕ) : ℂ))⁻¹) =
      ∏ p : {p // p ∈ S},
        localPrimeRawNormalizedExpansionTerm p.val (e p) := by
  unfold primeWheelRawExpansionWeight primeWheelRawExpansionDivisor
    localPrimeRawNormalizedExpansionTerm
  push_cast
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

private theorem localPrimeRawTailSum_eq_signedWeight
    (p : ℕ) (hp : Nat.Prime p) (c : Fin 3) :
    (∑ e : Fin 3,
      if c.val ≤ e.val then
        localPrimeRawNormalizedExpansionTerm p e
      else 0) =
      ((localPrimeRawSignedConductorWeight p c : ℝ) : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  fin_cases c
  · simp [localPrimeRawNormalizedExpansionTerm,
      localPrimeCombExpansionWeight,
      localPrimeRawSignedConductorWeight, Fin.sum_univ_succ]
    field_simp [hp0]
    ring
  · simp [localPrimeRawNormalizedExpansionTerm,
      localPrimeCombExpansionWeight,
      localPrimeRawSignedConductorWeight, Fin.sum_univ_succ]
    field_simp [hp0]
    ring
  · simp [localPrimeRawNormalizedExpansionTerm,
      localPrimeCombExpansionWeight,
      localPrimeRawSignedConductorWeight, Fin.sum_univ_succ]

/-- Exact normalized product formula for the actual arithmetic coefficient,
indexed by its genuine `0,1,2` prime-exponent conductor pattern. -/
theorem primeWheelRawConductorArithmeticCoefficient_normalized_eq_neg_prod
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (c : PrimeWheelRawExpansionPoint S) :
    primeWheelRawConductorArithmeticCoefficient
        S (primeWheelRawNaturalModulus S)
        (primeWheelRawExpansionDivisor S c) *
        (((primeWheelRawNaturalModulus S : ℕ) : ℂ)⁻¹) =
      -∏ p : {p // p ∈ S},
        ((localPrimeRawSignedConductorWeight p.val (c p) : ℝ) : ℂ) := by
  classical
  have hQpos : 0 < primeWheelRawNaturalModulus S := by
    unfold primeWheelRawNaturalModulus
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hprime p.val p.property).pos _
  unfold primeWheelRawConductorArithmeticCoefficient
  rw [neg_mul, Finset.sum_mul]
  apply congrArg Neg.neg
  calc
    (∑ e : PrimeWheelRawExpansionPoint S,
      (primeWheelRawExpansionWeight S e *
        (if primeWheelRawExpansionDivisor S c ∣
              primeWheelRawExpansionDivisor S e then
          ((((primeWheelRawNaturalModulus S) /
            primeWheelRawExpansionDivisor S e : ℕ) : ℂ))
        else 0)) *
          (((primeWheelRawNaturalModulus S : ℕ) : ℂ)⁻¹)) =
      ∑ e : PrimeWheelRawExpansionPoint S,
        if ∀ p : {p // p ∈ S}, (c p).val ≤ (e p).val then
          primeWheelRawExpansionWeight S e *
            ((((primeWheelRawExpansionDivisor S e : ℕ) : ℂ))⁻¹)
        else 0 := by
          apply Fintype.sum_congr
          intro e
          have hiff := rawExpansionDivisor_dvd_iff_pointwise S hprime c e
          by_cases hle : ∀ p : {p // p ∈ S}, (c p).val ≤ (e p).val
          · have hdiv : primeWheelRawExpansionDivisor S c ∣
                primeWheelRawExpansionDivisor S e := hiff.mpr hle
            rw [if_pos hdiv, if_pos hle]
            rw [mul_assoc,
              natQuotient_cast_mul_inv_eq_inv hQpos
                (rawExpansionDivisor_dvd_naturalModulus S hprime e)]
          · have hdiv : ¬ primeWheelRawExpansionDivisor S c ∣
                primeWheelRawExpansionDivisor S e :=
              fun h => hle (hiff.mp h)
            rw [if_neg hdiv, if_neg hle]
            ring
    _ =
      ∑ e : PrimeWheelRawExpansionPoint S,
        if ∀ p : {p // p ∈ S}, (c p).val ≤ (e p).val then
          ∏ p : {p // p ∈ S},
            localPrimeRawNormalizedExpansionTerm p.val (e p)
        else 0 := by
          apply Fintype.sum_congr
          intro e
          by_cases hle : ∀ p : {p // p ∈ S}, (c p).val ≤ (e p).val
          · simp only [if_pos hle]
            exact rawExpansionWeight_mul_invDivisor_eq_prod S e
          · simp only [if_neg hle]
    _ =
      ∑ e : PrimeWheelRawExpansionPoint S,
        ∏ p : {p // p ∈ S},
          if (c p).val ≤ (e p).val then
            localPrimeRawNormalizedExpansionTerm p.val (e p)
          else 0 := by
            apply Fintype.sum_congr
            intro e
            by_cases hle : ∀ p : {p // p ∈ S}, (c p).val ≤ (e p).val
            · rw [if_pos hle]
              apply Fintype.prod_congr
              intro p
              rw [if_pos (hle p)]
            · rw [if_neg hle]
              rcases not_forall.mp hle with ⟨p, hp⟩
              apply Eq.symm
              apply Finset.prod_eq_zero (Finset.mem_univ p)
              rw [if_neg hp]
    _ =
      ∏ p : {p // p ∈ S},
        ∑ e : Fin 3,
          if (c p).val ≤ e.val then
            localPrimeRawNormalizedExpansionTerm p.val e
          else 0 := by
            symm
            simpa using
              (Finset.prod_univ_sum
                (t := fun _p : {p // p ∈ S} =>
                  (Finset.univ : Finset (Fin 3)))
                (f := fun p e =>
                  if (c p).val ≤ e.val then
                    localPrimeRawNormalizedExpansionTerm p.val e
                  else 0))
    _ =
      ∏ p : {p // p ∈ S},
        ((localPrimeRawSignedConductorWeight p.val (c p) : ℝ) : ℂ) := by
          apply Fintype.prod_congr
          intro p
          exact localPrimeRawTailSum_eq_signedWeight
            p.val (hprime p.val p.property) (c p)

private theorem abs_localPrimeRawSignedConductorWeight_eq
    (p : ℕ) (hp : Nat.Prime p) (c : Fin 3) :
    |localPrimeRawSignedConductorWeight p c| =
      localPrimeRawAbsoluteConductorWeight p c := by
  have hpR : (1 : ℝ) ≤ p := by
    exact_mod_cast hp.one_le
  have hden : 0 < (p : ℝ) ^ 2 := by positivity
  fin_cases c
  · change
      |((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2| =
        ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2
    exact abs_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hden))
  · change
      |(1 - 2 * (p : ℝ)) / (p : ℝ) ^ 2| =
        (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2
    have hnum : 1 - 2 * (p : ℝ) ≤ 0 := by nlinarith
    rw [abs_div, abs_of_nonpos hnum, abs_of_pos hden]
    ring
  · change
      |1 / (p : ℝ) ^ 2| = 1 / (p : ℝ) ^ 2
    exact abs_of_nonneg (div_nonneg zero_le_one (le_of_lt hden))

/-- Norm of the normalized arithmetic coefficient as an explicit local product. -/
theorem norm_primeWheelRawConductorArithmeticCoefficient_normalized_eq
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (c : PrimeWheelRawExpansionPoint S) :
    ‖primeWheelRawConductorArithmeticCoefficient
        S (primeWheelRawNaturalModulus S)
        (primeWheelRawExpansionDivisor S c) *
        (((primeWheelRawNaturalModulus S : ℕ) : ℂ)⁻¹)‖ =
      primeWheelRawConductorPatternAbsoluteWeight S c := by
  rw [primeWheelRawConductorArithmeticCoefficient_normalized_eq_neg_prod
    S hprime c]
  unfold primeWheelRawConductorPatternAbsoluteWeight
  rw [norm_neg, norm_prod]
  apply Fintype.prod_congr
  intro p
  rw [Complex.norm_real]
  exact abs_localPrimeRawSignedConductorWeight_eq
    p.val (hprime p.val p.property) (c p)

private theorem localPrimeRawAbsoluteConductorWeight_nonneg
    (p : ℕ) (hp : Nat.Prime p) (c : Fin 3) :
    0 ≤ localPrimeRawAbsoluteConductorWeight p c := by
  have hpR : (2 : ℝ) ≤ p := by
    exact_mod_cast hp.two_le
  fin_cases c
  · change 0 ≤ ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2
    positivity
  · change 0 ≤ (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2
    have hnum : 0 ≤ 2 * (p : ℝ) - 1 := by nlinarith
    positivity
  · change 0 ≤ 1 / (p : ℝ) ^ 2
    positivity

private theorem localPrimeRawAbsoluteConductorWeight_le_decayEnvelope
    (p : ℕ) (hp : Nat.Prime p) (c : Fin 3) :
    localPrimeRawAbsoluteConductorWeight p c ≤
      localPrimeRawConductorDecayEnvelope p c := by
  have hpR : (1 : ℝ) ≤ p := by
    exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast hp.pos
  have hden : 0 < (p : ℝ) ^ 2 := by positivity
  fin_cases c
  · change ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2 ≤ 1
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  · change
      (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2 ≤ 2 / (p : ℝ)
    apply (div_le_iff₀ hden).2
    have hrewrite :
        (2 / (p : ℝ)) * (p : ℝ) ^ 2 = 2 * (p : ℝ) := by
      field_simp [ne_of_gt hp0]
    rw [hrewrite]
    nlinarith
  · change 1 / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) ^ 2
    exact le_rfl

/-- Pointwise conductor decay.  A first-power conductor coordinate costs at
most `2/p`, while a square coordinate costs exactly `1/p^2`. -/
theorem primeWheelRawConductorPatternAbsoluteWeight_le_decayEnvelope
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (c : PrimeWheelRawExpansionPoint S) :
    primeWheelRawConductorPatternAbsoluteWeight S c ≤
      primeWheelRawConductorPatternDecayEnvelope S c := by
  unfold primeWheelRawConductorPatternAbsoluteWeight
    primeWheelRawConductorPatternDecayEnvelope
  apply Finset.prod_le_prod
  · intro p hp
    exact localPrimeRawAbsoluteConductorWeight_nonneg
      p.val (hprime p.val p.property) (c p)
  · intro p hp
    exact localPrimeRawAbsoluteConductorWeight_le_decayEnvelope
      p.val (hprime p.val p.property) (c p)

private theorem sum_localPrimeRawAbsoluteConductorWeight
    (p : ℕ) (hp : Nat.Prime p) :
    (∑ c : Fin 3, localPrimeRawAbsoluteConductorWeight p c) =
      1 + 1 / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  simp [localPrimeRawAbsoluteConductorWeight, Fin.sum_univ_succ]
  field_simp [hp0]
  ring

/-- Exact total `l1` mass over all conductor exponent patterns. -/
theorem sum_primeWheelRawConductorPatternAbsoluteWeight_eq_prod
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (∑ c : PrimeWheelRawExpansionPoint S,
      primeWheelRawConductorPatternAbsoluteWeight S c) =
      ∏ p : {p // p ∈ S},
        (1 + 1 / (p.val : ℝ) ^ 2) := by
  unfold primeWheelRawConductorPatternAbsoluteWeight
  symm
  calc
    (∏ p : {p // p ∈ S},
        (1 + 1 / (p.val : ℝ) ^ 2)) =
      ∏ p : {p // p ∈ S},
        ∑ c : Fin 3,
          localPrimeRawAbsoluteConductorWeight p.val c := by
            apply Fintype.prod_congr
            intro p
            exact (sum_localPrimeRawAbsoluteConductorWeight
              p.val (hprime p.val p.property)).symm
    _ =
      ∑ c : PrimeWheelRawExpansionPoint S,
        ∏ p : {p // p ∈ S},
          localPrimeRawAbsoluteConductorWeight p.val (c p) := by
            simpa using
              (Finset.prod_univ_sum
                (t := fun _p : {p // p ∈ S} =>
                  (Finset.univ : Finset (Fin 3)))
                (f := fun p c =>
                  localPrimeRawAbsoluteConductorWeight p.val c))

private theorem sum_localPrimeRawMarkedWeight
    (p : ℕ) (hp : Nat.Prime p)
    (marked : Prop) [Decidable marked] (t : ℝ) :
    (∑ c : Fin 3,
      localPrimeRawAbsoluteConductorWeight p c *
        (if marked ∧ c.val ≠ 0 then t else 1)) =
      if marked then
        (((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2) +
          (2 / (p : ℝ)) * t
      else
        1 + 1 / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  by_cases hm : marked
  · simp [hm, localPrimeRawAbsoluteConductorWeight, Fin.sum_univ_succ]
    field_simp [hp0]
    ring
  · rw [if_neg hm]
    simp only [hm, false_and, if_false, mul_one]
    exact sum_localPrimeRawAbsoluteConductorWeight p hp

/-- Exact marked generating identity.  A marked prime contributes
`((p-1)/p)^2 + (2/p)t`; an unmarked prime contributes `1 + 1/p^2`. -/
theorem primeWheelRawConductorPatternGeneratingMass_eq_prod
    (S T : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (t : ℝ) :
    primeWheelRawConductorPatternGeneratingMass S T t =
      ∏ p : {p // p ∈ S},
        if p.val ∈ T then
          (((p.val : ℝ) - 1) ^ 2 / (p.val : ℝ) ^ 2) +
            (2 / (p.val : ℝ)) * t
        else
          1 + 1 / (p.val : ℝ) ^ 2 := by
  classical
  unfold primeWheelRawConductorPatternGeneratingMass
    primeWheelRawConductorPatternAbsoluteWeight
    primeWheelRawConductorPatternMarker
  calc
    (∑ c : PrimeWheelRawExpansionPoint S,
      (∏ p : {p // p ∈ S},
        localPrimeRawAbsoluteConductorWeight p.val (c p)) *
      (∏ p : {p // p ∈ S},
        if p.val ∈ T ∧ (c p).val ≠ 0 then t else 1)) =
      ∑ c : PrimeWheelRawExpansionPoint S,
        ∏ p : {p // p ∈ S},
          (localPrimeRawAbsoluteConductorWeight p.val (c p) *
            (if p.val ∈ T ∧ (c p).val ≠ 0 then t else 1)) := by
              apply Fintype.sum_congr
              intro c
              rw [Finset.prod_mul_distrib]
    _ =
      ∏ p : {p // p ∈ S},
        ∑ c : Fin 3,
          (localPrimeRawAbsoluteConductorWeight p.val c *
            (if p.val ∈ T ∧ c.val ≠ 0 then t else 1)) := by
              symm
              simpa using
                (Finset.prod_univ_sum
                  (t := fun _p : {p // p ∈ S} =>
                    (Finset.univ : Finset (Fin 3)))
                  (f := fun p c =>
                    localPrimeRawAbsoluteConductorWeight p.val c *
                      (if p.val ∈ T ∧ c.val ≠ 0 then t else 1)))
    _ =
      ∏ p : {p // p ∈ S},
        if p.val ∈ T then
          (((p.val : ℝ) - 1) ^ 2 / (p.val : ℝ) ^ 2) +
            (2 / (p.val : ℝ)) * t
        else
          1 + 1 / (p.val : ℝ) ^ 2 := by
            apply Fintype.prod_congr
            intro p
            exact sum_localPrimeRawMarkedWeight
              p.val (hprime p.val p.property) (p.val ∈ T) t

/-- Wheel primes not dividing the pinned lower primorial endpoint. -/
def primorialUntouchedWheelPrimes (k : ℕ) : Finset ℕ :=
  (primorialWheelPrimes k).filter fun p => ¬ p ∣ primorialBlockLower k

/-- Marked generating identity specialized to the wheel primes untouched by the
pinned primorial lower endpoint. -/
theorem primorialUntouchedRawConductorPatternGeneratingMass_eq_prod
    (k : ℕ) (t : ℝ) :
    primeWheelRawConductorPatternGeneratingMass
        (primorialWheelPrimes k) (primorialUntouchedWheelPrimes k) t =
      ∏ p : {p // p ∈ primorialWheelPrimes k},
        if p.val ∈ primorialUntouchedWheelPrimes k then
          (((p.val : ℝ) - 1) ^ 2 / (p.val : ℝ) ^ 2) +
            (2 / (p.val : ℝ)) * t
        else
          1 + 1 / (p.val : ℝ) ^ 2 := by
  exact primeWheelRawConductorPatternGeneratingMass_eq_prod
    (primorialWheelPrimes k) (primorialUntouchedWheelPrimes k)
    (fun p hp => prime_of_mem_primesUpTo hp) t

/-- The generic natural raw modulus agrees with the existing primorial
square-sensitive modulus. -/
theorem primeWheelRawNaturalModulus_primorial (k : ℕ) :
    primeWheelRawNaturalModulus (primorialWheelPrimes k) =
      primorialSquareSensitiveModulus k := by
  unfold primeWheelRawNaturalModulus primorialSquareSensitiveModulus
  exact Finset.prod_coe_sort (primorialWheelPrimes k) (fun p : ℕ => p ^ 2)

/-- From block `k >= 2`, the actual normalized primorial arithmetic coefficient
is exactly the signed local conductor product. -/
theorem primorialRawConductorArithmeticCoefficient_normalized_eq_neg_prod
    (k : ℕ) (hk : 2 ≤ k)
    (c : PrimeWheelRawExpansionPoint (primorialWheelPrimes k)) :
    primorialRawConductorArithmeticCoefficient k
        (primeWheelRawExpansionDivisor (primorialWheelPrimes k) c) *
        ((((primorialMinimalWheelSystem k).modulus : ℕ) : ℂ)⁻¹) =
      -∏ p : {p // p ∈ primorialWheelPrimes k},
        ((localPrimeRawSignedConductorWeight p.val (c p) : ℝ) : ℂ) := by
  unfold primorialRawConductorArithmeticCoefficient
  change
    primeWheelRawConductorArithmeticCoefficient
        (primorialWheelPrimes k) (primorialMinimalTorusModulus k)
        (primeWheelRawExpansionDivisor (primorialWheelPrimes k) c) *
        (((primorialMinimalTorusModulus k : ℕ) : ℂ)⁻¹) = _
  rw [primorialMinimalTorusModulus_eq_squareSensitiveModulus hk]
  rw [← primeWheelRawNaturalModulus_primorial k]
  exact primeWheelRawConductorArithmeticCoefficient_normalized_eq_neg_prod
    (primorialWheelPrimes k)
    (fun p hp => prime_of_mem_primesUpTo hp) c

end RHLean.Analysis