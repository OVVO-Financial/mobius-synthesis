import Mathlib
import RHLean.Arithmetic.MobiusFiniteDifferenceIdentification
import RHLean.Arithmetic.MobiusFourCellEndpointTransfer
import RHLean.Analysis.PrimeSieveAbelIdentity
import RHLean.Analysis.PrimeSieveBackwardAffineExcursion

/-!
# Fiberwise affine moduli for the finite Möbius difference operator

Bookkeeping only.  Every estimate in this module is termwise absolute by
design: it tracks how an affine increment modulus for `f` transports through
the divisor fibers of `finiteDifferenceOperator S f`, charging the intercept
only on fibers that actually move.  No cancellation estimate is asserted and
nothing here advances any quantitative frontier.

Contents:

* the active-fiber increment bound (intercept charged only on moving fibers);
* the worst-case Euler relaxation `A·h·Π(1+1/p) + (A+B)·2^{|S|}` — the
  exponential intercept is real and is stated, not hidden;
* the fresh-prime modulus recurrence: one fresh prime multiplies the slope
  by `1 + 1/p` and doubles the intercept, visibly;
* the exact rough/smooth bridge between the Abel-face discrepancy sum and
  the `K`-truncated finite-difference operator;
* the vanishing of the classical prime discrepancy at `0` and `1`
  (the logarithmic integral from `2` is `0` at both endpoints because the
  integrand `1/log u` is non-integrable across `u = 1`).
-/

open scoped ArithmeticFunction.Moebius BigOperators

open Set MeasureTheory

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-! ## The prime discrepancy vanishes at `0` and `1` -/

/-- `1/log u` is not interval-integrable across the singularity at `u = 1`:
on `(1, 2]` it dominates the non-integrable `1/(u-1)`. -/
theorem not_intervalIntegrable_inv_log_one_two :
    ¬ IntervalIntegrable (fun u : ℝ => (Real.log u)⁻¹)
      MeasureTheory.volume 1 2 := by
  intro hg
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (1 : ℝ) ≤ 2)] at hg
  have hfmeas : AEStronglyMeasurable (fun u : ℝ => (u - 1)⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioc 1 2)) :=
    ((measurable_id.sub measurable_const).inv).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂MeasureTheory.volume.restrict (Set.Ioc 1 2),
      ‖(u - 1)⁻¹‖ ≤ ‖(Real.log u)⁻¹‖ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have hsub : 0 < u - 1 := sub_pos.mpr hu.1
    have hlog : 0 < Real.log u := Real.log_pos hu.1
    have hle : Real.log u ≤ u - 1 :=
      Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hu.1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsub),
      abs_of_pos (inv_pos.mpr hlog)]
    exact inv_anti₀ hlog hle
  have hfint : MeasureTheory.IntegrableOn (fun u : ℝ => (u - 1)⁻¹)
      (Set.Ioc 1 2) := MeasureTheory.Integrable.mono hg hfmeas hbound
  have hfinterval : IntervalIntegrable (fun u : ℝ => (u - 1)⁻¹)
      MeasureTheory.volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (1 : ℝ) ≤ 2)).2 hfint
  rcases intervalIntegrable_sub_inv_iff.mp hfinterval with hc | hc
  · norm_num at hc
  · exact hc Set.left_mem_uIcc

/-- The repository's logarithmic integral from `2` vanishes at `0`. -/
theorem logarithmicIntegralFromTwo_zero :
    logarithmicIntegralFromTwo 0 = 0 := by
  unfold logarithmicIntegralFromTwo
  refine intervalIntegral.integral_undef fun hI =>
    not_intervalIntegrable_inv_log_one_two (hI.mono ?_ le_rfl)
  rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
    Set.uIcc_of_ge (by norm_num : (0 : ℝ) ≤ 2)]
  exact Set.Icc_subset_Icc (by norm_num) le_rfl

/-- The repository's logarithmic integral from `2` vanishes at `1`. -/
theorem logarithmicIntegralFromTwo_one :
    logarithmicIntegralFromTwo 1 = 0 := by
  unfold logarithmicIntegralFromTwo
  exact intervalIntegral.integral_undef fun hI =>
    not_intervalIntegrable_inv_log_one_two hI.symm

@[simp] theorem primeSievePrimeDiscrepancy_zero :
    primeSievePrimeDiscrepancy 0 = 0 := by
  unfold primeSievePrimeDiscrepancy primeSievePrefixPrimeCount
  rw [show (((0 : ℕ) : ℝ)) = 0 from by norm_num,
    logarithmicIntegralFromTwo_zero]
  simp

@[simp] theorem primeSievePrimeDiscrepancy_one :
    primeSievePrimeDiscrepancy 1 = 0 := by
  unfold primeSievePrimeDiscrepancy primeSievePrefixPrimeCount
  rw [show (((1 : ℕ) : ℝ)) = 1 from by norm_num,
    logarithmicIntegralFromTwo_one]
  have hIoc : Finset.Ioc 0 1 = {1} := by decide
  rw [hIoc]
  simp [primeSievePrimeIndicator]

/-! ## Möbius norm and shift commutation -/

/-- The complex Möbius weight has norm at most one. -/
theorem norm_moebius_le_one (d : ℕ) : ‖((μ d : ℤ) : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [norm_pow]
    simp
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    simp

/-- The canonical operator commutes with floor shifts. -/
theorem finiteDifferenceOperator_shift_comm
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (p : ℕ) (f : ℕ → R) :
    finiteDifferenceOperator S (shift p f) =
      shift p (finiteDifferenceOperator S f) := by
  funext x
  simp only [finiteDifferenceOperator_apply, shift]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-! ## Active-fiber increment bound -/

/-- **Bookkeeping only.**  Termwise absolute control of the operator
increment: the slope is charged per unit of divisor-fiber motion and the
intercept only on fibers that actually move. -/
theorem finiteDifferenceOperator_increment_norm_le_activeOn
    (S : Finset ℕ) (f : ℕ → ℂ)
    (A B : ℝ) (L U x h : ℕ)
    (hwindow : ∀ d ∈ (primorial S).divisors,
      L ≤ x / d ∧ (x + h) / d ≤ U)
    (hmod : ∀ a k : ℕ, L ≤ a → a + k ≤ U → 0 < k →
      ‖f (a + k) - f a‖ ≤ A * (k : ℝ) + B) :
    ‖finiteDifferenceOperator S f (x + h) -
        finiteDifferenceOperator S f x‖
      ≤ A * (∑ d ∈ (primorial S).divisors,
          ((((x + h) / d - x / d : ℕ) : ℝ)))
        + B * (((primorial S).divisors.filter
            (fun d => x / d < (x + h) / d)).card : ℝ) := by
  classical
  rw [finiteDifferenceOperator_apply, finiteDifferenceOperator_apply,
    ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ d ∈ (primorial S).divisors,
      ‖(((μ d : ℤ) : ℂ)) * f ((x + h) / d) -
          (((μ d : ℤ) : ℂ)) * f (x / d)‖ ≤
        A * ((((x + h) / d - x / d : ℕ) : ℝ)) +
          B * (if x / d < (x + h) / d then (1 : ℝ) else 0) := by
    intro d hd
    rw [← mul_sub, norm_mul]
    by_cases hmove : x / d < (x + h) / d
    · have hδpos : 0 < (x + h) / d - x / d := by omega
      have hsum : x / d + ((x + h) / d - x / d) = (x + h) / d := by omega
      have hb := hmod (x / d) ((x + h) / d - x / d) (hwindow d hd).1
        (by rw [hsum]; exact (hwindow d hd).2) hδpos
      rw [hsum] at hb
      rw [if_pos hmove]
      calc ‖((μ d : ℤ) : ℂ)‖ * ‖f ((x + h) / d) - f (x / d)‖
          ≤ 1 * (A * ((((x + h) / d - x / d : ℕ) : ℝ)) + B) :=
            mul_le_mul (norm_moebius_le_one d) hb (norm_nonneg _)
              zero_le_one
        _ = A * ((((x + h) / d - x / d : ℕ) : ℝ)) + B * 1 := by ring
    · have hle : x / d ≤ (x + h) / d :=
        Nat.div_le_div_right (by omega)
      have heq : (x + h) / d = x / d := by omega
      have hδ0 : ((x + h) / d - x / d : ℕ) = 0 := by omega
      rw [if_neg hmove, hδ0, heq, sub_self, norm_zero, mul_zero]
      simp
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole]

/-- **Worst-case Euler relaxation; not a cancellation estimate.**  The
exponential intercept `2^{|S|}` is real and stated. -/
theorem finiteDifferenceOperator_increment_norm_le_euler
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (f : ℕ → ℂ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (x h : ℕ)
    (hmod : ∀ a k : ℕ, 0 < k →
      ‖f (a + k) - f a‖ ≤ A * (k : ℝ) + B) :
    ‖finiteDifferenceOperator S f (x + h) -
        finiteDifferenceOperator S f x‖
      ≤ A * (h : ℝ) * (∏ p ∈ S, (1 + ((p : ℝ))⁻¹))
        + (A + B) * (((2 ^ S.card : ℕ) : ℝ)) := by
  classical
  have hact := finiteDifferenceOperator_increment_norm_le_activeOn
    S f A B 0 (x + h) x h
    (fun d _ => ⟨Nat.zero_le _, Nat.div_le_self _ _⟩)
    (fun a k _ _ hk => hmod a k hk)
  refine le_trans hact ?_
  have hcard := card_divisors_primorial S hprime
  have hsum := sum_inv_divisors_primorial S hprime
  have hδ : (∑ d ∈ (primorial S).divisors,
      ((((x + h) / d - x / d : ℕ) : ℝ)))
      ≤ (h : ℝ) * (∑ d ∈ (primorial S).divisors, ((d : ℝ))⁻¹)
        + ((primorial S).divisors.card : ℝ) := by
    have hterm : ∀ d ∈ (primorial S).divisors,
        ((((x + h) / d - x / d : ℕ)) : ℝ) ≤
          (h : ℝ) * ((d : ℝ))⁻¹ + 1 := by
      intro d hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have h1 : (x + h) / d - x / d ≤ h / d + 1 :=
        floor_add_div_sub_le x h d hd0
      calc ((((x + h) / d - x / d : ℕ)) : ℝ)
          ≤ (((h / d + 1 : ℕ)) : ℝ) := by exact_mod_cast h1
        _ = ((h / d : ℕ) : ℝ) + 1 := by push_cast; ring
        _ ≤ (h : ℝ) * ((d : ℝ))⁻¹ + 1 := by
            have hc : ((h / d : ℕ) : ℝ) ≤ (h : ℝ) / (d : ℝ) :=
              Nat.cast_div_le
            rw [div_eq_mul_inv] at hc
            linarith
    calc (∑ d ∈ (primorial S).divisors,
        ((((x + h) / d - x / d : ℕ) : ℝ)))
        ≤ ∑ d ∈ (primorial S).divisors,
            ((h : ℝ) * ((d : ℝ))⁻¹ + 1) := Finset.sum_le_sum hterm
      _ = (h : ℝ) * (∑ d ∈ (primorial S).divisors, ((d : ℝ))⁻¹)
          + ((primorial S).divisors.card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul, mul_one]
  have hmovecard : (((primorial S).divisors.filter
      (fun d => x / d < (x + h) / d)).card : ℝ)
      ≤ ((primorial S).divisors.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le _ _
  have hWpos : (0 : ℝ) ≤ ∑ d ∈ (primorial S).divisors, ((d : ℝ))⁻¹ :=
    Finset.sum_nonneg fun d _ => by positivity
  calc A * (∑ d ∈ (primorial S).divisors,
        ((((x + h) / d - x / d : ℕ) : ℝ)))
        + B * (((primorial S).divisors.filter
            (fun d => x / d < (x + h) / d)).card : ℝ)
      ≤ A * ((h : ℝ) * (∑ d ∈ (primorial S).divisors, ((d : ℝ))⁻¹)
            + ((primorial S).divisors.card : ℝ))
        + B * ((primorial S).divisors.card : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hδ hA)
          (mul_le_mul_of_nonneg_left hmovecard hB)
    _ = A * (h : ℝ) * (∑ d ∈ (primorial S).divisors, ((d : ℝ))⁻¹)
        + (A + B) * ((primorial S).divisors.card : ℝ) := by ring
    _ = A * (h : ℝ) * (∏ p ∈ S, (1 + ((p : ℝ))⁻¹))
        + (A + B) * (((2 ^ S.card : ℕ) : ℝ)) := by
        rw [hsum, hcard]

/-! ## Fresh-prime modulus recurrence -/

/-- Sharp step count for a positive step through a divisor fiber. -/
theorem floor_add_div_sub_le_ceil (x h p : ℕ) (hp : 0 < p) (hh : 0 < h) :
    (x + h) / p - x / p ≤ (h - 1) / p + 1 := by
  have hx : x < (x / p + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  have hh1 : h - 1 < ((h - 1) / p + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  set X1 := (x / p + 1) * p with hX1
  set X2 := ((h - 1) / p + 1) * p with hX2
  have key : x + h < X1 + X2 := by omega
  have hdiv : (x + h) / p < x / p + (h - 1) / p + 2 := by
    rw [Nat.div_lt_iff_lt_mul hp]
    calc x + h < X1 + X2 := key
      _ = (x / p + (h - 1) / p + 2) * p := by rw [hX1, hX2]; ring
  generalize hu : (x + h) / p = u at hdiv ⊢
  generalize hv : x / p = v at hdiv ⊢
  generalize hw : (h - 1) / p = w at hdiv ⊢
  omega

/-- **Fresh-prime modulus bookkeeping; the intercept doubles visibly.**  One
fresh prime multiplies the affine slope by `1 + 1/p` and doubles the
intercept.  Iterating from a single fiber reproduces the Euler worst case;
the recurrence makes the exponential growth explicit rather than sharper. -/
theorem finiteDifferenceOperator_insert_affine_modulus
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q)
    (f : ℕ → ℂ) (α C : ℝ)
    (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hmod : ∀ x h : ℕ, 0 < h →
      ‖finiteDifferenceOperator S f (x + h) -
          finiteDifferenceOperator S f x‖
        ≤ α * (((h - 1 : ℕ) : ℝ)) + C) :
    ∀ x h : ℕ, 0 < h →
      ‖finiteDifferenceOperator (insert p S) f (x + h) -
          finiteDifferenceOperator (insert p S) f x‖
        ≤ (α * (1 + ((p : ℝ))⁻¹)) * (((h - 1 : ℕ) : ℝ)) + 2 * C := by
  intro x h hh
  rw [finiteDifferenceOperator_insert S p hp hpS hprime f,
    finiteDifferenceOperator_shift_comm]
  simp only [Pi.sub_apply]
  have hrearr :
      finiteDifferenceOperator S f (x + h) -
          shift p (finiteDifferenceOperator S f) (x + h) -
        (finiteDifferenceOperator S f x -
          shift p (finiteDifferenceOperator S f) x) =
      (finiteDifferenceOperator S f (x + h) -
          finiteDifferenceOperator S f x) -
        (shift p (finiteDifferenceOperator S f) (x + h) -
          shift p (finiteDifferenceOperator S f) x) := by ring
  rw [hrearr]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := hmod x h hh
  have hp0 : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := by positivity
  have hh0 : (0 : ℝ) ≤ (((h - 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hxle : x / p ≤ (x + h) / p := Nat.div_le_div_right (by omega)
  simp only [shift]
  by_cases hmove : x / p < (x + h) / p
  · have hk : 0 < (x + h) / p - x / p := by omega
    have hsump : x / p + ((x + h) / p - x / p) = (x + h) / p := by omega
    have h2 := hmod (x / p) ((x + h) / p - x / p) hk
    rw [hsump] at h2
    have hkle : ((x + h) / p - x / p) - 1 ≤ (h - 1) / p := by
      have := floor_add_div_sub_le_ceil x h p hp.pos hh
      omega
    have hcast : ((((x + h) / p - x / p - 1 : ℕ)) : ℝ)
        ≤ (((h - 1 : ℕ)) : ℝ) * ((p : ℝ))⁻¹ := by
      calc ((((x + h) / p - x / p - 1 : ℕ)) : ℝ)
          ≤ ((((h - 1) / p : ℕ)) : ℝ) := by exact_mod_cast hkle
        _ ≤ (((h - 1 : ℕ)) : ℝ) / ((p : ℝ)) := Nat.cast_div_le
        _ = (((h - 1 : ℕ)) : ℝ) * ((p : ℝ))⁻¹ := div_eq_mul_inv _ _
    have h2' : ‖finiteDifferenceOperator S f ((x + h) / p) -
        finiteDifferenceOperator S f (x / p)‖
        ≤ α * ((((h - 1 : ℕ)) : ℝ) * ((p : ℝ))⁻¹) + C := by
      refine le_trans h2 ?_
      have := mul_le_mul_of_nonneg_left hcast hα
      linarith
    have := add_le_add h1 h2'
    refine le_trans this (le_of_eq ?_)
    ring
  · have heq : (x + h) / p = x / p := by omega
    rw [heq, sub_self, norm_zero, add_zero]
    refine le_trans h1 ?_
    have hnn : (0 : ℝ) ≤ α * ((p : ℝ))⁻¹ * (((h - 1 : ℕ) : ℝ)) := by
      positivity
    nlinarith

/-! ## The honest Abel-face bridge -/

/-- **The exact rough/smooth bridge.**  The Abel-face discrepancy sum is the
`K`-truncated finite-difference operator at the ambient prime set through `y`
plus the remainder supported (up to Möbius-zero terms) on the non-`y`-smooth
squarefree part of the quotient support.  Neither side is discarded. -/
theorem primeSieveMoebiusDiscrepancySum_eq_upTo_add_roughRemainder
    (y x : ℕ) :
    primeSieveMoebiusDiscrepancySum y x =
      finiteDifferenceOperatorUpTo (primesUpTo y) (x / (y + 1))
        primeSievePrimeDiscrepancy x +
      ∑ d ∈ (primeSieveQuotientSupport y x).filter
          (fun d => d ∉ (primorial (primesUpTo y)).divisors),
        (((μ d : ℤ) : ℂ)) * primeSievePrimeDiscrepancy (x / d) := by
  classical
  unfold primeSieveMoebiusDiscrepancySum
  rw [← Finset.sum_filter_add_sum_filter_not (primeSieveQuotientSupport y x)
    (fun d => d ∈ (primorial (primesUpTo y)).divisors)
    (fun d => (((μ d : ℤ) : ℂ)) * primeSievePrimeDiscrepancy (x / d))]
  congr 1
  simp only [finiteDifferenceOperatorUpTo]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [Finset.mem_filter, primeSieveQuotientSupport, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hK⟩, hdiv⟩
    exact ⟨hdiv, hK⟩
  · rintro ⟨hdiv, hK⟩
    have h1 : 0 < d := Nat.pos_of_mem_divisors hdiv
    exact ⟨⟨h1, hK⟩, hdiv⟩

end RHLean.Analysis

end
