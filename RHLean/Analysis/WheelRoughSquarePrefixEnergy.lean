import Mathlib
import RHLean.Analysis.PRoughSquarePrefixEnergy
import RHLean.Arithmetic.PrimorialTruncatedWheelBoundary

/-!
# Finite-wheel rough square-prefix energy transfer

This module iterates the one-prime roughing mechanism across an arbitrary fixed
finite set of genuine primes.  The analytic input is only the repository's
native square-prefix Mertens energy statement.  Every transport step uses the
exact finite recurrence

`T_(pW)(x) = T_W(x) + T_(pW)(floor (x / p))`

and the uniform scale contraction

`floor (x / p) + 1 <= (2 / 3) * (x + 1)`

for `p >= 2`.

The loss at exponent `r > 0` is explicit: each newly adjoined prime costs the
same factor

`(1 - (2 / 3)^r)^(-1)`.

Thus a finite wheel `P` costs the corresponding finite power indexed by
`P.card`.  No PNT, prime-distribution estimate, infinite Euler product,
Tauberian theorem, or zero-free region is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Complex-valued rough Mertens summatory function for an arbitrary wheel. -/
def wheelRoughMertensSummatory (W x : ℕ) : ℂ :=
  ((roughMertens W x : ℤ) : ℂ)

/-- Finite-wheel rough Mertens sum at the native complete-square endpoint. -/
def wheelRoughSquarePrefixMertens (P : Finset ℕ) (n : ℕ) : ℂ :=
  wheelRoughMertensSummatory (primorialWheelProduct P) (squarePrefixEndpoint n)

/-- Critical square-prefix energy statement for a fixed finite prime wheel. -/
def WheelRoughSquarePrefixEnergyBoundedStatement (P : Finset ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        ‖wheelRoughSquarePrefixMertens P n‖ ^ 2 ≤
          C * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε)

/-- Uniform loss of one fresh-prime transport step at power exponent `r`. -/
def wheelRoughPrimeLoss (r : ℝ) : ℝ :=
  (1 - Real.rpow ((2 : ℝ) / 3) r)⁻¹

/-- Explicit accumulated loss for a finite wheel. -/
def wheelRoughFiniteLoss (P : Finset ℕ) (r : ℝ) : ℝ :=
  (wheelRoughPrimeLoss r) ^ P.card

@[simp] theorem wheelRoughMertensSummatory_zero (W : ℕ) :
    wheelRoughMertensSummatory W 0 = 0 := by
  simp [wheelRoughMertensSummatory, roughMertens, roughMoebius]

private theorem wheelRoughMertensSummatory_one_eq_mertensSummatory (x : ℕ) :
    wheelRoughMertensSummatory 1 x = mertensSummatory x := by
  unfold wheelRoughMertensSummatory roughMertens roughMoebius mertensSummatory
  simp

/-- Exact fresh-prime extension recurrence in the complex-valued normalization. -/
theorem wheelRoughMertensSummatory_prime_extension
    {W p : ℕ} (hp : p.Prime) (hWp : Squarefree (p * W)) (x : ℕ) :
    wheelRoughMertensSummatory (p * W) x =
      wheelRoughMertensSummatory W x +
        wheelRoughMertensSummatory (p * W) (x / p) := by
  have h := roughMertens_prime_extension (W := W) hp hWp x
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  simpa [wheelRoughMertensSummatory] using hc

private theorem wheelRough_div_scale
    (p x : ℕ) (hp : p.Prime) (hx : p ≤ x)
    {r : ℝ} (hr : 0 < r) :
    Real.rpow (((x / p + 1 : ℕ) : ℝ)) r ≤
      Real.rpow ((2 : ℝ) / 3) r *
        Real.rpow (((x + 1 : ℕ) : ℝ)) r := by
  have hp2 : 2 ≤ p := hp.two_le
  have hmuldiv : p * (x / p) ≤ x := Nat.mul_div_le x p
  have htwo : 2 * (x / p) ≤ p * (x / p) :=
    Nat.mul_le_mul_right (x / p) hp2
  have hquot : 2 * (x / p) ≤ x := htwo.trans hmuldiv
  have hnat : 3 * (x / p + 1) ≤ 2 * (x + 1) := by omega
  have hnatR :
      (3 : ℝ) * (((x / p + 1 : ℕ) : ℝ)) ≤
        2 * (((x + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hbase :
      (((x / p + 1 : ℕ) : ℝ)) ≤
        ((2 : ℝ) / 3) * (((x + 1 : ℕ) : ℝ)) := by
    linarith
  have hpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ (((x / p + 1 : ℕ) : ℝ))) hbase hr.le
  calc
    Real.rpow (((x / p + 1 : ℕ) : ℝ)) r ≤
        Real.rpow (((2 : ℝ) / 3) * (((x + 1 : ℕ) : ℝ))) r := hpow
    _ = Real.rpow ((2 : ℝ) / 3) r *
        Real.rpow (((x + 1 : ℕ) : ℝ)) r :=
      Real.mul_rpow (by norm_num) (by positivity)

private theorem wheelRoughPrimeLoss_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ wheelRoughPrimeLoss r := by
  have hq1 : Real.rpow ((2 : ℝ) / 3) r < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hr
  unfold wheelRoughPrimeLoss
  exact inv_nonneg.mpr (sub_nonneg.mpr hq1.le)

private theorem wheelRoughFiniteLoss_nonneg
    (P : Finset ℕ) {r : ℝ} (hr : 0 < r) :
    0 ≤ wheelRoughFiniteLoss P r := by
  unfold wheelRoughFiniteLoss
  exact pow_nonneg (wheelRoughPrimeLoss_nonneg hr) P.card

/-- One fresh prime preserves a rough power bound, with the explicit geometric
loss `(1 - (2/3)^r)^(-1)`.  This is the reusable induction step missing from the
specialized `W = 1` theorem. -/
theorem wheelRoughPowerGrowth_prime_extension
    {W p : ℕ} (hp : p.Prime) (hWp : Squarefree (p * W))
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hbound : ∀ x : ℕ,
      ‖wheelRoughMertensSummatory W x‖ ≤
        K * Real.rpow ((x + 1 : ℕ) : ℝ) r) :
    ∀ x : ℕ,
      ‖wheelRoughMertensSummatory (p * W) x‖ ≤
        (K * wheelRoughPrimeLoss r) *
          Real.rpow ((x + 1 : ℕ) : ℝ) r := by
  let q : ℝ := Real.rpow ((2 : ℝ) / 3) r
  let D : ℝ := K / (1 - q)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (by norm_num) r
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hr
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hD0 : 0 ≤ D := div_nonneg hK hden.le
  have hDrel : K + q * D = D := by
    dsimp [D]
    field_simp
    ring
  have hKleD : K ≤ D := by
    have hqD : 0 ≤ q * D := mul_nonneg hq0 hD0
    linarith [hDrel]
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hsmall : x < p
      · have hdiv : x / p = 0 := Nat.div_eq_of_lt hsmall
        have hrec := wheelRoughMertensSummatory_prime_extension hp hWp x
        rw [hdiv, wheelRoughMertensSummatory_zero, add_zero] at hrec
        rw [hrec]
        exact (hbound x).trans
          (mul_le_mul_of_nonneg_right hKleD
            (Real.rpow_nonneg (by positivity) r))
      · have hpx : p ≤ x := Nat.le_of_not_gt hsmall
        have hxpos : 0 < x := lt_of_lt_of_le hp.pos hpx
        have hdivlt : x / p < x := Nat.div_lt_self hxpos hp.one_lt
        have hrec := wheelRoughMertensSummatory_prime_extension hp hWp x
        rw [hrec]
        have hscale := wheelRough_div_scale p x hp hpx hr
        have hchild := ih (x / p) hdivlt
        calc
          ‖wheelRoughMertensSummatory W x +
              wheelRoughMertensSummatory (p * W) (x / p)‖ ≤
              ‖wheelRoughMertensSummatory W x‖ +
                ‖wheelRoughMertensSummatory (p * W) (x / p)‖ :=
            norm_add_le _ _
          _ ≤ K * Real.rpow ((x + 1 : ℕ) : ℝ) r +
                D * Real.rpow ((x / p + 1 : ℕ) : ℝ) r :=
            add_le_add (hbound x) hchild
          _ ≤ K * Real.rpow ((x + 1 : ℕ) : ℝ) r +
                D * (q * Real.rpow ((x + 1 : ℕ) : ℝ) r) := by
            dsimp [q] at hscale ⊢
            exact add_le_add_left (mul_le_mul_of_nonneg_left hscale hD0) _
          _ = (K + q * D) * Real.rpow ((x + 1 : ℕ) : ℝ) r := by ring
          _ = D * Real.rpow ((x + 1 : ℕ) : ℝ) r := by rw [hDrel]
          _ = (K * wheelRoughPrimeLoss r) *
                Real.rpow ((x + 1 : ℕ) : ℝ) r := by
            dsimp [D, wheelRoughPrimeLoss, q]
            rw [div_eq_mul_inv]

private theorem prime_dvd_primorialWheelProduct_iff_local
    {P : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hprime : ∀ q ∈ P, q.Prime) :
    p ∣ primorialWheelProduct P ↔ p ∈ P := by
  classical
  unfold primorialWheelProduct
  constructor
  · intro h
    rcases (Prime.dvd_finset_prod_iff hp.prime id).mp h with ⟨q, hq, hpq⟩
    rcases (hprime q hq).eq_one_or_self_of_dvd p hpq with hpOne | hpEq
    · exact (hp.ne_one hpOne).elim
    · simpa [hpEq] using hq
  · intro hpP
    exact Finset.dvd_prod_of_mem id hpP

private theorem primorialWheelProduct_squarefree
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Squarefree (primorialWheelProduct P) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp [primorialWheelProduct]
  | @insert p P hpP ih =>
      have hp : p.Prime := hprime p (by simp)
      have hprimeP : ∀ q ∈ P, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hsqP : Squarefree (primorialWheelProduct P) := ih hprimeP
      have hpndvd : ¬ p ∣ primorialWheelProduct P := by
        intro hdiv
        exact hpP ((prime_dvd_primorialWheelProduct_iff_local hp hprimeP).1 hdiv)
      have hcop : Nat.Coprime p (primorialWheelProduct P) :=
        hp.coprime_iff_not_dvd.mpr hpndvd
      have hsqmul : Squarefree (p * primorialWheelProduct P) :=
        (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hsqP⟩
      simpa [primorialWheelProduct, hpP] using hsqmul

/-- Explicit finite-wheel iteration of the fresh-prime power-growth step.
If ordinary Mertens has a power bound with constant `K`, the wheel-rough sum has
the same exponent and constant multiplied by `wheelRoughFiniteLoss P r`. -/
theorem wheelRoughPowerGrowth_of_mertensPowerBound
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hM : ∀ x : ℕ,
      ‖mertensSummatory x‖ ≤
        K * Real.rpow ((x + 1 : ℕ) : ℝ) r) :
    ∀ x : ℕ,
      ‖wheelRoughMertensSummatory (primorialWheelProduct P) x‖ ≤
        (K * wheelRoughFiniteLoss P r) *
          Real.rpow ((x + 1 : ℕ) : ℝ) r := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      intro x
      simpa [primorialWheelProduct, wheelRoughFiniteLoss,
        wheelRoughMertensSummatory_one_eq_mertensSummatory] using hM x
  | @insert p P hpP ih =>
      have hp : p.Prime := hprime p (by simp)
      have hprimeP : ∀ q ∈ P, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hP := ih hprimeP
      have hsqP := primorialWheelProduct_squarefree P hprimeP
      have hpndvd : ¬ p ∣ primorialWheelProduct P := by
        intro hdiv
        exact hpP ((prime_dvd_primorialWheelProduct_iff_local hp hprimeP).1 hdiv)
      have hcop : Nat.Coprime p (primorialWheelProduct P) :=
        hp.coprime_iff_not_dvd.mpr hpndvd
      have hsq : Squarefree (p * primorialWheelProduct P) :=
        (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hsqP⟩
      have hKbase : 0 ≤ K * wheelRoughFiniteLoss P r :=
        mul_nonneg hK (wheelRoughFiniteLoss_nonneg P hr)
      have hstep := wheelRoughPowerGrowth_prime_extension hp hsq hr hKbase hP
      intro x
      have hx := hstep x
      have hcard : (insert p P).card = P.card + 1 := Finset.card_insert_of_notMem hpP
      have hloss :
          wheelRoughFiniteLoss (insert p P) r =
            wheelRoughFiniteLoss P r * wheelRoughPrimeLoss r := by
        unfold wheelRoughFiniteLoss
        rw [hcard, pow_succ]
      simpa [primorialWheelProduct, hpP, hloss, mul_assoc] using hx

/-- A finite genuine prime wheel preserves every Mertens power exponent
`r > 1/2`, with an explicit finite product loss. -/
theorem wheelRoughPowerGrowth_of_energy
    (hM : MertensEnergyBoundedStatement)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {r : ℝ} (hr : (1 : ℝ) / 2 < r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : ℕ,
        ‖wheelRoughMertensSummatory (primorialWheelProduct P) x‖ ≤
          (K * wheelRoughFiniteLoss P r) *
            Real.rpow ((x + 1 : ℕ) : ℝ) r := by
  rcases mertensPowerGrowth_of_energy hM hr with ⟨K, hK, hbound⟩
  refine ⟨K, hK, ?_⟩
  exact wheelRoughPowerGrowth_of_mertensPowerBound P hprime (by linarith) hK hbound

/-- The native square-prefix critical energy bound survives deletion of every
prime in an arbitrary fixed finite genuine-prime wheel. -/
theorem wheelRoughSquarePrefixEnergyBounded_of_squarePrefixEnergyBounded
    (hS : SquarePrefixEnergyBoundedStatement)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    WheelRoughSquarePrefixEnergyBoundedStatement P := by
  have hM : MertensEnergyBoundedStatement :=
    mertensEnergyBounded_of_squarePrefixEnergyBounded hS
  intro ε hε
  let r : ℝ := (1 : ℝ) / 2 + ε / 4
  have hr : (1 : ℝ) / 2 < r := by
    dsimp [r]
    linarith
  rcases wheelRoughPowerGrowth_of_energy hM P hprime hr with ⟨K, hK, hbound⟩
  let D : ℝ := K * wheelRoughFiniteLoss P r
  have hr0 : 0 < r := by linarith
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg hK (wheelRoughFiniteLoss_nonneg P hr0)
  refine ⟨D ^ 2, sq_nonneg D, ?_⟩
  intro n
  have hsample :
      ‖wheelRoughSquarePrefixMertens P n‖ ≤
        D * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r := by
    simpa [wheelRoughSquarePrefixMertens, D] using hbound (squarePrefixEndpoint n)
  have hsample0 : 0 ≤ ‖wheelRoughSquarePrefixMertens P n‖ := norm_nonneg _
  have hright0 :
      0 ≤ D * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r :=
    mul_nonneg hD (Real.rpow_nonneg (by positivity) r)
  have hsquare :
      ‖wheelRoughSquarePrefixMertens P n‖ ^ 2 ≤
        (D * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r) ^ 2 := by
    nlinarith
  have hendpoint :
      ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast squarePrefixEndpoint_add_one n
  have hbase : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hrpowEndpoint :
      Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r =
        Real.rpow ((n + 1 : ℕ) : ℝ) (2 * r) := by
    rw [hendpoint]
    have htwo : Real.rpow ((n + 1 : ℕ) : ℝ) (2 : ℝ) =
        (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := Real.rpow_natCast _ 2
    calc
      Real.rpow (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) r =
          Real.rpow (Real.rpow ((n + 1 : ℕ) : ℝ) (2 : ℝ)) r :=
        congrArg (fun t : ℝ => Real.rpow t r) htwo.symm
      _ = Real.rpow ((n + 1 : ℕ) : ℝ) ((2 : ℝ) * r) :=
        (Real.rpow_mul hbase.le (2 : ℝ) r).symm
  have hpowSquare :
      (Real.rpow ((n + 1 : ℕ) : ℝ) (2 * r)) ^ 2 =
        Real.rpow ((n + 1 : ℕ) : ℝ) (4 * r) := by
    rw [pow_two]
    calc
      Real.rpow ((n + 1 : ℕ) : ℝ) (2 * r) *
          Real.rpow ((n + 1 : ℕ) : ℝ) (2 * r) =
          Real.rpow ((n + 1 : ℕ) : ℝ) ((2 * r) + (2 * r)) :=
        (Real.rpow_add hbase (2 * r) (2 * r)).symm
      _ = Real.rpow ((n + 1 : ℕ) : ℝ) (4 * r) := by
        congr 1
        ring
  have hrexp : 4 * r = 2 + ε := by
    dsimp [r]
    ring
  calc
    ‖wheelRoughSquarePrefixMertens P n‖ ^ 2 ≤
        (D * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r) ^ 2 := hsquare
    _ = D ^ 2 * (Real.rpow ((n + 1 : ℕ) : ℝ) (2 * r)) ^ 2 := by
      rw [hrpowEndpoint]
      ring
    _ = D ^ 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (4 * r) := by rw [hpowSquare]
    _ = D ^ 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by rw [hrexp]

end RHLean.Analysis
