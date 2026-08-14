import Mathlib
import RHLean.Analysis.EulerCRTRoughnessRecursion
import RHLean.Analysis.MertensPowerGrowth

/-!
# One-prime rough Mertens energy transfer

For a fixed prime `p`, this module transfers the repository's ordinary Mertens
critical-scale energy bound to the summatory Mobius function with the multiples
of `p` removed.

The only structural input is the exact finite prime-extension recurrence already
proved in `EulerCRTRoughnessRecursion`:

`T_p(x) = M(x) + T_p(floor (x / p))`.

The recursive argument is contractive because once `x >= p >= 2`,

`floor (x / p) + 1 <= (2 / 3) * (x + 1)`.

No prime-distribution estimate, PNT input, Euler product, Tauberian theorem, or
zero-free region is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Complex-valued `p`-rough Mertens summatory function. -/
def pRoughMertensSummatory (p x : ℕ) : ℂ :=
  ((roughMertens p x : ℤ) : ℂ)

/-- The `p`-rough summatory function on the native complete-square endpoints. -/
def pRoughSquarePrefixMertens (p n : ℕ) : ℂ :=
  pRoughMertensSummatory p (squarePrefixEndpoint n)

/-- Critical square-prefix energy statement for the fixed-prime rough sum. -/
def PRoughSquarePrefixEnergyBoundedStatement (p : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        ‖pRoughSquarePrefixMertens p n‖ ^ 2 ≤
          C * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε)

@[simp] theorem pRoughMertensSummatory_zero (p : ℕ) (hp : p.Prime) :
    pRoughMertensSummatory p 0 = 0 := by
  simp [pRoughMertensSummatory, roughMertens, roughMoebius, hp.ne_one]

private theorem roughMertens_one_cast_eq_mertensSummatory (x : ℕ) :
    ((roughMertens 1 x : ℤ) : ℂ) = mertensSummatory x := by
  unfold roughMertens roughMoebius mertensSummatory
  simp

/-- Exact one-prime recurrence in the complex-valued summatory normalization. -/
theorem pRoughMertensSummatory_prime_extension
    (p x : ℕ) (hp : p.Prime) :
    pRoughMertensSummatory p x =
      mertensSummatory x + pRoughMertensSummatory p (x / p) := by
  have hsq : Squarefree (p * 1) := by
    simpa using hp.squarefree
  have h := roughMertens_prime_extension (W := 1) hp hsq x
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  simpa [pRoughMertensSummatory, roughMertens_one_cast_eq_mertensSummatory] using hc

private theorem pRough_div_scale
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

/-- A fixed prime roughing preserves every Mertens power exponent `r > 1/2`.
The loss is only a constant depending on `r`; the proof is the exact
prime-extension recursion plus the scale contraction `2/3`. -/
theorem pRoughPowerGrowth_of_energy
    (hM : MertensEnergyBoundedStatement)
    (p : ℕ) (hp : p.Prime) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ x : ℕ,
        ‖pRoughMertensSummatory p x‖ ≤
          D * Real.rpow ((x + 1 : ℕ) : ℝ) r := by
  rcases mertensPowerGrowth_of_energy hM hr with ⟨K, hK, hbound⟩
  let q : ℝ := Real.rpow ((2 : ℝ) / 3) r
  have hr0 : 0 < r := by linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (by norm_num) r
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hr0
  let D : ℝ := K / (1 - q)
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hD0 : 0 ≤ D := div_nonneg hK hden.le
  have hDrel : K + q * D = D := by
    dsimp [D]
    field_simp
    ring
  have hKleD : K ≤ D := by
    have hqD : 0 ≤ q * D := mul_nonneg hq0 hD0
    linarith [hDrel]
  refine ⟨D, hD0, ?_⟩
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hsmall : x < p
      · have hdiv : x / p = 0 := Nat.div_eq_of_lt hsmall
        have hrec := pRoughMertensSummatory_prime_extension p x hp
        rw [hdiv, pRoughMertensSummatory_zero p hp, add_zero] at hrec
        rw [hrec]
        exact (hbound x).trans
          (mul_le_mul_of_nonneg_right hKleD
            (Real.rpow_nonneg (by positivity) r))
      · have hpx : p ≤ x := Nat.le_of_not_gt hsmall
        have hxpos : 0 < x := lt_of_lt_of_le hp.pos hpx
        have hdivlt : x / p < x := Nat.div_lt_self hxpos hp.one_lt
        have hrec := pRoughMertensSummatory_prime_extension p x hp
        rw [hrec]
        have hscale := pRough_div_scale p x hp hpx hr0
        have hchild := ih (x / p) hdivlt
        calc
          ‖mertensSummatory x + pRoughMertensSummatory p (x / p)‖ ≤
              ‖mertensSummatory x‖ + ‖pRoughMertensSummatory p (x / p)‖ :=
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

/-- The native square-prefix critical energy bound survives deletion of the
multiples of any one fixed prime. -/
theorem pRoughSquarePrefixEnergyBounded_of_squarePrefixEnergyBounded
    (hS : SquarePrefixEnergyBoundedStatement)
    (p : ℕ) (hp : p.Prime) :
    PRoughSquarePrefixEnergyBoundedStatement p := by
  have hM : MertensEnergyBoundedStatement :=
    mertensEnergyBounded_of_squarePrefixEnergyBounded hS
  intro ε hε
  let r : ℝ := (1 : ℝ) / 2 + ε / 4
  have hr : (1 : ℝ) / 2 < r := by
    dsimp [r]
    linarith
  rcases pRoughPowerGrowth_of_energy hM p hp hr with ⟨D, hD, hbound⟩
  refine ⟨D ^ 2, sq_nonneg D, ?_⟩
  intro n
  have hsample :
      ‖pRoughSquarePrefixMertens p n‖ ≤
        D * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r := by
    simpa [pRoughSquarePrefixMertens] using hbound (squarePrefixEndpoint n)
  have hsample0 : 0 ≤ ‖pRoughSquarePrefixMertens p n‖ := norm_nonneg _
  have hright0 :
      0 ≤ D * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r :=
    mul_nonneg hD (Real.rpow_nonneg (by positivity) r)
  have hsquare :
      ‖pRoughSquarePrefixMertens p n‖ ^ 2 ≤
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
    ‖pRoughSquarePrefixMertens p n‖ ^ 2 ≤
        (D * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r) ^ 2 := hsquare
    _ = D ^ 2 * (Real.rpow ((n + 1 : ℕ) : ℝ) (2 * r)) ^ 2 := by
      rw [hrpowEndpoint]
      ring
    _ = D ^ 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (4 * r) := by rw [hpowSquare]
    _ = D ^ 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by rw [hrexp]

end RHLean.Analysis
