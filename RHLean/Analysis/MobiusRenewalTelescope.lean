import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# The Möbius renewal telescope

For every `g : ℕ → ℂ` and `X : ℕ`,

```text
sum_{n <= X} (g * 1)(n) * M(floor (X/n))  =  sum_{a <= X} g a,
```

where `(g * 1)(n) = sum_{d | n} g d` is the unit Dirichlet convolution and
`M = mertensSummatory`.

**Honest novelty tag**: this is the classical unit identity
`sum_{n <= X} M(floor (X/n)) = 1` Dirichlet-convolved with `g` — Fubini over
the hyperbola `{(a, b) : a·b ≤ X}` plus `μ * 1 = δ`.  It is recorded as a
kernel identity because it is the exact substrate for renewal-type routes
(Harman-schedule kernels `g d = λ_d·1_{d≤D}`, boundary operators), NOT as new
leverage and NOT as the closure of any route in `boundary/dead_lanes.json`.

The development: `mertensSummatory` as an `Icc 1 x` sum (the `m = 0` term
vanishes), the hyperbola swap (summing over divisor pairs by the product
first or by the first factor first agree), the unit identity
`sum_{b <= N} M(floor (N/b)) = 1` for `N >= 1`, and the g-weighted telescope.
Everything is exact and hypothesis-free (`X = 0` makes both sides empty
sums); no estimate is asserted anywhere.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Bridge: `mertensSummatory` as a sum over `Icc 1 x` (the `m = 0` term
vanishes). -/
theorem mertensSummatory_eq_sum_Icc (x : ℕ) :
    mertensSummatory x = ∑ m ∈ Finset.Icc 1 x, (((μ m : ℤ) : ℂ)) := by
  induction x with
  | zero => simp
  | succ x ih =>
      rw [mertensSummatory_succ, ih,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ x + 1)]

/-- **The hyperbola swap** (Fubini over divisor pairs): summing `F a b` over
all pairs with `a·b ≤ N` by the product `n = a·b` first or by `a` first
agree. -/
theorem sum_Icc_divisorsAntidiagonal_eq_sum_div (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2)
      = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), F a b := by
  classical
  calc (∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2)
      = ∑ z ∈ (Finset.Icc 1 N).sigma (fun n => n.divisorsAntidiagonal),
          F z.2.1 z.2.2 :=
        Finset.sum_sigma' (Finset.Icc 1 N) (fun n => n.divisorsAntidiagonal)
          (fun _ p => F p.1 p.2)
    _ = ∑ w ∈ (Finset.Icc 1 N).sigma (fun a => Finset.Icc 1 (N / a)),
          F w.1 w.2 := by
        refine Finset.sum_nbij' (i := fun z => ⟨z.2.1, z.2.2⟩)
          (j := fun w => ⟨w.1 * w.2, (w.1, w.2)⟩) ?_ ?_ ?_ ?_ ?_
        · rintro ⟨n, a, b⟩ hz
          rw [Finset.mem_sigma] at hz ⊢
          obtain ⟨hn, hp⟩ := hz
          rw [Finset.mem_Icc] at hn
          rw [Nat.mem_divisorsAntidiagonal] at hp
          obtain ⟨hab, hn0⟩ := hp
          have ha0 : 0 < a := by
            rcases Nat.eq_zero_or_pos a with h | h
            · exfalso; apply hn0; rw [← hab, h, Nat.zero_mul]
            · exact h
          have hb0 : 0 < b := by
            rcases Nat.eq_zero_or_pos b with h | h
            · exfalso; apply hn0; rw [← hab, h, Nat.mul_zero]
            · exact h
          have habN : a * b ≤ N := by
            rw [hab]; exact hn.2
          constructor
          · rw [Finset.mem_Icc]
            refine ⟨ha0, ?_⟩
            exact le_trans (Nat.le_mul_of_pos_right a hb0) habN
          · rw [Finset.mem_Icc]
            refine ⟨hb0, ?_⟩
            rw [Nat.le_div_iff_mul_le ha0]
            rw [Nat.mul_comm]
            exact habN
        · rintro ⟨a, b⟩ hw
          rw [Finset.mem_sigma] at hw ⊢
          obtain ⟨ha, hb⟩ := hw
          rw [Finset.mem_Icc] at ha hb
          have habN : a * b ≤ N := by
            have h := (Nat.le_div_iff_mul_le ha.1).1 hb.2
            rw [Nat.mul_comm] at h
            exact h
          have hab0 : 0 < a * b := Nat.mul_pos ha.1 hb.1
          constructor
          · rw [Finset.mem_Icc]
            exact ⟨hab0, habN⟩
          · rw [Nat.mem_divisorsAntidiagonal]
            exact ⟨rfl, hab0.ne'⟩
        · rintro ⟨n, a, b⟩ hz
          rw [Finset.mem_sigma] at hz
          obtain ⟨-, hp⟩ := hz
          rw [Nat.mem_divisorsAntidiagonal] at hp
          obtain ⟨hab, -⟩ := hp
          have hab' : a * b = n := hab
          subst hab'
          rfl
        · rintro ⟨a, b⟩ _
          rfl
        · rintro ⟨n, a, b⟩ _
          rfl
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), F a b :=
        (Finset.sum_sigma' (Finset.Icc 1 N) (fun a => Finset.Icc 1 (N / a))
          (fun a b => F a b)).symm

/-- The divisor sum of `μ` in `ℂ`: `Σ_{d ∣ n} μ d = δ_{n=1}` — the
`μ * 1 = δ` extraction, cast to the complex normalization. -/
theorem sum_divisors_moebius_eq_ite (n : ℕ) :
    (∑ i ∈ n.divisors, (((μ i : ℤ) : ℂ))) = if n = 1 then 1 else 0 := by
  have hz : (∑ i ∈ n.divisors, μ i) = if n = 1 then 1 else 0 := by
    have hconv : ((ArithmeticFunction.moebius *
          (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n) =
        (1 : ArithmeticFunction ℤ) n :=
      congrArg (fun f : ArithmeticFunction ℤ => f n)
        ArithmeticFunction.moebius_mul_coe_zeta
    rwa [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply]
      at hconv
  calc (∑ i ∈ n.divisors, (((μ i : ℤ) : ℂ)))
      = (((∑ i ∈ n.divisors, μ i : ℤ)) : ℂ) := by
        push_cast
        rfl
    _ = (((if n = 1 then 1 else 0 : ℤ)) : ℂ) := by rw [hz]
    _ = (if n = 1 then 1 else 0 : ℂ) := by
        split <;> simp

/-- **The classical unit identity** `Σ_{b ≤ N} M(⌊N/b⌋) = 1` (`N ≥ 1`) —
`μ * 1 = δ` summed along the hyperbola. -/
theorem sum_mertensSummatory_div_eq_one {N : ℕ} (hN : 1 ≤ N) :
    (∑ b ∈ Finset.Icc 1 N, mertensSummatory (N / b)) = 1 := by
  classical
  have hL : ∀ b ∈ Finset.Icc 1 N,
      mertensSummatory (N / b) = ∑ m ∈ Finset.Icc 1 (N / b), (((μ m : ℤ) : ℂ)) :=
    fun b _ => mertensSummatory_eq_sum_Icc (N / b)
  have hinner : ∀ n ∈ Finset.Icc 1 N,
      (∑ p ∈ n.divisorsAntidiagonal, (((μ p.2 : ℤ) : ℂ)))
        = if n = 1 then (1 : ℂ) else 0 := by
    intro n _
    have hanti : (∑ p ∈ n.divisorsAntidiagonal, (((μ p.2 : ℤ) : ℂ)))
        = ∑ i ∈ n.divisors, (((μ i : ℤ) : ℂ)) :=
      Nat.sum_divisorsAntidiagonal' (f := fun _ j => (((μ j : ℤ) : ℂ)))
    rw [hanti]
    exact sum_divisors_moebius_eq_ite n
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
  calc (∑ b ∈ Finset.Icc 1 N, mertensSummatory (N / b))
      = ∑ b ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / b), (((μ m : ℤ) : ℂ)) :=
        Finset.sum_congr rfl hL
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, (((μ p.2 : ℤ) : ℂ)) :=
        (sum_Icc_divisorsAntidiagonal_eq_sum_div
          (fun _ m => (((μ m : ℤ) : ℂ))) N).symm
    _ = ∑ n ∈ Finset.Icc 1 N, (if n = 1 then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl hinner
    _ = 1 := by simp [h1mem]

/-- **The g-weighted renewal telescope**: for every
`g : ℕ → ℂ` and `X : ℕ`,
`Σ_{n ≤ X} (g*1)(n) · M(⌊X/n⌋) = Σ_{a ≤ X} g a`.
Classical content: this is `Σ_{n≤X} M(⌊X/n⌋) = 1` Dirichlet-convolved with
`g`; recorded as a kernel identity because it is the exact substrate for
renewal-type routes (Harman-schedule kernels `g d = λ_d·1_{d≤D}`, boundary
operators), not as a novelty. -/
theorem sum_convolveOne_mul_mertensSummatory_div (g : ℕ → ℂ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (∑ d ∈ n.divisors, g d) * mertensSummatory (X / n))
      = ∑ a ∈ Finset.Icc 1 X, g a := by
  classical
  have hstep1 : ∀ n ∈ Finset.Icc 1 X,
      (∑ d ∈ n.divisors, g d) * mertensSummatory (X / n)
        = ∑ p ∈ n.divisorsAntidiagonal,
            g p.1 * mertensSummatory (X / p.1 / p.2) := by
    intro n _
    have hanti : (∑ p ∈ n.divisorsAntidiagonal,
          g p.1 * mertensSummatory (X / p.1 / p.2))
        = ∑ d ∈ n.divisors, g d * mertensSummatory (X / d / (n / d)) :=
      Nat.sum_divisorsAntidiagonal
        (f := fun a b => g a * mertensSummatory (X / a / b))
    rw [hanti, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [Nat.mem_divisors] at hd
    have harg : X / d / (n / d) = X / n := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hd.1]
    rw [harg]
  have hinner : ∀ a ∈ Finset.Icc 1 X,
      (∑ b ∈ Finset.Icc 1 (X / a), g a * mertensSummatory (X / a / b)) = g a := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hXa : 1 ≤ X / a := (Nat.one_le_div_iff ha.1).mpr ha.2
    rw [← Finset.mul_sum, sum_mertensSummatory_div_eq_one hXa, mul_one]
  calc (∑ n ∈ Finset.Icc 1 X, (∑ d ∈ n.divisors, g d) * mertensSummatory (X / n))
      = ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ n.divisorsAntidiagonal,
          g p.1 * mertensSummatory (X / p.1 / p.2) :=
        Finset.sum_congr rfl hstep1
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
          g a * mertensSummatory (X / a / b) :=
        sum_Icc_divisorsAntidiagonal_eq_sum_div
          (fun a b => g a * mertensSummatory (X / a / b)) X
    _ = ∑ a ∈ Finset.Icc 1 X, g a := Finset.sum_congr rfl hinner

end RHLean.Analysis

end
