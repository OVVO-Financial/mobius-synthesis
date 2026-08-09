import Mathlib

/-!
# Abstract energy recurrence

The stage-by-stage energy architecture supplies three ingredients:

```text
E_{j₀}            <= B x                       (base energy after 3, 5, 7)
E_{j+1}           <= A_j E_j + C_j x           (one further legal prime)
|Λ_n V_n|^2       <= D_n E_n                   (evaluation against the energy)
```

This module derives the exact iterated consequence

```text
E_n <= (∏_{r=j₀}^{n-1} A_r) B x  +  x ∑_{s=j₀}^{n-1} C_s ∏_{r=s+1}^{n-1} A_r
```

and hence

```text
|Λ_n V_n|^2 <= D_n x [ B ∏_{r} A_r + ∑_s C_s ∏_{r>s} A_r ].
```

It is pure algebra over `ℝ`: `A`, `C`, `D`, `B` and `x` are arbitrary, and the only
hypothesis beyond the three displayed inequalities is `0 ≤ A r`, which is what
lets the induction multiply through.  **No value of `A`, `B`, `C` or `D` is
asserted here, and no asymptotic specialization is made.**  In particular the
`D_n = 3^n` count and the range `n = O(log x / log log x)` are deliberately kept
outside this file: they belong to the analytic layer, and mixing them in would
turn an algebraic lemma into a conditional theorem.

The empirical status of the constants, recorded in
`research/TWO_ANCHOR_SLACK_COVERAGE.md`, is that on the tested post-`7` stages
`A_q^emp < 3.7`; the universal `(A, C)` inequality is open.
-/

noncomputable section

namespace RHLean.Proof

namespace EnergyRecurrence

/-- Accumulated inflation `∏_{r=s}^{n-1} A r` between two stages. -/
def inflation (A : ℕ → ℝ) (s n : ℕ) : ℝ := ∏ r ∈ Finset.Ico s n, A r

@[simp] theorem inflation_self (A : ℕ → ℝ) (s : ℕ) : inflation A s s = 1 := by
  simp [inflation]

theorem inflation_succ_top (A : ℕ → ℝ) {s n : ℕ} (h : s ≤ n) :
    inflation A s (n + 1) = inflation A s n * A n := by
  unfold inflation
  rw [Finset.prod_Ico_succ_top h]

theorem inflation_nonneg {A : ℕ → ℝ} (hA : ∀ r, 0 ≤ A r) (s n : ℕ) :
    0 ≤ inflation A s n :=
  Finset.prod_nonneg fun i _ => hA i

/-- The accumulated additive term `∑_{s=j₀}^{n-1} C s ∏_{r=s+1}^{n-1} A r`. -/
def additive (A C : ℕ → ℝ) (j₀ n : ℕ) : ℝ :=
  ∑ s ∈ Finset.Ico j₀ n, C s * inflation A (s + 1) n

@[simp] theorem additive_self (A C : ℕ → ℝ) (j₀ : ℕ) : additive A C j₀ j₀ = 0 := by
  simp [additive]

/-- The additive term satisfies the same one-stage recurrence as the energy. -/
theorem additive_succ_top (A C : ℕ → ℝ) {j₀ n : ℕ} (h : j₀ ≤ n) :
    additive A C j₀ (n + 1) = A n * additive A C j₀ n + C n := by
  unfold additive
  rw [Finset.sum_Ico_succ_top h, inflation_self]
  have hcongr : ∀ s ∈ Finset.Ico j₀ n,
      C s * inflation A (s + 1) (n + 1) = A n * (C s * inflation A (s + 1) n) := by
    intro s hs
    have hsn : s + 1 ≤ n := (Finset.mem_Ico.mp hs).2
    rw [inflation_succ_top A hsn]
    ring
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
  ring

/-- **Iterated energy estimate.**  A base bound at stage `j₀` and a one-stage
affine recurrence give the exact closed form at every later stage. -/
theorem energy_le (A C E : ℕ → ℝ) (x B : ℝ) (j₀ : ℕ)
    (hA : ∀ r, 0 ≤ A r)
    (hbase : E j₀ ≤ B * x)
    (hstep : ∀ j, j₀ ≤ j → E (j + 1) ≤ A j * E j + C j * x) :
    ∀ n, j₀ ≤ n →
      E n ≤ inflation A j₀ n * (B * x) + additive A C j₀ n * x := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using hbase
  | succ n hn ih =>
    have h1 : E (n + 1) ≤ A n * E n + C n * x := hstep n hn
    have h2 : A n * E n ≤
        A n * (inflation A j₀ n * (B * x) + additive A C j₀ n * x) :=
      mul_le_mul_of_nonneg_left ih (hA n)
    rw [inflation_succ_top A hn, additive_succ_top A C hn]
    nlinarith [h1, h2]

/-- The same estimate with the common factor `x` pulled out, in the shape the
proof programme states it. -/
theorem energy_le' (A C E : ℕ → ℝ) (x B : ℝ) (j₀ : ℕ)
    (hA : ∀ r, 0 ≤ A r)
    (hbase : E j₀ ≤ B * x)
    (hstep : ∀ j, j₀ ≤ j → E (j + 1) ≤ A j * E j + C j * x)
    (n : ℕ) (hn : j₀ ≤ n) :
    E n ≤ (B * inflation A j₀ n + additive A C j₀ n) * x := by
  have h := energy_le A C E x B j₀ hA hbase hstep n hn
  nlinarith [h]

/-- **Evaluation against the energy.**  Combining the iterated estimate with
`|Λ_n V_n|^2 ≤ D_n E_n` gives the closed form the programme targets. -/
theorem eval_le (A C E : ℕ → ℝ) (x B : ℝ) (j₀ : ℕ)
    (hA : ∀ r, 0 ≤ A r)
    (hbase : E j₀ ≤ B * x)
    (hstep : ∀ j, j₀ ≤ j → E (j + 1) ≤ A j * E j + C j * x)
    (n : ℕ) (hn : j₀ ≤ n) (lam D : ℝ) (hD : 0 ≤ D) (hlam : lam ≤ D * E n) :
    lam ≤ D * ((B * inflation A j₀ n + additive A C j₀ n) * x) := by
  have h := energy_le' A C E x B j₀ hA hbase hstep n hn
  have h' : D * E n ≤ D * ((B * inflation A j₀ n + additive A C j₀ n) * x) :=
    mul_le_mul_of_nonneg_left h hD
  linarith

/-! ## Stating the one-stage inequality correctly

`E_q(x) ≤ A E_{q^-}(x) + C x` is **not** a homogeneous Gram inequality and cannot
be one.  `homogeneous_of_affine` is the obstruction: if the affine bound held at
every dilation of a state, the additive constant would be invisible and the bound
would collapse to the homogeneous `f ≤ A g`.  So the inequality is meaningful only

* on the normalized legal arithmetic states arising at prefix `x`, or
* through a split of the refinement into a homogeneous bulk map and a bounded
  boundary vector, `T_{q,x} v = T_q^bulk v + b_{q,x}`.

`energy_affine_step` is the second route, with the cross term absorbed by Young's
inequality: from `‖T^bulk v‖^2 ≤ A₀ ‖v‖^2` and `‖b_{q,x}‖^2 ≤ C₀ x` it produces

```text
E_q(x) ≤ (1 + η) A₀ E_{q^-}(x) + (1 + η⁻¹) C₀ x
```

for every `η > 0`, which is exactly the shape `energy_le` iterates.  Only the
triangle inequality is used, so the statement holds in any normed group. -/

/-- **Scaling obstruction.**  An affine energy bound that survives every dilation
of a state forces the homogeneous bound: the additive constant dilutes like
`lam⁻²` and contributes nothing in the limit.  Hence an estimate with a genuine
`C x` term must be restricted to a normalization-fixed family of states. -/
theorem homogeneous_of_affine {f g A C : ℝ}
    (h : ∀ lam : ℝ, 1 ≤ lam → lam ^ 2 * f ≤ A * (lam ^ 2 * g) + C) :
    f ≤ A * g := by
  by_contra hcon
  push_neg at hcon
  set d : ℝ := f - A * g with hdef
  have hd : 0 < d := by
    simp only [hdef]
    linarith
  obtain ⟨n, hn⟩ := Archimedean.arch (C + 1) hd
  rw [nsmul_eq_mul] at hn
  set lam : ℝ := max 1 (n : ℝ) with hlamdef
  have hlam1 : (1 : ℝ) ≤ lam := le_max_left _ _
  have hlamn : (n : ℝ) ≤ lam := le_max_right _ _
  have hsq : lam ≤ lam ^ 2 := by nlinarith
  have hbig : C + 1 ≤ lam ^ 2 * d := by nlinarith [hn, hlamn, hd, hsq]
  have hstep := h lam hlam1
  have hexp : lam ^ 2 * d = lam ^ 2 * f - A * (lam ^ 2 * g) := by
    rw [hdef]; ring
  linarith

/-- Young's inequality in the form used to absorb the bulk-boundary cross term. -/
theorem sq_add_le_of_pos (s t : ℝ) {η : ℝ} (hη : 0 < η) :
    (s + t) ^ 2 ≤ (1 + η) * s ^ 2 + (1 + η⁻¹) * t ^ 2 := by
  have hne : η ≠ 0 := ne_of_gt hη
  have hinv : (0 : ℝ) ≤ η⁻¹ := le_of_lt (inv_pos.mpr hη)
  have key : 0 ≤ η⁻¹ * (η * s - t) ^ 2 := mul_nonneg hinv (sq_nonneg _)
  have h1 : η⁻¹ * η = 1 := inv_mul_cancel₀ hne
  have expand : η⁻¹ * (η * s - t) ^ 2 =
      (η⁻¹ * η) * (η * s ^ 2) - 2 * (η⁻¹ * η) * (s * t) + η⁻¹ * t ^ 2 := by
    ring
  rw [h1] at expand
  nlinarith [key, expand]

section Normed

variable {F : Type*} [NormedAddCommGroup F]

/-- **Bulk-plus-boundary refinement step.**  A homogeneous bulk bound and a
bounded boundary vector give the affine one-stage inequality, for every splitting
parameter `η > 0`.  This is the legitimate form of `E_q ≤ A E_{q^-} + C x`: the
multiplicative factor `(1 + η) A₀` is an operator bound while the additive term
`(1 + η⁻¹) C₀ x` is a boundary bound, and neither pretends to be the other. -/
theorem energy_affine_step {u b : F} {A₀ C₀ Eprev x η : ℝ} (hη : 0 < η)
    (hbulk : ‖u‖ ^ 2 ≤ A₀ * Eprev) (hb : ‖b‖ ^ 2 ≤ C₀ * x) :
    ‖u + b‖ ^ 2 ≤ (1 + η) * (A₀ * Eprev) + (1 + η⁻¹) * (C₀ * x) := by
  have htri : ‖u + b‖ ≤ ‖u‖ + ‖b‖ := norm_add_le u b
  have h0 : 0 ≤ ‖u + b‖ := norm_nonneg _
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  have hbn : 0 ≤ ‖b‖ := norm_nonneg b
  have hsq : ‖u + b‖ ^ 2 ≤ (‖u‖ + ‖b‖) ^ 2 := by nlinarith
  have hyoung := sq_add_le_of_pos ‖u‖ ‖b‖ hη
  have h1 : (0 : ℝ) ≤ 1 + η := by linarith
  have h2 : (0 : ℝ) ≤ 1 + η⁻¹ := by
    have : 0 < η⁻¹ := inv_pos.mpr hη
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hbulk h1, mul_le_mul_of_nonneg_left hb h2]

end Normed

/-! ## The evaluation constant `D_n = 3^n` is not an assumption

Each refinement replaces a component `Z` by three children summing to `Z`, so
Cauchy-Schwarz bounds the **parent** energy by three times the child energy.
Iterating from the unresolved stage, where the single component is the fibre
value itself, gives `|P_2|^2 = E_0 <= 3^n E_n`, which is exactly the third
hypothesis of the programme with `D_n = 3^n`.

Note which way this runs.  The tensor structure bounds `E_{j+1}` from **below**
and never from above: three children with a small signed sum can have arbitrarily
large squares.  So every upper bound `E_{j+1} <= A E_j + C x` is arithmetic
content about the legal states, and no part of it can be recovered from the shell
combinatorics.  That is the precise sense in which the `(A, C)` inequality is the
whole remaining problem. -/

theorem sq_add_three_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- Summed over the parents of one refinement stage. -/
theorem sum_sq_add_three_le {ι : Type*} (s : Finset ι) (a b c : ι → ℝ) :
    ∑ i ∈ s, (a i + b i + c i) ^ 2 ≤
      3 * ∑ i ∈ s, (a i ^ 2 + b i ^ 2 + c i ^ 2) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => sq_add_three_le (a i) (b i) (c i)

/-- `n` refinement stages lose at most a factor `3^n`. -/
theorem le_pow_three_mul {E : ℕ → ℝ} (h : ∀ j, E j ≤ 3 * E (j + 1)) (n : ℕ) :
    E 0 ≤ 3 ^ n * E n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h3 : (0 : ℝ) ≤ 3 ^ n := by positivity
    calc E 0 ≤ 3 ^ n * E n := ih
      _ ≤ 3 ^ n * (3 * E (n + 1)) := mul_le_mul_of_nonneg_left (h n) h3
      _ = 3 ^ (n + 1) * E (n + 1) := by ring

/-- **The full chain with no unproved evaluation constant.**  The base bound, the
one-stage recurrence and the three-way Cauchy-Schwarz give the fibre estimate
directly; `D_n = 3^n` is discharged rather than assumed. -/
theorem eval_le_three_pow (A C E : ℕ → ℝ) (x B : ℝ) (j₀ : ℕ)
    (hA : ∀ r, 0 ≤ A r)
    (hbase : E j₀ ≤ B * x)
    (hstep : ∀ j, j₀ ≤ j → E (j + 1) ≤ A j * E j + C j * x)
    (hCS : ∀ j, E j ≤ 3 * E (j + 1))
    (n : ℕ) (hn : j₀ ≤ n) :
    E 0 ≤ 3 ^ n * ((B * inflation A j₀ n + additive A C j₀ n) * x) :=
  eval_le A C E x B j₀ hA hbase hstep n hn (E 0) (3 ^ n) (by positivity)
    (le_pow_three_mul hCS n)

/-! ## Uniform stage constants

The only collapse performed here is replacing each `A r` by a common upper bound.
It is still an inequality between finite products, not an asymptotic statement. -/

theorem inflation_le_pow {A : ℕ → ℝ} {a : ℝ} (hA : ∀ r, 0 ≤ A r) (hle : ∀ r, A r ≤ a)
    (s n : ℕ) : inflation A s n ≤ a ^ (n - s) := by
  unfold inflation
  calc ∏ r ∈ Finset.Ico s n, A r ≤ ∏ _r ∈ Finset.Ico s n, a :=
        Finset.prod_le_prod (fun i _ => hA i) (fun i _ => hle i)
    _ = a ^ (n - s) := by rw [Finset.prod_const, Nat.card_Ico]

end EnergyRecurrence

end RHLean.Proof
