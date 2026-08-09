import Mathlib

/-!
# Signed canonical height: the corrected clock and the low-imbalance counting theorem

For squarefree `m > 1` with largest prime factor `q = P⁺(m)` and cofactor `c = m/q`,
the source clock is

```text
e(m) = ceil(sqrt(m+1)) - 1,      h(m) = q - 1,
```

and the signed canonical height and absolute imbalance are

```text
Y_*(m) = (q^2 - c^2)/2,          Z(m) = |Y_*(m)| = |q-c|(q+c)/2.
```

Two things are formalized here.

## The corrected clock identity

```text
mu(m) 1_{e <= n} = -mu(c) 1_{e <= n < h} + mu(m) 1_{max(e,h) <= n}
```

Because `m` is squarefree with `q` its largest prime factor, `mu(m) = -mu(c)`, so the
identity is carried entirely by the indicators, and `clock_indicator` proves it for
arbitrary `e h n`.  The variant with `1_{h <= n}` in the last term is **false** when
`h < e`; `false_clock_at_thirty` refutes it at `m = 30`, where `q = 5`, `c = 6`,
`e = 5`, `h = 4`, and at `n = 4` the two sides are `0` and `-1`.

The split `e < h` versus `h <= e` is the transport-born / born-smooth dichotomy, and
it agrees with the sign of `Y_*` except exactly at `c = q - 1`, the integer boundary
at entry.

## The unconditional low-imbalance counting theorem

For the block `B_n = [n^2, (n+1)^2)`,

```text
#{ m in B_n : mu(m) != 0, Z(m) <= H }  <=  1 + floor(H/n).
```

This is proved here in the sharper form it actually has: it is a statement about
**factor pairs**, with no reference to `mu`, to primality, or to which factor is
larger.  Writing a pair as `(u, u+d)` with `d` the gap, `Admissible n H u d` says the
product lies in `B_n` and the doubled imbalance `d(2u+d)` is at most `2H`.  Then

* `two_mul_le` — `2n <= 2u + d`, the arithmetic-geometric step;
* `gap_mul_le` — hence `d * n <= H`, so only `1 + floor(H/n)` gaps occur;
* `u_unique` — for a fixed gap at most one `u` puts the product in the block,
  because consecutive products for that gap differ by `(u+v)+1 >= 2n+1`, which
  exceeds the diameter `2n` of the block;
* `card_le` — the counting bound for any finite family of admissible pairs.

Since a squarefree `m` supplies the single pair `(c, q)` and distinct `m` have
distinct products, the bound applies to `#F_n^can(H)` a fortiori.

`window_energy_le` records the consequence used for the low band: a per-block bound
`C` gives `|S_n| <= C n` and hence local energy `<= 4 C^2 H N^2` on any window of
length `H <= N`.

Nothing here is asymptotic and nothing is assumed.  The remaining target — the high
canonical-imbalance population `Z(m) > n^{1+delta}`, retaining both signs of `Y_*` —
is not addressed by this module.

One simplification worth recording: the entry clock is the integer square root,

```text
ceil(sqrt(m+1)) - 1 = floor(sqrt(m)) = Nat.sqrt m,
```

checked over all `m < 2 * 10^6`, so `m ∈ B_n` is exactly `Nat.sqrt m = n`.
-/

noncomputable section

namespace RHLean.Proof

namespace SignedHeight

/-! ## The corrected clock identity -/

/-- The clock identity at the level of indicators.  The last term must be gated by
`max e h ≤ n`, written here as `e ≤ n ∧ h ≤ n`. -/
theorem clock_indicator (e h n : ℕ) :
    (if e ≤ n then (1 : ℤ) else 0) =
      (if e ≤ n ∧ n < h then (1 : ℤ) else 0) +
        (if e ≤ n ∧ h ≤ n then (1 : ℤ) else 0) := by
  split_ifs <;> omega

/-- The identity carrying the Möbius weight.  For squarefree `m` with largest prime
factor `q` and cofactor `c` one has `mu m = -mu c`, so a single weight `w = mu m`
suffices. -/
theorem clock_identity (w : ℤ) (e h n : ℕ) :
    w * (if e ≤ n then (1 : ℤ) else 0) =
      w * (if e ≤ n ∧ n < h then (1 : ℤ) else 0) +
        w * (if e ≤ n ∧ h ≤ n then (1 : ℤ) else 0) := by
  rw [clock_indicator e h n]
  ring

/-- **The `1_{h ≤ n}` variant is false.**  At `m = 30` we have `q = 5`, `c = 6`,
`e = 5`, `h = 4` and `mu 30 = -1`; at `n = 4` the corrected left side is `0` while the
variant evaluates to `-1`. -/
theorem false_clock_at_thirty :
    (-1 : ℤ) * (if (5 : ℕ) ≤ 4 then (1 : ℤ) else 0) ≠
      (-1 : ℤ) * (if (5 : ℕ) ≤ 4 ∧ (4 : ℕ) < 4 then (1 : ℤ) else 0) +
        (-1 : ℤ) * (if (4 : ℕ) ≤ 4 then (1 : ℤ) else 0) := by
  norm_num

/-! ## The low-imbalance counting theorem

A factor pair is written `(u, u + d)`: `u` the smaller factor, `d >= 0` the gap.  The
doubled absolute imbalance is `d * (2u + d) = |q - c| (q + c)`. -/

/-- The pair `(u, u+d)` has its product in `B_n = [n^2, (n+1)^2)` and doubled
imbalance at most `2H`. -/
def Admissible (n H u d : ℕ) : Prop :=
  1 ≤ u ∧ n ^ 2 ≤ u * (u + d) ∧ u * (u + d) < (n + 1) ^ 2 ∧ d * (2 * u + d) ≤ 2 * H

/-- The arithmetic-geometric step: the factor sum of a pair in `B_n` is at least `2n`. -/
theorem two_mul_le {n H u d : ℕ} (h : Admissible n H u d) : 2 * n ≤ 2 * u + d := by
  obtain ⟨-, hlo, -, -⟩ := h
  by_contra hcon
  push_neg at hcon
  have hsq : 4 * (u * (u + d)) ≤ (2 * u + d) ^ 2 := by nlinarith
  nlinarith

/-- Hence a small imbalance forces a small gap: `d * n ≤ H`. -/
theorem gap_mul_le {n H u d : ℕ} (h : Admissible n H u d) : d * n ≤ H := by
  have hsum := two_mul_le h
  obtain ⟨-, -, -, himb⟩ := h
  nlinarith

/-- For a fixed gap, the products of distinct `u` are more than the block diameter
apart, so at most one `u` is admissible. -/
theorem not_lt_of_admissible {n H u₁ u₂ d : ℕ}
    (h1 : Admissible n H u₁ d) (h2 : Admissible n H u₂ d) : ¬ u₁ < u₂ := by
  intro hlt
  have hsum := two_mul_le h1
  obtain ⟨-, hlo1, -, -⟩ := h1
  obtain ⟨-, -, hhi2, -⟩ := h2
  obtain ⟨k, rfl⟩ : ∃ k, u₂ = u₁ + 1 + k := ⟨u₂ - u₁ - 1, by omega⟩
  nlinarith

/-- At most one `u` per gap. -/
theorem u_unique {n H u₁ u₂ d : ℕ}
    (h1 : Admissible n H u₁ d) (h2 : Admissible n H u₂ d) : u₁ = u₂ := by
  have h12 := not_lt_of_admissible h1 h2
  have h21 := not_lt_of_admissible h2 h1
  omega

/-- **The counting theorem.**  Any finite family of admissible pairs for the block
`B_n` and imbalance budget `H` has at most `1 + floor(H/n)` members. -/
theorem card_le {n H : ℕ} (hn : 1 ≤ n) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, Admissible n H p.1 p.2) : S.card ≤ H / n + 1 := by
  have hmap : ∀ p ∈ S, p.2 ∈ Finset.range (H / n + 1) := by
    intro p hp
    have hd : p.2 * n ≤ H := gap_mul_le (hS p hp)
    have hle : p.2 ≤ H / n := (Nat.le_div_iff_mul_le hn).mpr hd
    simp only [Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) S := by
    intro p hp p' hp' hEq
    simp only at hEq
    have h1 : Admissible n H p.1 p'.2 := by rw [← hEq]; exact hS p hp
    exact Prod.ext (u_unique h1 (hS p' hp')) hEq
  have := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2) hmap hinj
  simpa using this

/-! ## The low-band energy consequence -/

/-- A per-block bound `C` gives local energy `4 C^2 H N^2` on a window of length
`H ≤ N`.  This is the estimate the fixed low-imbalance band satisfies
unconditionally, with `C = 1 + floor(Λ)`. -/
theorem window_energy_le {C : ℝ} (S : ℕ → ℝ) (N H : ℕ) (hC : 0 ≤ C)
    (hS : ∀ n : ℕ, |S n| ≤ C * n) (hHN : H ≤ N) :
    ∑ n ∈ Finset.range H, S (N + n) ^ 2 ≤ 4 * C ^ 2 * H * N ^ 2 := by
  have hterm : ∀ n ∈ Finset.range H, S (N + n) ^ 2 ≤ 4 * C ^ 2 * N ^ 2 := by
    intro n hn
    have hlt : n < H := Finset.mem_range.mp hn
    have hb : |S (N + n)| ≤ C * ((N : ℝ) + n) := by
      have := hS (N + n)
      push_cast at this
      exact this
    have hcast : (n : ℝ) ≤ (N : ℝ) := by
      have : n ≤ N := by omega
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have habs : |S (N + n)| ≤ 2 * C * N := by nlinarith [abs_nonneg (S (N + n))]
    have hsq : S (N + n) ^ 2 = |S (N + n)| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg (S (N + n))]
  calc ∑ n ∈ Finset.range H, S (N + n) ^ 2
      ≤ ∑ _n ∈ Finset.range H, (4 * C ^ 2 * N ^ 2) := Finset.sum_le_sum hterm
    _ = (H : ℝ) * (4 * C ^ 2 * N ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = 4 * C ^ 2 * H * N ^ 2 := by ring

end SignedHeight

end RHLean.Proof
