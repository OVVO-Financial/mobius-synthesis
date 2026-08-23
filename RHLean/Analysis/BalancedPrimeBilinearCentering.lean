import Mathlib

/-!
# Balanced prime bilinear centering

The canonical coefficient attached to a balanced square-block factorization
`n = u * v` is

```text
beta(u,v) = mu u * mu v * [u prime or v prime].
```

This module proves two exact facts about it and packages the analytic
obligations they expose.

## The inclusion-exclusion form

```text
beta(u,v) = - mu u * 1_P v - mu v * 1_P u - 1_P u * 1_P v
```

The third term is the correction for the both-prime overlap: when `u` and `v`
are both prime the first two terms each contribute `1`, and one must be removed.

## The five-piece centering

Splitting the prime indicator against any density `rho` through
`e = 1_P - rho` and expanding gives the exact decomposition

```text
beta = muE + eE + rhoE + muRho + rhoRho
```

with

```text
muE    = - mu u * e v   - mu v * e u        two oscillatory variables
eE     = - e u  * e v                       two centered error variables
rhoE   = - rho u * e v  - e u * rho v       one smooth, one oscillatory
muRho  = - mu u * rho v - mu v * rho u      one smooth, one Moebius
rhoRho = - rho u * rho v                    fully deterministic
```

`rho` is an arbitrary function here: no property of the logarithmic integral is
used, and no estimate is asserted.  The repository's singleton Li density is one
admissible instance.

## Why the grouping matters

Only `muE` and `eE` have two genuinely oscillatory arithmetic variables; those
two are the Type-II core.  `rhoE` carries a smooth deterministic factor and is
semilinear, so it belongs with the coherent side despite being algebraically
centered.  `muRho` is *not* deterministic: summed over a balanced region it is a
smoothed Moebius sum, and the diagnostics in
`research/COMPRESSION_ESCAPE_DEFECT_NOGO.md` record that it, not the Type-II
core, carries the energy.  The definitions below keep it separate from
`rhoRho` for exactly that reason.

No bound is proved in this file.  The two local-energy statements at the end are
`Prop`s, and the final theorem is the elementary consequence that controlling
both controls the balanced block sum.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-! ## The canonical balanced coefficient -/

/-- Real-valued prime indicator. -/
def primeIndicatorReal (n : ℕ) : ℝ := if n.Prime then 1 else 0

@[simp] theorem primeIndicatorReal_of_prime {n : ℕ} (h : n.Prime) :
    primeIndicatorReal n = 1 := by
  simp [primeIndicatorReal, h]

@[simp] theorem primeIndicatorReal_of_not_prime {n : ℕ} (h : ¬ n.Prime) :
    primeIndicatorReal n = 0 := by
  simp [primeIndicatorReal, h]

/-- Centered prime discrepancy against a density `rho`. -/
def primeDiscrepancy (rho : ℕ → ℝ) (n : ℕ) : ℝ :=
  primeIndicatorReal n - rho n

theorem primeIndicatorReal_eq_rho_add_discrepancy (rho : ℕ → ℝ) (n : ℕ) :
    primeIndicatorReal n = rho n + primeDiscrepancy rho n := by
  unfold primeDiscrepancy
  ring

/-- The canonical coefficient of a balanced factorization `n = u * v`. -/
def balancedCanonicalCoeff (u v : ℕ) : ℝ :=
  ((μ u : ℤ) : ℝ) * ((μ v : ℤ) : ℝ) *
    (if u.Prime ∨ v.Prime then 1 else 0)

/-- **Inclusion-exclusion form of the canonical balanced coefficient.** -/
theorem balancedCanonicalCoeff_eq_primeIndicator_form (u v : ℕ) :
    balancedCanonicalCoeff u v =
      -((μ u : ℤ) : ℝ) * primeIndicatorReal v
        - ((μ v : ℤ) : ℝ) * primeIndicatorReal u
        - primeIndicatorReal u * primeIndicatorReal v := by
  have hmu : u.Prime → ((μ u : ℤ) : ℝ) = -1 := fun h => by
    rw [ArithmeticFunction.moebius_apply_prime h]; norm_num
  have hmv : v.Prime → ((μ v : ℤ) : ℝ) = -1 := fun h => by
    rw [ArithmeticFunction.moebius_apply_prime h]; norm_num
  by_cases hu : u.Prime <;> by_cases hv : v.Prime
  · norm_num [balancedCanonicalCoeff, primeIndicatorReal, hu, hv, hmu hu, hmv hv]
  · norm_num [balancedCanonicalCoeff, primeIndicatorReal, hu, hv, hmu hu]
  · norm_num [balancedCanonicalCoeff, primeIndicatorReal, hu, hv, hmv hv]
  · norm_num [balancedCanonicalCoeff, primeIndicatorReal, hu, hv]

/-! ## The five centered pieces -/

/-- Moebius against centered prime error: two oscillatory variables. -/
def pieceMuE (rho : ℕ → ℝ) (u v : ℕ) : ℝ :=
  -((μ u : ℤ) : ℝ) * primeDiscrepancy rho v
    - ((μ v : ℤ) : ℝ) * primeDiscrepancy rho u

/-- Centered prime error against itself: two centered variables. -/
def pieceEE (rho : ℕ → ℝ) (u v : ℕ) : ℝ :=
  -primeDiscrepancy rho u * primeDiscrepancy rho v

/-- Density against centered prime error: semilinear, one smooth factor. -/
def pieceRhoE (rho : ℕ → ℝ) (u v : ℕ) : ℝ :=
  -rho u * primeDiscrepancy rho v - primeDiscrepancy rho u * rho v

/-- Moebius against density: smoothed Moebius, *not* deterministic. -/
def pieceMuRho (rho : ℕ → ℝ) (u v : ℕ) : ℝ :=
  -((μ u : ℤ) : ℝ) * rho v - ((μ v : ℤ) : ℝ) * rho u

/-- Density against itself: fully deterministic. -/
def pieceRhoRho (rho : ℕ → ℝ) (u v : ℕ) : ℝ :=
  -rho u * rho v

/-- **Exact five-piece centering of the canonical balanced coefficient.**
`rho` is arbitrary; no property of it is used. -/
theorem balancedCanonicalCoeff_five_piece (rho : ℕ → ℝ) (u v : ℕ) :
    balancedCanonicalCoeff u v =
      pieceMuE rho u v + pieceEE rho u v + pieceRhoE rho u v
        + pieceMuRho rho u v + pieceRhoRho rho u v := by
  rw [balancedCanonicalCoeff_eq_primeIndicator_form]
  unfold pieceMuE pieceEE pieceRhoE pieceMuRho pieceRhoRho primeDiscrepancy
  ring

/-! ## Type-II core and coherent complement -/

/-- The genuinely bilinear core: both variables oscillatory. -/
def typeIICore (rho : ℕ → ℝ) (u v : ℕ) : ℝ :=
  pieceMuE rho u v + pieceEE rho u v

/-- Everything else, including the semilinear `rhoE` and the smoothed Moebius
`muRho`. -/
def coherentComplement (rho : ℕ → ℝ) (u v : ℕ) : ℝ :=
  pieceRhoE rho u v + pieceMuRho rho u v + pieceRhoRho rho u v

/-- **The rebalanced two-piece split.** -/
theorem balancedCanonicalCoeff_eq_typeII_add_coherent (rho : ℕ → ℝ) (u v : ℕ) :
    balancedCanonicalCoeff u v =
      typeIICore rho u v + coherentComplement rho u v := by
  rw [balancedCanonicalCoeff_five_piece rho u v]
  unfold typeIICore coherentComplement
  ring

/-! ## The balanced region and block sums -/

/-- The repository's balanced region for the square block at `R`: pairs `(u,d)`
with `0 < d < u` and `R^2 <= u*(u+d) < (R+1)^2`.  Writing `v = u + d` this is
exactly `u < v < 2*u`. -/
def balancedPairs (R : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range (R + 2) ×ˢ Finset.range (R + 2)).filter
    (fun p => 0 < p.2 ∧ p.2 < p.1 ∧
      R ^ 2 ≤ p.1 * (p.1 + p.2) ∧ p.1 * (p.1 + p.2) < (R + 1) ^ 2)

/-- Balanced block sum of a coefficient, in `(u,d)` coordinates. -/
def blockSum (f : ℕ → ℕ → ℝ) (R : ℕ) : ℝ :=
  ∑ p ∈ balancedPairs R, f p.1 (p.1 + p.2)

/-- Balanced block sum of the canonical coefficient. -/
def blockBalanced (R : ℕ) : ℝ := blockSum balancedCanonicalCoeff R

/-- Balanced block sum of the Type-II core. -/
def blockTypeII (rho : ℕ → ℝ) (R : ℕ) : ℝ := blockSum (typeIICore rho) R

/-- Balanced block sum of the coherent complement. -/
def blockCoherent (rho : ℕ → ℝ) (R : ℕ) : ℝ := blockSum (coherentComplement rho) R

/-- **The block-level split.**  Exact for every `R` and every `rho`. -/
theorem blockBalanced_eq_typeII_add_coherent (rho : ℕ → ℝ) (R : ℕ) :
    blockBalanced R = blockTypeII rho R + blockCoherent rho R := by
  unfold blockBalanced blockTypeII blockCoherent blockSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ =>
    balancedCanonicalCoeff_eq_typeII_add_coherent rho p.1 (p.1 + p.2)

/-! ## Local energy and the two analytic obligations -/

/-- Translated prefix of a block sequence: the partial sum of blocks
`N, ..., N + j`. -/
def blockPrefix (g : ℕ → ℝ) (N j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), g (N + i)

/-- Translated-prefix local energy over a window of `H` starting points. -/
def localPrefixEnergy (g : ℕ → ℝ) (N H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range H, (blockPrefix g N j) ^ 2

theorem localPrefixEnergy_nonneg (g : ℕ → ℝ) (N H : ℕ) :
    0 ≤ localPrefixEnergy g N H :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The RH-scale local energy budget for a block sequence. -/
def LocalEnergyBoundedStatement (g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        localPrefixEnergy g N H ≤ C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- **Obligation one: the Type-II core.**  The diagnostics record this column as
flat and decreasing, so this is the tractable half. -/
def TypeIILocalEnergyBoundedStatement (rho : ℕ → ℝ) : Prop :=
  LocalEnergyBoundedStatement (blockTypeII rho)

/-- **Obligation two: the coherent complement.**  This contains `muRho`, a
smoothed Moebius sum, and is *not* a deterministic estimate. -/
def CoherentLocalEnergyBoundedStatement (rho : ℕ → ℝ) : Prop :=
  LocalEnergyBoundedStatement (blockCoherent rho)

private theorem sq_add_le_two (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

theorem blockPrefix_balanced_eq (rho : ℕ → ℝ) (N j : ℕ) :
    blockPrefix blockBalanced N j =
      blockPrefix (blockTypeII rho) N j + blockPrefix (blockCoherent rho) N j := by
  unfold blockPrefix
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => blockBalanced_eq_typeII_add_coherent rho (N + i)

/-- **Both obligations together control the balanced block sum.**  This is the
only implication claimed: no bound on either piece is proved here. -/
theorem localEnergyBounded_blockBalanced_of_both
    (rho : ℕ → ℝ)
    (hII : TypeIILocalEnergyBoundedStatement rho)
    (hcoh : CoherentLocalEnergyBoundedStatement rho) :
    LocalEnergyBoundedStatement blockBalanced := by
  intro ε hε
  obtain ⟨C₁, hC₁, hb₁⟩ := hII ε hε
  obtain ⟨C₂, hC₂, hb₂⟩ := hcoh ε hε
  refine ⟨2 * C₁ + 2 * C₂, by linarith, ?_⟩
  intro N H hH hHN
  have hstep : localPrefixEnergy blockBalanced N H ≤
      2 * localPrefixEnergy (blockTypeII rho) N H +
        2 * localPrefixEnergy (blockCoherent rho) N H := by
    unfold localPrefixEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [blockPrefix_balanced_eq rho N j]
    exact sq_add_le_two _ _
  have h1 := hb₁ N H hH hHN
  have h2 := hb₂ N H hH hHN
  calc localPrefixEnergy blockBalanced N H
      ≤ 2 * localPrefixEnergy (blockTypeII rho) N H +
          2 * localPrefixEnergy (blockCoherent rho) N H := hstep
    _ ≤ 2 * (C₁ * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) +
          2 * (C₂ * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) := by linarith
    _ = (2 * C₁ + 2 * C₂) * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

end RHLean.Analysis
