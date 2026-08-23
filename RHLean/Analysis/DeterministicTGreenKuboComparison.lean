import Mathlib
import RHLean.Analysis.LargePrimeTTransport

/-!
# Deterministic T-sector Green--Kubo comparison

This module separates the exact finite-state algebra from the still-open arithmetic
correlation estimate for the zero-free `T` sector.

`LargePrimeTTransport` proves the exact uniform-kernel model, including the stationary
identity `V_T(K) = 3*K`.  That identity must not be substituted for the diagonal of an
actual deterministic Mobius trajectory.  Along an arbitrary zero-free trajectory the
active observable takes values in `{ -3, -1, 1, 3 }`, so its squared diagonal is only
bounded above by `9*K`.

The present module proves the deterministic square expansion

`T(K)^2 = diagonal(K) + 2 * positiveLagPairs(K)`

and the comparison

`|positiveLagPairs(K)| <= B`

implies

`T(K)^2 <= 9*K + 2*B`.

The genuinely arithmetic RH-scale input is isolated as a named `Prop`, not an axiom:
for every positive epsilon, the aggregate positive-lag correlation should be
`O(K^(1+epsilon))`.  No Markov assumption and no one-step-to-all-lags inference appears
in this file.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-! ## The deterministic active observable -/

/-- Integer-valued copy of the active three-slot observable `a - b + c`.
It is definitionally independent of probabilistic or kernel structure. -/
def tCellObservableInt (s : TSignState) : ℤ :=
  (if s 0 then 1 else -1) -
    (if s 1 then 1 else -1) +
      (if s 2 then 1 else -1)

/-- The integer observable is exactly the same finite-state function as the rational
observable used by the uniform-kernel layer. -/
theorem tCellObservable_eq_intCast (s : TSignState) :
    tCellObservable s = (tCellObservableInt s : Rat) := by
  native_decide +revert

/-- Real-valued form used for deterministic correlation sums. -/
def tCellObservableReal (s : TSignState) : ℝ :=
  (tCellObservableInt s : ℝ)

/-- On every zero-free `T` state the squared active observable is at most `9`. -/
theorem tCellObservableInt_sq_le_nine (s : TSignState) :
    tCellObservableInt s ^ 2 ≤ 9 := by
  native_decide +revert

/-- Real version of the pointwise diagonal bound. -/
theorem tCellObservableReal_sq_le_nine (s : TSignState) :
    tCellObservableReal s ^ 2 ≤ 9 := by
  have hInt := tCellObservableInt_sq_le_nine s
  have hReal : ((tCellObservableInt s : ℝ) ^ 2) ≤ 9 := by
    exact_mod_cast hInt
  simpa [tCellObservableReal] using hReal

/-! ## Exact deterministic square expansion -/

/-- Sum of the active observable along the first `K` states of a deterministic trajectory. -/
def deterministicTSum (X : ℕ → TSignState) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, tCellObservableReal (X k)

/-- Diagonal contribution in the square of the deterministic trajectory sum. -/
def deterministicTDiagonal (X : ℕ → TSignState) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, tCellObservableReal (X k) ^ 2

/-- Aggregate over all strictly positive-lag pairs.

The endpoint indexing

`sum_{j<K} g(X_j) * sum_{i<j} g(X_i)`

counts each pair `i < j` exactly once.  Grouping those same pairs by `h = j-i` gives the
usual sum over positive lags, but no Markov-chain interpretation is used here. -/
def deterministicTPositiveLagPairSum (X : ℕ → TSignState) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K,
    tCellObservableReal (X j) * deterministicTSum X j

@[simp] theorem deterministicTSum_zero (X : ℕ → TSignState) :
    deterministicTSum X 0 = 0 := by
  simp [deterministicTSum]

@[simp] theorem deterministicTSum_succ (X : ℕ → TSignState) (K : ℕ) :
    deterministicTSum X (K + 1) =
      deterministicTSum X K + tCellObservableReal (X K) := by
  simp [deterministicTSum, Finset.sum_range_succ]

@[simp] theorem deterministicTDiagonal_zero (X : ℕ → TSignState) :
    deterministicTDiagonal X 0 = 0 := by
  simp [deterministicTDiagonal]

@[simp] theorem deterministicTDiagonal_succ (X : ℕ → TSignState) (K : ℕ) :
    deterministicTDiagonal X (K + 1) =
      deterministicTDiagonal X K + tCellObservableReal (X K) ^ 2 := by
  simp [deterministicTDiagonal, Finset.sum_range_succ]

@[simp] theorem deterministicTPositiveLagPairSum_zero (X : ℕ → TSignState) :
    deterministicTPositiveLagPairSum X 0 = 0 := by
  simp [deterministicTPositiveLagPairSum]

@[simp] theorem deterministicTPositiveLagPairSum_succ
    (X : ℕ → TSignState) (K : ℕ) :
    deterministicTPositiveLagPairSum X (K + 1) =
      deterministicTPositiveLagPairSum X K +
        tCellObservableReal (X K) * deterministicTSum X K := by
  simp [deterministicTPositiveLagPairSum, Finset.sum_range_succ]

/-- Exact deterministic Green--Kubo square expansion.  This is an algebraic identity for
an arbitrary trajectory, not an expectation under the uniform kernel. -/
theorem deterministicTSum_sq_eq_diagonal_add_two_mul_positiveLagPairSum
    (X : ℕ → TSignState) (K : ℕ) :
    deterministicTSum X K ^ 2 =
      deterministicTDiagonal X K +
        2 * deterministicTPositiveLagPairSum X K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [deterministicTSum_succ, deterministicTDiagonal_succ,
        deterministicTPositiveLagPairSum_succ]
      nlinarith [ih]

/-- The actual deterministic diagonal is bounded by `9*K`; it is not identified with the
uniform stationary expectation `3*K`. -/
theorem deterministicTDiagonal_le_nine_mul
    (X : ℕ → TSignState) (K : ℕ) :
    deterministicTDiagonal X K ≤ 9 * (K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [deterministicTDiagonal_succ]
      have hsq := tCellObservableReal_sq_le_nine (X K)
      calc
        deterministicTDiagonal X K + tCellObservableReal (X K) ^ 2
            ≤ 9 * (K : ℝ) + 9 := add_le_add ih hsq
        _ = 9 * ((K + 1 : ℕ) : ℝ) := by
          push_cast
          ring

/-- Elementary finite-state comparison lemma.  Any absolute bound on the aggregate
positive-lag pair sum immediately gives the corresponding deterministic square bound. -/
theorem deterministicTSum_sq_le_of_positiveLagPairSum_abs_le
    (X : ℕ → TSignState) (K : ℕ) (B : ℝ)
    (hLag : |deterministicTPositiveLagPairSum X K| ≤ B) :
    deterministicTSum X K ^ 2 ≤ 9 * (K : ℝ) + 2 * B := by
  rw [deterministicTSum_sq_eq_diagonal_add_two_mul_positiveLagPairSum]
  have hdiag := deterministicTDiagonal_le_nine_mul X K
  have hlag : deterministicTPositiveLagPairSum X K ≤ B :=
    (le_abs_self _).trans hLag
  linarith

/-! ## The open arithmetic frontier -/

/-- **Open deterministic higher-lag correlation target.**

For a specified arithmetic trajectory `X`, the aggregate of all positive-lag active-mode
pairs should have square-root-fluctuation energy scale: for every positive epsilon it is
`O(K^(1+epsilon))`.

This is a proposition-valued interface only.  The module does not assert it for the
actual Mobius trajectory, does not derive it from one-step transition counts, and does
not introduce it as an axiom. -/
def DeterministicTPositiveLagCorrelationBoundStatement
    (X : ℕ → TSignState) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ K : ℕ,
        |deterministicTPositiveLagPairSum X K| ≤
          C * Real.rpow (K : ℝ) (1 + ε)

/-- The named higher-lag correlation target feeds the elementary comparison lemma with
no probabilistic or Markov assumption. -/
theorem deterministicTSum_sq_rhScaleEnvelope_of_positiveLagCorrelationBound
    (X : ℕ → TSignState)
    (h : DeterministicTPositiveLagCorrelationBoundStatement X) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ K : ℕ,
          deterministicTSum X K ^ 2 ≤
            9 * (K : ℝ) +
              2 * C * Real.rpow (K : ℝ) (1 + ε) := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hcorr⟩
  refine ⟨C, hC, ?_⟩
  intro K
  have hcomp := deterministicTSum_sq_le_of_positiveLagPairSum_abs_le
    X K (C * Real.rpow (K : ℝ) (1 + ε)) (hcorr K)
  nlinarith

end RHLean.Analysis
