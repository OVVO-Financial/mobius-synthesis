import Mathlib
import RHLean.Analysis.LargePrimeTTransport
import RHLean.Analysis.SquarePrefixMertensBridge

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

open scoped ArithmeticFunction.Moebius BigOperators

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

/-! ## Classical Möbius Green--Kubo identity

The `40/30/30` population law belongs here, not in an independence model.  On
the actual deterministic Möbius trajectory the square of the prefix is exactly
its squarefree diagonal plus twice its aggregate positive-lag correlation.  The
diagonal is bounded by the number of physical sites because `mu(n)^2 <= 1`.
Thus every possible super-root contribution is concentrated in one signed,
one-sided correlation term; negative correlation helps and never needs to be
bounded in absolute value.
-/

/-- Real Möbius increment on the physical integer clock. -/
def realMoebiusStep (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ)

/-- Möbius prefix of length `K`, i.e. over the sites `0, ..., K-1`. -/
def realMertensLength (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, realMoebiusStep n

/-- Exact squarefree diagonal in the deterministic Mertens square expansion. -/
def realMertensDiagonal (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, realMoebiusStep n ^ 2

/-- Aggregate strictly positive-lag Möbius pair correlation. -/
def realMertensPositiveLagPairSum (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, realMoebiusStep n * realMertensLength n

@[simp] theorem realMertensLength_zero : realMertensLength 0 = 0 := by
  simp [realMertensLength]

@[simp] theorem realMertensLength_succ (K : ℕ) :
    realMertensLength (K + 1) =
      realMertensLength K + realMoebiusStep K := by
  simp [realMertensLength, Finset.sum_range_succ]

@[simp] theorem realMertensDiagonal_zero : realMertensDiagonal 0 = 0 := by
  simp [realMertensDiagonal]

@[simp] theorem realMertensDiagonal_succ (K : ℕ) :
    realMertensDiagonal (K + 1) =
      realMertensDiagonal K + realMoebiusStep K ^ 2 := by
  simp [realMertensDiagonal, Finset.sum_range_succ]

@[simp] theorem realMertensPositiveLagPairSum_zero :
    realMertensPositiveLagPairSum 0 = 0 := by
  simp [realMertensPositiveLagPairSum]

@[simp] theorem realMertensPositiveLagPairSum_succ (K : ℕ) :
    realMertensPositiveLagPairSum (K + 1) =
      realMertensPositiveLagPairSum K +
        realMoebiusStep K * realMertensLength K := by
  simp [realMertensPositiveLagPairSum, Finset.sum_range_succ]

/-- **Exact classical Green--Kubo identity for Möbius.** -/
theorem realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum
    (K : ℕ) :
    realMertensLength K ^ 2 =
      realMertensDiagonal K + 2 * realMertensPositiveLagPairSum K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [realMertensLength_succ, realMertensDiagonal_succ,
        realMertensPositiveLagPairSum_succ]
      nlinarith [ih]

/-- Every physical Möbius increment contributes at most one unit to the diagonal. -/
theorem realMoebiusStep_sq_le_one (n : ℕ) :
    realMoebiusStep n ^ 2 ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h]

/-- The squarefree diagonal is nonnegative. -/
theorem realMertensDiagonal_nonneg (K : ℕ) : 0 ≤ realMertensDiagonal K := by
  unfold realMertensDiagonal
  positivity

/-- The `mu=0` population can only reduce the diagonal; no density estimate is
needed for the sharp deterministic bound `diagonal <= K`. -/
theorem realMertensDiagonal_le (K : ℕ) :
    realMertensDiagonal K ≤ (K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [realMertensDiagonal_succ]
      have hstep := realMoebiusStep_sq_le_one K
      push_cast
      nlinarith

/-- The positive-lag object is literally the sum over all ordered pairs `m<n<K`.
No probabilistic interpretation is present. -/
theorem realMertensPositiveLagPairSum_eq_doubleSum (K : ℕ) :
    realMertensPositiveLagPairSum K =
      ∑ n ∈ Finset.range K,
        ∑ m ∈ Finset.range n, realMoebiusStep m * realMoebiusStep n := by
  unfold realMertensPositiveLagPairSum realMertensLength
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- The length-`x+1` real prefix is exactly the repository's complex Mertens sum. -/
theorem realMertensLength_cast_eq_mertensSummatory (x : ℕ) :
    ((realMertensLength (x + 1) : ℝ) : ℂ) = mertensSummatory x := by
  unfold realMertensLength realMoebiusStep mertensSummatory
  push_cast
  rfl

/-- Norm-square of the complex Mertens value is the ordinary real square. -/
theorem norm_mertensSummatory_sq_eq_realMertensLength_sq (x : ℕ) :
    ‖mertensSummatory x‖ ^ 2 = realMertensLength (x + 1) ^ 2 := by
  rw [← realMertensLength_cast_eq_mertensSummatory]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact sq_abs _

/-- **One-sided arithmetic target.**  Only positive aggregate covariance can
increase Mertens energy.  An absolute-value bound would be unnecessarily strong. -/
def MertensPositiveLagUpperBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ K : ℕ, 1 ≤ K →
        realMertensPositiveLagPairSum K ≤
          C * Real.rpow (K : ℝ) (1 + ε)

/-- A one-sided RH-scale upper bound on the actual aggregate Möbius covariance
implies the protected Mertens-energy criterion. -/
theorem mertensEnergyBounded_of_positiveLagUpperBounded
    (h : MertensPositiveLagUpperBoundedStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hcorr⟩
  let D : ℝ := 1 + 2 * C
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro x
  let K : ℕ := x + 1
  have hK : 1 ≤ K := by
    dsimp [K]
    omega
  have hcorrK := hcorr K hK
  have hdiagK := realMertensDiagonal_le K
  have hid := realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum K
  have hprefix :
      realMertensLength K ^ 2 ≤
        (K : ℝ) + 2 * C * Real.rpow (K : ℝ) (1 + ε) := by
    nlinarith
  have hbase : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hexp : (1 : ℝ) ≤ 1 + ε := by linarith
  have hlinear :
      (K : ℝ) ≤ Real.rpow (K : ℝ) (1 + ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [norm_mertensSummatory_sq_eq_realMertensLength_sq]
  change realMertensLength K ^ 2 ≤
    D * Real.rpow (K : ℝ) (1 + ε)
  calc
    realMertensLength K ^ 2 ≤
        (K : ℝ) + 2 * C * Real.rpow (K : ℝ) (1 + ε) := hprefix
    _ ≤ Real.rpow (K : ℝ) (1 + ε) +
        2 * C * Real.rpow (K : ℝ) (1 + ε) := by
      exact add_le_add_right hlinear _
    _ = D * Real.rpow (K : ℝ) (1 + ε) := by
      dsimp [D]
      ring

/-! ## Two-coordinate fresh-prime cancellation

The positive-lag correlation has a genuinely bilinear Euler action.  For a
fresh prime `p`, the four descendants `(m,n)`, `(p*m,n)`, `(m,p*n)`,
`(p*m,p*n)` have signs `+,-,-,+`.  The complete four-corner orbit therefore
cancels.  The physical ordering/cutoff leaves only two adjacent multiplicative
order shells, exactly analogous to the low-wheel double-cube shell theorem.
-/

/-- Indicator of the strictly ordered physical pair carrier `m<n<K`. -/
def positiveLagPairIndicator (K m n : ℕ) : ℝ :=
  if m < n ∧ n < K then 1 else 0

/-- Mixed finite difference obtained by adjoining `p` to either pair coordinate. -/
def positiveLagPairMixedPrimeCell (p K m n : ℕ) : ℝ :=
  positiveLagPairIndicator K m n -
    positiveLagPairIndicator K (p * m) n -
    positiveLagPairIndicator K m (p * n) +
    positiveLagPairIndicator K (p * m) (p * n)

/-- The mixed pair cell is supported only on the two adjacent order-crossing
shells.  This is a deterministic cutoff identity, not a distributional claim. -/
theorem positiveLagPairMixedPrimeCell_eq_orderShells
    (p K m n : ℕ) (hp : 1 ≤ p) :
    positiveLagPairMixedPrimeCell p K m n =
      (if m < n ∧ n < K ∧ n ≤ p * m then 1 else 0) -
        (if n ≤ m ∧ m < p * n ∧ p * n < K then 1 else 0) := by
  have hpPos : 0 < p := by omega
  by_cases hmn : m < n
  · have hpmn : p * m < p * n := Nat.mul_lt_mul_of_pos_left hmn hpPos
    have hnlepn : n ≤ p * n := by
      calc
        n = 1 * n := by simp
        _ ≤ p * n := Nat.mul_le_mul_right n hp
    have hmpn : m < p * n := hmn.trans_le hnlepn
    have hneg : ¬ n ≤ m := Nat.not_le_of_gt hmn
    have hcancel :
        positiveLagPairIndicator K m (p * n) =
          positiveLagPairIndicator K (p * m) (p * n) := by
      simp [positiveLagPairIndicator, hmpn, hpmn]
    rw [show positiveLagPairMixedPrimeCell p K m n =
        positiveLagPairIndicator K m n -
          positiveLagPairIndicator K (p * m) n by
        unfold positiveLagPairMixedPrimeCell
        rw [hcancel]
        ring]
    by_cases hnK : n < K
    · by_cases hcross : p * m < n
      · have hnotle : ¬ n ≤ p * m := Nat.not_le_of_gt hcross
        simp [positiveLagPairIndicator, hmn, hnK, hcross, hnotle, hneg]
      · have hle : n ≤ p * m := Nat.le_of_not_gt hcross
        simp [positiveLagPairIndicator, hmn, hnK, hcross, hle, hneg]
    · simp [positiveLagPairIndicator, hmn, hnK, hneg]
  · have hnm : n ≤ m := Nat.le_of_not_gt hmn
    have hmlepm : m ≤ p * m := by
      calc
        m = 1 * m := by simp
        _ ≤ p * m := Nat.mul_le_mul_right m hp
    have hnotpmn : ¬ p * m < n :=
      Nat.not_lt_of_ge (hnm.trans hmlepm)
    have hpnpm : p * n ≤ p * m := Nat.mul_le_mul_left p hnm
    have hnotpp : ¬ p * m < p * n := Nat.not_lt_of_ge hpnpm
    simp [positiveLagPairMixedPrimeCell, positiveLagPairIndicator,
      hmn, hnm, hnotpmn, hnotpp]

/-- Multiplication by a genuinely fresh prime flips one real Möbius increment. -/
theorem realMoebiusStep_mul_prime_eq_neg
    {p n : ℕ} (hp : p.Prime) (hnew : ¬ p ∣ n) :
    realMoebiusStep (p * n) = -realMoebiusStep n := by
  have hcop : Nat.Coprime p n := hp.coprime_iff_not_dvd.mpr hnew
  have hmu : μ (p * n) = -μ n := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    rw [ArithmeticFunction.moebius_apply_prime hp]
    simp
  simpa [realMoebiusStep] using congrArg (fun z : ℤ => (z : ℝ)) hmu

/-- **Fresh-prime four-corner cancellation with the physical cutoff retained.**
All Möbius dependence factors into the old pair weight; the new geometry is the
mixed order/cutoff cell. -/
theorem realMoebiusPair_fourCorners_eq_mixedPrimeCell
    {p K m n : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    realMoebiusStep m * realMoebiusStep n * positiveLagPairIndicator K m n +
        realMoebiusStep (p * m) * realMoebiusStep n *
          positiveLagPairIndicator K (p * m) n +
        realMoebiusStep m * realMoebiusStep (p * n) *
          positiveLagPairIndicator K m (p * n) +
        realMoebiusStep (p * m) * realMoebiusStep (p * n) *
          positiveLagPairIndicator K (p * m) (p * n) =
      realMoebiusStep m * realMoebiusStep n *
        positiveLagPairMixedPrimeCell p K m n := by
  rw [realMoebiusStep_mul_prime_eq_neg hp hpm,
    realMoebiusStep_mul_prime_eq_neg hp hpn]
  unfold positiveLagPairMixedPrimeCell
  ring

/-- After swapping the old coordinates, the two interior order-crossing shells
cancel.  For a genuinely fresh prime, only the top escape shell remains. -/
theorem positiveLagPairMixedPrimeCell_add_swap_eq_topEscape
    {p K m n : ℕ} (hp : p.Prime) (hmn : m < n) (hpn : ¬ p ∣ n) :
    positiveLagPairMixedPrimeCell p K m n +
        positiveLagPairMixedPrimeCell p K n m =
      if n < K ∧ K ≤ p * m then 1 else 0 := by
  have hp1 : 1 ≤ p := hp.one_le
  rw [positiveLagPairMixedPrimeCell_eq_orderShells p K m n hp1,
    positiveLagPairMixedPrimeCell_eq_orderShells p K n m hp1]
  have hnm : ¬ n < m := Nat.not_lt_of_ge hmn.le
  have hle : m ≤ n := hmn.le
  have hnotle : ¬ n ≤ m := Nat.not_le_of_gt hmn
  have hne : n ≠ p * m := by
    intro heq
    apply hpn
    rw [heq]
    simp
  by_cases hnK : n < K
  · by_cases htop : K ≤ p * m
    · have hnpm : n < p * m := lt_of_lt_of_le hnK htop
      have hnlepm : n ≤ p * m := hnpm.le
      have hnotpmK : ¬ p * m < K := Nat.not_lt_of_ge htop
      simp [hmn, hnm, hle, hnotle, hnK, htop, hnpm, hnlepm, hnotpmK]
    · have hpmK : p * m < K := Nat.lt_of_not_ge htop
      by_cases hnpm : n < p * m
      · have hnlepm : n ≤ p * m := hnpm.le
        simp [hmn, hnm, hle, hnotle, hnK, htop, hpmK, hnpm, hnlepm]
      · have hpmle : p * m ≤ n := Nat.le_of_not_gt hnpm
        have hpmne : p * m ≠ n := Ne.symm hne
        have hpmLt : p * m < n := lt_of_le_of_ne hpmle hpmne
        have hnot_nlepm : ¬ n ≤ p * m := Nat.not_le_of_gt hpmLt
        simp [hmn, hnm, hle, hnotle, hnK, htop, hpmK, hnpm, hnot_nlepm]
  · have hnoTop : ¬ (n < p * m ∧ p * m < K) := by
      intro h
      exact hnK (h.1.trans h.2)
    simp [hmn, hnm, hle, hnotle, hnK, hnoTop]

end RHLean.Analysis