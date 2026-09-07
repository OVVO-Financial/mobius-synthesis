import Mathlib
import RHLean.Analysis.MathlibMertensHook
import RHLean.Proof.ComplexVerticalLineGreenKubo

/-!
# Exact squarefree diagonal for vertical-line birth/death energy

The Green--Kubo inequality for the physical child-line process was first proved
with the pointwise envelope `event^2 <= 1`.  That loses the exact forty-percent
zero population before the signed covariance is even reached.

This file keeps the same birth/death carrier and proves the sharper pointwise
statement

`event(n)^2 <= mu(n)^2`.

Consequently the complete line-event diagonal is bounded by the existing
Mertens diagonal, i.e. the exact finite squarefree population.  Using the
repository's zero-count identity, this is

`K - 1 - Z(K - 1)`

for `K = (b+1)^2`, where `Z(x)` is the exact number of sites `1 <= n <= x`
with `mu(n)=0`.

Thus the limiting `40/30/30` law is used only in the safe direction: the zero
population can sharpen the diagonal.  No `30/30` sign balance is asserted on
the arithmetically selected birth/death set, and no independence assumption is
introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- **Exact squarefree pointwise envelope.**  A physical child line either does
not change endpoint status, in which case its event is zero, or it is born/dies,
in which case its event is plus or minus `mu(n)`.  Hence its squared event is bounded by
`mu(n)^2`, not merely by one. -/
theorem signedVerticalLineEventStep_sq_le_moebius_sq
    (a b n : ℕ) :
    signedVerticalLineEventStep a b n ^ 2 ≤ realMoebiusStep n ^ 2 := by
  by_cases hb : n ∈ orderedEulerCutActiveChildren (b + 1)
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · have hsq : 0 ≤ realMoebiusStep n ^ 2 := sq_nonneg _
      simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha] using hsq
    · simp [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha]
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · simp [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha]
    · have hsq : 0 ≤ realMoebiusStep n ^ 2 := sq_nonneg _
      simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha] using hsq

/-- **Exact finite squarefree diagonal bound.**  The line-event diagonal is
bounded by the ordinary deterministic Mertens diagonal on the same physical
prefix.  The right side is exactly the number of nonzero Mobius sites there. -/
theorem signedVerticalLineRunDiagonal_le_mertensDiagonal
    (a b : ℕ) :
    signedVerticalLineRunDiagonal a b ≤
      realMertensDiagonal ((b + 1) ^ 2) := by
  unfold signedVerticalLineRunDiagonal signedBlockEnergy realMertensDiagonal
  exact Finset.sum_le_sum
    (fun n _hn => signedVerticalLineEventStep_sq_le_moebius_sq a b n)

/-- At the square endpoint, the existing Mertens diagonal is exactly the full
prefix population minus the `mu=0` population.  The `n=0` site contributes zero,
so the physical endpoint is `K-1` rather than `K`. -/
theorem realMertensDiagonal_squareEndpoint_eq_sub_zeroCount
    (b : ℕ) :
    realMertensDiagonal ((b + 1) ^ 2) =
      ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) -
        (realMertensZeroCount ((b + 1) ^ 2 - 1) : ℝ) := by
  have hKpos : 0 < (b + 1) ^ 2 := by positivity
  have hKone : 1 ≤ (b + 1) ^ 2 := Nat.succ_le_iff.mpr hKpos
  have hKsub : ((b + 1) ^ 2 - 1) + 1 = (b + 1) ^ 2 :=
    Nat.sub_add_cancel hKone
  have hzero :=
    realMertensDiagonal_add_zeroCount_eq_endpoint ((b + 1) ^ 2 - 1)
  rw [hKsub] at hzero
  linarith

/-- The diagonal bound with the exact finite Mobius-zero population exposed. -/
theorem signedVerticalLineRunDiagonal_le_endpoint_sub_zeroCount
    (a b : ℕ) :
    signedVerticalLineRunDiagonal a b ≤
      ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) -
        (realMertensZeroCount ((b + 1) ^ 2 - 1) : ℝ) := by
  have hdiag := signedVerticalLineRunDiagonal_le_mertensDiagonal a b
  rw [realMertensDiagonal_squareEndpoint_eq_sub_zeroCount b] at hdiag
  exact hdiag

/-- **Squarefree Green--Kubo inequality.**  This is the previous line-energy
inequality with the crude unit diagonal replaced by the exact squarefree
Mertens diagonal. -/
theorem norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      realMertensDiagonal ((b + 1) ^ 2) +
        2 * signedVerticalLineRunCovariance a b := by
  have hid :=
    norm_signedVerticalIntervalMass_sq_eq_lineDiagonal_add_two_mul_covariance
      a b hab
  have hdiag := signedVerticalLineRunDiagonal_le_mertensDiagonal a b
  linarith

/-- Negative covariance remains harmless after the squarefree sharpening. -/
theorem norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_positiveCovariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      realMertensDiagonal ((b + 1) ^ 2) +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_covariance
      a b hab
  have hcov : signedVerticalLineRunCovariance a b ≤
      max 0 (signedVerticalLineRunCovariance a b) := le_max_right _ _
  linarith

/-- **Exact finite-density inequality.**  The complete signed vertical mass is
bounded by the exact nonzero Mobius population plus the positive cross-line
covariance.  This is the rigorous finite replacement for inserting a heuristic
`60%` diagonal density. -/
theorem norm_signedVerticalIntervalMass_sq_le_endpoint_sub_zeroCount_add_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) -
        (realMertensZeroCount ((b + 1) ^ 2 - 1) : ℝ) +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_positiveCovariance
      a b hab
  rw [realMertensDiagonal_squareEndpoint_eq_sub_zeroCount b] at hbase
  exact hbase

/-- Any finite lower bound for the zero density plugs into the line-energy
estimate without making a sign-balance assumption.  In particular a rigorous
version of `Z(x) >= delta*x - E` yields diagonal coefficient `1-delta`. -/
theorem norm_signedVerticalIntervalMass_sq_le_of_zeroCount_lowerBound
    (a b : ℕ) (hab : a ≤ b + 1) (δ E : ℝ)
    (hzero :
      δ * ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) - E ≤
        (realMertensZeroCount ((b + 1) ^ 2 - 1) : ℝ)) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (1 - δ) * ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) + E +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sub_zeroCount_add_covariance
      a b hab
  nlinarith

/-! ## Elementary finite squarefree-density estimate

We now discharge the density input by the first five prime squares
`4, 9, 25, 49, 121`.  The proof is the second Bonferroni inequality on these
five deterministic divisibility events.  Pair intersections are exact because
the prime squares are pairwise coprime.  Counting multiples in `1,...,x` uses
`Nat.card_multiples'`; the only loss is one floor-unit for each of the five
positive singleton terms.

The resulting coefficient is slightly larger than `3/8`, so uniformly

`Z(x) >= (3/8) x - 5`.

No asymptotic squarefree-density theorem or independence assumption is used.
-/

private def squareDivIndicator (d n : ℕ) : ℝ :=
  if d ∣ n then 1 else 0

private theorem sum_squareDivIndicator_Icc (d x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, squareDivIndicator d n) =
      ((x / d : ℕ) : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 x, squareDivIndicator d n) =
        (((Finset.Icc 1 x).filter fun n => d ∣ n).card : ℝ) := by
      simp [squareDivIndicator]
    _ = (((Finset.range x.succ).filter fun n => n ≠ 0 ∧ d ∣ n).card : ℝ) := by
      have hset :
          (Finset.Icc 1 x).filter (fun n => d ∣ n) =
            (Finset.range x.succ).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
        ext n
        simp
        omega
      rw [hset]
    _ = ((x / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.card_multiples' x d)

private theorem squareDivIndicator_mul_of_coprime
    {a b n : ℕ} (hab : Nat.Coprime a b) :
    squareDivIndicator a n * squareDivIndicator b n =
      squareDivIndicator (a * b) n := by
  have haProd : a ∣ a * b := ⟨b, rfl⟩
  have hbProd : b ∣ a * b := ⟨a, by simp [mul_comm]⟩
  by_cases ha : a ∣ n
  · by_cases hb : b ∣ n
    · have habd : a * b ∣ n := hab.mul_dvd_of_dvd_of_dvd ha hb
      simp [squareDivIndicator, ha, hb, habd]
    · have hnab : ¬ a * b ∣ n := by
        intro hnab
        exact hb (dvd_trans hbProd hnab)
      simp [squareDivIndicator, ha, hb, hnab]
  · have hnab : ¬ a * b ∣ n := by
      intro hnab
      exact ha (dvd_trans haProd hnab)
    simp [squareDivIndicator, ha, hnab]

private theorem sum_squareDivIndicator_mul_Icc
    (a b x : ℕ) (hab : Nat.Coprime a b) :
    (∑ n ∈ Finset.Icc 1 x,
      squareDivIndicator a n * squareDivIndicator b n) =
      ((x / (a * b) : ℕ) : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 1 x,
      squareDivIndicator a n * squareDivIndicator b n) =
        ∑ n ∈ Finset.Icc 1 x, squareDivIndicator (a * b) n := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact squareDivIndicator_mul_of_coprime hab
    _ = ((x / (a * b) : ℕ) : ℝ) :=
      sum_squareDivIndicator_Icc (a * b) x

private theorem natCast_div_ge_realDiv_sub_one
    (x d : ℕ) (hd : 0 < d) :
    (x : ℝ) / (d : ℝ) - 1 ≤ ((x / d : ℕ) : ℝ) := by
  have hmod : x % d < d := Nat.mod_lt x hd
  have hdecomp : d * (x / d) + x % d = x := Nat.div_add_mod x d
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmodR : ((x % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod
  have hdecompR :
      (d : ℝ) * ((x / d : ℕ) : ℝ) + ((x % d : ℕ) : ℝ) = (x : ℝ) := by
    exact_mod_cast hdecomp
  have hlt :
      (x : ℝ) < (((x / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
    nlinarith
  have hdiv :
      (x : ℝ) / (d : ℝ) < ((x / d : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hdR).2 hlt
  linarith

private theorem natCast_div_le_realDiv
    (x d : ℕ) (hd : 0 < d) :
    ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  apply (le_div_iff₀ hdR).2
  exact_mod_cast (Nat.div_mul_le_self x d)

private def fivePrimeSquareBonferroni (n : ℕ) : ℝ :=
  squareDivIndicator 4 n +
    squareDivIndicator 9 n +
    squareDivIndicator 25 n +
    squareDivIndicator 49 n +
    squareDivIndicator 121 n -
  (squareDivIndicator 4 n * squareDivIndicator 9 n +
    squareDivIndicator 4 n * squareDivIndicator 25 n +
    squareDivIndicator 4 n * squareDivIndicator 49 n +
    squareDivIndicator 4 n * squareDivIndicator 121 n +
    squareDivIndicator 9 n * squareDivIndicator 25 n +
    squareDivIndicator 9 n * squareDivIndicator 49 n +
    squareDivIndicator 9 n * squareDivIndicator 121 n +
    squareDivIndicator 25 n * squareDivIndicator 49 n +
    squareDivIndicator 25 n * squareDivIndicator 121 n +
    squareDivIndicator 49 n * squareDivIndicator 121 n)

private theorem fivePrimeSquareBonferroni_le_zeroIndicator (n : ℕ) :
    fivePrimeSquareBonferroni n ≤ realMoebiusZeroIndicator n := by
  by_cases hhit :
      4 ∣ n ∨ 9 ∣ n ∨ 25 ∣ n ∨ 49 ∣ n ∨ 121 ∣ n
  · have hnsq : ¬ Squarefree n := by
      intro hsq
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      rcases hhit with h4 | h9 | h25 | h49 | h121
      · exact (hsq 2 (by norm_num)) (by simpa using h4)
      · exact (hsq 3 (by norm_num)) (by simpa using h9)
      · exact (hsq 5 (by norm_num)) (by simpa using h25)
      · exact (hsq 7 (by norm_num)) (by simpa using h49)
      · exact (hsq 11 (by norm_num)) (by simpa using h121)
    have hmu : μ n = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    by_cases h4 : 4 ∣ n <;>
    by_cases h9 : 9 ∣ n <;>
    by_cases h25 : 25 ∣ n <;>
    by_cases h49 : 49 ∣ n <;>
    by_cases h121 : 121 ∣ n <;>
      simp [fivePrimeSquareBonferroni, squareDivIndicator,
        realMoebiusZeroIndicator, hmu, h4, h9, h25, h49, h121] <;>
      norm_num
  · have h4 : ¬ 4 ∣ n := by tauto
    have h9 : ¬ 9 ∣ n := by tauto
    have h25 : ¬ 25 ∣ n := by tauto
    have h49 : ¬ 49 ∣ n := by tauto
    have h121 : ¬ 121 ∣ n := by tauto
    by_cases hmu : μ n = 0 <;>
      simp [fivePrimeSquareBonferroni, squareDivIndicator,
        realMoebiusZeroIndicator, hmu, h4, h9, h25, h49, h121]

/-- **Uniform elementary zero-density estimate.**  The first five prime-square
faces alone force at least three-eighths of the physical sites to be Möbius
zeros, up to the five floor errors. -/
theorem realMertensZeroCount_ge_three_eighths_sub_five (x : ℕ) :
    (3 / 8 : ℝ) * (x : ℝ) - 5 ≤ (realMertensZeroCount x : ℝ) := by
  have hsum :
      (∑ n ∈ Finset.Icc 1 x, fivePrimeSquareBonferroni n) ≤
        ∑ n ∈ Finset.Icc 1 x, realMoebiusZeroIndicator n :=
    Finset.sum_le_sum (fun n _hn => fivePrimeSquareBonferroni_le_zeroIndicator n)
  have hbonf :
      (∑ n ∈ Finset.Icc 1 x, fivePrimeSquareBonferroni n) =
        (((x / 4 : ℕ) : ℝ) +
          ((x / 9 : ℕ) : ℝ) +
          ((x / 25 : ℕ) : ℝ) +
          ((x / 49 : ℕ) : ℝ) +
          ((x / 121 : ℕ) : ℝ)) -
        (((x / 36 : ℕ) : ℝ) +
          ((x / 100 : ℕ) : ℝ) +
          ((x / 196 : ℕ) : ℝ) +
          ((x / 484 : ℕ) : ℝ) +
          ((x / 225 : ℕ) : ℝ) +
          ((x / 441 : ℕ) : ℝ) +
          ((x / 1089 : ℕ) : ℝ) +
          ((x / 1225 : ℕ) : ℝ) +
          ((x / 3025 : ℕ) : ℝ) +
          ((x / 5929 : ℕ) : ℝ)) := by
    simp only [fivePrimeSquareBonferroni, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [sum_squareDivIndicator_Icc 4 x,
      sum_squareDivIndicator_Icc 9 x,
      sum_squareDivIndicator_Icc 25 x,
      sum_squareDivIndicator_Icc 49 x,
      sum_squareDivIndicator_Icc 121 x,
      sum_squareDivIndicator_mul_Icc 4 9 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 4 25 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 4 49 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 4 121 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 9 25 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 9 49 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 9 121 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 25 49 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 25 121 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 49 121 x (by norm_num)]
  rw [hbonf, sum_realMoebiusZeroIndicator_eq_zeroCount] at hsum
  have h4 := natCast_div_ge_realDiv_sub_one x 4 (by norm_num)
  have h9 := natCast_div_ge_realDiv_sub_one x 9 (by norm_num)
  have h25 := natCast_div_ge_realDiv_sub_one x 25 (by norm_num)
  have h49 := natCast_div_ge_realDiv_sub_one x 49 (by norm_num)
  have h121 := natCast_div_ge_realDiv_sub_one x 121 (by norm_num)
  have h36 := natCast_div_le_realDiv x 36 (by norm_num)
  have h100 := natCast_div_le_realDiv x 100 (by norm_num)
  have h196 := natCast_div_le_realDiv x 196 (by norm_num)
  have h484 := natCast_div_le_realDiv x 484 (by norm_num)
  have h225 := natCast_div_le_realDiv x 225 (by norm_num)
  have h441 := natCast_div_le_realDiv x 441 (by norm_num)
  have h1089 := natCast_div_le_realDiv x 1089 (by norm_num)
  have h1225 := natCast_div_le_realDiv x 1225 (by norm_num)
  have h3025 := natCast_div_le_realDiv x 3025 (by norm_num)
  have h5929 := natCast_div_le_realDiv x 5929 (by norm_num)
  let C : ℝ :=
    1 / 4 + 1 / 9 + 1 / 25 + 1 / 49 + 1 / 121 -
      (1 / 36 + 1 / 100 + 1 / 196 + 1 / 484 + 1 / 225 +
        1 / 441 + 1 / 1089 + 1 / 1225 + 1 / 3025 + 1 / 5929)
  have hfloor :
      C * (x : ℝ) - 5 ≤
        (((x / 4 : ℕ) : ℝ) +
          ((x / 9 : ℕ) : ℝ) +
          ((x / 25 : ℕ) : ℝ) +
          ((x / 49 : ℕ) : ℝ) +
          ((x / 121 : ℕ) : ℝ)) -
        (((x / 36 : ℕ) : ℝ) +
          ((x / 100 : ℕ) : ℝ) +
          ((x / 196 : ℕ) : ℝ) +
          ((x / 484 : ℕ) : ℝ) +
          ((x / 225 : ℕ) : ℝ) +
          ((x / 441 : ℕ) : ℝ) +
          ((x / 1089 : ℕ) : ℝ) +
          ((x / 1225 : ℕ) : ℝ) +
          ((x / 3025 : ℕ) : ℝ) +
          ((x / 5929 : ℕ) : ℝ)) := by
    dsimp [C]
    linarith
  have hC : (3 / 8 : ℝ) ≤ C := by
    norm_num [C]
  have hx : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hscale : (3 / 8 : ℝ) * (x : ℝ) ≤ C * (x : ℝ) :=
    mul_le_mul_of_nonneg_right hC hx
  linarith

/-- **Compiled finite-density Green--Kubo bound.**  Substituting the elementary
five-prime-square sieve into the exact line-energy identity leaves a `5/8`
diagonal coefficient and the same signed cross-line covariance term. -/
theorem norm_signedVerticalIntervalMass_sq_le_five_eighths_endpoint_add_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (5 / 8 : ℝ) * ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) + 5 +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hzero :=
    realMertensZeroCount_ge_three_eighths_sub_five ((b + 1) ^ 2 - 1)
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_of_zeroCount_lowerBound
      a b hab (3 / 8) 5 hzero
  norm_num at hbase ⊢
  exact hbase

/-- The converse pressure inequality is sharpened by the exact zero population:
large vertical mass must overcome the *squarefree* diagonal, not the full
physical prefix. -/
theorem signedVerticalLineRunCovariance_ge_half_squarefree_excess
    (a b : ℕ) (hab : a ≤ b + 1) :
    (‖signedVerticalIntervalMass a b‖ ^ 2 -
        realMertensDiagonal ((b + 1) ^ 2)) / 2 ≤
      signedVerticalLineRunCovariance a b := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_covariance
      a b hab
  linarith

/-! ## Active-child shell and covariance-boundary identification

The physical vertical-line carrier has no hidden arithmetic condition beyond
squarefreeness and the two square-root walls.  Every active child at root `R`
is a squarefree integer strictly in `(R,R^2)`, and conversely every such integer
has a unique ordered Euler cut: recursively strip its largest prime until the
remaining cofactor lies below `R`, placing stripped larger primes in the rough
high cofactor.  This turns prime-instability of the line mask into the literal
two-wall birth/top-escape geometry.
-/

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

/-- The literal squarefree physical shell between the root and square wall. -/
def orderedEulerCutSquarefreeShell (R : ℕ) : Finset ℕ :=
  (Finset.Ioo R (R ^ 2)).filter Squarefree

@[simp] theorem mem_orderedEulerCutSquarefreeShell
    {R n : ℕ} :
    n ∈ orderedEulerCutSquarefreeShell R ↔
      R < n ∧ n < R ^ 2 ∧ Squarefree n := by
  simp [orderedEulerCutSquarefreeShell, and_assoc]

/-- Every active physical child is squarefree. -/
theorem orderedEulerCutActiveChild_squarefree
    {R n : ℕ} (hn : n ∈ orderedEulerCutActiveChildren R) :
    Squarefree n := by
  rcases Finset.mem_image.mp hn with ⟨y, hy, rfl⟩
  have hshape := orderedEulerCutShape_of_mem_carrier hy
  have hlow := orderedEulerCut_lowSourceData hshape
  have hhighLow := orderedEulerCut_highCofactor_coprime_lowProduct hshape
  have hp : (orderedEulerCutPivot y).Prime := by
    simpa [orderedEulerCutPivot] using hshape.1
  have hcsq : Squarefree (orderedEulerCutHighCofactor y) := by
    simpa [orderedEulerCutHighCofactor] using hshape.2.2.1
  have hpc : ¬ orderedEulerCutPivot y ∣ orderedEulerCutHighCofactor y := by
    simpa [orderedEulerCutPivot, orderedEulerCutHighCofactor] using
      hshape.2.2.2.1
  have hcp : Nat.Coprime (orderedEulerCutHighCofactor y)
      (orderedEulerCutPivot y) :=
    ((hp.coprime_iff_not_dvd
      (n := orderedEulerCutHighCofactor y)).2 hpc).symm
  have hpLowSq :
      Squarefree (orderedEulerCutPivot y * orderedEulerCutLowProduct y) :=
    (Nat.squarefree_mul hlow.2.2.2.1).2
      ⟨hp.squarefree, hlow.2.2.1⟩
  have hcop : Nat.Coprime (orderedEulerCutHighCofactor y)
      (orderedEulerCutPivot y * orderedEulerCutLowProduct y) :=
    Nat.Coprime.mul_right hcp hhighLow
  change Squarefree
    (orderedEulerCutHighCofactor y *
      (orderedEulerCutPivot y * orderedEulerCutLowProduct y))
  exact (Nat.squarefree_mul hcop).2 ⟨hcsq, hpLowSq⟩

/-- Every active physical child is strictly above its current root. -/
theorem orderedEulerCutActiveChild_root_lt
    {R n : ℕ} (hn : n ∈ orderedEulerCutActiveChildren R) :
    R < n := by
  rcases Finset.mem_image.mp hn with ⟨y, hy, rfl⟩
  have hshape := orderedEulerCutShape_of_mem_carrier hy
  have hocc := mem_orderedEulerCutCarrier.mp hy
  have hfactor := orderedEulerCutOccursAt_factor_window hshape hocc
  have hc1 : 1 ≤ orderedEulerCutHighCofactor y := by
    simpa [orderedEulerCutHighCofactor] using hshape.2.1
  have hle : orderedEulerCutUpperFactor y ≤ orderedEulerCutChildInteger y := by
    have hmul := Nat.mul_le_mul_right (orderedEulerCutUpperFactor y) hc1
    simpa [orderedEulerCutUpperFactor, orderedEulerCutDeathRoot,
      orderedEulerCutChildInteger, orderedEulerCutHighCofactor] using hmul
  exact hfactor.2.trans_le hle

/-- **Squarefree shell realization.**  Every squarefree integer strictly between
`R` and `R^2` is the child of an ordered Euler cut active at `R`. -/
theorem orderedEulerCutActiveChild_of_squarefree_shell
    {R n : ℕ} (hR : 2 ≤ R) (hsq : Squarefree n)
    (hRn : R < n) (hnR : n < R ^ 2) :
    n ∈ orderedEulerCutActiveChildren R := by
  revert hsq hRn hnR
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hsq hRn hnR
      have hn1 : 1 < n := by omega
      let p := canonicalLargestPrimeFactor n
      let m := canonicalCofactor n
      have hdata : CanonicalSourceData p m := by
        simpa [p, m] using canonicalSourceData_of_squarefree hsq hn1
      rcases hdata with ⟨hp, hm1, hmsq, hcop, hdom⟩
      have hmp : m * p = n := by
        simpa [m, p] using canonicalCofactor_mul_largestPrimeFactor hn1
      have hmLt : m < n := by
        simpa [m] using canonicalCofactor_lt_self hn1
      have hsqrt : Nat.sqrt n < R := (Nat.sqrt_lt').2 hnR
      by_cases hmR : m ≤ R
      · have htprod : primeFaceProduct m.primeFactors = m := by
          simpa [primeFaceProduct] using Nat.prod_primeFactors_of_squarefree hmsq
        have hpn : p * m = n := by
          simpa [Nat.mul_comm] using hmp
        have hshape : OrderedEulerCutShape (m.primeFactors, (1, p)) := by
          change p.Prime ∧ 1 ≤ (1 : ℕ) ∧ Squarefree 1 ∧ ¬ p ∣ 1 ∧
            (∀ q ∈ m.primeFactors, q.Prime ∧ q < p) ∧ RoughAbove p 1
          refine ⟨hp, by simp, by simp, ?_, ?_, ?_⟩
          · intro hp1
            exact hp.ne_one (Nat.dvd_one.mp hp1)
          · intro q hq
            rcases Nat.mem_primeFactors.mp hq with ⟨hqPrime, hqm, _hm0⟩
            exact ⟨hqPrime, hdom q hqPrime hqm⟩
          · simp [RoughAbove]
        have hbirth : orderedEulerCutBirthRoot
            (m.primeFactors, (1, p)) ≤ R := by
          change max (primeFaceProduct m.primeFactors)
            (max (1 + 1)
              (Nat.sqrt (1 * (p * primeFaceProduct m.primeFactors)) + 1)) ≤ R
          rw [htprod, one_mul, hpn]
          apply Nat.max_le.mpr
          refine ⟨hmR, Nat.max_le.mpr ⟨?_, ?_⟩⟩ <;> omega
        have hdeath : R < orderedEulerCutDeathRoot
            (m.primeFactors, (1, p)) := by
          change R < p * primeFaceProduct m.primeFactors
          rw [htprod, hpn]
          exact hRn
        have hmem : (m.primeFactors, (1, p)) ∈ orderedEulerCutCarrier R :=
          mem_orderedEulerCutCarrier_iff_shape_lifetime.mpr
            ⟨hshape, hbirth, hdeath⟩
        apply Finset.mem_image.mpr
        refine ⟨(m.primeFactors, (1, p)), hmem, ?_⟩
        change 1 * (p * primeFaceProduct m.primeFactors) = n
        rw [htprod, one_mul, hpn]
      · have hRm : R < m := Nat.lt_of_not_ge hmR
        have hmActive : m ∈ orderedEulerCutActiveChildren R :=
          ih m hmLt hmsq hRm (hmLt.trans hnR)
        rcases Finset.mem_image.mp hmActive with ⟨y, hy, hychild⟩
        rcases y with ⟨t, ⟨c, q⟩⟩
        change c * (q * primeFaceProduct t) = m at hychild
        have hyShape0 := orderedEulerCutShape_of_mem_carrier hy
        have hyShape := hyShape0
        change q.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ q ∣ c ∧
          (∀ r ∈ t, r.Prime ∧ r < q) ∧ RoughAbove q c at hyShape
        rcases hyShape with
          ⟨hq, hc1, hcsq, hqNotC, hfaces, hrough⟩
        have hqDvdM : q ∣ m := by
          rw [← hychild]
          exact ⟨c * primeFaceProduct t, by ring⟩
        have hqp : q < p := hdom q hq hqDvdM
        have hcDvdM : c ∣ m := by
          rw [← hychild]
          exact ⟨q * primeFaceProduct t, rfl⟩
        have hpcop : Nat.Coprime p c :=
          hcop.coprime_dvd_right hcDvdM
        have hcsqNew : Squarefree (c * p) :=
          (Nat.squarefree_mul hpcop.symm).2 ⟨hcsq, hp.squarefree⟩
        have hqNotP : ¬ q ∣ p := by
          intro hqdp
          have heq : q = p :=
            (Nat.prime_dvd_prime_iff_eq hq hp).mp hqdp
          omega
        have hqNotCP : ¬ q ∣ c * p := by
          intro hqcp
          rcases hq.dvd_mul.mp hqcp with hqc | hqpDvd
          · exact hqNotC hqc
          · exact hqNotP hqpDvd
        have hroughNew : RoughAbove q (c * p) := by
          intro r hr
          rcases Nat.mem_primeFactors.mp hr with ⟨hrPrime, hrDvd, _hcp0⟩
          rcases hrPrime.dvd_mul.mp hrDvd with hrc | hrp
          · have hc0 : c ≠ 0 := by omega
            have hrMem : r ∈ c.primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hrPrime, hrc, hc0⟩
            exact hrough r hrMem
          · have hre : r = p :=
              (Nat.prime_dvd_prime_iff_eq hrPrime hp).mp hrp
            simpa [hre] using hqp
        have hzShape : OrderedEulerCutShape (t, (c * p, q)) := by
          change q.Prime ∧ 1 ≤ c * p ∧ Squarefree (c * p) ∧
            ¬ q ∣ c * p ∧
            (∀ r ∈ t, r.Prime ∧ r < q) ∧ RoughAbove q (c * p)
          refine ⟨hq, ?_, hcsqNew, hqNotCP, hfaces, hroughNew⟩
          have hcpos : 0 < c := by omega
          exact Nat.succ_le_iff.mpr (Nat.mul_pos hcpos hp.pos)
        have hzChildRaw : (c * p) * (q * primeFaceProduct t) = n := by
          calc
            (c * p) * (q * primeFaceProduct t) =
                (c * (q * primeFaceProduct t)) * p := by ring
            _ = m * p := by rw [hychild]
            _ = n := hmp
        have hzChild : orderedEulerCutChildInteger (t, (c * p, q)) = n := by
          exact hzChildRaw
        have hyLife :=
          (mem_orderedEulerCutCarrier_iff_shape_lifetime.mp hy).2
        have hyBirthRaw :
            max (primeFaceProduct t)
              (max (c + 1)
                (Nat.sqrt (c * (q * primeFaceProduct t)) + 1)) ≤ R := by
          simpa [orderedEulerCutBirthRoot, orderedEulerCutLowProduct,
            orderedEulerCutHighCofactor, orderedEulerCutChildInteger,
            orderedEulerCutPivot] using hyLife.1
        have hlowR : primeFaceProduct t ≤ R :=
          (Nat.max_le.mp hyBirthRaw).1
        have hdeathOld : R < q * primeFaceProduct t := by
          simpa [orderedEulerCutDeathRoot, orderedEulerCutPivot,
            orderedEulerCutLowProduct] using hyLife.2
        have hnewHighLt : c * p < R := by
          by_contra hnot
          have hhigh : R ≤ c * p := Nat.le_of_not_gt hnot
          have hdeathSucc : R + 1 ≤ q * primeFaceProduct t := by omega
          have hmul :
              R * (R + 1) ≤ (c * p) * (q * primeFaceProduct t) :=
            Nat.mul_le_mul hhigh hdeathSucc
          rw [hzChildRaw] at hmul
          have hRR : R ^ 2 < R * (R + 1) := by
            nlinarith
          omega
        have hbirth : orderedEulerCutBirthRoot (t, (c * p, q)) ≤ R := by
          change max (primeFaceProduct t)
            (max (c * p + 1)
              (Nat.sqrt ((c * p) * (q * primeFaceProduct t)) + 1)) ≤ R
          rw [hzChildRaw]
          apply Nat.max_le.mpr
          refine ⟨hlowR, Nat.max_le.mpr ⟨?_, ?_⟩⟩ <;> omega
        have hdeath : R < orderedEulerCutDeathRoot (t, (c * p, q)) := by
          simpa [orderedEulerCutDeathRoot, orderedEulerCutPivot,
            orderedEulerCutLowProduct] using hdeathOld
        have hmem : (t, (c * p, q)) ∈ orderedEulerCutCarrier R :=
          mem_orderedEulerCutCarrier_iff_shape_lifetime.mpr
            ⟨hzShape, hbirth, hdeath⟩
        apply Finset.mem_image.mpr
        exact ⟨(t, (c * p, q)), hmem, hzChild⟩

/-- **Exact active-child normal form.**  At every nontrivial root, the physical
vertical lines are precisely the squarefree integers in the open shell
`R < n < R^2`. -/
theorem orderedEulerCutActiveChildren_eq_squarefreeShell
    (R : ℕ) (hR : 2 ≤ R) :
    orderedEulerCutActiveChildren R = orderedEulerCutSquarefreeShell R := by
  ext n
  constructor
  · intro hn
    exact mem_orderedEulerCutSquarefreeShell.mpr
      ⟨orderedEulerCutActiveChild_root_lt hn,
        orderedEulerCutActiveChild_lt_root_sq hn,
        orderedEulerCutActiveChild_squarefree hn⟩
  · intro hn
    rcases mem_orderedEulerCutSquarefreeShell.mp hn with ⟨hRn, hnR, hsq⟩
    exact orderedEulerCutActiveChild_of_squarefree_shell hR hsq hRn hnR

/-- Membership in the vertical-line endpoint carrier is now a literal physical
squarefree-shell predicate. -/
theorem mem_orderedEulerCutActiveChildren_iff_squarefreeShell
    {R n : ℕ} (hR : 2 ≤ R) :
    n ∈ orderedEulerCutActiveChildren R ↔
      R < n ∧ n < R ^ 2 ∧ Squarefree n := by
  rw [orderedEulerCutActiveChildren_eq_squarefreeShell R hR]
  exact mem_orderedEulerCutSquarefreeShell

/-- Lower-wall crossing under one fresh prime. -/
def orderedEulerCutPrimeBirthBoundary (R p n : ℕ) : Prop :=
  n ≤ R ∧ R < p * n ∧ p * n < R ^ 2

/-- Upper-square-wall crossing under one fresh prime. -/
def orderedEulerCutPrimeTopEscapeBoundary (R p n : ℕ) : Prop :=
  R < n ∧ n < R ^ 2 ∧ R ^ 2 ≤ p * n

/-- A fresh-prime transition from inactive to active is exactly a lower-root
birth. -/
theorem orderedEulerCutPrime_inactive_to_active_iff_birth
    {R p n : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hsq : Squarefree n) (hpn : ¬ p ∣ n) :
    (p * n ∈ orderedEulerCutActiveChildren R ∧
        n ∉ orderedEulerCutActiveChildren R) ↔
      orderedEulerCutPrimeBirthBoundary R p n := by
  have hsqpn : Squarefree (p * n) :=
    (Nat.squarefree_mul ((hp.coprime_iff_not_dvd (n := n)).2 hpn)).2
      ⟨hp.squarefree, hsq⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hsq.ne_zero
  have hnle : n ≤ p * n := by
    have hp1 : 1 ≤ p := hp.one_le
    simpa [one_mul, Nat.mul_comm] using Nat.mul_le_mul_right n hp1
  constructor
  · rintro ⟨hpnActive, hnInactive⟩
    have hpData :=
      (mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).1 hpnActive
    have hnlt : n < R ^ 2 := hnle.trans_lt hpData.2.1
    have hnR : n ≤ R := by
      by_contra hnot
      have hRn : R < n := Nat.lt_of_not_ge hnot
      exact hnInactive
        ((mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).2
          ⟨hRn, hnlt, hsq⟩)
    exact ⟨hnR, hpData.1, hpData.2.1⟩
  · rintro ⟨hnR, hRpn, hpnlt⟩
    refine ⟨?_, ?_⟩
    · exact (mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).2
        ⟨hRpn, hpnlt, hsqpn⟩
    · intro hnActive
      have hnData :=
        (mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).1 hnActive
      omega

/-- A fresh-prime transition from active to inactive is exactly an upper-square
escape. -/
theorem orderedEulerCutPrime_active_to_inactive_iff_topEscape
    {R p n : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hsq : Squarefree n) (hpn : ¬ p ∣ n) :
    (n ∈ orderedEulerCutActiveChildren R ∧
        p * n ∉ orderedEulerCutActiveChildren R) ↔
      orderedEulerCutPrimeTopEscapeBoundary R p n := by
  have hsqpn : Squarefree (p * n) :=
    (Nat.squarefree_mul ((hp.coprime_iff_not_dvd (n := n)).2 hpn)).2
      ⟨hp.squarefree, hsq⟩
  have hnle : n ≤ p * n := by
    have hp1 : 1 ≤ p := hp.one_le
    simpa [one_mul, Nat.mul_comm] using Nat.mul_le_mul_right n hp1
  constructor
  · rintro ⟨hnActive, hpnInactive⟩
    have hnData :=
      (mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).1 hnActive
    have hsqWall : R ^ 2 ≤ p * n := by
      by_contra hnot
      have hpnlt : p * n < R ^ 2 := Nat.lt_of_not_ge hnot
      have hRpn : R < p * n := hnData.1.trans_le hnle
      exact hpnInactive
        ((mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).2
          ⟨hRpn, hpnlt, hsqpn⟩)
    exact ⟨hnData.1, hnData.2.1, hsqWall⟩
  · rintro ⟨hRn, hnlt, hwall⟩
    refine ⟨?_, ?_⟩
    · exact (mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).2
        ⟨hRn, hnlt, hsq⟩
    · intro hpnActive
      have hpData :=
        (mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).1 hpnActive
      omega

/-- **Endpoint-instability identification.**  Under a fresh prime, endpoint
membership changes if and only if that prime crosses one of the two physical
walls: lower-root birth or upper-square escape. -/
theorem orderedEulerCutPrime_membership_unstable_iff_birth_or_topEscape
    {R p n : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hsq : Squarefree n) (hpn : ¬ p ∣ n) :
    ¬ ((p * n ∈ orderedEulerCutActiveChildren R) ↔
        n ∈ orderedEulerCutActiveChildren R) ↔
      orderedEulerCutPrimeBirthBoundary R p n ∨
        orderedEulerCutPrimeTopEscapeBoundary R p n := by
  constructor
  · intro hunstable
    by_cases hpActive : p * n ∈ orderedEulerCutActiveChildren R
    · have hnInactive : n ∉ orderedEulerCutActiveChildren R := by
        intro hnActive
        exact hunstable ⟨fun _ => hnActive, fun _ => hpActive⟩
      exact Or.inl
        ((orderedEulerCutPrime_inactive_to_active_iff_birth
          hR hp hsq hpn).1 ⟨hpActive, hnInactive⟩)
    · have hnActive : n ∈ orderedEulerCutActiveChildren R := by
        by_contra hnInactive
        exact hunstable
          ⟨fun hpMem => (hpActive hpMem).elim,
            fun hnMem => (hnInactive hnMem).elim⟩
      exact Or.inr
        ((orderedEulerCutPrime_active_to_inactive_iff_topEscape
          hR hp hsq hpn).1 ⟨hnActive, hpActive⟩)
  · intro hboundary hstable
    rcases hboundary with hbirth | hescape
    · have hstatus :=
        (orderedEulerCutPrime_inactive_to_active_iff_birth
          hR hp hsq hpn).2 hbirth
      exact hstatus.2 (hstable.1 hstatus.1)
    · have hstatus :=
        (orderedEulerCutPrime_active_to_inactive_iff_topEscape
          hR hp hsq hpn).2 hescape
      exact hstatus.2 (hstable.2 hstatus.1)

/-- **Covariance-mask boundary identification.**  Any fresh-prime failure of
the line-event mask is owned at one of the two run endpoints by the same
physical lower-root birth or upper-square top-escape wall.  Thus mask
instability is not an additional covariance population. -/
theorem signedVerticalLineEventMask_prime_unstable_imp_birth_or_topEscape
    {a b p n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b + 1)
    (hp : p.Prime) (hsq : Squarefree n) (hpn : ¬ p ∣ n)
    (hunstable : signedVerticalLineEventMask a b (p * n) ≠
      signedVerticalLineEventMask a b n) :
    (orderedEulerCutPrimeBirthBoundary a p n ∨
      orderedEulerCutPrimeTopEscapeBoundary a p n) ∨
    (orderedEulerCutPrimeBirthBoundary (b + 1) p n ∨
      orderedEulerCutPrimeTopEscapeBoundary (b + 1) p n) := by
  rcases signedVerticalLineEventMask_prime_unstable_imp_endpoint_unstable
      hunstable with hleft | hright
  · exact Or.inl
      ((orderedEulerCutPrime_membership_unstable_iff_birth_or_topEscape
        ha hp hsq hpn).1 hleft)
  · exact Or.inr
      ((orderedEulerCutPrime_membership_unstable_iff_birth_or_topEscape
        hb hp hsq hpn).1 hright)

end RHLean.Proof