import Mathlib
import RHLean.Analysis.NativePNTLogSums
import RHLean.Analysis.NativePNTEvolvingTailState
import RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence

/-!
# Structural obstruction for the absolute evolving-tail state

The current evolving-tail recurrence self-composes a nonnegative one-log
remainder profile. Its canonical first remainder contains the absolute
factorial defect centered at `N log N`, so the sharp factorial estimate forces
a linear floor. Self-composition then multiplies that floor by `log N`.

The final theorem below applies to the whole evolving cost, not just the second
remainder. The exact tail/small reciprocal partition cancels the small
reciprocal mass between the kernel defect and small-quotient excess, leaving at
most `alpha * N * log(N)^2` of negative compensation outside the positive
second remainder.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The canonical first absolute remainder contains the linear factorial floor
coming from `log(N!) = N log N - N + 1 + O(log N)`. -/
theorem nativePNTFirstRemainder_ge_linear_sub_log
    (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) - 1 - Real.log (N : ℝ) ≤ nativePNTFirstRemainder N := by
  have hfac := nativeLogFactorial_sub_main_abs_le N hN
  have hfacUpper :
      Real.log ((Nat.factorial N : ℕ) : ℝ) -
          ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1) ≤
        Real.log (N : ℝ) :=
    (abs_le.mp hfac).2
  have hneg :
      (N : ℝ) - 1 - Real.log (N : ℝ) ≤
        -(Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log (N : ℝ)) := by
    linarith
  calc
    (N : ℝ) - 1 - Real.log (N : ℝ) ≤
        -(Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log (N : ℝ)) := hneg
    _ ≤ |Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log (N : ℝ)| := neg_le_abs _
    _ ≤ |nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ)| :=
      le_add_of_nonneg_left (abs_nonneg _)
    _ = nativePNTFirstRemainder N := by
      rfl

/-- The canonical first remainder is nonnegative. -/
theorem nativePNTFirstRemainder_nonneg (N : ℕ) :
    0 ≤ nativePNTFirstRemainder N := by
  unfold nativePNTFirstRemainder
  positivity

/-- The first von-Mangoldt absolute error mass is nonnegative. -/
theorem nativeLambdaErrorMass_nonneg (N : ℕ) :
    0 ≤ nativeLambdaErrorMass N := by
  unfold nativeLambdaErrorMass
  apply Finset.sum_nonneg
  intro d _hd
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)

/-- Pushing the canonical first remainder through reciprocal von-Mangoldt
fibres preserves nonnegativity. -/
theorem nativeLambdaRemainderMass_first_nonneg (N : ℕ) :
    0 ≤ nativeLambdaRemainderMass nativePNTFirstRemainder N := by
  unfold nativeLambdaRemainderMass
  apply Finset.sum_nonneg
  intro d _hd
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (nativePNTFirstRemainder_nonneg (N / d))

/-- The canonical second remainder contains the endpoint first remainder times
`log N` as an explicit summand. -/
theorem nativePNTSecondRemainder_ge_first_mul_log (N : ℕ) :
    nativePNTFirstRemainder N * Real.log (N : ℝ) ≤
      nativePNTSecondRemainder N := by
  have hE := nativeLambdaErrorMass_nonneg N
  have hR := nativeLambdaRemainderMass_first_nonneg N
  simp only [nativePNTSecondRemainder, nativePNTSecondRemainderFrom]
  linarith

/-- Consequently the second absolute remainder has an explicit `N log N`
scale floor. -/
theorem nativePNTSecondRemainder_ge_linear_log_floor
    (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) - 1 - Real.log (N : ℝ)) * Real.log (N : ℝ) ≤
      nativePNTSecondRemainder N := by
  have hfirst := nativePNTFirstRemainder_ge_linear_sub_log N hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hmul := mul_le_mul_of_nonneg_right hfirst hlog0
  exact hmul.trans (nativePNTSecondRemainder_ge_first_mul_log N)

/-- Reciprocal `Lambda_2` mass on the contracted quotient tail is nonnegative. -/
theorem nativeLambdaTwoTailRecipMass_nonneg (N M : ℕ) :
    0 ≤ nativeLambdaTwoTailRecipMass N M := by
  unfold nativeLambdaTwoTailRecipMass nativePNTSquarePrefixTailFiberSet
  apply Finset.sum_nonneg
  intro n hn
  have hnI : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- The exact small-quotient error mass is nonnegative before subtracting the
current tail slope. -/
theorem nativeLambdaTwoSmallQuotientErrorMass_nonneg (N M : ℕ) :
    0 ≤ nativeLambdaTwoSmallQuotientErrorMass N M := by
  unfold nativeLambdaTwoSmallQuotientErrorMass
    nativePNTSquarePrefixSmallQuotientFiberSet
  apply Finset.sum_nonneg
  intro n hn
  have hnI : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  exact mul_nonneg (nativeLambdaTwo_nonneg n hn1) (abs_nonneg _)

/-- **Full structural obstruction.** In the canonical positive remainder state,
the exact tail/small partition cancels the small reciprocal mass between the
kernel defect and finite-prefix excess. Thus the entire evolving cost is
bounded below by the unavoidable second-remainder floor minus only
`alpha * N * log(N)^2`.

At every fixed polynomial scale `N = alpha^(-r)`, the ratio of this `N log N`
floor to a cubic `alpha^3 N log(N)^2` budget diverges as `alpha -> 0`. -/
theorem nativePNTEvolvingTailCost_ge_canonical_obstruction
    (N M : ℕ) (alpha : ℝ)
    (hN : 1 ≤ N) (halpha : 0 ≤ alpha) :
    ((N : ℝ) - 1 - Real.log (N : ℝ)) * Real.log (N : ℝ) -
        alpha * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
      nativePNTEvolvingTailCost nativePNTFirstRemainder N M alpha := by
  have hsecond := nativePNTSecondRemainder_ge_linear_log_floor N hN
  have hsecond' :
      ((N : ℝ) - 1 - Real.log (N : ℝ)) * Real.log (N : ℝ) ≤
        nativePNTSecondRemainderFrom nativePNTFirstRemainder N := by
    simpa [nativePNTSecondRemainder] using hsecond
  have htail := nativeLambdaTwoTailRecipMass_nonneg N M
  have hsmall := nativeLambdaTwoSmallQuotientErrorMass_nonneg N M
  have halphaN : 0 ≤ alpha * (N : ℝ) :=
    mul_nonneg halpha (by positivity)
  have htailTerm :
      0 ≤ alpha * (N : ℝ) * nativeLambdaTwoTailRecipMass N M :=
    mul_nonneg halphaN htail
  have hsplit := nativeLambdaTwoTailRecipMass_add_small_eq N M
  unfold nativePNTEvolvingTailCost nativePNTSmallQuotientExcess
    nativeLambdaTwoRecipDefect
  rw [← hsplit]
  nlinarith

/-! ## Subdoubling obstruction for moving cutoffs -/

/-- The second von Mangoldt kernel has zero mass at the trivial reciprocal
fibre. -/
theorem nativeLambdaTwo_one : nativeLambdaTwo 1 = 0 := by
  rw [nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution]
  simp [arithmeticLogWeight_apply]

/-- If the new endpoint has not even doubled the old tail cutoff, the only
possible reciprocal tail fibre at that endpoint is `n = 1`, whose `Lambda_2`
weight is zero.  Hence the entire good-tail reciprocal mass vanishes, for every
candidate contracted slope `beta`.

This is exactly the geometry of consecutive square cutoffs: their ratio tends
to one, not two. -/
theorem nativeLambdaTwoGoodTailRecipMass_eq_zero_of_lt_two_mul
    (N M : ℕ) (beta : ℝ) (hNM : N < 2 * M) :
    nativeLambdaTwoGoodTailRecipMass N M beta = 0 := by
  classical
  unfold nativeLambdaTwoGoodTailRecipMass
    nativePNTSquarePrefixGoodTailFiberSet nativePNTSquarePrefixTailFiberSet
  apply Finset.sum_eq_zero
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnTail, _hnGood⟩
  rcases Finset.mem_filter.mp hnTail with ⟨hnI, hMdiv⟩
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  have hnEq : n = 1 := by
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    have hMn : M * n ≤ N :=
      (Nat.le_div_iff_mul_le (by omega : 0 < n)).1 hMdiv
    have h2Mn : 2 * M ≤ M * n := by
      have h := Nat.mul_le_mul_left M hn2
      simpa [Nat.mul_comm] using h
    omega
  subst n
  simp [nativeLambdaTwo_one]

/-- **Exact obstruction to using the current one-step cubic consumer across a
subdoubling cutoff move.**  At the mandatory first endpoint `N = L`, the
positive good-tail term is identically zero whenever `L < 2*M`.  If the
already-proved canonical absolute-remainder floor is positive there, the net
gain is negative, so no positive cubic coefficient can satisfy
`CubicGainFromTo M L alpha c`.

No asymptotic estimate and no affine/onset argument is used. -/
theorem primeSieveStateDependentSelberg_no_positive_cubicGainFromTo_of_subdoubling
    (M L : ℕ) (alpha c : ℝ)
    (hL : 3 ≤ L) (hLM : L < 2 * M)
    (halpha : 0 < alpha) (hc : 0 < c)
    (hobs :
      alpha * (L : ℝ) * (Real.log (L : ℝ)) ^ 2 <
        ((L : ℝ) - 1 - Real.log (L : ℝ)) * Real.log (L : ℝ)) :
    ¬ PrimeSieveStateDependentSelbergCubicGainFromTo M L alpha c := by
  intro hgain
  rcases hgain with ⟨_hML, hgain⟩
  rcases hgain L le_rfl with ⟨beta, _hbeta0, _hbeta, hpower⟩
  have hgood0 :=
    nativeLambdaTwoGoodTailRecipMass_eq_zero_of_lt_two_mul L M beta hLM
  have hcost := nativePNTEvolvingTailCost_ge_canonical_obstruction
    L M alpha (by omega) halpha.le
  have hnetNeg :
      primeSieveStateDependentSelbergNetGain L M alpha beta < 0 := by
    rw [primeSieveStateDependentSelbergNetGain_eq, hgood0]
    nlinarith
  have hLR : 0 < (L : ℝ) := by
    exact_mod_cast (show 0 < L by omega)
  have hlog : 0 < Real.log (L : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < L by omega)
  have hlhs :
      0 < c * alpha ^ 3 * (L : ℝ) * (Real.log (L : ℝ)) ^ 2 := by
    positivity
  unfold PrimeSieveStateDependentSelbergStateHasPowerGain at hpower
  linarith

end RHLean.Analysis
