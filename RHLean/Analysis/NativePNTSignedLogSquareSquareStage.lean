import Mathlib
import RHLean.Analysis.NativePNTSignedLogSquareDyadicCell
import RHLean.Analysis.NativePNTSummatorySelberg
import RHLean.Analysis.PrimeSieveBaseEightShallowAttack

/-!
# Square-stage realization of the signed log-square cells

This module places the signed `Lambda_2` dyadic cell on the repository's
actual square-block and exact-activity prime-wheel coordinate.

At the complete-square endpoint

`X_t = (t+1)^2 - 1`,

and for a transition cofactor `t/4 < c <= t/2`, the exact active-prime packet
is literally the reciprocal band

`X_t/(2c) < q <= X_t/c`.

Thus the two Chebyshev endpoints in

`Lambda_2(c) * (E(X_t/c) - E(X_t/(2c)))`

are not free reciprocal samples: they are the two endpoints of one genuine
square-stage exact-activity packet.  The final theorems transport the existing
same-sign signed surplus and opposite-sign no-crossing alternative onto this
packet coordinate.  No Selberg remainder is estimated here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Region II from the dyadic square-stage packet decomposition:
`t/4 < c <= t/2`. -/
def nativePNTSquareStageTransitionCofactors (t : ℕ) : Finset ℕ :=
  Finset.Icc (t / 4 + 1) (t / 2)

/-- Membership in the transition block gives the upper half-scale condition
needed for the exact-activity lower endpoint to be `X_t/(2c)`. -/
theorem nativePNTSquareStageTransitionCofactor_two_mul_le
    {t c : ℕ} (hc : c ∈ nativePNTSquareStageTransitionCofactors t) :
    2 * c ≤ t := by
  have hcI := Finset.mem_Icc.mp hc
  have hhalf : 2 * (t / 2) ≤ t := by omega
  exact (Nat.mul_le_mul_left 2 hcI.2).trans hhalf

/-- Every transition cofactor is positive once the transition block is
occupied. -/
theorem nativePNTSquareStageTransitionCofactor_pos
    {t c : ℕ} (hc : c ∈ nativePNTSquareStageTransitionCofactors t) :
    0 < c := by
  have hcI := Finset.mem_Icc.mp hc
  omega

/-- Below the half-scale boundary, the square-stage reciprocal predecessor is
already beyond the square-root cutoff. -/
theorem nativePNTSquareStage_sqrt_le_dyadicLower
    (t c : ℕ) (hc : 1 ≤ c) (hct : 2 * c ≤ t) :
    t + 1 ≤ squarePrefixEndpoint t / (2 * c) := by
  have h2cpos : 0 < 2 * c := by omega
  apply (Nat.le_div_iff_mul_le h2cpos).2
  have hmul : (t + 1) * (2 * c) ≤ (t + 1) * t :=
    Nat.mul_le_mul_left (t + 1) hct
  have hlt : (t + 1) * t < (t + 1) * (t + 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self t) (by omega)
  have hsq : (t + 1) * (t + 1) = squarePrefixEndpoint t + 1 := by
    simpa [pow_two] using (squarePrefixEndpoint_add_one t).symm
  rw [hsq] at hlt
  omega

/-- **Architecture bridge.**  On the square-stage half-scale range, the
repository's exact active-prime interval is exactly the dyadic reciprocal band
used by the signed log-square cell. -/
theorem exactActivityPrimeInterval_eq_logSquareDyadicBand
    (t c : ℕ) (hc : 1 ≤ c) (hct : 2 * c ≤ t) :
    exactActivityPrimeInterval t c =
      (Finset.Ioc
        (squarePrefixEndpoint t / (2 * c))
        (squarePrefixEndpoint t / c)).filter Nat.Prime := by
  have hcpos : 0 < c := by omega
  rw [exactActivityPrimeInterval_eq_reciprocalPrimeBand t c hcpos]
  unfold primeSieveExactActivityReciprocalPrimeBand
  have hlower := nativePNTSquareStage_sqrt_le_dyadicLower t c hc hct
  change
    (Finset.Ioc
      (max (t + 1) (squarePrefixEndpoint t / (2 * c)))
      (squarePrefixEndpoint t / c)).filter Nat.Prime =
      (Finset.Ioc
        (squarePrefixEndpoint t / (2 * c))
        (squarePrefixEndpoint t / c)).filter Nat.Prime
  rw [max_eq_right hlower]

/-- Transition-block specialization of the exact architecture bridge. -/
theorem exactActivityPrimeInterval_eq_logSquareDyadicBand_of_transition
    {t c : ℕ} (hc : c ∈ nativePNTSquareStageTransitionCofactors t) :
    exactActivityPrimeInterval t c =
      (Finset.Ioc
        (squarePrefixEndpoint t / (2 * c))
        (squarePrefixEndpoint t / c)).filter Nat.Prime := by
  exact exactActivityPrimeInterval_eq_logSquareDyadicBand t c
    (nativePNTSquareStageTransitionCofactor_pos hc)
    (nativePNTSquareStageTransitionCofactor_two_mul_le hc)

/-- The Chebyshev error increment across one exact square-stage activity packet. -/
def nativePNTSquareStageExactActivityErrorIncrement (t c : ℕ) : ℝ :=
  nativePNTError (squarePrefixEndpoint t / c) -
    nativePNTError (squarePrefixEndpoint t / (2 * c))

/-- The positive-kernel dyadic cell is exactly the error increment across the
same two endpoints as the square-stage exact-activity packet. -/
theorem nativePNTLambdaTwoDyadicSignedCell_squareStage_eq
    (t c : ℕ) :
    nativePNTLambdaTwoDyadicSignedCell (squarePrefixEndpoint t) c =
      nativeLambdaTwo c * nativePNTSquareStageExactActivityErrorIncrement t c := by
  rfl

/-- Same-sign beta-bad endpoints of one transition packet release the existing
positive `Lambda_2` local charge, now on the genuine square-stage coordinate. -/
theorem nativePNTSquareStageTransition_absSurplus_ge_of_bad_sameSign
    (t c : ℕ) (beta : ℝ)
    (hc : c ∈ nativePNTSquareStageTransitionCofactors t)
    (hbeta : 0 ≤ beta)
    (hsource :
      beta * ((squarePrefixEndpoint t / c : ℕ) : ℝ) ≤
        |nativePNTError (squarePrefixEndpoint t / c)|)
    (hchild :
      beta * ((squarePrefixEndpoint t / (2 * c) : ℕ) : ℝ) ≤
        |nativePNTError (squarePrefixEndpoint t / (2 * c))|)
    (hsign :
      (0 ≤ nativePNTError (squarePrefixEndpoint t / c) ∧
        0 ≤ nativePNTError (squarePrefixEndpoint t / (2 * c))) ∨
      (nativePNTError (squarePrefixEndpoint t / c) ≤ 0 ∧
        nativePNTError (squarePrefixEndpoint t / (2 * c)) ≤ 0)) :
    2 * beta * ((squarePrefixEndpoint t / (2 * c) : ℕ) : ℝ) *
        nativeLambdaTwo c ≤
      nativePNTLambdaTwoDyadicAbsSurplus (squarePrefixEndpoint t) c := by
  exact nativePNTLambdaTwoDyadicAbsSurplus_ge_of_bad_sameSign
    (squarePrefixEndpoint t) c beta
    (nativePNTSquareStageTransitionCofactor_pos hc) hbeta
    hsource hchild hsign

/-- Opposite-sign transition-packet endpoints force a beta-good integer inside
that very packet span once the native one-step no-crossing inequalities hold. -/
theorem nativePNTSquareStageTransition_exists_good_of_oppositeSign
    (t c : ℕ) (beta : ℝ)
    (hc : c ∈ nativePNTSquareStageTransitionCofactors t)
    (hbeta : 0 < beta)
    (hdown :
      1 < beta *
        (2 * ((squarePrefixEndpoint t / (2 * c) : ℕ) : ℝ) + 1))
    (hup :
      Real.log (((squarePrefixEndpoint t / c) + 1 : ℕ) : ℝ) - 1 <
        beta *
          (2 * ((squarePrefixEndpoint t / (2 * c) : ℕ) : ℝ) + 1))
    (hopposite :
      (nativePNTError (squarePrefixEndpoint t / (2 * c)) ≤ 0 ∧
        0 ≤ nativePNTError (squarePrefixEndpoint t / c)) ∨
      (nativePNTError (squarePrefixEndpoint t / c) ≤ 0 ∧
        0 ≤ nativePNTError (squarePrefixEndpoint t / (2 * c)))) :
    ∃ n ∈ Finset.Icc
        (squarePrefixEndpoint t / (2 * c))
        (squarePrefixEndpoint t / c),
      |nativePNTError n| < beta * (n : ℝ) := by
  have hcpos : 0 < c := nativePNTSquareStageTransitionCofactor_pos hc
  have hct : 2 * c ≤ t :=
    nativePNTSquareStageTransitionCofactor_two_mul_le hc
  have hA : 1 ≤ squarePrefixEndpoint t / (2 * c) := by
    have hsqrt := nativePNTSquareStage_sqrt_le_dyadicLower t c hcpos hct
    omega
  have hAB : squarePrefixEndpoint t / (2 * c) ≤ squarePrefixEndpoint t / c := by
    exact Nat.div_le_div_left (by omega) (by omega)
  exact nativePNTError_exists_beta_good_between_of_oppositeSign
    (squarePrefixEndpoint t / (2 * c))
    (squarePrefixEndpoint t / c) beta hA hAB hbeta hdown hup hopposite

/-! ## Quantitative mass of the genuine Region II packet family -/

/-- Total second-Selberg coefficient carried by the actual transition cofactors. -/
def nativePNTSquareStageTransitionLambdaTwoMass (t : ℕ) : ℝ :=
  ∑ c ∈ nativePNTSquareStageTransitionCofactors t, nativeLambdaTwo c

/-- At stages divisible by four, Region II is exactly the dyadic cofactor block
`(s, 2s]`. -/
theorem nativePNTSquareStageTransitionCofactors_four_mul (s : ℕ) :
    nativePNTSquareStageTransitionCofactors (4 * s) =
      Finset.Icc (s + 1) (2 * s) := by
  unfold nativePNTSquareStageTransitionCofactors
  have hfour : 4 * s / 4 = s := by omega
  have htwo : 4 * s / 2 = 2 * s := by omega
  rw [hfour, htwo]

/-- Therefore its coefficient mass is the exact increment of the summatory
second von Mangoldt kernel across `(s,2s]`. -/
theorem nativePNTSquareStageTransitionLambdaTwoMass_four_mul_eq
    (s : ℕ) (hs : 1 ≤ s) :
    nativePNTSquareStageTransitionLambdaTwoMass (4 * s) =
      nativeLambdaTwoSummatory (2 * s) - nativeLambdaTwoSummatory s := by
  unfold nativePNTSquareStageTransitionLambdaTwoMass
  rw [nativePNTSquareStageTransitionCofactors_four_mul]
  unfold nativeLambdaTwoSummatory
  have hsets :
      Finset.Icc 1 (2 * s) =
        Finset.Icc 1 s ∪ Finset.Icc (s + 1) (2 * s) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 1 s) (Finset.Icc (s + 1) (2 * s)) := by
    rw [Finset.disjoint_left]
    intro n hn hs'
    rw [Finset.mem_Icc] at hn hs'
    omega
  rw [hsets, Finset.sum_union hdis]
  ring

/-- On an explicit large square stage, the genuine Region II packets already
carry at least `s log s` of `Lambda_2` coefficient mass.  This theorem only
certifies the available packet resource; the decisive contraction must still
retain the signs of the cells in the signed second-Selberg recurrence. -/
theorem nativePNTSquareStageTransitionLambdaTwoMass_ge_mul_log
    (s : ℕ) (hs : 3 ≤ s)
    (hlarge :
      3 * (2 * (Real.log 4 + 2) + 172) ≤
        Real.log (s : ℝ) + 4 * Real.log 2) :
    (s : ℝ) * Real.log (s : ℝ) ≤
      nativePNTSquareStageTransitionLambdaTwoMass (4 * s) := by
  have hmass := nativePNTSquareStageTransitionLambdaTwoMass_four_mul_eq
    s (by omega)
  have hsBound := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le s hs
  have h2s : 3 ≤ 2 * s := by omega
  have h2Bound := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le (2 * s) h2s
  rw [abs_le] at hsBound h2Bound
  have hsUpper :
      nativeLambdaTwoSummatory s ≤
        2 * (s : ℝ) * Real.log (s : ℝ) +
          (2 * (Real.log 4 + 2) + 172) * (s : ℝ) := by
    linarith [hsBound.2]
  have h2Lower :
      2 * ((2 * s : ℕ) : ℝ) * Real.log ((2 * s : ℕ) : ℝ) -
          (2 * (Real.log 4 + 2) + 172) * ((2 * s : ℕ) : ℝ) ≤
        nativeLambdaTwoSummatory (2 * s) := by
    linarith [h2Bound.1]
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hlogmul :
      Real.log ((2 * s : ℕ) : ℝ) = Real.log 2 + Real.log (s : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (by norm_num) (ne_of_gt hspos)]
    norm_num
  rw [hlogmul] at h2Lower
  push_cast at h2Lower
  have hlargeMul :=
    mul_le_mul_of_nonneg_left hlarge (show (0 : ℝ) ≤ (s : ℝ) by positivity)
  rw [hmass]
  nlinarith [h2Lower, hsUpper, hlargeMul]

end RHLean.Analysis
