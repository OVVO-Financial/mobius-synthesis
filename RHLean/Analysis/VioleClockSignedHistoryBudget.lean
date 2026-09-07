import Mathlib
import RHLean.Analysis.OriginalVioleFunction

/-!
# Signed-history budget for direct Viole cutoff propagation

The adjacent square block is a seed, not a uniform payment at every later
endpoint. Strong induction supplies the new slope on all proper reciprocal
quotients already beyond `L`; the old tail supplies the transition strip
`M <= q < L`; only the finite history `q < M` remains signed.

This module packages the exact propagation budget. Its subdoubling seed
specialization is deliberately analyzed below: at `N = L` the recursive and
transition ledgers vanish, so the signed-history residual is exactly the
current normalized endpoint error times `log L`. Thus the seed clause itself
is equivalent to the desired endpoint contraction; the genuinely new
arithmetic input must enter before this consumer, through a local signed
comparison of the old endpoint with the new square-block response.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The normalized floor average restricted to a finite divisor carrier. -/
def nativePNTNormalizedFloorAverageOn
    (N : Nat) (S : Finset Nat) : Real :=
  ∑ d ∈ S,
    nativePNTNormalizedFloorWeight N d * nativePNTNormalizedError (N / d)

/-- Recursive part: quotients already at or above the new cutoff `L`. -/
def nativePNTDirectCutoffRecursiveAverage
    (N L : Nat) : Real :=
  nativePNTNormalizedFloorAverageOn N
    (nativePNTSquarePrefixTailFiberSet N L)

/-- Old-only transition part: `M <= floor(N/d) < L`. -/
def nativePNTDirectCutoffTransitionAverage
    (N M L : Nat) : Real :=
  nativePNTNormalizedFloorAverageOn N
    (nativePNTDirectCutoffTransitionDivisorSet N M L)

/-- Signed finite history: quotients strictly below the old cutoff `M`. -/
def nativePNTDirectCutoffHistoryAverage
    (N M : Nat) : Real :=
  nativePNTNormalizedFloorAverageOn N
    (nativePNTSquarePrefixSmallQuotientFiberSet N M)

/-- Total normalized floor weight on the recursively controlled region. -/
def nativePNTDirectCutoffRecursiveWeight
    (N L : Nat) : Real :=
  ∑ d ∈ nativePNTSquarePrefixTailFiberSet N L,
    nativePNTNormalizedFloorWeight N d

/-- Total normalized floor weight on the old-only transition annulus. -/
def nativePNTDirectCutoffTransitionWeight
    (N M L : Nat) : Real :=
  ∑ d ∈ nativePNTDirectCutoffTransitionDivisorSet N M L,
    nativePNTNormalizedFloorWeight N d

/-- The full normalized floor average splits exactly into recursively controlled,
transition, and finite-history pieces. -/
theorem nativePNTNormalizedFloorAverage_eq_recursive_add_transition_add_history
    (N M L : Nat) (hML : M <= L) :
    nativePNTNormalizedFloorAverage N =
      nativePNTDirectCutoffRecursiveAverage N L +
        nativePNTDirectCutoffTransitionAverage N M L +
          nativePNTDirectCutoffHistoryAverage N M := by
  let f : Nat -> Real := fun d =>
    nativePNTNormalizedFloorWeight N d * nativePNTNormalizedError (N / d)
  have hsplitL :
      (∑ d ∈ nativePNTSquarePrefixTailFiberSet N L, f d) +
          (∑ d ∈ nativePNTSquarePrefixSmallQuotientFiberSet N L, f d) =
        ∑ d ∈ Finset.Icc 1 N, f d := by
    unfold nativePNTSquarePrefixTailFiberSet
      nativePNTSquarePrefixSmallQuotientFiberSet
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.Icc 1 N)
        (p := fun d => L <= N / d)
        (f := f))
  have hsubset :
      nativePNTSquarePrefixSmallQuotientFiberSet N M ⊆
        nativePNTSquarePrefixSmallQuotientFiberSet N L := by
    intro d hd
    unfold nativePNTSquarePrefixSmallQuotientFiberSet at hd ⊢
    rcases Finset.mem_filter.mp hd with ⟨hdI, hdq⟩
    exact Finset.mem_filter.mpr ⟨hdI, hdq.trans_le hML⟩
  have hsplitSmall := Finset.sum_sdiff hsubset (f := f)
  unfold nativePNTNormalizedFloorAverage
    nativePNTDirectCutoffRecursiveAverage
    nativePNTDirectCutoffTransitionAverage
    nativePNTDirectCutoffHistoryAverage
    nativePNTNormalizedFloorAverageOn
    nativePNTDirectCutoffTransitionDivisorSet
  dsimp [f] at hsplitL hsplitSmall ⊢
  linarith

/-- Recursive region estimate furnished by the strong-induction hypothesis.
The `d=1` fibre has zero von-Mangoldt weight; every other quotient is strictly
smaller than `N`. -/
theorem nativePNTDirectCutoffRecursiveAverage_abs_le
    (N L : Nat) (alpha' : Real)
    (hN : 1 <= N) (_hL : L <= N) (_halpha' : 0 <= alpha')
    (hnew : forall q : Nat, L <= q -> q < N ->
      |nativePNTError q| <= alpha' * (q : Real)) :
    |nativePNTDirectCutoffRecursiveAverage N L| <=
      alpha' * nativePNTDirectCutoffRecursiveWeight N L := by
  unfold nativePNTDirectCutoffRecursiveAverage
    nativePNTNormalizedFloorAverageOn nativePNTDirectCutoffRecursiveWeight
  calc
    |∑ d ∈ nativePNTSquarePrefixTailFiberSet N L,
        nativePNTNormalizedFloorWeight N d * nativePNTNormalizedError (N / d)| <=
      ∑ d ∈ nativePNTSquarePrefixTailFiberSet N L,
        |nativePNTNormalizedFloorWeight N d * nativePNTNormalizedError (N / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ d ∈ nativePNTSquarePrefixTailFiberSet N L,
        nativePNTNormalizedFloorWeight N d * alpha' := by
      apply Finset.sum_le_sum
      intro d hd
      have hdI := (Finset.mem_filter.mp hd).1
      have hLd : L <= N / d := (Finset.mem_filter.mp hd).2
      have hw0 := nativePNTNormalizedFloorWeight_nonneg N d
      by_cases hd1 : d = 1
      · subst d
        have hLambda1 : Λ 1 = 0 := by simp
        unfold nativePNTNormalizedFloorWeight
        simp [hLambda1]
      · have hd2 : 2 <= d := by
          have hdpos : 1 <= d := (Finset.mem_Icc.mp hdI).1
          omega
        have hqLt : N / d < N :=
          nativePNTDirectCutoff_recursive_quotient_lt N d hN hd2
        have hraw := hnew (N / d) hLd hqLt
        have hqNat : 0 < N / d := by
          have hdpos : 0 < d := by omega
          exact Nat.div_pos (Finset.mem_Icc.mp hdI).2 hdpos
        have hqpos : (0 : Real) < ((N / d : Nat) : Real) := by
          exact_mod_cast hqNat
        have hnorm : |nativePNTNormalizedError (N / d)| <= alpha' := by
          unfold nativePNTNormalizedError
          rw [abs_div, abs_of_pos hqpos]
          exact (div_le_iff₀ hqpos).2 hraw
        rw [abs_mul, abs_of_nonneg hw0]
        exact mul_le_mul_of_nonneg_left hnorm hw0
    _ = alpha' *
        (∑ d ∈ nativePNTSquarePrefixTailFiberSet N L,
          nativePNTNormalizedFloorWeight N d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring

/-- Transition-region estimate from the old true tail. -/
theorem nativePNTDirectCutoffTransitionAverage_abs_le
    (N M L : Nat) (alpha : Real)
    (_halpha : 0 <= alpha)
    (hold : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real)) :
    |nativePNTDirectCutoffTransitionAverage N M L| <=
      alpha * nativePNTDirectCutoffTransitionWeight N M L := by
  unfold nativePNTDirectCutoffTransitionAverage
    nativePNTNormalizedFloorAverageOn nativePNTDirectCutoffTransitionWeight
  calc
    |∑ d ∈ nativePNTDirectCutoffTransitionDivisorSet N M L,
        nativePNTNormalizedFloorWeight N d * nativePNTNormalizedError (N / d)| <=
      ∑ d ∈ nativePNTDirectCutoffTransitionDivisorSet N M L,
        |nativePNTNormalizedFloorWeight N d * nativePNTNormalizedError (N / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ d ∈ nativePNTDirectCutoffTransitionDivisorSet N M L,
        nativePNTNormalizedFloorWeight N d * alpha := by
      apply Finset.sum_le_sum
      intro d hd
      have hdq := (mem_nativePNTDirectCutoffTransitionDivisorSet_iff N M L d).mp hd
      have hw0 := nativePNTNormalizedFloorWeight_nonneg N d
      have hraw := hold (N / d) hdq.2.1
      have hdI := Finset.mem_Icc.mp hdq.1
      have hqNat : 0 < N / d := by
        have hdpos : 0 < d := by omega
        exact Nat.div_pos hdI.2 hdpos
      have hqpos : (0 : Real) < ((N / d : Nat) : Real) := by
        exact_mod_cast hqNat
      have hnorm : |nativePNTNormalizedError (N / d)| <= alpha := by
        unfold nativePNTNormalizedError
        rw [abs_div, abs_of_pos hqpos]
        exact (div_le_iff₀ hqpos).2 hraw
      rw [abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_left hnorm hw0
    _ = alpha *
        (∑ d ∈ nativePNTDirectCutoffTransitionDivisorSet N M L,
          nativePNTNormalizedFloorWeight N d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring

/-- Signed finite-history residual left after removing all quotients below `M`
from the exact normalized Selberg remainder. -/
def nativePNTDirectCutoffSignedHistoryResidual
    (N M : Nat) : Real :=
  nativePNTNormalizedExactSignedRemainder N -
    nativePNTDirectCutoffHistoryAverage N M

/-- **Reduced endpoint budget.** There is no occurrence of the current
endpoint error on the right. Recursive quotient mass is charged at `alpha'`,
the old-only transition annulus at `alpha`, and the sub-`M` history remains
signed inside one residual. -/
def NativePNTDirectCutoffSignedHistoryBudgetLaw
    (M L : Nat) (alpha alpha' : Real) : Prop :=
  2 <= M ∧ M <= L ∧ 0 < alpha' ∧ alpha' <= alpha ∧
    forall N : Nat, L <= N ->
      |nativePNTDirectCutoffSignedHistoryResidual N M| +
          alpha' * nativePNTDirectCutoffRecursiveWeight N L +
          alpha * nativePNTDirectCutoffTransitionWeight N M L <=
        alpha' * Real.log (N : Real)

/-- The signed-history budget supplies the local strong-induction step. -/
theorem nativePNTDirectCutoffInductionLaw_of_signedHistoryBudget
    (M L : Nat) (alpha alpha' : Real)
    (hlaw : NativePNTDirectCutoffSignedHistoryBudgetLaw M L alpha alpha') :
    NativePNTDirectCutoffInductionLaw M L alpha alpha' := by
  rcases hlaw with ⟨hM2, hML, halpha', hale, hbudget⟩
  refine ⟨hM2, hML, halpha', hale, ?_⟩
  intro N hLN hnew hold
  have hN1 : 1 <= N := by omega
  have hNpos : (0 : Real) < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hrec := nativePNTNormalized_signed_floor_recurrence_eq_exactRemainder N hN1
  have hsplit :=
    nativePNTNormalizedFloorAverage_eq_recursive_add_transition_add_history
      N M L hML
  have hrecursive :=
    nativePNTDirectCutoffRecursiveAverage_abs_le
      N L alpha' hN1 hLN halpha'.le hnew
  have htransition :=
    nativePNTDirectCutoffTransitionAverage_abs_le
      N M L alpha (by linarith) hold
  have hbud := hbudget N hLN
  have hidentity :
      nativePNTNormalizedError N * Real.log (N : Real) =
        nativePNTDirectCutoffSignedHistoryResidual N M -
          nativePNTDirectCutoffRecursiveAverage N L -
          nativePNTDirectCutoffTransitionAverage N M L := by
    unfold nativePNTDirectCutoffSignedHistoryResidual
    linarith
  have hmulAbs :
      |nativePNTNormalizedError N * Real.log (N : Real)| <=
        alpha' * Real.log (N : Real) := by
    rw [hidentity]
    calc
      |nativePNTDirectCutoffSignedHistoryResidual N M -
          nativePNTDirectCutoffRecursiveAverage N L -
          nativePNTDirectCutoffTransitionAverage N M L| <=
        |nativePNTDirectCutoffSignedHistoryResidual N M| +
          |nativePNTDirectCutoffRecursiveAverage N L| +
          |nativePNTDirectCutoffTransitionAverage N M L| := by
            calc
              |nativePNTDirectCutoffSignedHistoryResidual N M -
                  nativePNTDirectCutoffRecursiveAverage N L -
                  nativePNTDirectCutoffTransitionAverage N M L| <=
                |nativePNTDirectCutoffSignedHistoryResidual N M -
                    nativePNTDirectCutoffRecursiveAverage N L| +
                  |nativePNTDirectCutoffTransitionAverage N M L| := abs_sub _ _
              _ <= (|nativePNTDirectCutoffSignedHistoryResidual N M| +
                    |nativePNTDirectCutoffRecursiveAverage N L|) +
                  |nativePNTDirectCutoffTransitionAverage N M L| :=
                add_le_add_right (abs_sub _ _) _
              _ = _ := by ring
      _ <= |nativePNTDirectCutoffSignedHistoryResidual N M| +
          alpha' * nativePNTDirectCutoffRecursiveWeight N L +
          alpha * nativePNTDirectCutoffTransitionWeight N M L := by
        linarith
      _ <= alpha' * Real.log (N : Real) := hbud
  have hnorm : |nativePNTNormalizedError N| <= alpha' := by
    rw [abs_mul, abs_of_pos hlog] at hmulAbs
    have hmulAbs' :
        Real.log (N : Real) * |nativePNTNormalizedError N| <=
          Real.log (N : Real) * alpha' := by
      simpa [mul_comm] using hmulAbs
    exact (mul_le_mul_iff_right₀ hlog).mp hmulAbs'
  unfold nativePNTNormalizedError at hnorm
  rw [abs_div, abs_of_pos hNpos] at hnorm
  exact (div_le_iff₀ hNpos).1 hnorm

/-- **Direct tail advance from the reduced signed-history budget.** -/
theorem primeSieveStateDependentSelberg_tailAbove_of_signedHistoryBudget
    (M L : Nat) (alpha alpha' : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hlaw : NativePNTDirectCutoffSignedHistoryBudgetLaw M L alpha alpha') :
    PrimeSieveStateDependentSelbergTailAbove L alpha' := by
  exact nativePNTDirectCutoffInductionLaw_step M L alpha alpha' htail
    (nativePNTDirectCutoffInductionLaw_of_signedHistoryBudget
      M L alpha alpha' hlaw)

/-! ## Exact seed specialization -/

/-- At the first endpoint `N = L`, the recursively controlled average vanishes:
there is no proper quotient `q` with `L <= q < L`, and the only endpoint fibre
`d = 1` has von-Mangoldt weight zero. -/
theorem nativePNTDirectCutoffRecursiveAverage_endpoint_eq_zero
    (L : Nat) (hL : 1 <= L) :
    nativePNTDirectCutoffRecursiveAverage L L = 0 := by
  have hbound :=
    nativePNTDirectCutoffRecursiveAverage_abs_le L L 0 hL le_rfl le_rfl
      (fun q hLq hqL => by omega)
  have hle : |nativePNTDirectCutoffRecursiveAverage L L| <= 0 := by
    simpa using hbound
  have habs : |nativePNTDirectCutoffRecursiveAverage L L| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp habs

/-- At a subdoubling seed endpoint the transition average vanishes because the
moving old-only quotient annulus is empty. -/
theorem nativePNTDirectCutoffTransitionAverage_endpoint_eq_zero_of_subdoubling
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTDirectCutoffTransitionAverage L M L = 0 := by
  unfold nativePNTDirectCutoffTransitionAverage
  rw [nativePNTDirectCutoffTransitionDivisorSet_endpoint_eq_empty_of_subdoubling
    M L hM hML hsub]
  simp [nativePNTNormalizedFloorAverageOn]

/-- Therefore, at a subdoubling seed endpoint the finite-history average is the
entire normalized floor average. -/
theorem nativePNTDirectCutoffHistoryAverage_endpoint_eq_floorAverage_of_subdoubling
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTDirectCutoffHistoryAverage L M = nativePNTNormalizedFloorAverage L := by
  have hsplit :=
    nativePNTNormalizedFloorAverage_eq_recursive_add_transition_add_history
      L M L hML
  have hrec0 := nativePNTDirectCutoffRecursiveAverage_endpoint_eq_zero L
    (hM.trans hML)
  have htrans0 :=
    nativePNTDirectCutoffTransitionAverage_endpoint_eq_zero_of_subdoubling
      M L hM hML hsub
  rw [hrec0, htrans0] at hsplit
  simpa using hsplit.symm

/-- **Seed identity.** At `N = L < 2M`, the signed-history residual is
exactly the current normalized endpoint error times `log L`. Hence it contains
no smaller seed obligation by itself. -/
theorem nativePNTDirectCutoffSignedHistoryResidual_endpoint_eq_error_mul_log
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTDirectCutoffSignedHistoryResidual L M =
      nativePNTNormalizedError L * Real.log (L : Real) := by
  have hrec :=
    nativePNTNormalized_signed_floor_recurrence_eq_exactRemainder L
      (hM.trans hML)
  have hhist :=
    nativePNTDirectCutoffHistoryAverage_endpoint_eq_floorAverage_of_subdoubling
      M L hM hML hsub
  unfold nativePNTDirectCutoffSignedHistoryResidual
  rw [hhist]
  linarith

/-- The recursively controlled *weight* also vanishes at the seed endpoint. -/
theorem nativePNTDirectCutoffRecursiveWeight_endpoint_eq_zero
    (L : Nat) (hL : 1 <= L) :
    nativePNTDirectCutoffRecursiveWeight L L = 0 := by
  unfold nativePNTDirectCutoffRecursiveWeight nativePNTSquarePrefixTailFiberSet
  apply Finset.sum_eq_zero
  intro d hd
  rcases Finset.mem_filter.mp hd with ⟨hdI, hLd⟩
  have hd1 : d = 1 := by
    by_contra hne
    have hd2 : 2 <= d := by
      have hdpos : 1 <= d := (Finset.mem_Icc.mp hdI).1
      omega
    have hlt : L / d < L :=
      nativePNTDirectCutoff_recursive_quotient_lt L d hL hd2
    omega
  subst d
  simp [nativePNTNormalizedFloorWeight]

/-- The transition *weight* vanishes at the same subdoubling endpoint. -/
theorem nativePNTDirectCutoffTransitionWeight_endpoint_eq_zero_of_subdoubling
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTDirectCutoffTransitionWeight L M L = 0 := by
  unfold nativePNTDirectCutoffTransitionWeight
  rw [nativePNTDirectCutoffTransitionDivisorSet_endpoint_eq_empty_of_subdoubling
    M L hM hML hsub]
  simp

/-- The complete seed clause of the signed-history budget is equivalent to the
desired new-slope endpoint estimate. This is the exact reason the budget
is a propagation consumer rather than an independent seed theorem. -/
theorem nativePNTDirectCutoffSignedHistoryBudget_seed_iff_normalizedError
    (M L : Nat) (alpha alpha' : Real)
    (hM : 2 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    (|nativePNTDirectCutoffSignedHistoryResidual L M| +
          alpha' * nativePNTDirectCutoffRecursiveWeight L L +
          alpha * nativePNTDirectCutoffTransitionWeight L M L <=
        alpha' * Real.log (L : Real)) ↔
      |nativePNTNormalizedError L| <= alpha' := by
  have hM1 : 1 <= M := by omega
  have hL2 : 2 <= L := hM.trans hML
  have hlog : 0 < Real.log (L : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < L by omega)
  rw [nativePNTDirectCutoffSignedHistoryResidual_endpoint_eq_error_mul_log
      M L hM1 hML hsub,
    nativePNTDirectCutoffRecursiveWeight_endpoint_eq_zero L (by omega),
    nativePNTDirectCutoffTransitionWeight_endpoint_eq_zero_of_subdoubling
      M L hM1 hML hsub]
  simp only [mul_zero, add_zero, abs_mul, abs_of_pos hlog]
  exact mul_le_mul_iff_left₀ hlog

/-- The square-block von-Mangoldt discrepancy is exactly the change in the PNT
error across the block. This is the local signed object that must interact with
the old endpoint error to start a contracted square step. -/
theorem nativePNTError_sub_eq_lambdaSquareBlockMass_sub_length
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTError L - nativePNTError M =
      nativePNTLambdaSquareBlockMass M L - ((L - M : Nat) : Real) := by
  rw [nativePNTLambdaSquareBlockMass_eq_psi_sub M L hM hML]
  unfold nativePNTError
  rw [Nat.cast_sub hML]
  ring

end RHLean.Analysis