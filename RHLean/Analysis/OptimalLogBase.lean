import Mathlib
import RHLean.Analysis.VioleClockSignedHistoryBudget
import RHLean.Analysis.NativePNTSignedWheelRemainder
import RHLean.Analysis.BlockCovarianceDecomposition

/-!
# Exact optimum logarithmic base

For a real-valued counting function `P`, the logarithmic base that makes

`x / log_b(x) = P(x)`

is obtained exactly from change of base:

`log b = P(x) * log x / x`.

Thus

`b_opt(x) = exp (P(x) * log x / x) = x ^ (P(x) / x)`

on the positive real domain. When `P` is the prime-counting function, the
prime number theorem is precisely the statement that the exponent tends to
`1`; continuity of `exp` then gives `b_opt(x) -> e`.

This file deliberately states the asymptotic theorem against the PNT ratio as
an explicit hypothesis. It therefore isolates the elementary optimum-base
argument from whichever formal prime-number-theorem theorem is later used to
supply that hypothesis.
-/

noncomputable section

open Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Real logarithm to an arbitrary base, written by change of base. -/
def logBase (b x : ℝ) : ℝ :=
  Real.log x / Real.log b

/-- The exact logarithmic base that makes `x / log_b x` reproduce the supplied
counting function `P`, whenever the relevant denominators are nonzero. -/
def optimalLogBase (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (P x * Real.log x / x)

/-- The exact optimum logarithmic base is always positive. -/
theorem optimalLogBase_pos (P : ℝ → ℝ) (x : ℝ) :
    0 < optimalLogBase P x := by
  exact Real.exp_pos _

/-- The logarithm of the optimum base is exactly the normalized counting
ratio. -/
@[simp] theorem log_optimalLogBase (P : ℝ → ℝ) (x : ℝ) :
    Real.log (optimalLogBase P x) = P x * Real.log x / x := by
  simp [optimalLogBase]

/-- Multiplicative change-of-base form of the exact reconstruction identity. -/
theorem optimalLogBase_reconstructs_mul
    (P : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) :
    x * Real.log (optimalLogBase P x) / Real.log x = P x := by
  rw [log_optimalLogBase]
  field_simp

/-- Exact reconstruction in the original form `x / log_(b_opt x) x = P x`. -/
theorem x_div_logBase_optimalLogBase
    (P : ℝ → ℝ) {x : ℝ}
    (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) (hPx : P x ≠ 0) :
    x / logBase (optimalLogBase P x) x = P x := by
  rw [logBase, log_optimalLogBase]
  field_simp

/-- A prime-number-theorem ratio tending to `1` forces the corresponding exact
optimum logarithmic base to tend to Euler's number `e = exp 1`. -/
theorem optimalLogBase_tendsto_e
    (P : ℝ → ℝ)
    (hPNT : Tendsto (fun x : ℝ => P x * Real.log x / x) atTop (𝓝 1)) :
    Tendsto (optimalLogBase P) atTop (𝓝 (Real.exp 1)) := by
  have hExp : ContinuousAt Real.exp (1 : ℝ) := by
    fun_prop
  simpa [optimalLogBase, Function.comp_def] using hExp.tendsto.comp hPNT

/-- Equivalent formulation using the normalized ratio as a named function. -/
def normalizedCountingRatio (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  P x * Real.log x / x

@[simp] theorem optimalLogBase_eq_exp_normalizedCountingRatio
    (P : ℝ → ℝ) (x : ℝ) :
    optimalLogBase P x = Real.exp (normalizedCountingRatio P x) := by
  rfl

/-- The asymptotic result in terms of `normalizedCountingRatio`. -/
theorem optimalLogBase_tendsto_e_of_normalizedCountingRatio
    (P : ℝ → ℝ)
    (hPNT : Tendsto (normalizedCountingRatio P) atTop (𝓝 1)) :
    Tendsto (optimalLogBase P) atTop (𝓝 (Real.exp 1)) := by
  apply optimalLogBase_tendsto_e P
  simpa [normalizedCountingRatio] using hPNT

/-! ## Sequential cross energy for adjacent Viole blocks

The signed-history budget propagates a seed after the first endpoint, but
its subdoubling seed clause is equivalent to the desired endpoint contraction.
The non-circular seed therefore lives one level earlier: in the signed
interaction of the inherited endpoint error with the discrepancy created by the
new block.
-/

/-- Signed PNT-error discrepancy created between two physical cutoffs. -/
def nativePNTSequentialSquareBlockDiscrepancy (M L : Nat) : Real :=
  nativePNTError L - nativePNTError M

/-- Sequential old/new cross energy `X = E(M) * (E(L)-E(M))`. -/
def nativePNTSequentialSquareBlockCrossEnergy (M L : Nat) : Real :=
  nativePNTError M * nativePNTSequentialSquareBlockDiscrepancy M L

/-- The discrepancy is exactly the von-Mangoldt block discrepancy. -/
theorem nativePNTSequentialSquareBlockDiscrepancy_eq_lambdaMass_sub_length
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTSequentialSquareBlockDiscrepancy M L =
      nativePNTLambdaSquareBlockMass M L - ((L - M : Nat) : Real) := by
  unfold nativePNTSequentialSquareBlockDiscrepancy
  exact nativePNTError_sub_eq_lambdaSquareBlockMass_sub_length M L hM hML

/-- Exact two-block energy identity. The diagonal `D^2` and cross term `2X`
are the complete change in endpoint energy. -/
theorem nativePNTError_sq_sub_sq_eq_two_mul_crossEnergy_add_discrepancy_sq
    (M L : Nat) :
    nativePNTError L ^ 2 - nativePNTError M ^ 2 =
      2 * nativePNTSequentialSquareBlockCrossEnergy M L +
        nativePNTSequentialSquareBlockDiscrepancy M L ^ 2 := by
  unfold nativePNTSequentialSquareBlockCrossEnergy
    nativePNTSequentialSquareBlockDiscrepancy
  ring

/-- A cross-energy budget is a non-circular seed consumer. -/
theorem nativePNTSequentialCrossEnergy_seed_contraction
    (M L : Nat) (alpha alpha' : Real)
    (halpha : 0 <= alpha) (halpha' : 0 <= alpha')
    (hold : |nativePNTError M| <= alpha * (M : Real))
    (hcross :
      2 * nativePNTSequentialSquareBlockCrossEnergy M L +
          nativePNTSequentialSquareBlockDiscrepancy M L ^ 2 <=
        (alpha' * (L : Real)) ^ 2 - (alpha * (M : Real)) ^ 2) :
    |nativePNTError L| <= alpha' * (L : Real) := by
  have hMtarget0 : 0 <= alpha * (M : Real) :=
    mul_nonneg halpha (Nat.cast_nonneg M)
  have hLtarget0 : 0 <= alpha' * (L : Real) :=
    mul_nonneg halpha' (Nat.cast_nonneg L)
  have hMsq :
      nativePNTError M ^ 2 <= (alpha * (M : Real)) ^ 2 := by
    have habsSq :
        |nativePNTError M| ^ 2 <= (alpha * (M : Real)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hMtarget0).2 hold
    simpa [sq_abs] using habsSq
  have henergy :=
    nativePNTError_sq_sub_sq_eq_two_mul_crossEnergy_add_discrepancy_sq M L
  have hLsq :
      nativePNTError L ^ 2 <= (alpha' * (L : Real)) ^ 2 := by
    nlinarith
  have habsLsq :
      |nativePNTError L| ^ 2 <= (alpha' * (L : Real)) ^ 2 := by
    simpa [sq_abs] using hLsq
  exact (sq_le_sq₀ (abs_nonneg _) hLtarget0).1 habsLsq

/-- Signed PNT-error increment of one Viole clock block. -/
def violeClockErrorIncrement (r : Nat) : Real :=
  nativePNTError (violeClockCutoff (r + 1)) -
    nativePNTError (violeClockCutoff r)

/-- Viole block increments telescope exactly to the endpoint error. -/
theorem signedBlockPrefix_violeClockErrorIncrement (R : Nat) :
    signedBlockPrefix violeClockErrorIncrement R =
      nativePNTError (violeClockCutoff R) := by
  induction R with
  | zero =>
      simp [signedBlockPrefix, violeClockCutoff, nativePNTError, nativePsi]
  | succ R ih =>
      rw [signedBlockPrefix_succ, ih]
      unfold violeClockErrorIncrement
      ring

/-- Sequential cross energy at Viole block `r`. -/
def violeClockSequentialCrossEnergy (r : Nat) : Real :=
  nativePNTSequentialSquareBlockCrossEnergy
    (violeClockCutoff r) (violeClockCutoff (r + 1))

/-- `X_r` is literally the one-step increment of the repository's generic
signed-block cross covariance on the PNT-error block increments. -/
theorem violeClockSequentialCrossEnergy_eq_crossCovariance_increment
    (r : Nat) :
    violeClockSequentialCrossEnergy r =
      signedBlockCrossCovariance violeClockErrorIncrement (r + 1) -
        signedBlockCrossCovariance violeClockErrorIncrement r := by
  rw [signedBlockCrossCovariance_succ,
    signedBlockPrefix_violeClockErrorIncrement]
  unfold violeClockSequentialCrossEnergy
    nativePNTSequentialSquareBlockCrossEnergy
    nativePNTSequentialSquareBlockDiscrepancy
    violeClockErrorIncrement
  ring

/-! ## Exact shared/new fibre difference -/

/-- Shared old-fibre drift when the endpoint moves from `M` to `L`. -/
def nativePNTSequentialSharedFiberDrift (M L : Nat) : Real :=
  ∑ d ∈ Finset.Icc 1 M,
    Λ d * (nativePNTError (L / d) - nativePNTError (M / d))

/-- Genuinely new divisor fibres born in `(M,L]`. -/
def nativePNTSequentialNewFiberMass (M L : Nat) : Real :=
  ∑ d ∈ Finset.Ioc M L,
    Λ d * nativePNTError (L / d)

/-- The full signed reciprocal error-mass increment splits exactly into shared
old-fibre drift plus genuinely new fibres. -/
theorem nativePNTLambdaSignedErrorMass_sub_eq_shared_add_new
    (M L : Nat) (_hM : 1 <= M) (hML : M <= L) :
    (∑ d ∈ Finset.Icc 1 L, Λ d * nativePNTError (L / d)) -
        (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (M / d)) =
      nativePNTSequentialSharedFiberDrift M L +
        nativePNTSequentialNewFiberMass M L := by
  have hset :
      Finset.Icc 1 L = Finset.Icc 1 M ∪ Finset.Ioc M L := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Icc 1 M) (Finset.Ioc M L) := by
    rw [Finset.disjoint_left]
    intro d hdM hdBlock
    rw [Finset.mem_Icc] at hdM
    rw [Finset.mem_Ioc] at hdBlock
    omega
  have hsplit :
      (∑ d ∈ Finset.Icc 1 L, Λ d * nativePNTError (L / d)) =
        (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (L / d)) +
          ∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (L / d) := by
    rw [hset, Finset.sum_union hdis]
  rw [hsplit]
  unfold nativePNTSequentialSharedFiberDrift nativePNTSequentialNewFiberMass
  have hshared :
      (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (L / d)) -
          (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (M / d)) =
        ∑ d ∈ Finset.Icc 1 M,
          Λ d * (nativePNTError (L / d) - nativePNTError (M / d)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  calc
    (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (L / d)) +
          (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (L / d)) -
          (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (M / d)) =
      ((∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (L / d)) -
          (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (M / d))) +
        (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (L / d)) := by ring
    _ =
      (∑ d ∈ Finset.Icc 1 M,
        Λ d * (nativePNTError (L / d) - nativePNTError (M / d))) +
        (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (L / d)) := by
      rw [hshared]

/-- Exact difference of the signed Selberg recurrences at `M` and `L`. -/
theorem nativePNTSignedSelberg_recurrence_difference_eq_shared_add_new
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTError L * Real.log (L : Real) -
        nativePNTError M * Real.log (M : Real) +
        nativePNTSequentialSharedFiberDrift M L +
        nativePNTSequentialNewFiberMass M L =
      nativePNTSignedSelbergRemainder L - nativePNTSignedSelbergRemainder M := by
  have hLrec := nativePNTError_mul_log_add_mobiusSigned_eq_remainder L
  have hMrec := nativePNTError_mul_log_add_mobiusSigned_eq_remainder M
  rw [← nativeLambdaSignedErrorMass_eq_mobiusReciprocal] at hLrec hMrec
  have hsplit :=
    nativePNTLambdaSignedErrorMass_sub_eq_shared_add_new M L hM hML
  linarith

/-- At a subdoubling seed endpoint every new divisor has quotient one. -/
theorem nativePNTSequentialNewFiberMass_endpoint_of_subdoubling
    (M L : Nat) (hsub : L < 2 * M) :
    nativePNTSequentialNewFiberMass M L =
      -nativePNTLambdaSquareBlockMass M L := by
  unfold nativePNTSequentialNewFiberMass nativePNTLambdaSquareBlockMass
  calc
    (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (L / d)) =
        ∑ d ∈ Finset.Ioc M L, -(Λ d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdI := Finset.mem_Ioc.mp hd
      have hlo : 1 * d <= L := by simpa using hdI.2
      have hhi : L < (1 + 1) * d := by
        have htwo : 2 * M < 2 * d := by omega
        omega
      have hdiv : L / d = 1 := Nat.div_eq_of_lt_le hlo hhi
      rw [hdiv]
      simp [nativePNTError, nativePsi]
    _ = -(∑ d ∈ Finset.Ioc M L, Λ d) := by
      rw [Finset.sum_neg_distrib]

/-- Subdoubling recurrence difference after replacing new fibres by the exact
block mass. -/
theorem nativePNTSignedSelberg_recurrence_difference_subdoubling
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTError L * Real.log (L : Real) -
        nativePNTError M * Real.log (M : Real) +
        nativePNTSequentialSharedFiberDrift M L -
        nativePNTLambdaSquareBlockMass M L =
      nativePNTSignedSelbergRemainder L - nativePNTSignedSelbergRemainder M := by
  have h := nativePNTSignedSelberg_recurrence_difference_eq_shared_add_new
    M L hM hML
  rw [nativePNTSequentialNewFiberMass_endpoint_of_subdoubling M L hsub] at h
  linarith

/-- Exact seed equation in the sequential discrepancy `D=E(L)-E(M)`. -/
theorem nativePNTSequentialDiscrepancy_mul_log_sub_one_eq
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTSequentialSquareBlockDiscrepancy M L *
          (Real.log (L : Real) - 1) +
        nativePNTError M *
          (Real.log (L : Real) - Real.log (M : Real)) +
        nativePNTSequentialSharedFiberDrift M L - ((L - M : Nat) : Real) =
      nativePNTSignedSelbergRemainder L - nativePNTSignedSelbergRemainder M := by
  have hrec :=
    nativePNTSignedSelberg_recurrence_difference_subdoubling M L hM hML hsub
  have hD :=
    nativePNTSequentialSquareBlockDiscrepancy_eq_lambdaMass_sub_length
      M L hM hML
  unfold nativePNTSequentialSquareBlockDiscrepancy at hD ⊢
  rw [Nat.cast_sub hML] at hD ⊢
  nlinarith

/-! ## Exact bridge to the existing reciprocal Möbius coordinate -/

/-- Shared-fibre drift in the generic Möbius logarithmic reciprocal coordinate. -/
def nativePNTSequentialSharedMobiusReciprocalMass (M L : Nat) : Real :=
  nativePNTMobiusLogReciprocalMass M
    (fun d => nativePNTError (L / d) - nativePNTError (M / d))

/-- Exact Fubini bridge to the existing prime-by-prime reciprocal coordinate. -/
theorem nativePNTSequentialSharedFiberDrift_eq_mobiusReciprocalMass
    (M L : Nat) :
    nativePNTSequentialSharedFiberDrift M L =
      nativePNTSequentialSharedMobiusReciprocalMass M L := by
  unfold nativePNTSequentialSharedFiberDrift
    nativePNTSequentialSharedMobiusReciprocalMass
  simpa using
    (nativeLambdaWeighted_eq_mobiusLogReciprocalMass M
      (fun d => nativePNTError (L / d) - nativePNTError (M / d)))

/-- The change of the full signed reciprocal mass equals shared reciprocal drift
plus the already-defined new-block Möbius correlation. -/
theorem nativePNTMobiusReciprocalSignedErrorMass_sub_eq_shared_add_blockCorrelation
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTMobiusReciprocalSignedErrorMass L -
        nativePNTMobiusReciprocalSignedErrorMass M =
      nativePNTSequentialSharedMobiusReciprocalMass M L +
        nativePNTSignedSquareBlockMobiusCorrelation L M L := by
  have hsplit :=
    nativePNTLambdaSignedErrorMass_sub_eq_shared_add_new M L hM hML
  rw [nativeLambdaSignedErrorMass_eq_mobiusReciprocal,
    nativeLambdaSignedErrorMass_eq_mobiusReciprocal] at hsplit
  rw [nativePNTSequentialSharedFiberDrift_eq_mobiusReciprocalMass] at hsplit
  have hblock := nativeLambdaSquareBlockWeighted_eq_mobiusCorrelation L M L
  unfold nativePNTSequentialNewFiberMass at hsplit
  rw [hblock] at hsplit
  exact hsplit

/-- The same carrier identity with the new-block correlation expanded into its
existing parity-mean plus centered-covariance decomposition. -/
theorem nativePNTMobiusReciprocalSignedErrorMass_sub_eq_shared_add_blockMeanCovariance
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTMobiusReciprocalSignedErrorMass L -
        nativePNTMobiusReciprocalSignedErrorMass M =
      nativePNTSequentialSharedMobiusReciprocalMass M L +
        (nativePNTSignedSquareBlockCofactorCard L : Real) *
          (nativePNTSignedSquareBlockParityMean L *
              nativePNTSignedSquareBlockResponseMean L M L +
            nativePNTSignedSquareBlockCovariance L M L) := by
  rw [nativePNTMobiusReciprocalSignedErrorMass_sub_eq_shared_add_blockCorrelation
      M L hM hML,
    nativePNTSignedSquareBlockMobiusCorrelation_eq_card_mul_mean_add_covariance
      L M L (hM.trans hML)]

/-- Shared reciprocal drift is the full reciprocal-mass change after removing
the new-block correlation. -/
theorem nativePNTSequentialSharedMobiusReciprocalMass_eq_full_sub_old_sub_block
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTSequentialSharedMobiusReciprocalMass M L =
      nativePNTMobiusReciprocalSignedErrorMass L -
        nativePNTMobiusReciprocalSignedErrorMass M -
          nativePNTSignedSquareBlockMobiusCorrelation L M L := by
  have h :=
    nativePNTMobiusReciprocalSignedErrorMass_sub_eq_shared_add_blockCorrelation
      M L hM hML
  linarith

/-- Multiplying the exact seed equation by the inherited endpoint error exposes
`X(M,L)` directly against the existing reciprocal Möbius mass. -/
theorem nativePNTSequentialCrossEnergy_mul_log_sub_one_eq_mobiusReciprocal
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTSequentialSquareBlockCrossEnergy M L *
          (Real.log (L : Real) - 1) +
        nativePNTError M ^ 2 *
          (Real.log (L : Real) - Real.log (M : Real)) +
        nativePNTError M *
          nativePNTSequentialSharedMobiusReciprocalMass M L -
        nativePNTError M * ((L - M : Nat) : Real) =
      nativePNTError M *
        (nativePNTSignedSelbergRemainder L - nativePNTSignedSelbergRemainder M) := by
  have hseed :=
    nativePNTSequentialDiscrepancy_mul_log_sub_one_eq M L hM hML hsub
  rw [nativePNTSequentialSharedFiberDrift_eq_mobiusReciprocalMass] at hseed
  unfold nativePNTSequentialSquareBlockCrossEnergy
  linear_combination nativePNTError M * hseed

end RHLean.Analysis