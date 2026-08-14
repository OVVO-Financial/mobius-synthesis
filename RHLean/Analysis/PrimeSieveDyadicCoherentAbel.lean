import Mathlib
import RHLean.Analysis.PrimeSieveAbelIdentity

/-!
# Dyadic coherent / wavelet decomposition of the reciprocal prime-sieve error

The quotient-fibre prime-sieve error is an exact Mertens-weighted sum

`E(y,x) = sum_d Delta_d(y,x) * M(d)`

on the reciprocal index `d`.  This module decomposes that finite `d`-family by
the predetermined dyadic label `floor(log2 d)`.  Inside every occupied dyadic
block we subtract the literal block mean of the reciprocal prime discrepancy.
The resulting wavelet has exactly zero block sum.

That zero mean has an important exact consequence.  Extend one block wavelet by
zero to the whole quotient support and form the negative prefix potential.  Its
forward difference is the block wavelet and its terminal value is exactly zero.
The existing finite Mertens Abel identity therefore has no endpoint term on
that block.  Summing over all occupied blocks gives a boundary-free Mobius
representation of the complete wavelet part of `E`.

Finally the same decomposition is pushed through the repository's canonical
square-wheel zero-mode centering.  Thus the live nonzero response is exactly

`H = coherentChannel - 2 * centeredWaveletError`.

Everything in this file is finite algebra.  The critical-scale bounds suggested
by the accompanying diagnostics are stated only as propositions at the bottom;
no analytic estimate, PNT error bound, or RH-strength cancellation is asserted.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Predetermined dyadic label on the positive reciprocal index. -/
def primeSieveDyadicIndex (d : ℕ) : ℕ := Nat.log2 d

/-- The occupied part of one dyadic reciprocal block inside the quotient support. -/
def primeSieveDyadicBlock (y x j : ℕ) : Finset ℕ :=
  (primeSieveQuotientSupport y x).filter fun d => primeSieveDyadicIndex d = j

/-- Dyadic labels actually represented in the finite quotient support. -/
def primeSieveDyadicBlockIndices (y x : ℕ) : Finset ℕ :=
  (primeSieveQuotientSupport y x).image primeSieveDyadicIndex

@[simp] theorem mem_primeSieveDyadicBlock
    {y x j d : ℕ} :
    d ∈ primeSieveDyadicBlock y x j ↔
      d ∈ primeSieveQuotientSupport y x ∧ primeSieveDyadicIndex d = j := by
  simp [primeSieveDyadicBlock]

/-- Literal average reciprocal prime discrepancy on one occupied dyadic block.
The inverse-of-zero convention makes this definition total; only occupied
blocks are used in the mean-zero theorem below. -/
def primeSieveDyadicBlockMean (y x j : ℕ) : ℂ :=
  (((primeSieveDyadicBlock y x j).card : ℂ)⁻¹) *
    ∑ d ∈ primeSieveDyadicBlock y x j,
      primeSieveReciprocalPrimeDiscrepancy y x d

/-- Mean-zero dyadic residual of the reciprocal prime discrepancy. -/
def primeSieveDyadicWavelet (y x d : ℕ) : ℂ :=
  primeSieveReciprocalPrimeDiscrepancy y x d -
    primeSieveDyadicBlockMean y x (primeSieveDyadicIndex d)

/-- Pointwise coherent plus mean-zero decomposition of one reciprocal atom. -/
theorem primeSieveReciprocalPrimeDiscrepancy_eq_dyadicMean_add_wavelet
    (y x d : ℕ) :
    primeSieveReciprocalPrimeDiscrepancy y x d =
      primeSieveDyadicBlockMean y x (primeSieveDyadicIndex d) +
        primeSieveDyadicWavelet y x d := by
  unfold primeSieveDyadicWavelet
  ring

/-- Every occupied dyadic block has exactly zero wavelet mass. -/
theorem sum_primeSieveDyadicWavelet_block_eq_zero
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    (∑ d ∈ primeSieveDyadicBlock y x j,
      primeSieveDyadicWavelet y x d) = 0 := by
  classical
  rcases Finset.mem_image.mp hj with ⟨d, hd, hidx⟩
  have hdB : d ∈ primeSieveDyadicBlock y x j := by
    simp [primeSieveDyadicBlock, hd, hidx]
  have hcardNat : 0 < (primeSieveDyadicBlock y x j).card :=
    Finset.card_pos.mpr ⟨d, hdB⟩
  have hcard : (((primeSieveDyadicBlock y x j).card : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardNat)
  have hreindex :
      (∑ e ∈ primeSieveDyadicBlock y x j,
          primeSieveDyadicWavelet y x e) =
        ∑ e ∈ primeSieveDyadicBlock y x j,
          (primeSieveReciprocalPrimeDiscrepancy y x e -
            primeSieveDyadicBlockMean y x j) := by
    apply Finset.sum_congr rfl
    intro e he
    have he0 := he
    simp [primeSieveDyadicBlock] at he0
    simp [primeSieveDyadicWavelet, he0.2]
  rw [hreindex, Finset.sum_sub_distrib]
  have hconst :
      (∑ _e ∈ primeSieveDyadicBlock y x j,
          primeSieveDyadicBlockMean y x j) =
        ((primeSieveDyadicBlock y x j).card : ℂ) *
          primeSieveDyadicBlockMean y x j := by
    simp [nsmul_eq_mul]
  rw [hconst]
  unfold primeSieveDyadicBlockMean
  field_simp [hcard]
  ring

/-- Coherent dyadic part of the quotient-reindexed prime error. -/
def primeSieveDyadicCoherentPNTError (y x : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    primeSieveDyadicBlockMean y x (primeSieveDyadicIndex d) *
      mertensSummatory d

/-- Mean-zero dyadic part of the quotient-reindexed prime error. -/
def primeSieveDyadicWaveletPNTError (y x : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    primeSieveDyadicWavelet y x d * mertensSummatory d

/-- Exact coherent plus wavelet decomposition of the prime-sieve PNT error. -/
theorem primeSievePNTError_eq_dyadicCoherent_add_wavelet
    (y x : ℕ) :
    primeSievePNTError y x =
      primeSieveDyadicCoherentPNTError y x +
        primeSieveDyadicWaveletPNTError y x := by
  rw [primeSievePNTError_eq_reciprocalPNTError]
  unfold primeSieveReciprocalPNTError
    primeSieveDyadicCoherentPNTError primeSieveDyadicWaveletPNTError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  unfold primeSieveDyadicWavelet
  ring

/-! ## Boundary-free Abel transform on each dyadic block -/

/-- Extend one dyadic wavelet block by zero to the whole reciprocal support. -/
def primeSieveDyadicBlockWaveletMask (y x j d : ℕ) : ℂ :=
  if d ∈ primeSieveDyadicBlock y x j then
    primeSieveDyadicWavelet y x d
  else 0

/-- The masked wavelet still has zero total mass on the complete quotient support. -/
theorem sum_primeSieveDyadicBlockWaveletMask_eq_zero
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    (∑ d ∈ primeSieveQuotientSupport y x,
      primeSieveDyadicBlockWaveletMask y x j d) = 0 := by
  classical
  have hblock := sum_primeSieveDyadicWavelet_block_eq_zero (y := y) (x := x) hj
  have hfilter :
      (primeSieveQuotientSupport y x).filter
          (fun d => d ∈ primeSieveDyadicBlock y x j) =
        primeSieveDyadicBlock y x j := by
    ext d
    simp [primeSieveDyadicBlock]
  unfold primeSieveDyadicBlockWaveletMask
  rw [← Finset.sum_filter, hfilter]
  exact hblock

/-- Negative prefix before `d` for one masked dyadic wavelet.
This is the Abel potential whose forward difference is the wavelet. -/
def primeSieveDyadicBlockAbelPotential (y x j d : ℕ) : ℂ :=
  - ∑ t ∈ Finset.Icc 1 (d - 1),
      primeSieveDyadicBlockWaveletMask y x j t

/-- On the reciprocal support the Abel potential has exactly the masked wavelet
as its forward difference. -/
theorem primeSieveDyadicBlockAbelPotential_forwardDifference
    {y x j d : ℕ} (hd : d ∈ primeSieveQuotientSupport y x) :
    primeSieveDyadicBlockAbelPotential y x j d -
        primeSieveDyadicBlockAbelPotential y x j (d + 1) =
      primeSieveDyadicBlockWaveletMask y x j d := by
  have hdIcc : d ∈ Finset.Icc 1 (x / (y + 1)) := by
    simpa [primeSieveQuotientSupport] using hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  have hsum :
      (∑ t ∈ Finset.Icc 1 d,
        primeSieveDyadicBlockWaveletMask y x j t) =
        (∑ t ∈ Finset.Icc 1 (d - 1),
          primeSieveDyadicBlockWaveletMask y x j t) +
          primeSieveDyadicBlockWaveletMask y x j d := by
    rw [← hpred]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ d - 1 + 1)]
    have hback : d - 1 + 1 - 1 = d - 1 := by omega
    rw [hback]
  unfold primeSieveDyadicBlockAbelPotential
  rw [show d + 1 - 1 = d by omega, hsum]
  ring

/-- The terminal Abel potential vanishes exactly because the dyadic block was
mean-centered before summation by parts. -/
theorem primeSieveDyadicBlockAbelPotential_top_eq_zero
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    primeSieveDyadicBlockAbelPotential y x j (x / (y + 1) + 1) = 0 := by
  have hzero := sum_primeSieveDyadicBlockWaveletMask_eq_zero
    (y := y) (x := x) hj
  have hsum :
      (∑ t ∈ Finset.Icc 1 (x / (y + 1)),
        primeSieveDyadicBlockWaveletMask y x j t) = 0 := by
    simpa [primeSieveQuotientSupport] using hzero
  unfold primeSieveDyadicBlockAbelPotential
  simp only [Nat.add_sub_cancel]
  rw [hsum]
  simp

/-- Mertens-weighted contribution of one mean-zero dyadic block. -/
def primeSieveDyadicBlockWaveletMertensContribution
    (y x j : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    primeSieveDyadicBlockWaveletMask y x j d * mertensSummatory d

/-- One block has a finite Abel identity with **no endpoint term**.
The usual Mertens boundary vanishes because the masked block wavelet has zero
sum. -/
theorem primeSieveDyadicBlockWaveletMertensContribution_eq_boundaryFreeAbel
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    primeSieveDyadicBlockWaveletMertensContribution y x j =
      ∑ d ∈ primeSieveQuotientSupport y x,
        (((μ d : ℤ) : ℂ)) * primeSieveDyadicBlockAbelPotential y x j d := by
  let K := x / (y + 1)
  let F : ℕ → ℂ := fun d => primeSieveDyadicBlockAbelPotential y x j d
  have habel := sum_mertensSummatory_mul_forwardDifference F K
  have htop : F (K + 1) = 0 := by
    dsimp [F, K]
    exact primeSieveDyadicBlockAbelPotential_top_eq_zero (y := y) (x := x) hj
  unfold primeSieveDyadicBlockWaveletMertensContribution
  change
    (∑ d ∈ Finset.Icc 1 K,
      primeSieveDyadicBlockWaveletMask y x j d * mertensSummatory d) = _
  calc
    (∑ d ∈ Finset.Icc 1 K,
        primeSieveDyadicBlockWaveletMask y x j d * mertensSummatory d) =
      ∑ d ∈ Finset.Icc 1 K,
        mertensSummatory d * (F d - F (d + 1)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hds : d ∈ primeSieveQuotientSupport y x := by
            simpa [primeSieveQuotientSupport, K] using hd
          rw [primeSieveDyadicBlockAbelPotential_forwardDifference hds]
          ring
    _ = (∑ d ∈ Finset.Icc 1 K, (((μ d : ℤ) : ℂ)) * F d) -
          mertensSummatory K * F (K + 1) := habel
    _ = ∑ d ∈ Finset.Icc 1 K, (((μ d : ℤ) : ℂ)) * F d := by
          rw [htop]
          ring
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
          (((μ d : ℤ) : ℂ)) * primeSieveDyadicBlockAbelPotential y x j d := by
          rfl

/-- At a fixed reciprocal index exactly one occupied dyadic block contributes
its wavelet mask. -/
theorem sum_primeSieveDyadicBlockWaveletMask_eq_wavelet
    {y x d : ℕ} (hd : d ∈ primeSieveQuotientSupport y x) :
    (∑ j ∈ primeSieveDyadicBlockIndices y x,
      primeSieveDyadicBlockWaveletMask y x j d) =
        primeSieveDyadicWavelet y x d := by
  classical
  have hj : primeSieveDyadicIndex d ∈ primeSieveDyadicBlockIndices y x :=
    Finset.mem_image.mpr ⟨d, hd, rfl⟩
  rw [Finset.sum_eq_single (primeSieveDyadicIndex d)]
  · simp [primeSieveDyadicBlockWaveletMask, primeSieveDyadicBlock, hd]
  · intro j _hj hne
    have hidxne : primeSieveDyadicIndex d ≠ j := Ne.symm hne
    simp [primeSieveDyadicBlockWaveletMask, primeSieveDyadicBlock, hd, hidxne]
  · intro hnot
    exact False.elim (hnot hj)

/-- The whole wavelet error is the sum of its occupied dyadic block contributions. -/
theorem primeSieveDyadicWaveletPNTError_eq_sum_blockContributions
    (y x : ℕ) :
    primeSieveDyadicWaveletPNTError y x =
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        primeSieveDyadicBlockWaveletMertensContribution y x j := by
  classical
  unfold primeSieveDyadicWaveletPNTError
    primeSieveDyadicBlockWaveletMertensContribution
  calc
    (∑ d ∈ primeSieveQuotientSupport y x,
        primeSieveDyadicWavelet y x d * mertensSummatory d) =
      ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ j ∈ primeSieveDyadicBlockIndices y x,
          primeSieveDyadicBlockWaveletMask y x j d) * mertensSummatory d := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [sum_primeSieveDyadicBlockWaveletMask_eq_wavelet hd]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        ∑ j ∈ primeSieveDyadicBlockIndices y x,
          primeSieveDyadicBlockWaveletMask y x j d * mertensSummatory d := by
          apply Finset.sum_congr rfl
          intro d _hd
          rw [Finset.sum_mul]
    _ = ∑ j ∈ primeSieveDyadicBlockIndices y x,
        ∑ d ∈ primeSieveQuotientSupport y x,
          primeSieveDyadicBlockWaveletMask y x j d * mertensSummatory d := by
          rw [Finset.sum_comm]

/-- **Boundary-free Abel representation of the complete dyadic wavelet error.**
No global term `M(K) * R(y)` remains: every dyadic block was centered before
Abel summation, so each block endpoint term is identically zero. -/
theorem primeSieveDyadicWaveletPNTError_eq_boundaryFreeAbel
    (y x : ℕ) :
    primeSieveDyadicWaveletPNTError y x =
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        ∑ d ∈ primeSieveQuotientSupport y x,
          (((μ d : ℤ) : ℂ)) * primeSieveDyadicBlockAbelPotential y x j d := by
  rw [primeSieveDyadicWaveletPNTError_eq_sum_blockContributions]
  apply Finset.sum_congr rfl
  intro j hj
  exact primeSieveDyadicBlockWaveletMertensContribution_eq_boundaryFreeAbel hj

/-! ## Push the decomposition through the canonical square-wheel centering -/

/-- Centered coherent dyadic prime-error component at the canonical block-safe cutoff. -/
def primorialDyadicCoherentPNTErrorCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x => primeSieveDyadicCoherentPNTError
      (primorialPNTPrimeSieveCutoff k) x)

/-- Centered mean-zero dyadic prime-error component at the same cutoff. -/
def primorialDyadicWaveletPNTErrorCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x => primeSieveDyadicWaveletPNTError
      (primorialPNTPrimeSieveCutoff k) x)

/-- The centered prime error splits exactly into coherent and wavelet channels. -/
theorem primorialPNTErrorCenteredResponse_eq_dyadicCoherent_add_wavelet
    (k n : ℕ) :
    primorialPNTErrorCenteredResponse k n =
      primorialDyadicCoherentPNTErrorCenteredResponse k n +
        primorialDyadicWaveletPNTErrorCenteredResponse k n := by
  unfold primorialPNTErrorCenteredResponse
    primorialDyadicCoherentPNTErrorCenteredResponse
    primorialDyadicWaveletPNTErrorCenteredResponse
    primorialSquareZeroModeCenter
  dsimp
  rw [primeSievePNTError_eq_dyadicCoherent_add_wavelet
        (primorialPNTPrimeSieveCutoff k) (squarePrefixEndpoint n),
      primeSievePNTError_eq_dyadicCoherent_add_wavelet
        (primorialPNTPrimeSieveCutoff k) (primorialBlockLower k),
      primeSievePNTError_eq_dyadicCoherent_add_wavelet
        (primorialPNTPrimeSieveCutoff k) (primorialBlockUpper k)]
  ring

/-- Coherent channel left after pairing the corrected comb with twice the
centered dyadic mean of the reciprocal prime discrepancy. -/
def primorialDyadicCoherentChannel (k n : ℕ) : ℂ :=
  primorialPNTCorrectedCombCenteredResponse k n -
    2 * primorialDyadicCoherentPNTErrorCenteredResponse k n

/-- **Canonical the earlier development decomposition.**  The live nonzero wheel response is the
coherent channel minus twice the centered mean-zero reciprocal wavelet. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_dyadicCoherent_sub_two_wavelet
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      primorialDyadicCoherentChannel k n -
        2 * primorialDyadicWaveletPNTErrorCenteredResponse k n := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_error
    k n hlower hupper]
  rw [primorialPNTErrorCenteredResponse_eq_dyadicCoherent_add_wavelet]
  unfold primorialDyadicCoherentChannel
  ring

/-! ## Explicit open analytic targets

These propositions name the two estimates suggested by the finite diagnostics.
They are deliberately not proved here.  Exact decomposition is not quantitative
progress until one of these predicates is inhabited.
-/

/-- Squared `L2` mass of all boundary-free dyadic Abel potentials at one point. -/
def primeSieveDyadicAbelPotentialEnergy (y x : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    ∑ d ∈ primeSieveQuotientSupport y x,
      ‖primeSieveDyadicBlockAbelPotential y x j d‖ ^ 2

/-- Uniform pointwise power bound for the coherent channel on canonical square samples. -/
def DyadicCoherentChannelPowerBound (r : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (k n : ℕ),
      2 ≤ k →
      primorialBlockLower k < squarePrefixEndpoint n →
      squarePrefixEndpoint n ≤ primorialBlockUpper k →
      ‖primorialDyadicCoherentChannel k n‖ ≤
        K * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r

/-- RH-scale coherent-channel target. -/
def DyadicCoherentChannelRHScale : Prop :=
  ∀ ε : ℝ, 0 < ε →
    DyadicCoherentChannelPowerBound ((1 : ℝ) / 2 + ε)

/-- Critical-scale `L2` target for the boundary-free Abel coefficient field. -/
def DyadicAbelPotentialEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k n : ℕ),
        2 ≤ k →
        primorialBlockLower k < squarePrefixEndpoint n →
        squarePrefixEndpoint n ≤ primorialBlockUpper k →
        primeSieveDyadicAbelPotentialEnergy
            (primorialPNTPrimeSieveCutoff k) (squarePrefixEndpoint n) ≤
          C * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) (1 + ε)

/-- Dispersion target for the Mobius signs against the boundary-free Abel field.
Together with `DyadicAbelPotentialEnergyBoundedStatement`, this is the exact
shape suggested by the experiment for recovering square-root scale in the
wavelet channel. -/
def DyadicMobiusDispersionBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k n : ℕ),
        2 ≤ k →
        primorialBlockLower k < squarePrefixEndpoint n →
        squarePrefixEndpoint n ≤ primorialBlockUpper k →
        ‖primeSieveDyadicWaveletPNTError
            (primorialPNTPrimeSieveCutoff k) (squarePrefixEndpoint n)‖ ^ 2 ≤
          C * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) ε *
            primeSieveDyadicAbelPotentialEnergy
              (primorialPNTPrimeSieveCutoff k) (squarePrefixEndpoint n)

end RHLean.Analysis
