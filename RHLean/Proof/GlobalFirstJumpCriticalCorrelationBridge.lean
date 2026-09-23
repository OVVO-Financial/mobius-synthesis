import Mathlib
import RHLean.Analysis.BlockCovarianceRefinement
import RHLean.Analysis.MertensCovarianceDescent
import RHLean.Analysis.PrimeWheelRunOthelloBoundary
import RHLean.Proof.GlobalFirstJumpCofactorCompression
import RHLean.Proof.CanonicalRoughCriticalCorrelationContraction
import RHLean.Proof.PrimeCombReciprocalBandCancellation
import RHLean.Proof.SquareRootLowPrimeMatchedCoreMertensObstruction

/-!
# Critical reciprocal-correlation bridge for the recombined defect

The first-jump-only norm target is too strong.  After recombination, the exact
endpoint object is `lowWheelCanonicalDefectLedger R`.  The canonical rough
correlation already differs from this defect by only the single root Mobius
atom, while its reciprocal prefixes are exactly the coordinate on which the
fresh-prime Euler factor `1 - 1/p` acts.

The conditional Abel return is retained, but its proposed uniform
`(log R + 1) / R` prefix premise is refuted here: the first prefix is the
unsigned unit-cofactor prime-partner count.  The active quantitative target is
instead the signed post-root covariance remainder below, whose bound remains
open.  No first-jump-prime or cofactor-column norm is inserted in the argument.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic

/-- The canonical defect is the lower Mertens value minus the square endpoint
Mertens value. -/
theorem canonicalDefectLedger_eq_mertens_sub_squareRootEndpoint
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalDefectLedger R =
      mertensSummatory R - mertensSummatory (squareRootEndpoint R) := by
  have hdown := squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR
  have hend := squarePrefixMertens_pred_eq_mertens_squareRootEndpoint R (by omega)
  rw [hend] at hdown
  rw [lowWheelCanonicalDefectLedger_eq_downcrossLedger]
  linear_combination hdown

/-- **Defect/correlation bridge.**  The RH-critical canonical rough correlation
misses the recombined endpoint defect by exactly one Mobius atom at the root. -/
theorem canonicalDefectLedger_eq_roughCorrelation_add_rootAtom
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalDefectLedger R =
      squareRootCanonicalRoughCorrelation R + canonicalMoebiusWeight R := by
  rw [canonicalDefectLedger_eq_mertens_sub_squareRootEndpoint R hR,
    squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R (by omega)]
  have hsucc := RHLean.Analysis.mertensSummatory_succ (R - 1)
  have hpred : R - 1 + 1 = R := by omega
  rw [hpred] at hsucc
  rw [hsucc]
  unfold canonicalMoebiusWeight
  ring

/-- A proposed sufficient reciprocal-prefix scale for an `R log R` endpoint.
The implication below is valid, but the premise is impossible: the unit prefix
is an unsigned prime-partner count.  See
`not_criticalReciprocalPrefixRootBound`. -/
def CriticalReciprocalPrefixRootBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ∀ k ≤ squareRootEndpoint R,
        ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ ≤
          C * (Real.log (R : ℝ) + 1) / (R : ℝ)

/-- The first reciprocal prefix contains only the unit-cofactor response.
The existing renewal collapse identifies it with a literal prime count, before
any asymptotic estimate or choice of an Euler compression order. -/
theorem criticalReciprocalPrefix_one_eq_partnerCard
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughCorrelationReciprocalPrefix R 1 =
      ((squareRootCanonicalRoughPrimePartnerSet R 1).card : ℂ) := by
  have hzero : squareRootCanonicalRoughCorrelationReciprocalSummand R 0 = 0 := by
    simp [squareRootCanonicalRoughCorrelationReciprocalSummand,
      squareRootCanonicalRoughResponseCenteredReciprocalSummand,
      squareRootCanonicalRoughParityReciprocalSummand]
  unfold squareRootCanonicalRoughCorrelationReciprocalPrefix inclusivePrefix
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add, hzero]
  rw [squareRootCanonicalRoughCorrelationReciprocalSummand_eq_weighted_response_div
    R (by decide : 0 < 1),
    squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R 1 hR,
    squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card]
  simp [canonicalMoebiusWeight]

/-- In the physical partner coordinate the unit prefix counts precisely the
primes in the inclusive interval `[R, R^2 - 1]`. -/
theorem criticalReciprocalPrefix_unitPartnerSet
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughPrimePartnerSet R 1 =
      (Finset.Icc R (squareRootEndpoint R)).filter Nat.Prime := by
  ext q
  rw [mem_squareRootCanonicalRoughPrimePartnerSet_iff hR (by decide : 0 < 1),
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hq, _hfresh, hlo, hhi⟩
    exact ⟨⟨by simpa using hlo, by simpa using hhi⟩, hq⟩
  · rintro ⟨⟨hlo, hhi⟩, hq⟩
    refine ⟨hq, ?_, by simpa using hlo, by simpa using hhi⟩
    simpa [canonicalLargestPrimeFactor] using hq.one_lt

/-- Every prime root supplies a unit partner itself.  Consequently the first
prefix stays at least one along an unbounded sequence of roots. -/
theorem one_le_norm_criticalReciprocalPrefix_one_of_prime
    {R : ℕ} (hR : R.Prime) :
    1 ≤ ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R 1‖ := by
  have hRtwo : 2 ≤ R := hR.two_le
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hmem : R ∈ squareRootCanonicalRoughPrimePartnerSet R 1 := by
    rw [criticalReciprocalPrefix_unitPartnerSet R hRtwo]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hRX⟩, hR⟩
  have hcard : 1 ≤ (squareRootCanonicalRoughPrimePartnerSet R 1).card :=
    Finset.card_pos.mpr ⟨R, hmem⟩
  rw [criticalReciprocalPrefix_one_eq_partnerCard R hRtwo]
  simpa using (show (1 : ℝ) ≤
    ((squareRootCanonicalRoughPrimePartnerSet R 1).card : ℝ) by exact_mod_cast hcard)

/-- **The uniform small-prefix premise is false.**  Its right side tends to
zero, whereas its unit prefix is at least one at every prime root.  Only
Euclid's infinitude of primes and `log R / R -> 0` are needed; no PNT or
Mertens estimate enters the obstruction. -/
theorem not_criticalReciprocalPrefixRootBound :
    ¬ CriticalReciprocalPrefixRootBound := by
  rintro ⟨C, _hC, hbound⟩
  have hlog : Filter.Tendsto
      (fun R : ℕ => Real.log (R : ℝ) / (R : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun R : ℕ => (1 : ℝ) / (R : ℝ))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hlim : Filter.Tendsto
      (fun R : ℕ => C * (Real.log (R : ℝ) + 1) / (R : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [add_div, mul_div_assoc, add_zero, mul_zero] using
      (hlog.add hinv).const_mul C
  have hsmall : ∀ᶠ R : ℕ in Filter.atTop,
      C * (Real.log (R : ℝ) + 1) / (R : ℝ) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rcases Filter.eventually_atTop.mp hsmall with ⟨N, hN⟩
  rcases Nat.exists_infinite_primes (max 3 N) with ⟨R, hRlarge, hRprime⟩
  have hRthree : 3 ≤ R := (le_max_left 3 N).trans hRlarge
  have hNR : N ≤ R := (le_max_right 3 N).trans hRlarge
  have hX : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    omega
  have hlo := one_le_norm_criticalReciprocalPrefix_one_of_prime hRprime
  have hhi := hbound R hRthree 1 hX
  have hlt := hN R hNR
  linarith

/-- A critical reciprocal-prefix bound gives the corresponding `R log R` bound
on the uncentered canonical rough correlation. -/
theorem roughCorrelationLogBound_of_criticalReciprocalPrefixRootBound
    (hprefix : CriticalReciprocalPrefixRootBound) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 3 ≤ R →
        ‖squareRootCanonicalRoughCorrelation R‖ ≤
          C * (R : ℝ) * (Real.log (R : ℝ) + 1) := by
  rcases hprefix with ⟨C, hC, hprefix⟩
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro R hR
  let L : ℝ := Real.log (R : ℝ) + 1
  let A : ℝ := C * L / (R : ℝ)
  have hA : ∀ k ≤ squareRootEndpoint R,
      ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ ≤ A := by
    intro k hk
    simpa [A, L] using hprefix R hR k hk
  have habel :=
    squareRootCanonicalRoughCorrelation_norm_le_two_endpoint_mul R A hA
  have hRpos : 0 < (R : ℝ) := by positivity
  have hR0 : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  have hlog : 0 ≤ Real.log (R : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ R by omega)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    linarith
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg hC hL0) hRpos.le
  have hXnat : squareRootEndpoint R ≤ R ^ 2 := by
    unfold squareRootEndpoint
    omega
  have hX : (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hXnat
  calc
    ‖squareRootCanonicalRoughCorrelation R‖ ≤
        2 * (squareRootEndpoint R : ℝ) * A := habel
    _ ≤ 2 * ((R : ℝ) ^ 2) * A := by
      have h2 : 2 * (squareRootEndpoint R : ℝ) ≤ 2 * ((R : ℝ) ^ 2) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right h2 hA0
    _ = (2 * C) * (R : ℝ) * L := by
      dsimp [A]
      field_simp [hR0]
    _ = (2 * C) * (R : ℝ) * (Real.log (R : ℝ) + 1) := by rfl

/-- **Concrete closure criterion.**  Control the exact reciprocal correlation
prefixes at their native `log R / R` scale, and the recombined dense-plus-first-
jump endpoint satisfies the desired `R log R` bound.  The extra `+1` in the
constant pays only for the single root Mobius atom. -/
theorem recombinedCanonicalDefectLogBound_of_criticalReciprocalPrefixRootBound
    (hprefix : CriticalReciprocalPrefixRootBound) :
    RecombinedCanonicalDefectLogBound := by
  rcases roughCorrelationLogBound_of_criticalReciprocalPrefixRootBound hprefix with
    ⟨C, hC, hcorr⟩
  refine ⟨C + 1, by linarith, ?_⟩
  intro R hR
  rw [canonicalDefectLedger_eq_roughCorrelation_add_rootAtom R hR]
  have hmu : ‖canonicalMoebiusWeight R‖ ≤ (1 : ℝ) := by
    rcases ArithmeticFunction.moebius_eq_or R with h | h | h <;>
      simp [canonicalMoebiusWeight, h]
  have hcorrR := hcorr R hR
  have hRone : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hlog : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg hRone
  have hLone : (1 : ℝ) ≤ Real.log (R : ℝ) + 1 := by linarith
  have hscaleOne :
      (1 : ℝ) ≤ (R : ℝ) * (Real.log (R : ℝ) + 1) := by
    have hmul := mul_le_mul hRone hLone (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ (R : ℝ))
    simpa using hmul
  calc
    ‖squareRootCanonicalRoughCorrelation R + canonicalMoebiusWeight R‖ ≤
        ‖squareRootCanonicalRoughCorrelation R‖ +
          ‖canonicalMoebiusWeight R‖ := norm_add_le _ _
    _ ≤ C * (R : ℝ) * (Real.log (R : ℝ) + 1) + 1 :=
      add_le_add hcorrR hmu
    _ ≤ (C + 1) * (R : ℝ) * (Real.log (R : ℝ) + 1) := by
      calc
        C * (R : ℝ) * (Real.log (R : ℝ) + 1) + 1 ≤
            C * (R : ℝ) * (Real.log (R : ℝ) + 1) +
              (R : ℝ) * (Real.log (R : ℝ) + 1) :=
          add_le_add_left hscaleOne _
        _ = (C + 1) * (R : ℝ) * (Real.log (R : ℝ) + 1) := by ring

/-! ## Post-root covariance descent on reciprocal bands

This is the second-difference route.  A post-root prime family is an exact
sign-reversed copy of a lower prefix in mass and an isometric copy in pair
covariance.  Grouping by `z = floor(W/p)` therefore leaves one lower-scale
covariance value per reciprocal band, multiplied only by the population of that
band.  No norm and no PNT estimate enters this identity.
-/

/-- Pair covariance carried by every post-root prime family in one reciprocal
quotient band. -/
def postRootReciprocalBandFamilyCovariance (W z : ℕ) : ℝ :=
  ∑ p ∈ primeCombPostRootReciprocalBand W z,
    largePrimeFamilyPairSum p (z + 1)

/-- A post-root reciprocal band is literally its prime multiplicity times the
one lower-scale covariance `C(z+1)`.  This is the exact scale descent that the
fixed-prime norm route destroyed. -/
theorem postRootReciprocalBandFamilyCovariance_eq_card_mul_lowerCovariance
    (W z : ℕ) (hz : 0 < z) :
    postRootReciprocalBandFamilyCovariance W z =
      ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        realMertensPositiveLagPairSum (z + 1) := by
  unfold postRootReciprocalBandFamilyCovariance
  calc
    (∑ p ∈ primeCombPostRootReciprocalBand W z,
        largePrimeFamilyPairSum p (z + 1)) =
      ∑ _p ∈ primeCombPostRootReciprocalBand W z,
        realMertensPositiveLagPairSum (z + 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases mem_primeCombPostRootReciprocalBand.mp hp with
        ⟨hpBand, hpRoot⟩
      have hpPrime := primeCombReciprocalBand_prime hpBand
      have hW : W < p * p := (Nat.sqrt_lt).1 hpRoot
      have hdiv := primeCombReciprocalBand_div_eq hz hpBand
      calc
        largePrimeFamilyPairSum p (z + 1) =
            largePrimeFamilyPairSum p (W / p + 1) := by rw [hdiv]
        _ = realMertensPositiveLagPairSum (W / p + 1) :=
          largePrimeFamilyPairSum_postRoot hpPrime hW
        _ = realMertensPositiveLagPairSum (z + 1) := by rw [hdiv]
    _ = ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        realMertensPositiveLagPairSum (z + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- The multiplicity of a post-root reciprocal band is bounded by the literal
integer width of the corresponding quotient interval.  This throws away both
primality and the post-root restriction, so it needs no PNT input. -/
theorem card_primeCombPostRootReciprocalBand_le_width
    (W z : ℕ) :
    (primeCombPostRootReciprocalBand W z).card ≤
      W / z - W / (z + 1) := by
  have hsub :
      primeCombPostRootReciprocalBand W z ⊆
        Finset.Ioc (W / (z + 1)) (W / z) := by
    intro p hp
    rcases mem_primeCombPostRootReciprocalBand.mp hp with ⟨hpBand, _hpRoot⟩
    rcases mem_primeCombReciprocalBand.mp hpBand with ⟨hlow, hhigh, _hpPrime⟩
    exact Finset.mem_Ioc.mpr ⟨hlow, hhigh⟩
  calc
    (primeCombPostRootReciprocalBand W z).card ≤
        (Finset.Ioc (W / (z + 1)) (W / z)).card :=
      Finset.card_le_card hsub
    _ = W / z - W / (z + 1) := by simp

/-- Signed band covariance needs only the positive part of the lower-scale
covariance.  In particular a negative lower covariance helps rather than costs
anything. -/
theorem postRootReciprocalBandFamilyCovariance_le_width_mul_positivePart
    (W z : ℕ) (hz : 0 < z) :
    postRootReciprocalBandFamilyCovariance W z ≤
      ((W / z - W / (z + 1) : ℕ) : ℝ) *
        max (realMertensPositiveLagPairSum (z + 1)) 0 := by
  rw [postRootReciprocalBandFamilyCovariance_eq_card_mul_lowerCovariance W z hz]
  have hcard :
      ((primeCombPostRootReciprocalBand W z).card : ℝ) ≤
        ((W / z - W / (z + 1) : ℕ) : ℝ) := by
    exact_mod_cast card_primeCombPostRootReciprocalBand_le_width W z
  have hcov :
      realMertensPositiveLagPairSum (z + 1) ≤
        max (realMertensPositiveLagPairSum (z + 1)) 0 :=
    le_max_left _ _
  have hcard0 :
      (0 : ℝ) ≤ ((primeCombPostRootReciprocalBand W z).card : ℝ) := by positivity
  have hmax0 :
      (0 : ℝ) ≤ max (realMertensPositiveLagPairSum (z + 1)) 0 :=
    le_max_right _ _
  calc
    ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        realMertensPositiveLagPairSum (z + 1) ≤
      ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        max (realMertensPositiveLagPairSum (z + 1)) 0 :=
      mul_le_mul_of_nonneg_left hcov hcard0
    _ ≤ ((W / z - W / (z + 1) : ℕ) : ℝ) *
        max (realMertensPositiveLagPairSum (z + 1)) 0 :=
      mul_le_mul_of_nonneg_right hcard hmax0

/-! ## Exact Bessel remainder after the post-root families

The band identities above identify every post-root prime family with a complete
lower-scale covariance copy.  The only same-scale object left after removing all
of them is the cross-family/smooth covariance.  Green--Kubo turns this remainder
into one exact Bessel defect.  This is the intended target for a canonical
pair-owner/four-corner charging argument.
-/

/-- Literal post-root prime coordinates at endpoint `W`. -/
def postRootPrimeFamilySet (W : ℕ) : Finset ℕ :=
  (Finset.Ioc (Nat.sqrt W) W).filter Nat.Prime

@[simp] theorem mem_postRootPrimeFamilySet {W p : ℕ} :
    p ∈ postRootPrimeFamilySet W ↔ Nat.sqrt W < p ∧ p ≤ W ∧ p.Prime := by
  simp [postRootPrimeFamilySet, and_assoc]

/-- Total covariance inherited from all complete post-root prime families. -/
def postRootPrimeFamilyCovarianceTotal (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet W,
    realMertensPositiveLagPairSum (W / p + 1)

/-- The inherited covariance is literally the sum of the actual physical family
covariances, with no absolute value or prime-density estimate. -/
theorem postRootPrimeFamilyCovarianceTotal_eq_actualFamilies (W : ℕ) :
    postRootPrimeFamilyCovarianceTotal W =
      ∑ p ∈ postRootPrimeFamilySet W,
        largePrimeFamilyPairSum p (W / p + 1) := by
  unfold postRootPrimeFamilyCovarianceTotal
  apply Finset.sum_congr rfl
  intro p hp
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  have hW : W < p * p := (Nat.sqrt_lt).1 hpRoot
  exact (largePrimeFamilyPairSum_postRoot hpPrime hW).symm

/-- Signed same-scale covariance after all complete post-root family copies have
been removed. -/
def postRootCovarianceRemainder (W : ℕ) : ℝ :=
  realMertensPositiveLagPairSum (W + 1) -
    postRootPrimeFamilyCovarianceTotal W

/-- Sum of the lower-scale Mertens energies carried by the post-root families. -/
def postRootFamilyMertensSquareEnergy (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet W,
    ‖mertensSummatory (W / p)‖ ^ 2

/-- Sum of the exact lower-scale squarefree diagonals carried by those families. -/
def postRootFamilyDiagonalEnergy (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet W,
    realMertensDiagonal (W / p + 1)

/-- The part of the global diagonal not assigned to the post-root families. -/
def postRootComplementDiagonalResidual (W : ℕ) : ℝ :=
  realMertensDiagonal (W + 1) - postRootFamilyDiagonalEnergy W

/-- The inherited post-root covariance is half lower-scale Mertens energy minus
lower-scale diagonal energy. -/
theorem postRootPrimeFamilyCovarianceTotal_eq_energyDifference (W : ℕ) :
    postRootPrimeFamilyCovarianceTotal W =
      (postRootFamilyMertensSquareEnergy W -
        postRootFamilyDiagonalEnergy W) / 2 := by
  unfold postRootPrimeFamilyCovarianceTotal
    postRootFamilyMertensSquareEnergy postRootFamilyDiagonalEnergy
  simp_rw [realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

/-- **Exact Bessel-defect identity.**  Twice the unexplained covariance is the
global Mertens energy minus the complementary diagonal and all inherited
lower-scale family energies. -/
theorem two_mul_postRootCovarianceRemainder_eq_besselDefect (W : ℕ) :
    2 * postRootCovarianceRemainder W =
      ‖mertensSummatory W‖ ^ 2 -
        postRootComplementDiagonalResidual W -
        postRootFamilyMertensSquareEnergy W := by
  unfold postRootCovarianceRemainder postRootComplementDiagonalResidual
  rw [realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal W,
    postRootPrimeFamilyCovarianceTotal_eq_energyDifference W]
  ring

/-- A sufficient one-sided target: after removing every complete lower-scale
post-root family covariance, the remaining positive same-scale covariance is
only linear in the physical endpoint. -/
def PostRootCovarianceLinearRemainderStatement : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ W : ℕ, 2 ≤ W →
      postRootCovarianceRemainder W ≤ D * (W : ℝ)

/-- The weaker one-sided target needed for Mertens energy: the signed remainder
may have any positive power loss over linear growth, with its constant depending
on that loss. This is an explicit arithmetic hypothesis, not a proved bound. -/
def PostRootCovariancePowerRemainderStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ W : ℕ, 2 ≤ W →
        postRootCovarianceRemainder W ≤ D * Real.rpow (W : ℝ) (1 + ε)

/-- A linear remainder satisfies every positive-power remainder target. -/
theorem postRootCovariancePowerRemainder_of_linear
    (hlin : PostRootCovarianceLinearRemainderStatement) :
    PostRootCovariancePowerRemainderStatement := by
  intro ε hε
  rcases hlin with ⟨D, hD, hrem⟩
  refine ⟨D, hD, ?_⟩
  intro W hW
  have hbase : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast (by omega : 1 ≤ W)
  have hone : Real.rpow (W : ℝ) (1 : ℝ) = (W : ℝ) :=
    (Real.rpow_eq_pow (W : ℝ) (1 : ℝ)).trans (Real.rpow_one (W : ℝ))
  have hpow : (W : ℝ) ≤ Real.rpow (W : ℝ) (1 + ε) := by
    calc
      (W : ℝ) = Real.rpow (W : ℝ) (1 : ℝ) := hone.symm
      _ ≤ Real.rpow (W : ℝ) (1 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  exact (hrem W hW).trans (mul_le_mul_of_nonneg_left hpow hD)

/-- Equivalent Bessel form of the same one-sided linear statement. -/
def PostRootCovarianceBesselLinearStatement : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ W : ℕ, 2 ≤ W →
      ‖mertensSummatory W‖ ^ 2 ≤
        postRootComplementDiagonalResidual W +
          postRootFamilyMertensSquareEnergy W +
          2 * D * (W : ℝ)

/-- The covariance-remainder and Bessel-defect formulations are literally
equivalent. -/
theorem postRootCovarianceLinearRemainder_iff_besselLinear :
    PostRootCovarianceLinearRemainderStatement ↔
      PostRootCovarianceBesselLinearStatement := by
  constructor
  · rintro ⟨D, hD, hrem⟩
    refine ⟨D, hD, ?_⟩
    intro W hW
    have h := hrem W hW
    have hid := two_mul_postRootCovarianceRemainder_eq_besselDefect W
    nlinarith
  · rintro ⟨D, hD, hbessel⟩
    refine ⟨D, hD, ?_⟩
    intro W hW
    have h := hbessel W hW
    have hid := two_mul_postRootCovarianceRemainder_eq_besselDefect W
    nlinarith

/-- The linear remainder gives the exact recurrence used by the exponent
bootstrap: global covariance is inherited lower-scale covariance plus a linear
same-scale charge. -/
theorem globalCovariance_le_postRootFamilies_add_linear
    (hlin : PostRootCovarianceLinearRemainderStatement) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ W : ℕ, 2 ≤ W →
        realMertensPositiveLagPairSum (W + 1) ≤
          postRootPrimeFamilyCovarianceTotal W + D * (W : ℝ) := by
  rcases hlin with ⟨D, hD, hrem⟩
  refine ⟨D, hD, ?_⟩
  intro W hW
  have h := hrem W hW
  unfold postRootCovarianceRemainder at h
  linarith

/-! ## First-separation owner promotion on the quadratic carrier -/

private theorem prime_dvd_squarefreePrimeFamilyParent_iff_of_ne
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) :
    q ∣ squarefreePrimeFamilyParent p n ↔ q ∣ n := by
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    constructor
    · intro hqd
      rcases hqd with ⟨k, hk⟩
      refine ⟨p * k, ?_⟩
      rw [← Nat.mul_div_cancel' hpn, hk]
      ring
    · intro hqn
      have hprod : q ∣ p * (n / p) := by
        rw [Nat.mul_div_cancel' hpn]
        exact hqn
      rcases hq.dvd_mul.mp hprod with hqdp | hqd
      · have heq : q = p :=
          (Nat.prime_dvd_prime_iff_eq hq hp).mp hqdp
        exact (hqp heq).elim
      · exact hqd
  · simp [hpn]

private theorem squarefreePrimeFamilyParent_pos
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    0 < squarefreePrimeFamilyParent p n := by
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    exact Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  · simpa [hpn] using hn

private theorem squarefree_squarefreePrimeFamilyParent
    {p n : ℕ} (hn : Squarefree n) :
    Squarefree (squarefreePrimeFamilyParent p n) := by
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    exact hn.squarefree_of_dvd
      ⟨p, (Nat.div_mul_cancel hpn).symm⟩
  · simpa [hpn] using hn

private theorem mem_squarefreePrimeFace_parent_iff_of_ne
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hn : 0 < n) :
    q ∈ squarefreePrimeFace (squarefreePrimeFamilyParent p n) ↔
      q ∈ squarefreePrimeFace n := by
  have hparentPos := squarefreePrimeFamilyParent_pos hp hn
  have hdvd : q ∣ squarefreePrimeFamilyParent p n ↔ q ∣ n :=
    prime_dvd_squarefreePrimeFamilyParent_iff_of_ne (n := n) hp hq hqp
  constructor
  · intro hface
    have hmem : q ∈ (squarefreePrimeFamilyParent p n).primeFactors := by
      simpa [squarefreePrimeFace] using hface
    have hqdiv : q ∣ squarefreePrimeFamilyParent p n :=
      (Nat.mem_primeFactors.mp hmem).2.1
    have hqdivn : q ∣ n := hdvd.mp hqdiv
    have hmemn : q ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqdivn, hn.ne'⟩
    simpa [squarefreePrimeFace] using hmemn
  · intro hface
    have hmem : q ∈ n.primeFactors := by
      simpa [squarefreePrimeFace] using hface
    have hqdiv : q ∣ n := (Nat.mem_primeFactors.mp hmem).2.1
    have hqdivp : q ∣ squarefreePrimeFamilyParent p n := hdvd.mpr hqdiv
    have hmemp : q ∈ (squarefreePrimeFamilyParent p n).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqdivp, hparentPos.ne'⟩
    simpa [squarefreePrimeFace] using hmemp

private theorem owner_not_mem_squarefreePrimeFace_parent
    {p n : ℕ} (hp : p.Prime) (hn : Squarefree n) :
    p ∉ squarefreePrimeFace (squarefreePrimeFamilyParent p n) := by
  intro hface
  have hmem : p ∈ (squarefreePrimeFamilyParent p n).primeFactors := by
    simpa [squarefreePrimeFace] using hface
  exact (squarefreePrimeFamilyParent_not_dvd hp hn)
    ((Nat.mem_primeFactors.mp hmem).2.1)

/-- **Owner promotion after stripping the first separating prime.**  Let `p` be
the unique least prime on which two distinct squarefree endpoints differ.  Strip
`p` from the endpoint that carries it (and leave the other endpoint unchanged).
If the two stripped parents are still distinct, their next first-separation
owner is strictly larger than `p`.

This is the triangularity needed by the quadratic four-corner descent: the two
mixed `p`-corners are the current owner layer, while the old stripped pair lies
strictly later in the owner order. -/
theorem squarefreePairFreshPrimeOwner_lt_parentOwner
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hmn : m ≠ n) (hmpos : 0 < m) (hnpos : 0 < n)
    (hparentNe :
      squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m ≠
        squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n) :
    squarefreePairFreshPrimeOwner m n <
      squarefreePairFreshPrimeOwner
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m)
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n) := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hm hn hmn
  have humsq : Squarefree um := by
    dsimp [um]
    exact squarefree_squarefreePrimeFamilyParent hm
  have hunsq : Squarefree un := by
    dsimp [un]
    exact squarefree_squarefreePrimeFamilyParent hn
  have humpos : 0 < um := by
    dsimp [um]
    exact squarefreePrimeFamilyParent_pos hp hmpos
  have hunpos : 0 < un := by
    dsimp [un]
    exact squarefreePrimeFamilyParent_pos hp hnpos
  have hne : um ≠ un := by
    simpa [p, um, un] using hparentNe
  let q := squarefreePairFreshPrimeOwner um un
  have hqPrime : q.Prime := squarefreePairFreshPrimeOwner_prime humsq hunsq hne
  have hqXor := squarefreePairFreshPrimeOwner_xor humsq hunsq hne
  by_contra hnot
  have hqle : q ≤ p := Nat.le_of_not_gt hnot
  have hfaceEq : q ∈ squarefreePrimeFace um ↔ q ∈ squarefreePrimeFace un := by
    by_cases hqp : q = p
    · have hnotUm : p ∉ squarefreePrimeFace um := by
        dsimp [um]
        exact owner_not_mem_squarefreePrimeFace_parent hp hm
      have hnotUn : p ∉ squarefreePrimeFace un := by
        dsimp [un]
        exact owner_not_mem_squarefreePrimeFace_parent hp hn
      constructor
      · intro hmem
        exact (hnotUm (hqp ▸ hmem)).elim
      · intro hmem
        exact (hnotUn (hqp ▸ hmem)).elim
    · have hq_lt_p : q < p := by omega
      have hchron :
          q ∈ squarefreePrimeFace m ↔ q ∈ squarefreePrimeFace n :=
        squarefreePairFreshPrimeOwner_chronology hm hn hmn hq_lt_p
      have hqm : q ∈ squarefreePrimeFace um ↔ q ∈ squarefreePrimeFace m := by
        dsimp [um]
        exact mem_squarefreePrimeFace_parent_iff_of_ne hp hqPrime hqp hmpos
      have hqn : q ∈ squarefreePrimeFace un ↔ q ∈ squarefreePrimeFace n := by
        dsimp [un]
        exact mem_squarefreePrimeFace_parent_iff_of_ne hp hqPrime hqp hnpos
      exact hqm.trans (hchron.trans hqn.symm)
  rcases hqXor with h | h
  · exact h.2 (hfaceEq.mp h.1)
  · exact h.2 (hfaceEq.mpr h.1)

/-- Membership in a squarefree-face symmetric difference always certifies a
genuine prime coordinate. -/
private theorem prime_of_mem_squarefreePairFreshPrimeSet
    {q m n : ℕ} (hq : q ∈ squarefreePairFreshPrimeSet m n) :
    q.Prime := by
  unfold squarefreePairFreshPrimeSet at hq
  rcases Finset.mem_union.mp hq with hq | hq
  · have hface : q ∈ squarefreePrimeFace m :=
      (Finset.mem_sdiff.mp hq).1
    have hmem : q ∈ m.primeFactors := by
      simpa [squarefreePrimeFace] using hface
    exact (Nat.mem_primeFactors.mp hmem).1
  · have hface : q ∈ squarefreePrimeFace n :=
      (Finset.mem_sdiff.mp hq).1
    have hmem : q ∈ n.primeFactors := by
      simpa [squarefreePrimeFace] using hface
    exact (Nat.mem_primeFactors.mp hmem).1

/-- **Exact owner-coordinate erasure.**  Stripping the least separating prime
from both squarefree endpoints removes exactly that coordinate from their
symmetric-difference face.  Every other prime coordinate is unchanged. -/
theorem squarefreePairFreshPrimeSet_parent_eq_erase_owner
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hmn : m ≠ n) (hmpos : 0 < m) (hnpos : 0 < n) :
    squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m)
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n) =
      (squarefreePairFreshPrimeSet m n).erase
        (squarefreePairFreshPrimeOwner m n) := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  change squarefreePairFreshPrimeSet um un =
    (squarefreePairFreshPrimeSet m n).erase p
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hm hn hmn
  have hnotUm : p ∉ squarefreePrimeFace um := by
    dsimp [um]
    exact owner_not_mem_squarefreePrimeFace_parent hp hm
  have hnotUn : p ∉ squarefreePrimeFace un := by
    dsimp [un]
    exact owner_not_mem_squarefreePrimeFace_parent hp hn
  ext q
  by_cases hqp : q = p
  · subst q
    constructor
    · intro hmem
      unfold squarefreePairFreshPrimeSet at hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact (hnotUm (Finset.mem_sdiff.mp h).1).elim
      · exact (hnotUn (Finset.mem_sdiff.mp h).1).elim
    · intro hmem
      exact ((Finset.mem_erase.mp hmem).1 rfl).elim
  · constructor
    · intro hmem
      have hqPrime : q.Prime :=
        prime_of_mem_squarefreePairFreshPrimeSet hmem
      have hqm : q ∈ squarefreePrimeFace um ↔
          q ∈ squarefreePrimeFace m := by
        dsimp [um]
        exact mem_squarefreePrimeFace_parent_iff_of_ne
          hp hqPrime hqp hmpos
      have hqn : q ∈ squarefreePrimeFace un ↔
          q ∈ squarefreePrimeFace n := by
        dsimp [un]
        exact mem_squarefreePrimeFace_parent_iff_of_ne
          hp hqPrime hqp hnpos
      apply Finset.mem_erase.mpr
      refine ⟨hqp, ?_⟩
      unfold squarefreePairFreshPrimeSet at hmem ⊢
      simpa only [Finset.mem_union, Finset.mem_sdiff, hqm, hqn] using hmem
    · intro hmem
      have horig : q ∈ squarefreePairFreshPrimeSet m n :=
        (Finset.mem_erase.mp hmem).2
      have hqPrime : q.Prime :=
        prime_of_mem_squarefreePairFreshPrimeSet horig
      have hqm : q ∈ squarefreePrimeFace um ↔
          q ∈ squarefreePrimeFace m := by
        dsimp [um]
        exact mem_squarefreePrimeFace_parent_iff_of_ne
          hp hqPrime hqp hmpos
      have hqn : q ∈ squarefreePrimeFace un ↔
          q ∈ squarefreePrimeFace n := by
        dsimp [un]
        exact mem_squarefreePrimeFace_parent_iff_of_ne
          hp hqPrime hqp hnpos
      unfold squarefreePairFreshPrimeSet at horig ⊢
      simpa only [Finset.mem_union, Finset.mem_sdiff, hqm, hqn] using horig

/-- Owner stripping is a strict finite descent: the differing-prime face loses
exactly one coordinate at every step. -/
theorem squarefreePairFreshPrimeSet_parent_card_add_one
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hmn : m ≠ n) (hmpos : 0 < m) (hnpos : 0 < n) :
    (squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m)
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n)).card + 1 =
      (squarefreePairFreshPrimeSet m n).card := by
  rw [squarefreePairFreshPrimeSet_parent_eq_erase_owner
    hm hn hmn hmpos hnpos]
  rw [Finset.card_erase_of_mem
    (squarefreePairFreshPrimeOwner_mem hm hn hmn)]
  have hcard :
      0 < (squarefreePairFreshPrimeSet m n).card :=
    Finset.card_pos.mpr (squarefreePairFreshPrimeSet_nonempty hm hn hmn)
  omega

/-- **Signed owner descent.**  A physical pair is one mixed corner of its
owner's fresh-prime square, so stripping that owner reverses the pair weight
exactly. -/
theorem squarefreePairFreshPrimeOwner_pairWeight_eq_neg_parentPairWeight
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hmn : m ≠ n) (hmpos : 0 < m) (hnpos : 0 < n) :
    realMoebiusStep m * realMoebiusStep n =
      -(realMoebiusStep
          (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m) *
        realMoebiusStep
          (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n)) := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  change realMoebiusStep m * realMoebiusStep n =
    -(realMoebiusStep um * realMoebiusStep un)
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hm hn hmn
  have hcube :=
    squarefreePairFreshPrimeOwner_parentCube hm hn hmn hmpos hnpos
  change (¬ p ∣ um) ∧ (¬ p ∣ un) ∧
      ((m = p * um ∧ n = un) ∨ (m = um ∧ n = p * un)) at hcube
  rcases hcube with ⟨hpm, hpn, h | h⟩
  · rw [h.1, h.2, realMoebiusStep_mul_prime_eq_neg hp hpm]
    ring
  · rw [h.1, h.2, realMoebiusStep_mul_prime_eq_neg hp hpn]
    ring

end RHLean.Proof
