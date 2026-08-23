import Mathlib
import RHLean.Analysis.SquareRootPostCrossingRenewal

/-!
# Canonical rough-prime covariance after the shallow crossing

The orientation-free renewal row from
`SquareRootPostCrossingRenewal` still presents its cancellation in reciprocal
depth.  This module pushes the complete lower-triangular renewal back onto the
cofactor coordinate.

For one cofactor `c`, its response contains both its diagonal reciprocal-prime
multiplicity and every strict quotient descendant, paired with the appropriate
lower Mertens state.  The complete post-crossing tail is then exactly

```text
explicit packet baseline - sum_c mu(c) * cofactorResponse(c).
```

Thus the remaining nonlocal cancellation is a literal finite correlation
between the Möbius-parity field and one intact rough-prime response field.  No
mean-zero assertion, norm split, probabilistic independence, or quantitative
estimate is used here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- Prime multiplicity carried by cofactor `c` in reciprocal layer `z`.  The
largest-prime-factor cutoff is the canonical freshness condition. -/
def squareRootCanonicalRoughPrimeMultiplicity (R c z : ℕ) : ℂ :=
  primeSieveReciprocalPrimeCount (canonicalLargestPrimeFactor c)
    (squareRootEndpoint R / c) z

/-- The contribution of one cofactor to one lower renewal row.  The first term
is the diagonal fibre; the sum retains every strict descendant. -/
def squareRootCanonicalRoughCofactorRowResponse
    (R c y : ℕ) : ℂ :=
  squareRootCanonicalRoughPrimeMultiplicity R c y +
    ∑ z ∈ Finset.Icc (y + 1) (R - 1),
      squareRootCanonicalRoughPrimeMultiplicity R c z *
        squareRootReplacementQuotientKernel z y

/-- Complete scalar response of one cofactor after pairing its intact renewal
row with all lower Mertens states. -/
def squareRootCanonicalRoughCofactorResponse (R c : ℕ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 (R - 1),
    squareRootCanonicalRoughCofactorRowResponse R c y *
      mertensSummatory y

/-- The complete lower-triangular Mertens renewal state seen from reciprocal
depth `z`.  The zero depth is retained in the ambient range only for convenient
matrix notation; every positive depth will collapse to the unit state. -/
def squareRootCanonicalRoughRenewalState (R z : ℕ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 (R - 1),
    squareRootReplacementQuotientKernel z y * mertensSummatory y

/-- Total number of canonical fresh-prime partners carried by one cofactor.
Unlike the response above, this field contains no Mertens value. -/
def squareRootCanonicalRoughPrimePartnerCount (R c : ℕ) : ℂ :=
  ∑ z ∈ Finset.Icc 1 (R - 1),
    squareRootCanonicalRoughPrimeMultiplicity R c z

/-- The uncentered Möbius--rough-prime correlation numerator. -/
def squareRootCanonicalRoughCorrelation (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
    canonicalMoebiusWeight c *
      squareRootCanonicalRoughCofactorResponse R c

/-- Number of cofactors in the canonical rough-prime correlation. -/
def squareRootCanonicalRoughCofactorCard (R : ℕ) : ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).card

/-- Total Möbius parity on the canonical cofactor range. -/
def squareRootCanonicalRoughParitySum (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
    canonicalMoebiusWeight c

/-- Total unweighted response on the same cofactor range. -/
def squareRootCanonicalRoughResponseSum (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
    squareRootCanonicalRoughCofactorResponse R c

/-- Uniform mean of the Möbius parity field. -/
def squareRootCanonicalRoughParityMean (R : ℕ) : ℂ :=
  squareRootCanonicalRoughParitySum R /
    (squareRootCanonicalRoughCofactorCard R : ℂ)

/-- Uniform mean of the intact cofactor response field. -/
def squareRootCanonicalRoughResponseMean (R : ℕ) : ℂ :=
  squareRootCanonicalRoughResponseSum R /
    (squareRootCanonicalRoughCofactorCard R : ℂ)

/-- Uniform centered covariance of Möbius parity with the complete rough-prime
response.  This is normalized by the number of active cofactor coordinates;
no probabilistic hypothesis is attached to the definition. -/
def squareRootCanonicalRoughCovariance (R : ℕ) : ℂ :=
  (((squareRootCanonicalRoughCofactorCard R : ℕ) : ℂ) *
        squareRootCanonicalRoughCorrelation R -
      squareRootCanonicalRoughParitySum R *
        squareRootCanonicalRoughResponseSum R) /
    (((squareRootCanonicalRoughCofactorCard R : ℕ) : ℂ) ^ 2)

/-- The terminal and crossing-removal part of the canonical row.  It is kept
explicit rather than hidden inside an unjustified mean-zero convention. -/
def squareRootPostCrossingCanonicalBaseline (R K j : ℕ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 (R - 1),
    ((if y = R - 1 then 1 else 0) +
        squareRootCrossingRemovalCoefficient R K j y) *
      mertensSummatory y

/-- One full canonical rough fibre is the negative Möbius-weighted sum of its
cofactor multiplicities. -/
theorem replacementFibreCanonicalRoughFullMass_eq_neg_sum_multiplicity
    (R z : ℕ) :
    replacementFibreCanonicalRoughFullMass R z =
      -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          squareRootCanonicalRoughPrimeMultiplicity R c z := by
  rfl

/-- The canonical cofactor range is nonempty at every relevant root scale. -/
theorem squareRootCanonicalRoughCofactorCard_pos
    (R : ℕ) (hR : 2 ≤ R) :
    0 < squareRootCanonicalRoughCofactorCard R := by
  unfold squareRootCanonicalRoughCofactorCard
  apply Finset.card_pos.mpr
  refine ⟨1, ?_⟩
  simp only [Finset.mem_Icc, le_refl, true_and]
  unfold squareRootEndpoint
  have hsq : 4 ≤ R ^ 2 := by nlinarith
  omega

private theorem sum_range_mul_quotientKernel_eq_diagonal_add_strict
    (F : ℕ → ℂ) (R y : ℕ) (hy : 1 ≤ y) (hyR : y < R) :
    (∑ z ∈ Finset.range R,
        F z * squareRootReplacementQuotientKernel z y) =
      F y +
        ∑ z ∈ Finset.Icc (y + 1) (R - 1),
          F z * squareRootReplacementQuotientKernel z y := by
  let f : ℕ → ℂ := fun z =>
    F z * squareRootReplacementQuotientKernel z y
  have hzero : (∑ z ∈ Finset.range y, f z) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    have hzy : z < y := Finset.mem_range.mp hz
    unfold f
    rw [squareRootReplacementQuotientKernel_eq_zero_of_lt hzy]
    ring
  have hset :
      Finset.Ico (y + 1) R = Finset.Icc (y + 1) (R - 1) := by
    ext z
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  calc
    (∑ z ∈ Finset.range R,
        F z * squareRootReplacementQuotientKernel z y) =
        (∑ z ∈ Finset.range (y + 1), f z) +
          ∑ z ∈ Finset.Ico (y + 1) R, f z := by
            simpa [f] using
              (Finset.sum_range_add_sum_Ico f
                (Nat.succ_le_of_lt hyR)).symm
    _ = ((∑ z ∈ Finset.range y, f z) + f y) +
          ∑ z ∈ Finset.Ico (y + 1) R, f z := by
            rw [Finset.sum_range_succ]
    _ = f y + ∑ z ∈ Finset.Ico (y + 1) R, f z := by
          rw [hzero, zero_add]
    _ = F y +
          ∑ z ∈ Finset.Icc (y + 1) (R - 1),
            F z * squareRootReplacementQuotientKernel z y := by
      unfold f
      rw [squareRootReplacementQuotientKernel_self hy, hset]
      ring

/-- The unit Möbius renewal identity in the exact finite quotient-kernel
coordinates used by the canonical rough response. -/
theorem squareRootCanonicalRoughRenewalState_eq_one
    (R z : ℕ) (hz : 1 ≤ z) (hzR : z < R) :
    squareRootCanonicalRoughRenewalState R z = 1 := by
  classical
  have hfull :
      (∑ y ∈ Finset.range R,
          squareRootReplacementQuotientKernel z y *
            mertensSummatory y) = 1 := by
    unfold squareRootReplacementQuotientKernel
    calc
      (∑ y ∈ Finset.range R,
          (∑ k ∈ Finset.Icc 1 z, if z / k = y then 1 else 0) *
            mertensSummatory y) =
        ∑ y ∈ Finset.range R,
          ∑ k ∈ Finset.Icc 1 z,
            (if z / k = y then 1 else 0) * mertensSummatory y := by
              apply Finset.sum_congr rfl
              intro y _hy
              rw [Finset.sum_mul]
      _ = ∑ k ∈ Finset.Icc 1 z,
          ∑ y ∈ Finset.range R,
            (if z / k = y then 1 else 0) * mertensSummatory y := by
              rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.Icc 1 z, mertensSummatory (z / k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkI := Finset.mem_Icc.mp hk
            have hqle : z / k ≤ z := Nat.div_le_self z k
            have hqR : z / k < R := hqle.trans_lt hzR
            have hqmem : z / k ∈ Finset.range R :=
              Finset.mem_range.mpr hqR
            calc
              (∑ y ∈ Finset.range R,
                  (if z / k = y then 1 else 0) * mertensSummatory y) =
                ∑ y ∈ Finset.range R,
                  if z / k = y then mertensSummatory y else 0 := by
                    apply Finset.sum_congr rfl
                    intro y _hy
                    by_cases heq : z / k = y <;> simp [heq]
              _ = mertensSummatory (z / k) := by simp [hqmem]
      _ = 1 := RHLean.Analysis.sum_mertensSummatory_div_eq_one hz
  have hset :
      Finset.range R = ({0} : Finset ℕ) ∪ Finset.Icc 1 (R - 1) := by
    ext y
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Icc]
    omega
  have hdisj :
      Disjoint ({0} : Finset ℕ) (Finset.Icc 1 (R - 1)) := by
    simp
  unfold squareRootCanonicalRoughRenewalState
  rw [hset, Finset.sum_union hdisj] at hfull
  simpa using hfull

/-- Fubini identifies the intact cofactor response with its prime
multiplicities paired against the complete renewal state. -/
theorem squareRootCanonicalRoughCofactorResponse_eq_sum_mul_renewalState
    (R c : ℕ) :
    squareRootCanonicalRoughCofactorResponse R c =
      ∑ z ∈ Finset.range R,
        squareRootCanonicalRoughPrimeMultiplicity R c z *
          squareRootCanonicalRoughRenewalState R z := by
  classical
  unfold squareRootCanonicalRoughCofactorResponse
    squareRootCanonicalRoughCofactorRowResponse
    squareRootCanonicalRoughRenewalState
  calc
    (∑ y ∈ Finset.Icc 1 (R - 1),
        (squareRootCanonicalRoughPrimeMultiplicity R c y +
          ∑ z ∈ Finset.Icc (y + 1) (R - 1),
            squareRootCanonicalRoughPrimeMultiplicity R c z *
              squareRootReplacementQuotientKernel z y) *
          mertensSummatory y) =
      ∑ y ∈ Finset.Icc 1 (R - 1),
        (∑ z ∈ Finset.range R,
          squareRootCanonicalRoughPrimeMultiplicity R c z *
            squareRootReplacementQuotientKernel z y) *
          mertensSummatory y := by
            apply Finset.sum_congr rfl
            intro y hy
            rcases Finset.mem_Icc.mp hy with ⟨hy1, hyR⟩
            rw [sum_range_mul_quotientKernel_eq_diagonal_add_strict
              (squareRootCanonicalRoughPrimeMultiplicity R c) R y
              hy1 (by omega)]
    _ = ∑ z ∈ Finset.range R,
        squareRootCanonicalRoughPrimeMultiplicity R c z *
          ∑ y ∈ Finset.Icc 1 (R - 1),
            squareRootReplacementQuotientKernel z y *
              mertensSummatory y := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring

/-- **Cofactorwise renewal collapse.**  The apparently Mertens-dependent
descendant response is exactly the nonnegative prime-partner multiplicity.
All lower-scale Mertens values have telescoped before any norm is taken. -/
theorem squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount
    (R c : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughCofactorResponse R c =
      squareRootCanonicalRoughPrimePartnerCount R c := by
  classical
  rw [squareRootCanonicalRoughCofactorResponse_eq_sum_mul_renewalState]
  unfold squareRootCanonicalRoughPrimePartnerCount
  have hset :
      Finset.range R = ({0} : Finset ℕ) ∪ Finset.Icc 1 (R - 1) := by
    ext z
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Icc]
    omega
  have hdisj :
      Disjoint ({0} : Finset ℕ) (Finset.Icc 1 (R - 1)) := by
    simp
  rw [hset, Finset.sum_union hdisj]
  have hzero : squareRootCanonicalRoughRenewalState R 0 = 0 := by
    unfold squareRootCanonicalRoughRenewalState
      squareRootReplacementQuotientKernel
    simp
  rw [Finset.sum_singleton, hzero, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro z hz
  rcases Finset.mem_Icc.mp hz with ⟨hz1, hzR⟩
  rw [squareRootCanonicalRoughRenewalState_eq_one R z hz1 (by omega),
    mul_one]

/-- The uncentered correlation is literally Möbius parity tested against the
nonnegative prime-partner count. -/
theorem squareRootCanonicalRoughCorrelation_eq_weighted_primePartnerCount
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughCorrelation R =
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          squareRootCanonicalRoughPrimePartnerCount R c := by
  unfold squareRootCanonicalRoughCorrelation
  apply Finset.sum_congr rfl
  intro c _hc
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR]

/-- The parity zero mode on the cofactor range is exactly the endpoint Mertens
value. -/
theorem squareRootCanonicalRoughParitySum_eq_mertensSummatory
    (R : ℕ) :
    squareRootCanonicalRoughParitySum R =
      mertensSummatory (squareRootEndpoint R) := by
  unfold squareRootCanonicalRoughParitySum canonicalMoebiusWeight
  exact (mertensSummatory_eq_sum_Icc (squareRootEndpoint R)).symm

private theorem squareRootReplacementTailMoebiusCoefficient_zero
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootReplacementTailMoebiusCoefficient R 0 = 0 := by
  unfold squareRootReplacementTailMoebiusCoefficient
  apply Finset.sum_eq_zero
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnR, hnX⟩
  have hnpos : 0 < n := by omega
  have hq1 : 1 ≤ squareRootEndpoint R / n :=
    (Nat.one_le_div_iff hnpos).2 hnX
  have hne : squareRootEndpoint R / n ≠ 0 := by omega
  simp [hne]

/-- **No hidden gain in the covariance reindexing.**  After the unit renewal
collapse and unique rough-prime fibre dictionary, the parity/partner
correlation is exactly the negative complementary Mertens tail. -/
theorem squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughCorrelation R =
      mertensSummatory (R - 1) -
        mertensSummatory (squareRootEndpoint R) := by
  classical
  rw [squareRootCanonicalRoughCorrelation_eq_weighted_primePartnerCount
    R hR]
  unfold squareRootCanonicalRoughPrimePartnerCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ z ∈ Finset.Icc 1 (R - 1),
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          canonicalMoebiusWeight c *
            squareRootCanonicalRoughPrimeMultiplicity R c z) =
      -∑ z ∈ Finset.Icc 1 (R - 1),
        squareRootReplacementTailMoebiusCoefficient R z := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro z hz
          rcases Finset.mem_Icc.mp hz with ⟨hz1, hzR⟩
          rw [squareRootReplacementTailMoebiusCoefficient_eq_canonicalRoughFullMass
              R z hR hz1 (by omega),
            replacementFibreCanonicalRoughFullMass_eq_neg_sum_multiplicity]
          ring
    _ = -∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z := by
      have hset :
          Finset.range R = ({0} : Finset ℕ) ∪ Finset.Icc 1 (R - 1) := by
        ext z
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_Icc]
        omega
      have hdisj :
          Disjoint ({0} : Finset ℕ) (Finset.Icc 1 (R - 1)) := by
        simp
      rw [hset, Finset.sum_union hdisj, Finset.sum_singleton,
        squareRootReplacementTailMoebiusCoefficient_zero R hR, zero_add]
    _ = -(mertensSummatory (squareRootEndpoint R) -
          mertensSummatory (R - 1)) := by
      rw [sum_squareRootReplacementTailMoebiusCoefficient_eq_mertens_sub_pred
        R hR]
    _ = mertensSummatory (R - 1) -
          mertensSummatory (squareRootEndpoint R) := by ring

/-- The direct critical estimate on the parity/prime-partner correlation. -/
def SquareRootCanonicalRoughCorrelationBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

private theorem canonicalRough_norm_sq_add_le_two (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

private theorem canonicalRough_sq_le_rpow_two_add
    {R : ℕ} {ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) :
    (R : ℝ) ^ 2 ≤ Real.rpow (R : ℝ) (2 + ε) := by
  have hbase : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hexp : (2 : ℝ) ≤ 2 + ε := by linarith
  have h := Real.rpow_le_rpow_of_exponent_le hbase hexp
  simpa [Real.rpow_two] using h

/-- Square-prefix critical control bounds the concrete covariance numerator. -/
theorem squareRootCanonicalRoughCorrelationBounded_of_squarePrefixEnergyBounded
    (hS : SquarePrefixEnergyBoundedStatement) :
    SquareRootCanonicalRoughCorrelationBoundedStatement := by
  intro ε hε
  rcases hS ε hε with ⟨C, hC, hbound⟩
  let D : ℝ := 2 + 2 * C
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro R hR
  have hsum := canonicalRough_norm_sq_add_le_two
    (mertensSummatory (R - 1))
    (-mertensSummatory (squareRootEndpoint R))
  have hcorrSq :
      ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
        2 * ‖mertensSummatory (R - 1)‖ ^ 2 +
          2 * ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 := by
    rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
      R hR]
    simpa [sub_eq_add_neg] using hsum
  have hMpred := norm_mertensSummatory_sub_le 0 (R - 1) (Nat.zero_le _)
  rw [mertensSummatory_zero, sub_zero] at hMpred
  have hMpredSq :
      ‖mertensSummatory (R - 1)‖ ^ 2 ≤ (R : ℝ) ^ 2 := by
    have hpredCast : (((R - 1 : ℕ) : ℝ)) ≤ (R : ℝ) := by
      exact_mod_cast Nat.sub_le R 1
    have hMpred' :
        ‖mertensSummatory (R - 1)‖ ≤ (((R - 1 : ℕ) : ℝ)) := by
      simpa using hMpred
    have hMpredR : ‖mertensSummatory (R - 1)‖ ≤ (R : ℝ) :=
      hMpred'.trans hpredCast
    nlinarith [norm_nonneg (mertensSummatory (R - 1))]
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega : 1 ≤ R)
  have hMendpoint :
      ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤
        C * Real.rpow (R : ℝ) (2 + ε) := by
    simpa [squarePrefixMertens, squarePrefixEndpoint, hpred] using
      hbound (R - 1)
  have hpow := canonicalRough_sq_le_rpow_two_add (by omega : 1 ≤ R) hε
  calc
    ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
        2 * ‖mertensSummatory (R - 1)‖ ^ 2 +
          2 * ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 := hcorrSq
    _ ≤ 2 * ((R : ℝ) ^ 2) +
          2 * (C * Real.rpow (R : ℝ) (2 + ε)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hMpredSq (by norm_num))
        (mul_le_mul_of_nonneg_left hMendpoint (by norm_num))
    _ ≤ 2 * Real.rpow (R : ℝ) (2 + ε) +
          2 * (C * Real.rpow (R : ℝ) (2 + ε)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) _
    _ = D * Real.rpow (R : ℝ) (2 + ε) := by
      dsimp [D]
      ring

/-- Conversely, the parity/prime-partner covariance numerator reconstructs the
square-prefix Mertens value up to the trivially bounded lower endpoint. -/
theorem squarePrefixEnergyBounded_of_squareRootCanonicalRoughCorrelationBounded
    (hC : SquareRootCanonicalRoughCorrelationBoundedStatement) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases hC ε hε with ⟨C, hC0, hbound⟩
  let D : ℝ := 2 + 2 * C
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [squarePrefixMertens, squarePrefixEndpoint, D, hD]
  · let R : ℕ := n + 1
    have hR : 2 ≤ R := by
      dsimp [R]
      omega
    have hcorr :=
      squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R hR
    have hpred : R - 1 = n := by
      dsimp [R]
    have hendpoint : squareRootEndpoint R = squarePrefixEndpoint n := by
      dsimp [R]
      unfold squareRootEndpoint squarePrefixEndpoint
      rfl
    have hreconstruct :
        mertensSummatory (squarePrefixEndpoint n) =
          mertensSummatory n - squareRootCanonicalRoughCorrelation R := by
      rw [hcorr, hpred, hendpoint]
      ring
    have hsum := canonicalRough_norm_sq_add_le_two
      (mertensSummatory n) (-squareRootCanonicalRoughCorrelation R)
    have hMpred := norm_mertensSummatory_sub_le 0 n (Nat.zero_le _)
    rw [mertensSummatory_zero, sub_zero] at hMpred
    have hMpredSq :
        ‖mertensSummatory n‖ ^ 2 ≤ (R : ℝ) ^ 2 := by
      have hnR : (n : ℝ) ≤ (R : ℝ) := by
        dsimp [R]
        exact_mod_cast Nat.le_succ n
      have hMpred' : ‖mertensSummatory n‖ ≤ (n : ℝ) := by
        simpa using hMpred
      have hMpredR : ‖mertensSummatory n‖ ≤ (R : ℝ) :=
        hMpred'.trans hnR
      nlinarith [norm_nonneg (mertensSummatory n)]
    have hcorrBound := hbound R hR
    have hpow := canonicalRough_sq_le_rpow_two_add (by omega : 1 ≤ R) hε
    have hbase : ((n + 1 : ℕ) : ℝ) = (R : ℝ) := by rfl
    rw [squarePrefixMertens, hreconstruct]
    calc
      ‖mertensSummatory n - squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
          2 * ‖mertensSummatory n‖ ^ 2 +
            2 * ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 := by
        simpa [sub_eq_add_neg] using hsum
      _ ≤ 2 * ((R : ℝ) ^ 2) +
            2 * (C * Real.rpow (R : ℝ) (2 + ε)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hMpredSq (by norm_num))
          (mul_le_mul_of_nonneg_left hcorrBound (by norm_num))
      _ ≤ 2 * Real.rpow (R : ℝ) (2 + ε) +
            2 * (C * Real.rpow (R : ℝ) (2 + ε)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) _
      _ = D * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by
        rw [hbase]
        dsimp [D]
        ring

/-- The normalized-covariance numerator is exactly the full critical Mertens
energy problem, with no loss in either direction. -/
theorem squareRootCanonicalRoughCorrelationBounded_iff_mertensEnergyBounded :
    SquareRootCanonicalRoughCorrelationBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  rw [mertensEnergyBounded_iff_squarePrefixEnergyBounded]
  exact ⟨squarePrefixEnergyBounded_of_squareRootCanonicalRoughCorrelationBounded,
    squareRootCanonicalRoughCorrelationBounded_of_squarePrefixEnergyBounded⟩

private theorem sum_centered_mul_centered
    {α : Type*} (s : Finset α) (f g : α → ℂ)
    (hcard : (s.card : ℂ) ≠ 0) :
    (∑ x ∈ s,
        (f x - (∑ t ∈ s, f t) / (s.card : ℂ)) *
          (g x - (∑ t ∈ s, g t) / (s.card : ℂ))) =
      (∑ x ∈ s, f x * g x) -
        (∑ x ∈ s, f x) * (∑ x ∈ s, g x) / (s.card : ℂ) := by
  classical
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard]
  ring

/-- The algebraic covariance definition is literally the average product of
the centered parity and response fields. -/
theorem squareRootCanonicalRoughCovariance_eq_centered_average
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughCovariance R =
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          (canonicalMoebiusWeight c -
              squareRootCanonicalRoughParityMean R) *
            (squareRootCanonicalRoughCofactorResponse R c -
              squareRootCanonicalRoughResponseMean R)) /
        (squareRootCanonicalRoughCofactorCard R : ℂ) := by
  classical
  let s := Finset.Icc 1 (squareRootEndpoint R)
  have hcardNat : s.card ≠ 0 := by
    dsimp [s]
    exact Nat.ne_of_gt (squareRootCanonicalRoughCofactorCard_pos R hR)
  have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast hcardNat
  have hcenter := sum_centered_mul_centered s
    canonicalMoebiusWeight
    (squareRootCanonicalRoughCofactorResponse R) hcard
  unfold squareRootCanonicalRoughCovariance
    squareRootCanonicalRoughParityMean
    squareRootCanonicalRoughResponseMean
    squareRootCanonicalRoughParitySum
    squareRootCanonicalRoughResponseSum
    squareRootCanonicalRoughCorrelation
    squareRootCanonicalRoughCofactorCard
  dsimp [s] at hcenter hcard
  rw [hcenter]
  field_simp [hcard]

/-- Exact mean-plus-covariance decomposition of the uncentered correlation.
The mean term is retained explicitly; dropping it would insert the unresolved
Mertens zero mode by hand. -/
theorem squareRootCanonicalRoughCorrelation_eq_card_mul_mean_add_covariance
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughCorrelation R =
      (squareRootCanonicalRoughCofactorCard R : ℂ) *
        (squareRootCanonicalRoughParityMean R *
            squareRootCanonicalRoughResponseMean R +
          squareRootCanonicalRoughCovariance R) := by
  classical
  have hcardNat : squareRootCanonicalRoughCofactorCard R ≠ 0 :=
    Nat.ne_of_gt (squareRootCanonicalRoughCofactorCard_pos R hR)
  have hcard : (squareRootCanonicalRoughCofactorCard R : ℂ) ≠ 0 := by
    exact_mod_cast hcardNat
  unfold squareRootCanonicalRoughCovariance
    squareRootCanonicalRoughParityMean
    squareRootCanonicalRoughResponseMean
  field_simp [hcard]
  ring

/-- The normalized parity mean is exactly the endpoint Mertens zero mode divided
by the number of cofactors. -/
theorem squareRootCanonicalRoughParityMean_eq_mertens_div_card
    (R : ℕ) :
    squareRootCanonicalRoughParityMean R =
      mertensSummatory (squareRootEndpoint R) /
        (squareRootCanonicalRoughCofactorCard R : ℂ) := by
  unfold squareRootCanonicalRoughParityMean
  rw [squareRootCanonicalRoughParitySum_eq_mertensSummatory]

/-- After renewal collapse, the response mean is the uniform mean of the plain
prime-partner counts. -/
theorem squareRootCanonicalRoughResponseMean_eq_primePartnerMean
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughResponseMean R =
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          squareRootCanonicalRoughPrimePartnerCount R c) /
        (squareRootCanonicalRoughCofactorCard R : ℂ) := by
  unfold squareRootCanonicalRoughResponseMean
    squareRootCanonicalRoughResponseSum
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  exact squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR

/-- Exact normalized-covariance form of the complementary Mertens tail.  This
is the precise sense in which the nonlocal parity correlation is a covariance:
the desired tail is the cofactor count times `mean product + covariance`. -/
theorem squareRootCanonicalRoughMeanProduct_add_covariance_eq_tail_div_card
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughParityMean R *
          squareRootCanonicalRoughResponseMean R +
        squareRootCanonicalRoughCovariance R =
      (mertensSummatory (R - 1) -
          mertensSummatory (squareRootEndpoint R)) /
        (squareRootCanonicalRoughCofactorCard R : ℂ) := by
  have hcardNat : squareRootCanonicalRoughCofactorCard R ≠ 0 :=
    Nat.ne_of_gt (squareRootCanonicalRoughCofactorCard_pos R hR)
  have hcard : (squareRootCanonicalRoughCofactorCard R : ℂ) ≠ 0 := by
    exact_mod_cast hcardNat
  apply (eq_div_iff hcard).2
  calc
    (squareRootCanonicalRoughParityMean R *
          squareRootCanonicalRoughResponseMean R +
        squareRootCanonicalRoughCovariance R) *
          (squareRootCanonicalRoughCofactorCard R : ℂ) =
      (squareRootCanonicalRoughCofactorCard R : ℂ) *
        (squareRootCanonicalRoughParityMean R *
            squareRootCanonicalRoughResponseMean R +
          squareRootCanonicalRoughCovariance R) := by ring
    _ = squareRootCanonicalRoughCorrelation R :=
      (squareRootCanonicalRoughCorrelation_eq_card_mul_mean_add_covariance
        R hR).symm
    _ = mertensSummatory (R - 1) -
          mertensSummatory (squareRootEndpoint R) :=
      squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R hR

/-- Solving the preceding identity for the centered covariance exposes the
unavoidable zero-mode product explicitly. -/
theorem squareRootCanonicalRoughCovariance_eq_tail_div_card_sub_meanProduct
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughCovariance R =
      (mertensSummatory (R - 1) -
          mertensSummatory (squareRootEndpoint R)) /
          (squareRootCanonicalRoughCofactorCard R : ℂ) -
        squareRootCanonicalRoughParityMean R *
          squareRootCanonicalRoughResponseMean R := by
  have h :=
    squareRootCanonicalRoughMeanProduct_add_covariance_eq_tail_div_card R hR
  linear_combination h

/-- Cofactorwise expansion of one complete canonical renewal row. -/
theorem canonicalRoughFullMass_add_strictDescendants_eq_neg_cofactorResponse
    (R y : ℕ) :
    replacementFibreCanonicalRoughFullMass R y +
        squareRootCanonicalRoughStrictDescendantTransform R y =
      -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          squareRootCanonicalRoughCofactorRowResponse R c y := by
  classical
  unfold squareRootCanonicalRoughStrictDescendantTransform
    squareRootCanonicalRoughCofactorRowResponse
  simp_rw [replacementFibreCanonicalRoughFullMass_eq_neg_sum_multiplicity]
  simp_rw [neg_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  rw [Finset.sum_add_distrib]
  ring_nf

/-- Pairing the complete canonical rough renewal with the lower Mertens row is
exactly the negative Möbius--response correlation. -/
theorem sum_canonicalRoughRenewal_mul_mertens_eq_neg_correlation
    (R : ℕ) :
    (∑ y ∈ Finset.Icc 1 (R - 1),
        (replacementFibreCanonicalRoughFullMass R y +
            squareRootCanonicalRoughStrictDescendantTransform R y) *
          mertensSummatory y) =
      -squareRootCanonicalRoughCorrelation R := by
  classical
  simp_rw [canonicalRoughFullMass_add_strictDescendants_eq_neg_cofactorResponse]
  unfold squareRootCanonicalRoughCorrelation
    squareRootCanonicalRoughCofactorResponse
  simp_rw [neg_mul, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  ring_nf

/-- **Exact covariance seam.**  The entire post-crossing tail is its explicit
packet baseline minus one uncentered Möbius--rough-prime correlation. -/
theorem squareRootPostCrossingCoupledTail_eq_baseline_sub_correlation
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      squareRootPostCrossingCanonicalBaseline R K j -
        squareRootCanonicalRoughCorrelation R := by
  rw [squareRootPostCrossingCoupledTail_eq_canonicalRoughRow
    R K j hR hK hKR]
  unfold squareRootPostCrossingCanonicalRoughCoefficient
    squareRootPostCrossingCanonicalBaseline
  rw [show (∑ y ∈ Finset.Icc 1 (R - 1),
      ((if y = R - 1 then (1 : ℂ) else 0) +
          squareRootCrossingRemovalCoefficient R K j y +
            replacementFibreCanonicalRoughFullMass R y +
              squareRootCanonicalRoughStrictDescendantTransform R y) *
        mertensSummatory y) =
      (∑ y ∈ Finset.Icc 1 (R - 1),
        ((if y = R - 1 then (1 : ℂ) else 0) +
            squareRootCrossingRemovalCoefficient R K j y) *
          mertensSummatory y) +
      ∑ y ∈ Finset.Icc 1 (R - 1),
        (replacementFibreCanonicalRoughFullMass R y +
            squareRootCanonicalRoughStrictDescendantTransform R y) *
          mertensSummatory y by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro y _hy
        ring]
  rw [sum_canonicalRoughRenewal_mul_mertens_eq_neg_correlation]
  ring

/-- Covariance form of the exact seam.  The explicit mean product and centered
covariance remain signed together before the norm. -/
theorem squareRootPostCrossingCoupledTail_eq_baseline_sub_mean_covariance
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      squareRootPostCrossingCanonicalBaseline R K j -
        (squareRootCanonicalRoughCofactorCard R : ℂ) *
          (squareRootCanonicalRoughParityMean R *
              squareRootCanonicalRoughResponseMean R +
            squareRootCanonicalRoughCovariance R) := by
  rw [squareRootPostCrossingCoupledTail_eq_baseline_sub_correlation
      R K j hR hK hKR,
    squareRootCanonicalRoughCorrelation_eq_card_mul_mean_add_covariance
      R (by omega)]

/-- Critical bound stated directly on the exact mean-plus-covariance seam.
The validity hypotheses are identical to the existing post-crossing tail
statement, and the mean term is not discarded. -/
def SquareRootCanonicalRoughCovarianceBoundedStatement (K₀ : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R K j : ℕ,
        3 ≤ R →
        K ≤ K₀ →
        SquareRootPacketCrossesAt R K →
        j ≤ squareRootReciprocalPrimeLayerCard R K →
        0 ≤ squareRootCrossingLayerPartialPacketInt R K j →
        squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) →
        ‖squareRootPostCrossingCanonicalBaseline R K j -
            (squareRootCanonicalRoughCofactorCard R : ℂ) *
              (squareRootCanonicalRoughParityMean R *
                  squareRootCanonicalRoughResponseMean R +
                squareRootCanonicalRoughCovariance R)‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- The covariance estimate is neither weaker nor stronger than the coupled
tail target: after the exact cofactor reindexing, it is literally the same
finite inequality. -/
theorem squareRootCanonicalRoughCovarianceBounded_iff_coupledTailBounded
    (K₀ : ℕ) :
    SquareRootCanonicalRoughCovarianceBoundedStatement K₀ ↔
      SquareRootPostCrossingCoupledTailBoundedStatement K₀ := by
  constructor
  · intro hcov ε hε
    rcases hcov ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R K j hR hK hcross hj hV0 hVK
    have hKR : K < R := by
      rcases squareRootPacketCrossing_has_postRootPrime hcross with
        ⟨q, _hqPrime, hRq, _hqX, hqK⟩
      rw [← hqK]
      exact squareRootEndpoint_div_lt_root_of_root_le (by omega) (by omega)
    rw [squareRootPostCrossingCoupledTail_eq_baseline_sub_mean_covariance
      R K j hR hcross.1 hKR]
    exact hbound R K j hR hK hcross hj hV0 hVK
  · intro htail ε hε
    rcases htail ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R K j hR hK hcross hj hV0 hVK
    have hKR : K < R := by
      rcases squareRootPacketCrossing_has_postRootPrime hcross with
        ⟨q, _hqPrime, hRq, _hqX, hqK⟩
      rw [← hqK]
      exact squareRootEndpoint_div_lt_root_of_root_le (by omega) (by omega)
    rw [← squareRootPostCrossingCoupledTail_eq_baseline_sub_mean_covariance
      R K j hR hcross.1 hKR]
    exact hbound R K j hR hK hcross hj hV0 hVK

end RHLean.Proof
