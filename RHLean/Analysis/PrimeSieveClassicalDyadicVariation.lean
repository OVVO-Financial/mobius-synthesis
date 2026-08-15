import Mathlib
import RHLean.Analysis.PrimeSieveReciprocalChildVariance

/-!
# Classical dyadic quadratic variation route for the reciprocal prime discrepancy

The child-interval variance route isolates the remaining base-eight packet input
as a sign-blind local `L2` statement.  This module removes the last reciprocal
sum notation from that premise.

Write

`D(d) = pi(max y (floor (x / d))) - Li(max y (floor (x / d)))`.

At every midpoint node `[a,b)` with split `m`, the child-interval variance is
exactly

`(b-a) * (||D(a)-D(m)||^2 + ||D(m)-D(b)||^2)`.

Iterating this identity down the same midpoint tree identifies the complete
base-eight child-variance square function with a classical dyadic quadratic
variation of `pi-Li` along the reciprocal lattice.  Thus the analytic premise
can be stated without packet residuals, reciprocal interval sums, or Mobius
weights.

No prime-distribution estimate is proved here.  The contribution is an exact
change of coordinates and the resulting independent entrances into the existing
packet, chord, Abel, and RH architectures.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Recursive dyadic quadratic variation of the clipped classical discrepancy
`D(d) = pi(max y (x/d)) - Li(max y (x/d))` over the midpoint tree. -/
def primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
    (y x : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, _a, _b => 0
  | depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        ((b - a : ℕ) : ℝ) *
            (‖primeSieveDyadicClippedDiscrepancy y x a -
                primeSieveDyadicClippedDiscrepancy y x m‖ ^ 2 +
              ‖primeSieveDyadicClippedDiscrepancy y x m -
                primeSieveDyadicClippedDiscrepancy y x b‖ ^ 2) +
          primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
            y x depth a m +
          primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
            y x depth m b
      else 0

/-- On every reciprocal-support interval, the recursive sign-blind child
variance is exactly the classical clipped-discrepancy quadratic variation. -/
theorem primeSieveReciprocalLowFrequencyChildIntervalVariance_eq_clippedQuadraticVariation
    (y x depth a b : ℕ)
    (ha : 1 ≤ a)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveReciprocalLowFrequencyChildIntervalVariance y x depth a b =
      primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
        y x depth a b := by
  induction depth generalizing a b with
  | zero => rfl
  | succ depth ih =>
      by_cases hsplit : a + 1 < b
      · let m := dyadicPacketMidpoint a b
        have hm : a < m ∧ m < b := by
          dsimp [m, dyadicPacketMidpoint]
          omega
        have hm1 : 1 ≤ m := ha.trans hm.1.le
        have hmB : m ≤ x / (y + 1) + 1 := hm.2.le.trans hb
        have hnode :=
          primeSieveReciprocalChildIntervalVariance_eq_clippedDiscrepancyDrops
            (y := y) (x := x) (a := a) (m := m) (b := b)
            ha hm.1.le hm.2.le hb
        have hleft := ih a m ha hmB
        have hright := ih m b hm1 hb
        simp only [primeSieveReciprocalLowFrequencyChildIntervalVariance,
          primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation,
          hsplit, if_true]
        change
          primeSieveReciprocalChildIntervalVariance y x a m b +
              primeSieveReciprocalLowFrequencyChildIntervalVariance
                y x depth a m +
              primeSieveReciprocalLowFrequencyChildIntervalVariance
                y x depth m b =
            ((b - a : ℕ) : ℝ) *
                (‖primeSieveDyadicClippedDiscrepancy y x a -
                    primeSieveDyadicClippedDiscrepancy y x m‖ ^ 2 +
                  ‖primeSieveDyadicClippedDiscrepancy y x m -
                    primeSieveDyadicClippedDiscrepancy y x b‖ ^ 2) +
              primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
                y x depth a m +
              primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
                y x depth m b
        rw [hnode, hleft, hright]
      · simp [primeSieveReciprocalLowFrequencyChildIntervalVariance,
          primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation, hsplit]

/-- Global dyadic quadratic variation through depth `J`, summed over all
occupied reciprocal dyadic blocks. -/
def primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction
    (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation y x (min J j)
      (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)

/-- The global classical quadratic variation is exactly the child-interval
variance square function. -/
theorem primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction_eq_childIntervalVariance
    (y x J : ℕ) :
    primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction
        y x J =
      primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction
        y x J := by
  unfold primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction
    primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction
  apply Finset.sum_congr rfl
  intro j _hj
  have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
    simpa [primeSieveDyadicBlockLeft] using (Nat.one_le_pow' j 1)
  have hright :
      primeSieveDyadicBlockRight y x j + 1 ≤ x / (y + 1) + 1 := by
    unfold primeSieveDyadicBlockRight
    exact Nat.add_le_add_right
      (min_le_left (x / (y + 1)) (2 ^ (j + 1) - 1)) 1
  exact
    (primeSieveReciprocalLowFrequencyChildIntervalVariance_eq_clippedQuadraticVariation
      y x (min J j) (primeSieveDyadicBlockLeft j)
        (primeSieveDyadicBlockRight y x j + 1) hleft1 hright).symm

/-- Base-eight successor version of the classical clipped-discrepancy quadratic
variation square function. -/
def primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction
    (k x : ℕ) : ℝ :=
  primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction
    (primorialPNTPrimeSieveCutoff k) x
    (dyadicPacketBaseEightCutoff k x + 1)

/-- At the base-eight successor cutoff the classical quadratic variation is
literally the sign-blind child-interval variance square function from #332. -/
theorem primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction_eq_childIntervalVariance
    (k x : ℕ) :
    primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction k x =
      primeSieveBaseEightChildIntervalVarianceSquareFunction k x := by
  simpa [primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction,
    primeSieveBaseEightChildIntervalVarianceSquareFunction] using
    primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction_eq_childIntervalVariance
      (primorialPNTPrimeSieveCutoff k) x
      (dyadicPacketBaseEightCutoff k x + 1)

/-- Critical block-uniform bound for the classical reciprocal-lattice dyadic
quadratic variation of `pi-Li`. -/
def DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction
            k x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The classical `pi-Li` dyadic-variation premise is exactly equivalent to the
sign-blind child-interval variance premise. -/
theorem dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance :
    DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement ↔
      DyadicPrimeReciprocalLowFrequencyChildIntervalVarianceBlockBoundedStatement := by
  constructor
  · intro hQ ε hε
    obtain ⟨C, hC, hQb⟩ := hQ ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    have h := hQb k x hk hlow hup
    rw [primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction_eq_childIntervalVariance]
      at h
    exact h
  · intro hV ε hε
    obtain ⟨C, hC, hVb⟩ := hV ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    have h := hVb k x hk hlow hup
    rw [primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction_eq_childIntervalVariance]
    exact h

/-- A classical `pi-Li` dyadic-variation estimate therefore controls the full
base-eight recursive packet tree. -/
theorem dyadicPacketTreeEnergyBlockBounded_of_baseEightClippedDiscrepancyQuadraticVariation
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (k x : ℕ),
          2 ≤ k →
          primorialBlockLower k ≤ x →
          x ≤ primorialBlockUpper k →
          primeSieveDyadicPacketTreeEnergy
              (primorialPNTPrimeSieveCutoff k) x ≤
            C * Real.rpow ((x : ℝ) + 1) (1 + ε) :=
  dyadicPacketTreeEnergyBlockBounded_of_baseEightReciprocalChildIntervalVariance
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)

/-- The same classical variation premise implies the older dyadic chord-energy
criterion for `pi-Li`. -/
theorem dyadicPrimeDiscrepancyChordEnergyBlockBounded_of_baseEightClippedDiscrepancyQuadraticVariation
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement) :
    DyadicPrimeDiscrepancyChordEnergyBlockBoundedStatement :=
  dyadicPrimeDiscrepancyChordEnergyBlockBounded_of_baseEightReciprocalChildIntervalVariance
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)

/-- The same classical variation premise also implies the boundary-free Abel
potential energy criterion. -/
theorem dyadicAbelPotentialEnergyBlockBounded_of_baseEightClippedDiscrepancyQuadraticVariation
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement) :
    DyadicAbelPotentialEnergyBlockBoundedStatement :=
  dyadicAbelPotentialEnergyBlockBounded_of_baseEightReciprocalChildIntervalVariance
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)

/-- RH entrance through the direct base-eight packet route, with the only packet
input stated as classical dyadic quadratic variation of `pi-Li`. -/
theorem riemannHypothesis_of_baseEightClippedDiscrepancyQuadraticVariationPackage
    (hC : DyadicCoherentChannelRHScale)
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement :=
  riemannHypothesis_of_baseEightReciprocalChildIntervalVariancePackage hC
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)
    hD

/-- Independent RH entrance through the older chord/Abel route, driven by the
same classical `pi-Li` dyadic quadratic variation premise. -/
theorem riemannHypothesis_of_baseEightClippedDiscrepancyQuadraticVariationChordPackage
    (hC : DyadicCoherentChannelRHScale)
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement :=
  riemannHypothesis_of_baseEightReciprocalChildIntervalVarianceChordPackage hC
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)
    hD

/-! ## Block-local Mobius dispersion -/

/-- The `L2` Abel-potential energy carried by one dyadic reciprocal block. -/
def primeSieveDyadicBlockAbelPotentialEnergy (y x j : ℕ) : ℝ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    ‖primeSieveDyadicBlockAbelPotential y x j d‖ ^ 2

/-- The global Abel energy is exactly the sum of its dyadic block energies. -/
theorem primeSieveDyadicAbelPotentialEnergy_eq_sum_blockAbelPotentialEnergy
    (y x : ℕ) :
    primeSieveDyadicAbelPotentialEnergy y x =
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        primeSieveDyadicBlockAbelPotentialEnergy y x j := by
  rfl

/-- Block-local Mobius dispersion.  On an occupied block the left side is,
by the existing boundary-free Abel identity, exactly the Mobius pairing against
that block's Abel potential. -/
def DyadicBlockwiseMobiusDispersionBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x j : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        j ∈ primeSieveDyadicBlockIndices
          (primorialPNTPrimeSieveCutoff k) x →
        ‖primeSieveDyadicBlockWaveletMertensContribution
            (primorialPNTPrimeSieveCutoff k) x j‖ ^ 2 ≤
          C * Real.rpow ((x : ℝ) + 1) ε *
            primeSieveDyadicBlockAbelPotentialEnergy
              (primorialPNTPrimeSieveCutoff k) x j

private theorem classicalVariation_dyadicIndex_le_log_succ
    {y x j : ℕ}
    (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    j ≤ Nat.log 2 (x + 1) := by
  classical
  rcases Finset.mem_image.mp hj with ⟨d, hd, hidx⟩
  have hdI := Finset.mem_Icc.mp hd
  have hdx : d ≤ x + 1 := by
    calc
      d ≤ x / (y + 1) := hdI.2
      _ ≤ x := Nat.div_le_self _ _
      _ ≤ x + 1 := by omega
  rw [← hidx]
  simpa [primeSieveDyadicIndex, Nat.log2_eq_log_two] using
    (Nat.log_mono_right hdx)

private theorem classicalVariation_dyadicBlockIndices_card_le_log_succ
    (y x : ℕ) :
    (primeSieveDyadicBlockIndices y x).card ≤ Nat.log 2 (x + 1) + 1 := by
  let M := Nat.log 2 (x + 1)
  have hsubset :
      primeSieveDyadicBlockIndices y x ⊆ Finset.range (M + 1) := by
    intro j hj
    have hjM : j ≤ M := by
      simpa [M] using classicalVariation_dyadicIndex_le_log_succ hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hjM)
  simpa using Finset.card_le_card hsubset

private theorem classicalVariation_dyadicBlockIndices_card_le_subpolynomial
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y x : ℕ),
        ((primeSieveDyadicBlockIndices y x).card : ℝ) ≤
          C * Real.rpow ((x : ℝ) + 1) ε := by
  obtain ⟨C, hC, hCb⟩ :=
    RHLean.Proof.card_divisors_le_subpolynomial hε
  refine ⟨C, hC, ?_⟩
  intro y x
  let M := Nat.log 2 (x + 1)
  have hcardNat : (primeSieveDyadicBlockIndices y x).card ≤ M + 1 := by
    simpa [M] using classicalVariation_dyadicBlockIndices_card_le_log_succ y x
  have hcard :
      ((primeSieveDyadicBlockIndices y x).card : ℝ) ≤ (((M + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hcardNat
  have hpowOne : 1 ≤ 2 ^ M := by
    simpa using (Nat.one_le_pow' M 1)
  have hdiv := hCb (2 ^ M) hpowOne
  have hdivCard : (2 ^ M).divisors.card = M + 1 := by
    have h := congrArg Finset.card (Nat.divisors_prime_pow Nat.prime_two M)
    simpa using h
  rw [hdivCard] at hdiv
  have hpowNat : 2 ^ M ≤ x + 1 := by
    dsimp [M]
    exact Nat.pow_log_le_self 2 (by omega)
  have hpowCast : (((2 ^ M : ℕ) : ℝ)) ≤ (x : ℝ) + 1 := by
    exact_mod_cast hpowNat
  have hrpow :
      Real.rpow (((2 ^ M : ℕ) : ℝ)) ε ≤
        Real.rpow ((x : ℝ) + 1) ε :=
    Real.rpow_le_rpow (by positivity) hpowCast hε.le
  have hcPow := mul_le_mul_of_nonneg_left hrpow hC
  exact hcard.trans (hdiv.trans hcPow)

private theorem norm_finset_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hnorm := norm_sum_le s f
  have hsum0 : 0 ≤ ∑ i ∈ s, ‖f i‖ :=
    Finset.sum_nonneg fun _i _hi => norm_nonneg _
  have hsq :
      ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum0).2 hnorm
  have hcauchy :=
    Finset.sum_mul_sq_le_sq_mul_sq s
      (fun _i => (1 : ℝ)) (fun i => ‖f i‖)
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := hsq
    _ ≤ (∑ i ∈ s, (1 : ℝ) ^ 2) *
        (∑ i ∈ s, ‖f i‖ ^ 2) := by
      simpa using hcauchy
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by simp

/-- A block-local dispersion estimate implies the original global Mobius
dispersion statement.  Recombining the blocks costs only their logarithmic
cardinality, which is absorbed into the epsilon by the divisor-count bound. -/
theorem dyadicMobiusDispersionBlockBounded_of_blockwise
    (hB : DyadicBlockwiseMobiusDispersionBlockBoundedStatement) :
    DyadicMobiusDispersionBlockBoundedStatement := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨CB, hCB, hBb⟩ := hB (ε / 2) hhalf
  obtain ⟨CN, hCN, hNb⟩ :=
    classicalVariation_dyadicBlockIndices_card_le_subpolynomial hhalf
  refine ⟨CN * CB, mul_nonneg hCN hCB, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let S := primeSieveDyadicBlockIndices y x
  let B : ℝ := (x : ℝ) + 1
  let P : ℝ := Real.rpow B (ε / 2)
  let E : ℝ := primeSieveDyadicAbelPotentialEnergy y x
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact Real.rpow_nonneg (by positivity) _
  have hE0 : 0 ≤ E := by
    dsimp [E]
    unfold primeSieveDyadicAbelPotentialEnergy
    positivity
  have hcount : (S.card : ℝ) ≤ CN * P := by
    simpa [S, y, B, P] using hNb y x
  have hsum :
      (∑ j ∈ S,
        ‖primeSieveDyadicBlockWaveletMertensContribution y x j‖ ^ 2) ≤
        CB * P * E := by
    calc
      (∑ j ∈ S,
          ‖primeSieveDyadicBlockWaveletMertensContribution y x j‖ ^ 2) ≤
        ∑ j ∈ S,
          CB * P * primeSieveDyadicBlockAbelPotentialEnergy y x j := by
            apply Finset.sum_le_sum
            intro j hj
            have hb := hBb k x j hk hlow hup
            have hlocal := hb (by simpa [S, y] using hj)
            simpa [y, B, P] using hlocal
      _ = CB * P *
          (∑ j ∈ S, primeSieveDyadicBlockAbelPotentialEnergy y x j) := by
            rw [Finset.mul_sum]
      _ = CB * P * E := by
            dsimp [E]
            rw [primeSieveDyadicAbelPotentialEnergy_eq_sum_blockAbelPotentialEnergy]
  have hcauchy :
      ‖primeSieveDyadicWaveletPNTError y x‖ ^ 2 ≤
        (S.card : ℝ) *
          (∑ j ∈ S,
            ‖primeSieveDyadicBlockWaveletMertensContribution y x j‖ ^ 2) := by
    rw [primeSieveDyadicWaveletPNTError_eq_sum_blockContributions]
    simpa [S] using
      norm_finset_sum_sq_le_card_mul_sum_norm_sq S
        (fun j => primeSieveDyadicBlockWaveletMertensContribution y x j)
  have hright0 : 0 ≤ CB * P * E :=
    mul_nonneg (mul_nonneg hCB hP0) hE0
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hP2 : P ^ 2 = Real.rpow B ε := by
    dsimp [P]
    rw [pow_two, ← Real.rpow_add hBpos]
    congr 1
    ring
  change
    ‖primeSieveDyadicWaveletPNTError y x‖ ^ 2 ≤
      (CN * CB) * Real.rpow B ε * E
  calc
    ‖primeSieveDyadicWaveletPNTError y x‖ ^ 2 ≤
        (S.card : ℝ) *
          (∑ j ∈ S,
            ‖primeSieveDyadicBlockWaveletMertensContribution y x j‖ ^ 2) :=
      hcauchy
    _ ≤ (S.card : ℝ) * (CB * P * E) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (CN * P) * (CB * P * E) :=
      mul_le_mul_of_nonneg_right hcount hright0
    _ = (CN * CB) * P ^ 2 * E := by ring
    _ = (CN * CB) * Real.rpow B ε * E := by rw [hP2]

/-- RH package with both open analytic inputs localized: classical dyadic
quadratic variation for the prime discrepancy, and blockwise Mobius dispersion
for the boundary-free Abel pairing. -/
theorem riemannHypothesis_of_baseEightClippedDiscrepancyVariationBlockwiseMobiusPackage
    (hC : DyadicCoherentChannelRHScale)
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement)
    (hD : DyadicBlockwiseMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicAnalyticPackage hC
  · exact
      dyadicAbelPotentialEnergyBlockBounded_of_baseEightClippedDiscrepancyQuadraticVariation hQ
  · exact dyadicMobiusDispersionBlockBounded_of_blockwise hD

end RHLean.Analysis
