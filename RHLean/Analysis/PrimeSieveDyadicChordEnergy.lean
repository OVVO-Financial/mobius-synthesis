import Mathlib
import RHLean.Analysis.PrimeSieveDyadicAnalyticBridge

/-!
# Dyadic chord geometry of the reciprocal prime discrepancy

An earlier layer introduced a mean-zero dyadic decomposition of the reciprocal-quotient
prime discrepancy and the boundary-free Abel potential.  An earlier layer proved that a
critical block-uniform `L2` bound for those Abel potentials, together with
Mobius dispersion and coherent-channel control, is sufficient for RH.

This file identifies the Abel coefficient field itself with a more classical
prime-distribution object.

Write

`R(t) = pi(t) - Li(t)`

and let

`D(d) = R(max y (floor (x/d)))`.

On the quotient support the reciprocal prime discrepancy is exactly the forward
difference `D(d) - D(d+1)`.  A dyadic block is an honest integer interval

`[2^j, min(K, 2^(j+1)-1)]`,  where `K = x/(y+1)`.

Consequently the block mean is the secant slope of `D` across the block, and the
Abel potential at an index inside the block is exactly the deviation of
`D(d)` from that secant chord.  Outside the block the potential vanishes.
Therefore the full Abel-potential energy is exactly a dyadic chord-deviation
energy for the classical prime discrepancy.

No prime-distribution estimate is proved here.  This is a finite exact change of
coordinates which turns the energy hypothesis into a concrete curvature
statement for `pi-Li` along the reciprocal lattice.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Left endpoint of the full `j`-th dyadic reciprocal block. -/
def primeSieveDyadicBlockLeft (j : ℕ) : ℕ := 2 ^ j

/-- Right endpoint after intersecting the `j`-th dyadic block with the finite
quotient support. -/
def primeSieveDyadicBlockRight (y x j : ℕ) : ℕ :=
  min (x / (y + 1)) (2 ^ (j + 1) - 1)

/-- The clipped classical prime discrepancy whose forward differences are the
reciprocal-interval discrepancies. -/
def primeSieveDyadicClippedDiscrepancy (y x d : ℕ) : ℂ :=
  primeSievePrimeDiscrepancy (max y (x / d))

/-- The `Nat.log2` block used in an earlier layer is literally an integer interval. -/
theorem primeSieveDyadicBlock_eq_explicitIcc (y x j : ℕ) :
    primeSieveDyadicBlock y x j =
      Finset.Icc (primeSieveDyadicBlockLeft j)
        (primeSieveDyadicBlockRight y x j) := by
  classical
  ext d
  rw [mem_primeSieveDyadicBlock]
  simp only [primeSieveQuotientSupport, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd1, hdK⟩, hidx⟩
    have hdne : d ≠ 0 := by omega
    have hlog : Nat.log 2 d = j := by
      simpa [primeSieveDyadicIndex, Nat.log2_eq_log_two] using hidx
    have hspec : 2 ^ j ≤ d ∧ d < 2 ^ (j + 1) :=
      (Nat.log_eq_iff (b := 2) (m := j) (n := d)
        (Or.inr ⟨by norm_num, hdne⟩)).mp hlog
    have hdPow : d ≤ 2 ^ (j + 1) - 1 := by
      have hp : 0 < 2 ^ (j + 1) := by positivity
      omega
    exact ⟨hspec.1, le_min hdK hdPow⟩
  · rintro ⟨hleft, hright⟩
    have hdK : d ≤ x / (y + 1) := hright.trans (min_le_left _ _)
    have hdPow : d ≤ 2 ^ (j + 1) - 1 :=
      hright.trans (min_le_right _ _)
    have hpowOne : 1 ≤ 2 ^ j := by
      simpa using (Nat.one_le_pow' j 1)
    have hd1 : 1 ≤ d := hpowOne.trans hleft
    have hdlt : d < 2 ^ (j + 1) := by
      have hp : 0 < 2 ^ (j + 1) := by positivity
      omega
    have hlog : Nat.log 2 d = j :=
      Nat.log_eq_of_pow_le_of_lt_pow hleft hdlt
    have hidx : primeSieveDyadicIndex d = j := by
      simpa [primeSieveDyadicIndex, Nat.log2_eq_log_two] using hlog
    exact ⟨⟨hd1, hdK⟩, hidx⟩

/-- Occupancy is exactly the assertion that the explicit dyadic interval is
nonempty. -/
theorem primeSieveDyadicBlockLeft_le_right_of_mem_indices
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    primeSieveDyadicBlockLeft j ≤ primeSieveDyadicBlockRight y x j := by
  classical
  rcases Finset.mem_image.mp hj with ⟨d, hd, hidx⟩
  have hdB : d ∈ primeSieveDyadicBlock y x j :=
    mem_primeSieveDyadicBlock.mpr ⟨hd, hidx⟩
  rw [primeSieveDyadicBlock_eq_explicitIcc] at hdB
  exact (Finset.mem_Icc.mp hdB).1.trans (Finset.mem_Icc.mp hdB).2

/-- The reciprocal prime discrepancy is a forward difference of the clipped
classical discrepancy. -/
theorem primeSieveReciprocalPrimeDiscrepancy_eq_clipped_forwardDifference
    {y x d : ℕ} (hd : d ∈ primeSieveQuotientSupport y x) :
    primeSieveReciprocalPrimeDiscrepancy y x d =
      primeSieveDyadicClippedDiscrepancy y x d -
        primeSieveDyadicClippedDiscrepancy y x (d + 1) := by
  have hy : y < x / d :=
    lt_div_of_mem_primeSieveQuotientSupport hd
  have hmaxd : max y (x / d) = x / d := max_eq_right hy.le
  have hle : primeSieveReciprocalLower y x d ≤
      primeSieveReciprocalUpper x d := by
    have hmono : x / (d + 1) ≤ x / d :=
      Nat.div_le_div_left (by omega) (by
        rcases Finset.mem_Icc.mp hd with ⟨hd1, _⟩
        omega)
    simp only [primeSieveReciprocalLower, primeSieveReciprocalUpper]
    exact max_le hy.le hmono
  rw [primeSieveReciprocalPrimeDiscrepancy_eq_sub y x d hle]
  simp only [primeSieveDyadicClippedDiscrepancy,
    primeSieveReciprocalLower, primeSieveReciprocalUpper, hmaxd]

/-- Finite telescoping of a forward-difference sum on an ordinary integer
interval. -/
private theorem sum_Ico_forwardDifference
    (f : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    (∑ d ∈ Finset.Ico a b, (f d - f (d + 1))) = f a - f b := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases h : a ≤ b
      · rw [Finset.sum_Ico_succ_top h, ih h]
        ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- Reciprocal discrepancies telescope on every subinterval of the quotient
support. -/
theorem sum_primeSieveReciprocalPrimeDiscrepancy_Ico_eq
    {y x a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ x / (y + 1) + 1) :
    (∑ d ∈ Finset.Ico a b,
      primeSieveReciprocalPrimeDiscrepancy y x d) =
      primeSieveDyadicClippedDiscrepancy y x a -
        primeSieveDyadicClippedDiscrepancy y x b := by
  calc
    (∑ d ∈ Finset.Ico a b,
        primeSieveReciprocalPrimeDiscrepancy y x d) =
      ∑ d ∈ Finset.Ico a b,
        (primeSieveDyadicClippedDiscrepancy y x d -
          primeSieveDyadicClippedDiscrepancy y x (d + 1)) := by
        apply Finset.sum_congr rfl
        intro d hdIco
        have hmem := Finset.mem_Ico.mp hdIco
        have hd1 : 1 ≤ d := ha.trans hmem.1
        have hdK : d ≤ x / (y + 1) := by omega
        exact primeSieveReciprocalPrimeDiscrepancy_eq_clipped_forwardDifference
          (Finset.mem_Icc.mpr ⟨hd1, hdK⟩)
    _ = primeSieveDyadicClippedDiscrepancy y x a -
        primeSieveDyadicClippedDiscrepancy y x b :=
      sum_Ico_forwardDifference _ hab

/-- Exact cardinality of an occupied truncated dyadic block. -/
theorem card_primeSieveDyadicBlock
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    (primeSieveDyadicBlock y x j).card =
      primeSieveDyadicBlockRight y x j + 1 - primeSieveDyadicBlockLeft j := by
  have hle := primeSieveDyadicBlockLeft_le_right_of_mem_indices hj
  rw [primeSieveDyadicBlock_eq_explicitIcc]
  have hset :
      Finset.Icc (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j) =
        Finset.Ico (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1) := by
    ext d
    simp
    omega
  rw [hset, Nat.card_Ico]

/-- The total reciprocal discrepancy on one occupied dyadic block is exactly
one clipped-discrepancy drop across its two endpoints. -/
theorem sum_primeSieveReciprocalPrimeDiscrepancy_dyadicBlock_eq
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    (∑ d ∈ primeSieveDyadicBlock y x j,
      primeSieveReciprocalPrimeDiscrepancy y x d) =
      primeSieveDyadicClippedDiscrepancy y x (primeSieveDyadicBlockLeft j) -
        primeSieveDyadicClippedDiscrepancy y x
          (primeSieveDyadicBlockRight y x j + 1) := by
  have hle := primeSieveDyadicBlockLeft_le_right_of_mem_indices hj
  have hrightK : primeSieveDyadicBlockRight y x j ≤ x / (y + 1) :=
    min_le_left _ _
  have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
    simpa [primeSieveDyadicBlockLeft] using (Nat.one_le_pow' j 1)
  rw [primeSieveDyadicBlock_eq_explicitIcc]
  have hset :
      Finset.Icc (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j) =
        Finset.Ico (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1) := by
    ext d
    simp
    omega
  rw [hset]
  exact sum_primeSieveReciprocalPrimeDiscrepancy_Ico_eq
    hleft1 (by omega) (by omega)

/-- The block mean is literally the secant slope of the clipped classical prime
discrepancy across the dyadic block. -/
theorem card_mul_primeSieveDyadicBlockMean_eq_secantDrop
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    (((primeSieveDyadicBlock y x j).card : ℕ) : ℂ) *
        primeSieveDyadicBlockMean y x j =
      primeSieveDyadicClippedDiscrepancy y x (primeSieveDyadicBlockLeft j) -
        primeSieveDyadicClippedDiscrepancy y x
          (primeSieveDyadicBlockRight y x j + 1) := by
  have hsum := sum_primeSieveReciprocalPrimeDiscrepancy_dyadicBlock_eq hj
  have hcardNat : 0 < (primeSieveDyadicBlock y x j).card := by
    rcases Finset.mem_image.mp hj with ⟨d, hd, hidx⟩
    exact Finset.card_pos.mpr ⟨d, mem_primeSieveDyadicBlock.mpr ⟨hd, hidx⟩⟩
  have hcard : ((((primeSieveDyadicBlock y x j).card : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardNat)
  unfold primeSieveDyadicBlockMean
  rw [hsum]
  field_simp [hcard]

/-- The cumulative mean-zero wavelet from the left endpoint to an in-block
index is a discrepancy drop minus the affine secant contribution. -/
theorem sum_primeSieveDyadicWavelet_Ico_left_eq
    {y x j d : ℕ} (hdB : d ∈ primeSieveDyadicBlock y x j) :
    (∑ t ∈ Finset.Ico (primeSieveDyadicBlockLeft j) d,
      primeSieveDyadicWavelet y x t) =
      primeSieveDyadicClippedDiscrepancy y x (primeSieveDyadicBlockLeft j) -
        primeSieveDyadicClippedDiscrepancy y x d -
        ((((d - primeSieveDyadicBlockLeft j : ℕ)) : ℂ) *
          primeSieveDyadicBlockMean y x j) := by
  have hdE := hdB
  rw [primeSieveDyadicBlock_eq_explicitIcc] at hdE
  rcases Finset.mem_Icc.mp hdE with ⟨hleftd, hdright⟩
  have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
    simpa [primeSieveDyadicBlockLeft] using (Nat.one_le_pow' j 1)
  have hdK : d ≤ x / (y + 1) := by
    exact (mem_primeSieveDyadicBlock.mp hdB).1 |> Finset.mem_Icc.mp |>.2
  have hrewrite :
      (∑ t ∈ Finset.Ico (primeSieveDyadicBlockLeft j) d,
        primeSieveDyadicWavelet y x t) =
      ∑ t ∈ Finset.Ico (primeSieveDyadicBlockLeft j) d,
        (primeSieveReciprocalPrimeDiscrepancy y x t -
          primeSieveDyadicBlockMean y x j) := by
    apply Finset.sum_congr rfl
    intro t ht
    have htI := Finset.mem_Ico.mp ht
    have htB : t ∈ primeSieveDyadicBlock y x j := by
      rw [primeSieveDyadicBlock_eq_explicitIcc]
      exact Finset.mem_Icc.mpr ⟨htI.1, by omega⟩
    have hidx := (mem_primeSieveDyadicBlock.mp htB).2
    simp [primeSieveDyadicWavelet, hidx]
  rw [hrewrite, Finset.sum_sub_distrib]
  have hdelta := sum_primeSieveReciprocalPrimeDiscrepancy_Ico_eq
    (y := y) (x := x) hleft1 hleftd (by omega : d ≤ x / (y + 1) + 1)
  rw [hdelta]
  have hconst :
      (∑ _t ∈ Finset.Ico (primeSieveDyadicBlockLeft j) d,
        primeSieveDyadicBlockMean y x j) =
      (((Finset.Ico (primeSieveDyadicBlockLeft j) d).card : ℕ) : ℂ) *
        primeSieveDyadicBlockMean y x j := by
    simp [nsmul_eq_mul]
  rw [hconst, Nat.card_Ico]

/-- Prime-discrepancy deviation from the secant chord of its dyadic block. -/
def primeSieveDyadicChordResidual (y x j d : ℕ) : ℂ :=
  primeSieveDyadicClippedDiscrepancy y x d -
    primeSieveDyadicClippedDiscrepancy y x (primeSieveDyadicBlockLeft j) +
    ((((d - primeSieveDyadicBlockLeft j : ℕ)) : ℂ) *
      primeSieveDyadicBlockMean y x j)

/-- On its own dyadic block, the Abel potential is exactly the chord
residual of the classical prime discrepancy. -/
theorem primeSieveDyadicBlockAbelPotential_eq_chordResidual
    {y x j d : ℕ} (hdB : d ∈ primeSieveDyadicBlock y x j) :
    primeSieveDyadicBlockAbelPotential y x j d =
      primeSieveDyadicChordResidual y x j d := by
  have hdE := hdB
  rw [primeSieveDyadicBlock_eq_explicitIcc] at hdE
  rcases Finset.mem_Icc.mp hdE with ⟨hleftd, hdright⟩
  have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
    simpa [primeSieveDyadicBlockLeft] using (Nat.one_le_pow' j 1)
  have hfilter :
      (Finset.Icc 1 (d - 1)).filter
          (fun t => t ∈ primeSieveDyadicBlock y x j) =
        Finset.Ico (primeSieveDyadicBlockLeft j) d := by
    ext t
    rw [Finset.mem_filter]
    rw [primeSieveDyadicBlock_eq_explicitIcc]
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨ht1, htd⟩, ⟨hleftt, htright⟩⟩
      exact ⟨hleftt, by omega⟩
    · rintro ⟨hleftt, htd⟩
      exact ⟨⟨hleft1.trans hleftt, by omega⟩, ⟨hleftt, by omega⟩⟩
  have hmask :
      (∑ t ∈ Finset.Icc 1 (d - 1),
        primeSieveDyadicBlockWaveletMask y x j t) =
      ∑ t ∈ Finset.Ico (primeSieveDyadicBlockLeft j) d,
        primeSieveDyadicWavelet y x t := by
    unfold primeSieveDyadicBlockWaveletMask
    rw [← Finset.sum_filter, hfilter]
  unfold primeSieveDyadicBlockAbelPotential
  rw [hmask, sum_primeSieveDyadicWavelet_Ico_left_eq hdB]
  unfold primeSieveDyadicChordResidual
  ring

/-- At the successor of the right endpoint, the same chord closes exactly. -/
theorem primeSieveDyadicChordResidual_right_succ_eq_zero
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    primeSieveDyadicChordResidual y x j
      (primeSieveDyadicBlockRight y x j + 1) = 0 := by
  have hsec := card_mul_primeSieveDyadicBlockMean_eq_secantDrop hj
  have hcard := card_primeSieveDyadicBlock hj
  unfold primeSieveDyadicChordResidual
  rw [hcard] at hsec
  linear_combination hsec

/-- On the quotient support the block Abel potential is zero away from its own
explicit dyadic interval. -/
theorem primeSieveDyadicBlockAbelPotential_eq_zero_of_not_mem
    {y x j d : ℕ}
    (hj : j ∈ primeSieveDyadicBlockIndices y x)
    (hd : d ∈ primeSieveQuotientSupport y x)
    (hdB : d ∉ primeSieveDyadicBlock y x j) :
    primeSieveDyadicBlockAbelPotential y x j d = 0 := by
  have hblock := primeSieveDyadicBlock_eq_explicitIcc y x j
  have hle := primeSieveDyadicBlockLeft_le_right_of_mem_indices hj
  have hdSupp := Finset.mem_Icc.mp hd
  have hnot : ¬ (primeSieveDyadicBlockLeft j ≤ d ∧
      d ≤ primeSieveDyadicBlockRight y x j) := by
    intro h
    apply hdB
    rw [hblock]
    exact Finset.mem_Icc.mpr h
  by_cases hbefore : d < primeSieveDyadicBlockLeft j
  · have hfilter :
        (Finset.Icc 1 (d - 1)).filter
            (fun t => t ∈ primeSieveDyadicBlock y x j) = ∅ := by
      ext t
      rw [Finset.mem_filter]
      rw [hblock]
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]
      omega
    unfold primeSieveDyadicBlockAbelPotential
      primeSieveDyadicBlockWaveletMask
    rw [← Finset.sum_filter, hfilter]
    simp
  · have hafter : primeSieveDyadicBlockRight y x j < d := by omega
    have hfilter :
        (Finset.Icc 1 (d - 1)).filter
            (fun t => t ∈ primeSieveDyadicBlock y x j) =
          primeSieveDyadicBlock y x j := by
      ext t
      rw [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro htB
        rw [hblock] at htB
        rcases Finset.mem_Icc.mp htB with ⟨hleftt, htright⟩
        have ht1 : 1 ≤ t := by
          have hpos : 0 < primeSieveDyadicBlockLeft j := by
            unfold primeSieveDyadicBlockLeft
            positivity
          omega
        have htd : t ≤ d - 1 := by omega
        exact ⟨Finset.mem_Icc.mpr ⟨ht1, htd⟩, by
          rw [hblock]
          exact htB⟩
    have hzero := sum_primeSieveDyadicWavelet_block_eq_zero hj
    unfold primeSieveDyadicBlockAbelPotential
      primeSieveDyadicBlockWaveletMask
    rw [← Finset.sum_filter, hfilter, hzero]
    simp

/-- Dyadic chord-deviation energy of the clipped classical prime discrepancy. -/
def primeSieveDyadicChordEnergy (y x : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    ∑ d ∈ primeSieveDyadicBlock y x j,
      ‖primeSieveDyadicChordResidual y x j d‖ ^ 2

/-- The Abel-potential energy is exactly the prime-discrepancy chord energy. -/
theorem primeSieveDyadicAbelPotentialEnergy_eq_chordEnergy
    (y x : ℕ) :
    primeSieveDyadicAbelPotentialEnergy y x =
      primeSieveDyadicChordEnergy y x := by
  classical
  unfold primeSieveDyadicAbelPotentialEnergy primeSieveDyadicChordEnergy
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ d ∈ primeSieveQuotientSupport y x,
        ‖primeSieveDyadicBlockAbelPotential y x j d‖ ^ 2) =
      ∑ d ∈ primeSieveQuotientSupport y x,
        if d ∈ primeSieveDyadicBlock y x j then
          ‖primeSieveDyadicBlockAbelPotential y x j d‖ ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro d hd
            by_cases hdB : d ∈ primeSieveDyadicBlock y x j
            · simp [hdB]
            · have hz := primeSieveDyadicBlockAbelPotential_eq_zero_of_not_mem
                hj hd hdB
              simp [hdB, hz]
    _ = ∑ d ∈ primeSieveDyadicBlock y x j,
          ‖primeSieveDyadicBlockAbelPotential y x j d‖ ^ 2 := by
            rw [← Finset.sum_filter]
            have hfilter :
                (primeSieveQuotientSupport y x).filter
                    (fun d => d ∈ primeSieveDyadicBlock y x j) =
                  primeSieveDyadicBlock y x j := by
              ext d
              simp [mem_primeSieveDyadicBlock]
            rw [hfilter]
    _ = ∑ d ∈ primeSieveDyadicBlock y x j,
          ‖primeSieveDyadicChordResidual y x j d‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro d hdB
            rw [primeSieveDyadicBlockAbelPotential_eq_chordResidual hdB]

/-- Critical block-uniform chord-energy target for the classical prime
discrepancy. -/
def DyadicPrimeDiscrepancyChordEnergyBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicChordEnergy
            (primorialPNTPrimeSieveCutoff k) x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The Abel-energy hypothesis is exactly the dyadic chord-energy
hypothesis. -/
theorem dyadicAbelPotentialEnergyBlockBounded_iff_chordEnergyBlockBounded :
    DyadicAbelPotentialEnergyBlockBoundedStatement ↔
      DyadicPrimeDiscrepancyChordEnergyBlockBoundedStatement := by
  constructor
  · intro hE ε hε
    obtain ⟨C, hC, hCb⟩ := hE ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    rw [← primeSieveDyadicAbelPotentialEnergy_eq_chordEnergy]
    exact hCb k x hk hlow hup
  · intro hE ε hε
    obtain ⟨C, hC, hCb⟩ := hE ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    rw [primeSieveDyadicAbelPotentialEnergy_eq_chordEnergy]
    exact hCb k x hk hlow hup

/-- The full RH reduction can therefore be stated directly in terms of a
critical dyadic chord-energy estimate for `pi-Li`. -/
theorem riemannHypothesis_of_dyadicChordAnalyticPackage
    (hC : DyadicCoherentChannelRHScale)
    (hE : DyadicPrimeDiscrepancyChordEnergyBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicAnalyticPackage hC
  · exact dyadicAbelPotentialEnergyBlockBounded_iff_chordEnergyBlockBounded.mpr hE
  · exact hD

end RHLean.Analysis
