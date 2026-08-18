import Mathlib
import RHLean.Analysis.ExactActivityPrimeIntervals
import RHLean.Analysis.PrimeSievePNTGoodMassChargeAttack

/-!
# Base-eight shallow packet attack

An earlier layer made the deep packet tail unconditional at the base-eight cutoff.  The
remaining packet-side input is the successor-shallow estimate.  This module
opens that shallow energy without separating `pi` and `Li`.

For every midpoint node `[a,b)` with split `m`, the existing signed sibling
identity writes the packet as the weighted reciprocal-discrepancy contrast

`(m-a) * sum_[m,b) Delta_d - (b-m) * sum_[a,m) Delta_d`.

The recursive square function below uses exactly those contrasts.  The first
result of the attack is an exact identification with the existing recursive
packet tree, hence with the base-eight successor-shallow energy.  The shallow
energy is then flattened into the finite sum of its exact packet levels.

The module also connects the older exact-activity coordinate directly to the
reciprocal coordinate.  At square stage `X = (t+1)^2`, the exact active-prime
interval for cofactor `c` is precisely the prime set in the reciprocal band

`max (t+1) ((X-1)/(2c)) < q <= (X-1)/c`.

Thus exact activity really does land on a dyadic reciprocal band.  What it does
not by itself supply is the critical signed prime-minus-Li square-function
estimate across all low packet levels.  The final block-uniform square-function
statement below isolates that remaining analytic frontier, while the root-level
corollary isolates the first necessary low-frequency obstruction.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Exact-activity bridge to the reciprocal coordinate -/

/-- Prime set in the reciprocal band corresponding to one exact-activity
cofactor at square stage `t`.  The ambient reciprocal point is
`x = (t+1)^2 - 1` and the post-square-root cutoff is `y = t+1`. -/
def primeSieveExactActivityReciprocalPrimeBand (t c : ℕ) : Finset ℕ :=
  (Finset.Ioc
      (max (t + 1) (((t + 1) ^ 2 - 1) / (2 * c)))
      (((t + 1) ^ 2 - 1) / c)).filter Nat.Prime

/-- Membership in the reciprocal band is exactly the product form of the
exact-activity inequalities. -/
theorem mem_primeSieveExactActivityReciprocalPrimeBand_iff
    {t c q : ℕ} (hc : 0 < c) :
    q ∈ primeSieveExactActivityReciprocalPrimeBand t c ↔
      q.Prime ∧ t + 2 ≤ q ∧
        (t + 1) ^ 2 ≤ 2 * (c * q) ∧
          c * q < (t + 1) ^ 2 := by
  have h2c : 0 < 2 * c := by positivity
  have hsquare : 0 < (t + 1) ^ 2 := by positivity
  have hpredlt : (t + 1) ^ 2 - 1 < (t + 1) ^ 2 := by omega
  simp only [primeSieveExactActivityReciprocalPrimeBand,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hmax, hup⟩, hprime⟩
    have hparts := (max_lt_iff.mp hmax)
    have htq : t + 2 ≤ q := by omega
    have hmul0 :
        (t + 1) ^ 2 - 1 < q * (2 * c) :=
      (Nat.div_lt_iff_lt_mul h2c).1 hparts.2
    have hmul :
        (t + 1) ^ 2 - 1 < 2 * (c * q) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul0
    have hmiddle : (t + 1) ^ 2 ≤ 2 * (c * q) := by omega
    have hupmul : q * c ≤ (t + 1) ^ 2 - 1 :=
      (Nat.le_div_iff_mul_le hc).1 hup
    have hprodle : c * q ≤ (t + 1) ^ 2 - 1 := by
      simpa [Nat.mul_comm] using hupmul
    have hprod : c * q < (t + 1) ^ 2 := hprodle.trans_lt hpredlt
    exact ⟨hprime, htq, hmiddle, hprod⟩
  · rintro ⟨hprime, htq, hmiddle, hprod⟩
    refine ⟨?_, hprime⟩
    constructor
    · apply (max_lt_iff).2
      refine ⟨by omega, ?_⟩
      apply (Nat.div_lt_iff_lt_mul h2c).2
      have hpred : (t + 1) ^ 2 - 1 < 2 * (c * q) :=
        hpredlt.trans_le hmiddle
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hpred
    · apply (Nat.le_div_iff_mul_le hc).2
      have hle : c * q ≤ (t + 1) ^ 2 - 1 := Nat.le_pred_of_lt hprod
      simpa [Nat.mul_comm] using hle

/-- The exact active-prime interval is literally the reciprocal prime band at
the associated square stage. -/
theorem exactActivityPrimeInterval_eq_reciprocalPrimeBand
    (t c : ℕ) (hc : 0 < c) :
    exactActivityPrimeInterval t c =
      primeSieveExactActivityReciprocalPrimeBand t c := by
  ext q
  rw [mem_exactActivityPrimeInterval,
    exactActivityPrimeBounds_iff_product_bounds hc]
  exact (mem_primeSieveExactActivityReciprocalPrimeBand_iff hc).symm

/-- Consequently the exact compressed source mass is the cardinality of that
reciprocal prime band times the already-existing signed cofactor weight. -/
theorem exactActivityPrimeSourceMass_eq_reciprocalPrimeBand_card_nsmul
    {N c t : ℕ} (hc : 0 < c) (hct : c ≤ t) (htN : t ≤ N) :
    exactActivityPrimeSourceMass N c t =
      (primeSieveExactActivityReciprocalPrimeBand t c).card •
        (-canonicalMoebiusWeight c) := by
  rw [exactActivityPrimeSourceMass_eq_card_nsmul hc hct htN,
    exactActivityPrimeInterval_eq_reciprocalPrimeBand t c hc]

/-! ## Signed reciprocal sibling square function -/

/-- Weighted left-versus-right reciprocal discrepancy on one midpoint node.
This is the arithmetic numerator of the signed sibling residual and keeps
`pi - Li` intact as one signed object. -/
def primeSieveReciprocalSiblingContrast
    (y x a m b : ℕ) : ℂ :=
  (((m - a : ℕ) : ℂ) *
      (∑ d ∈ Finset.Ico m b,
        primeSieveReciprocalPrimeDiscrepancy y x d)) -
    (((b - m : ℕ) : ℂ) *
      (∑ d ∈ Finset.Ico a m,
        primeSieveReciprocalPrimeDiscrepancy y x d))

/-- Exact node identity: on reciprocal support, the width-normalized signed
sibling packet is the normalized weighted discrepancy contrast. -/
theorem primeSieveSignedSiblingPacketResidual_eq_reciprocalSiblingContrast
    {y x a m b : ℕ}
    (ha : 1 ≤ a) (ham : a ≤ m) (hmb : m ≤ b)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveSignedSiblingPacketResidual y x a m b =
      (((b - a : ℕ) : ℂ)⁻¹) *
        primeSieveReciprocalSiblingContrast y x a m b := by
  unfold primeSieveSignedSiblingPacketResidual
    primeSieveReciprocalSiblingContrast
  rw [primeSieveSignedSiblingPacket_eq_weighted_intervalDiscrepancies
    ha ham hmb hb]

/-- Recursive low-frequency square function on one reciprocal interval.  It is
written directly in terms of weighted sums of the unsplit reciprocal prime
minus Li discrepancy. -/
def primeSieveReciprocalLowFrequencyIntervalEnergy
    (y x : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, _a, _b => 0
  | depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        ((b - a : ℕ) : ℝ) *
            ‖(((b - a : ℕ) : ℂ)⁻¹ *
              primeSieveReciprocalSiblingContrast y x a m b)‖ ^ 2 +
          primeSieveReciprocalLowFrequencyIntervalEnergy y x depth a m +
          primeSieveReciprocalLowFrequencyIntervalEnergy y x depth m b
      else 0

/-- On every interval contained in reciprocal support, the existing midpoint
packet tree is exactly the reciprocal-discrepancy low-frequency square
function. -/
theorem primeSieveDyadicPacketIntervalTreeEnergy_eq_reciprocalLowFrequencyIntervalEnergy
    (y x depth a b : ℕ)
    (ha : 1 ≤ a)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveDyadicPacketIntervalTreeEnergy y x depth a b =
      primeSieveReciprocalLowFrequencyIntervalEnergy y x depth a b := by
  induction depth generalizing a b with
  | zero =>
      simp [primeSieveReciprocalLowFrequencyIntervalEnergy,
        primeSieveDyadicPacketIntervalTreeEnergy_zero]
  | succ depth ih =>
      rw [primeSieveDyadicPacketIntervalTreeEnergy_succ]
      by_cases hsplit : a + 1 < b
      · let m := dyadicPacketMidpoint a b
        have hm : a < m ∧ m < b := by
          dsimp [m, dyadicPacketMidpoint]
          omega
        have hm1 : 1 ≤ m := ha.trans hm.1.le
        have hmB : m ≤ x / (y + 1) + 1 := hm.2.le.trans hb
        have hres :
            primeSieveSignedSiblingPacketResidual y x a m b =
              (((b - a : ℕ) : ℂ)⁻¹) *
                primeSieveReciprocalSiblingContrast y x a m b :=
          primeSieveSignedSiblingPacketResidual_eq_reciprocalSiblingContrast
            ha hm.1.le hm.2.le hb
        simp [primeSieveReciprocalLowFrequencyIntervalEnergy, hsplit, m,
          hres, ih a m ha hmB, ih m b hm1 hb]
      · simp [primeSieveReciprocalLowFrequencyIntervalEnergy, hsplit]

/-- The global reciprocal low-frequency square function through depth `J` on
every occupied dyadic block. -/
def primeSieveReciprocalLowFrequencySquareFunction
    (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveReciprocalLowFrequencyIntervalEnergy y x (min J j)
      (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)

/-- Exact global identification with the existing shallow packet energy. -/
theorem primeSieveReciprocalLowFrequencySquareFunction_eq_shallowEnergy
    (y x J : ℕ) :
    primeSieveReciprocalLowFrequencySquareFunction y x J =
      primeSieveDyadicPacketShallowEnergy y x J := by
  unfold primeSieveReciprocalLowFrequencySquareFunction
    primeSieveDyadicPacketShallowEnergy primeSieveDyadicPacketTreeBlockEnergy
  apply Finset.sum_congr rfl
  intro j hj
  have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
    unfold primeSieveDyadicBlockLeft
    have hpow : 0 < 2 ^ j := by positivity
    omega
  have hright :
      primeSieveDyadicBlockRight y x j + 1 ≤ x / (y + 1) + 1 := by
    unfold primeSieveDyadicBlockRight
    exact Nat.add_le_add_right
      (min_le_left (x / (y + 1)) (2 ^ (j + 1) - 1)) 1
  exact (primeSieveDyadicPacketIntervalTreeEnergy_eq_reciprocalLowFrequencyIntervalEnergy
    y x (min J j) (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1) hleft1 hright).symm

/-- The shallow tree is the finite sum of the exact packet levels below the
cutoff.  This removes the recursive wrapper from the remaining analytic target. -/
theorem primeSieveDyadicPacketShallowEnergy_eq_sum_levelEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J =
      ∑ r ∈ Finset.range J, primeSieveDyadicPacketLevelEnergy y x r := by
  induction J with
  | zero =>
      unfold primeSieveDyadicPacketShallowEnergy
        primeSieveDyadicPacketTreeBlockEnergy
      simp
  | succ J ih =>
      rw [primeSieveDyadicPacketShallowEnergy_succ_eq, ih,
        Finset.sum_range_succ]

/-- Fully expanded finite-level form: each shallow level is the exact signed
midpoint energy on every occupied block still alive at that level. -/
theorem primeSieveDyadicPacketShallowEnergy_eq_sum_intervalLevelEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J =
      ∑ r ∈ Finset.range J,
        ∑ j ∈ primeSieveDyadicBlockIndices y x,
          if r < j then
            primeSieveDyadicPacketIntervalLevelEnergy y x r
              (primeSieveDyadicBlockLeft j)
              (primeSieveDyadicBlockRight y x j + 1)
          else 0 := by
  rw [primeSieveDyadicPacketShallowEnergy_eq_sum_levelEnergy]
  apply Finset.sum_congr rfl
  intro r _hr
  exact primeSieveDyadicPacketLevelEnergy_eq_sum_intervalLevelEnergy y x r

/-- Shallow packet energy is monotone across arbitrary cutoff depths. -/
theorem primeSieveDyadicPacketShallowEnergy_mono
    (y x : ℕ) {r s : ℕ} (hrs : r ≤ s) :
    primeSieveDyadicPacketShallowEnergy y x r ≤
      primeSieveDyadicPacketShallowEnergy y x s := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih =>
      exact ih.trans (primeSieveDyadicPacketShallowEnergy_le_succ y x s)

/-- Base-eight successor shallow square function selected by an earlier layer. -/
def primeSieveBaseEightShallowSquareFunction (k x : ℕ) : ℝ :=
  primeSieveReciprocalLowFrequencySquareFunction
    (primorialPNTPrimeSieveCutoff k) x
    (dyadicPacketBaseEightCutoff k x + 1)

/-- The base-eight square function is literally the successor-shallow packet
energy left open by an earlier layer. -/
theorem primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy
    (k x : ℕ) :
    primeSieveBaseEightShallowSquareFunction k x =
      primeSieveDyadicPacketShallowEnergy
        (primorialPNTPrimeSieveCutoff k) x
        (dyadicPacketBaseEightCutoff k x + 1) := by
  simpa [primeSieveBaseEightShallowSquareFunction] using
    primeSieveReciprocalLowFrequencySquareFunction_eq_shallowEnergy
      (primorialPNTPrimeSieveCutoff k) x
      (dyadicPacketBaseEightCutoff k x + 1)

/-- At the base-eight successor cutoff, the remaining square function is the
finite sum of levels `0 <= r <= log_8(x+1)`. -/
theorem primeSieveBaseEightShallowSquareFunction_eq_sum_levelEnergy
    (k x : ℕ) :
    primeSieveBaseEightShallowSquareFunction k x =
      ∑ r ∈ Finset.range (dyadicPacketBaseEightCutoff k x + 1),
        primeSieveDyadicPacketLevelEnergy
          (primorialPNTPrimeSieveCutoff k) x r := by
  rw [primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy,
    primeSieveDyadicPacketShallowEnergy_eq_sum_levelEnergy]

/-- The first low-frequency layer of the reciprocal square function.  This is
the root sibling energy on every occupied dyadic reciprocal block. -/
def primeSieveReciprocalRootSiblingSquareFunction (y x : ℕ) : ℝ :=
  primeSieveReciprocalLowFrequencySquareFunction y x 1

/-- The root sibling square function is exactly packet level zero. -/
theorem primeSieveReciprocalRootSiblingSquareFunction_eq_levelEnergy_zero
    (y x : ℕ) :
    primeSieveReciprocalRootSiblingSquareFunction y x =
      primeSieveDyadicPacketLevelEnergy y x 0 := by
  unfold primeSieveReciprocalRootSiblingSquareFunction
  rw [primeSieveReciprocalLowFrequencySquareFunction_eq_shallowEnergy,
    primeSieveDyadicPacketShallowEnergy_eq_sum_levelEnergy]
  simp

/-- Necessary root-level analytic estimate.  Any proof of the complete
base-eight shallow square-function bound must already control this first
low-frequency sibling layer at critical scale. -/
def DyadicPrimeReciprocalRootSiblingBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveReciprocalRootSiblingSquareFunction
            (primorialPNTPrimeSieveCutoff k) x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The exact low-frequency arithmetic statement exposed by an earlier layer.  It asks for
a critical block-uniform bound on the reciprocal-discrepancy Haar square
function at the base-eight successor cutoff. -/
def DyadicPrimeReciprocalLowFrequencySquareFunctionBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveBaseEightShallowSquareFunction k x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The complete base-eight low-frequency estimate necessarily contains the
root sibling estimate.  Thus level zero is already a concrete analytic
obstruction if a direct all-level proof is unavailable. -/
theorem dyadicPrimeReciprocalLowFrequencySquareFunctionBlockBounded_implies_rootSibling
    (h : DyadicPrimeReciprocalLowFrequencySquareFunctionBlockBoundedStatement) :
    DyadicPrimeReciprocalRootSiblingBlockBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let J := dyadicPacketBaseEightCutoff k x
  have hroot :
      primeSieveReciprocalRootSiblingSquareFunction y x ≤
        primeSieveDyadicPacketShallowEnergy y x 1 := by
    rw [primeSieveReciprocalRootSiblingSquareFunction_eq_levelEnergy_zero]
    simpa using primeSieveDyadicPacketLevelEnergy_le_shallow_succ y x 0
  have hmono :
      primeSieveDyadicPacketShallowEnergy y x 1 ≤
        primeSieveDyadicPacketShallowEnergy y x (J + 1) :=
    primeSieveDyadicPacketShallowEnergy_mono y x (by omega)
  have hfull := hCb k x hk hlow hup
  change primeSieveReciprocalRootSiblingSquareFunction y x ≤
    C * Real.rpow ((x : ℝ) + 1) (1 + ε)
  calc
    primeSieveReciprocalRootSiblingSquareFunction y x ≤
        primeSieveDyadicPacketShallowEnergy y x 1 := hroot
    _ ≤ primeSieveDyadicPacketShallowEnergy y x (J + 1) := hmono
    _ = primeSieveBaseEightShallowSquareFunction k x := by
      symm
      simpa [y, J] using
        primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy k x
    _ ≤ C * Real.rpow ((x : ℝ) + 1) (1 + ε) := hfull

/-- The new arithmetic square-function statement is exactly equivalent to the
remaining successor-shallow packet hypothesis in the terminal package. -/
theorem dyadicPrimeReciprocalLowFrequencySquareFunctionBlockBounded_iff_baseEightShallow :
    DyadicPrimeReciprocalLowFrequencySquareFunctionBlockBoundedStatement ↔
      DyadicPacketShallowEnergyBlockBoundedStatement
        (dyadicPacketSuccCutoff dyadicPacketBaseEightCutoff) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hCb⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    have hs := hCb k x hk hlow hup
    rw [primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy] at hs
    simpa [dyadicPacketSuccCutoff] using hs
  · intro h ε hε
    obtain ⟨C, hC, hCb⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    have hs := hCb k x hk hlow hup
    rw [primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy]
    simpa [dyadicPacketSuccCutoff] using hs

/-- RH can now be stated with the packet-side shallow input entirely in the
reciprocal-discrepancy square-function coordinate exposed above. -/
theorem riemannHypothesis_of_baseEightReciprocalLowFrequencyPackage
    (hC : DyadicCoherentChannelRHScale)
    (hS : DyadicPrimeReciprocalLowFrequencySquareFunctionBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_baseEightPacketAnalyticPackage hC
  · exact
      dyadicPrimeReciprocalLowFrequencySquareFunctionBlockBounded_iff_baseEightShallow.mp hS
  · exact hD

end RHLean.Analysis
