import Mathlib
import RHLean.Proof.RiemannHypothesisBridge

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Local squared energy of a complex-valued sequence on `[N, N + H)`. -/
def localSequenceEnergy (f : ℕ → ℂ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ‖f (N + h)‖ ^ 2

/--
An exact low/high geometric partition of the actual-start sequence.

The pointwise low-sector estimate is stated at squared-energy level because this
is the precise input needed for the translated-window criterion.
-/
structure ActualStartGeometricPartition
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) where
  low : ℕ → ℂ
  high : ℕ → ℂ
  lowConstant : ℝ
  lowConstant_nonneg : 0 ≤ lowConstant
  recombine : ∀ n, start.actual n = low n + high n
  low_energy_pointwise :
    ∀ n, ‖low n‖ ^ 2 ≤ lowConstant * (n : ℝ) ^ 2

/-- Local low-sector energy on `[N, N + H)`. -/
def actualStartLocalLowEnergy
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    {start : ActualStartConfiguration skeleton data}
    (partition : ActualStartGeometricPartition start)
    (N H : ℕ) : ℝ :=
  localSequenceEnergy partition.low N H

/-- Local high-sector energy on `[N, N + H)`. -/
def actualStartLocalHighEnergy
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    {start : ActualStartConfiguration skeleton data}
    (partition : ActualStartGeometricPartition start)
    (N H : ℕ) : ℝ :=
  localSequenceEnergy partition.high N H

/-- The high-sector version of the uniform local square-prefix criterion. -/
def ActualStartHighUniformLocalBoundedStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    {start : ActualStartConfiguration skeleton data}
    (partition : ActualStartGeometricPartition start) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        actualStartLocalHighEnergy partition N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

private theorem norm_sq_add_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem norm_sq_sub_le_two (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  simpa [sub_eq_add_neg] using norm_sq_add_le_two x (-y)

/-- The pointwise linear low-sector bound gives a translated-window `H N^2` bound. -/
theorem actualStart_localLowEnergy_le
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    {start : ActualStartConfiguration skeleton data}
    (partition : ActualStartGeometricPartition start)
    (N H : ℕ)
    (hHN : H ≤ N) :
    actualStartLocalLowEnergy partition N H ≤
      4 * partition.lowConstant * (H : ℝ) * (N : ℝ) ^ 2 := by
  unfold actualStartLocalLowEnergy localSequenceEnergy
  calc
    (∑ h ∈ Finset.range H, ‖partition.low (N + h)‖ ^ 2) ≤
        ∑ _h ∈ Finset.range H,
          4 * partition.lowConstant * (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro h hh
      have hlt : h < H := Finset.mem_range.mp hh
      have hindexNat : N + h ≤ 2 * N := by omega
      have hindex : ((N + h : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        exact_mod_cast hindexNat
      have hsq : ((N + h : ℕ) : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
        have hleft : 0 ≤ ((N + h : ℕ) : ℝ) := by positivity
        have hright : 0 ≤ (N : ℝ) := by positivity
        nlinarith
      calc
        ‖partition.low (N + h)‖ ^ 2 ≤
            partition.lowConstant * ((N + h : ℕ) : ℝ) ^ 2 :=
          partition.low_energy_pointwise (N + h)
        _ ≤ partition.lowConstant * (4 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq partition.lowConstant_nonneg
        _ = 4 * partition.lowConstant * (N : ℝ) ^ 2 := by ring
    _ = (H : ℝ) * (4 * partition.lowConstant * (N : ℝ) ^ 2) := by simp
    _ = 4 * partition.lowConstant * (H : ℝ) * (N : ℝ) ^ 2 := by ring

/-- The geometric low sector automatically satisfies the RH-scale local bound. -/
theorem actualStart_lowUniformLocalBounded
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    {start : ActualStartConfiguration skeleton data}
    (partition : ActualStartGeometricPartition start) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ N H : ℕ, 1 ≤ H → H ≤ N →
          actualStartLocalLowEnergy partition N H ≤
            C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by
  intro ε hε
  refine ⟨4 * partition.lowConstant,
    mul_nonneg (by norm_num) partition.lowConstant_nonneg, ?_⟩
  intro N H hH hHN
  have hN1 : 1 ≤ N := hH.trans hHN
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hexponent : (2 : ℝ) ≤ 2 + ε := by linarith
  have hpow : (N : ℝ) ^ 2 ≤ Real.rpow (N : ℝ) (2 + ε) := by
    rw [← Real.rpow_natCast]
    exact (Real.monotone_rpow_of_base_ge_one hbase) hexponent
  have hfourLow : 0 ≤ 4 * partition.lowConstant :=
    mul_nonneg (by norm_num) partition.lowConstant_nonneg
  have hcoefficient : 0 ≤ 4 * partition.lowConstant * (H : ℝ) :=
    mul_nonneg hfourLow (Nat.cast_nonneg H)
  calc
    actualStartLocalLowEnergy partition N H ≤
        4 * partition.lowConstant * (H : ℝ) * (N : ℝ) ^ 2 :=
      actualStart_localLowEnergy_le partition N H hHN
    _ ≤ 4 * partition.lowConstant * (H : ℝ) *
          Real.rpow (N : ℝ) (2 + ε) :=
      mul_le_mul_of_nonneg_left hpow hcoefficient
    _ = (4 * partition.lowConstant) * (H : ℝ) *
          Real.rpow (N : ℝ) (2 + ε) := by ring

/-- Total local energy is controlled by twice the low and high local energies. -/
theorem actualStart_localFrameEnergy_le_two_low_add_high
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (partition : ActualStartGeometricPartition start)
    (N H : ℕ) :
    actualStartLocalFrameEnergy start N H ≤
      2 * actualStartLocalLowEnergy partition N H +
        2 * actualStartLocalHighEnergy partition N H := by
  unfold actualStartLocalFrameEnergy actualStartLocalLowEnergy
    actualStartLocalHighEnergy localSequenceEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  rw [partition.recombine]
  exact norm_sq_add_le_two _ _

/-- High local energy is controlled by twice the total and low local energies. -/
theorem actualStart_localHighEnergy_le_two_total_add_low
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (partition : ActualStartGeometricPartition start)
    (N H : ℕ) :
    actualStartLocalHighEnergy partition N H ≤
      2 * actualStartLocalFrameEnergy start N H +
        2 * actualStartLocalLowEnergy partition N H := by
  unfold actualStartLocalFrameEnergy actualStartLocalLowEnergy
    actualStartLocalHighEnergy localSequenceEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  have hhigh : partition.high (N + h) =
      start.actual (N + h) - partition.low (N + h) := by
    rw [partition.recombine]
    simp
  rw [hhigh]
  exact norm_sq_sub_le_two _ _

/--
Once the low sector has its elementary local bound, the total and high-sector
uniform local criteria are logically equivalent. No low/high cross-term estimate
is needed.
-/
theorem actualStart_uniformLocalBounded_iff_highUniformLocalBounded
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (partition : ActualStartGeometricPartition start) :
    ActualStartUniformLocalBoundedStatement start ↔
      ActualStartHighUniformLocalBoundedStatement partition := by
  constructor
  · intro htotal ε hε
    rcases htotal ε hε with ⟨Ctotal, hCtotal, htotalBound⟩
    rcases actualStart_lowUniformLocalBounded partition ε hε with
      ⟨Clow, hClow, hlowBound⟩
    refine ⟨2 * Ctotal + 2 * Clow, by nlinarith, ?_⟩
    intro N H hH hHN
    have htotalNH := htotalBound N H hH hHN
    have hlowNH := hlowBound N H hH hHN
    calc
      actualStartLocalHighEnergy partition N H ≤
          2 * actualStartLocalFrameEnergy start N H +
            2 * actualStartLocalLowEnergy partition N H :=
        actualStart_localHighEnergy_le_two_total_add_low start partition N H
      _ ≤ 2 * (Ctotal * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) +
            2 * (Clow * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) := by
        nlinarith
      _ = (2 * Ctotal + 2 * Clow) * (H : ℝ) *
            Real.rpow (N : ℝ) (2 + ε) := by ring
  · intro hhigh ε hε
    rcases hhigh ε hε with ⟨Chigh, hChigh, hhighBound⟩
    rcases actualStart_lowUniformLocalBounded partition ε hε with
      ⟨Clow, hClow, hlowBound⟩
    refine ⟨2 * Clow + 2 * Chigh, by nlinarith, ?_⟩
    intro N H hH hHN
    have hlowNH := hlowBound N H hH hHN
    have hhighNH := hhighBound N H hH hHN
    calc
      actualStartLocalFrameEnergy start N H ≤
          2 * actualStartLocalLowEnergy partition N H +
            2 * actualStartLocalHighEnergy partition N H :=
        actualStart_localFrameEnergy_le_two_low_add_high start partition N H
      _ ≤ 2 * (Clow * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) +
            2 * (Chigh * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) := by
        nlinarith
      _ = (2 * Clow + 2 * Chigh) * (H : ℝ) *
            Real.rpow (N : ℝ) (2 + ε) := by ring

/--
Pure architectural equivalence: for an exact geometric low/high partition with
the proved elementary low-sector bound, the high-sector local criterion is
equivalent to RH through the explicit square-prefix bridge.
-/
theorem actualStart_highUniformLocalBounded_iff_riemannHypothesis
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (partition : ActualStartGeometricPartition start)
    (bridge : ActualStartRHBridge start) :
    ActualStartHighUniformLocalBoundedStatement partition ↔
      RiemannHypothesisStatement := by
  calc
    ActualStartHighUniformLocalBoundedStatement partition ↔
        ActualStartUniformLocalBoundedStatement start :=
      (actualStart_uniformLocalBounded_iff_highUniformLocalBounded
        start partition).symm
    _ ↔ RiemannHypothesisStatement :=
      actualStart_uniformLocalBounded_iff_riemannHypothesis start bridge

end RHLean.Analysis
