import Mathlib
import RHLean.Analysis.BlockCovarianceDecomposition
import RHLean.Analysis.BlockCovarianceRefinement
import RHLean.Proof.ComplexVerticalFiberSpacing

/-!
# Green--Kubo inequality on physical squared-Fermat child lines

`ComplexVerticalFiberSpacing` reduces the ordered Euler frontier at each root to
one active atom per physical child integer and proves that a child present at
both endpoints contributes exactly zero to the run difference.  This file takes
the next quantitative step: square the *whole signed birth/death population*
before taking any absolute values.

For a run from root `a` to root `b+1`, define one real event variable at each
physical child integer `n`:

* `0` if the child has the same endpoint status;
* `-mu(n)` if the child is born into the active endpoint set;
* `+mu(n)` if the child dies from the active endpoint set.

The sum of these variables is exactly the complex vertical-interval mass after
casting to `C`.  Hence the generic deterministic Green--Kubo identity gives

`||V(a,b)||^2 = diagonal + 2 * lineCovariance`.

Every event variable lies in `{-1,0,1}`, and every active child at root `R` is
strictly below `R^2`.  Therefore, without counting births and deaths separately,

`diagonal <= (b+1)^2`.

This yields the unconditional one-sided inequality

`||V(a,b)||^2 <= (b+1)^2 + 2 * max 0 lineCovariance`.

Under strict subdoubling this becomes

`||V(a,b)||^2 <= 2*a^2 + 2 * max 0 lineCovariance`.

Thus the diagonal is already at the required root-square energy scale.  The
only quantity capable of producing supercritical growth is the *positive*
aggregate covariance among distinct physical birth/death lines.  No triangle
inequality over lines, unsigned population bound, PNT input, independence
hypothesis, or RH hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Real endpoint charges on physical child lines -/

/-- Real form of the conserved physical-child charge `-mu(n)`. -/
def orderedEulerCutChildChargeReal (n : ℕ) : ℝ :=
  -((μ n : ℤ) : ℝ)

@[simp] theorem orderedEulerCutChildChargeReal_cast (n : ℕ) :
    ((orderedEulerCutChildChargeReal n : ℝ) : ℂ) =
      orderedEulerCutChildCharge n := by
  simp [orderedEulerCutChildChargeReal, orderedEulerCutChildCharge,
    canonicalMoebiusWeight]

/-- Real endpoint contribution of one physical child line. -/
def orderedEulerCutChildEndpointChargeReal (R n : ℕ) : ℝ :=
  if n ∈ orderedEulerCutActiveChildren R then
    orderedEulerCutChildChargeReal n
  else 0

@[simp] theorem orderedEulerCutChildEndpointChargeReal_cast (R n : ℕ) :
    ((orderedEulerCutChildEndpointChargeReal R n : ℝ) : ℂ) =
      orderedEulerCutChildEndpointCharge R n := by
  by_cases h : n ∈ orderedEulerCutActiveChildren R <;>
    simp [orderedEulerCutChildEndpointChargeReal,
      orderedEulerCutChildEndpointCharge, h]

/-- Every active physical child lies strictly below the square of its current
root.  This is the birth-root square cutoff, expressed directly on the child
coordinate. -/
theorem orderedEulerCutActiveChild_lt_root_sq
    {R n : ℕ} (hn : n ∈ orderedEulerCutActiveChildren R) :
    n < R ^ 2 := by
  rcases Finset.mem_image.mp hn with ⟨y, hy, rfl⟩
  have hshape := orderedEulerCutShape_of_mem_carrier hy
  have hocc := mem_orderedEulerCutCarrier.mp hy
  have hsqrt :=
    (orderedEulerCutOccursAt_sqrt_factor_window hshape hocc).2.1
  exact (Nat.sqrt_lt').1 hsqrt

/-- Hence the active-child set embeds in the physical integer prefix below
`R^2`. -/
theorem orderedEulerCutActiveChildren_subset_range_sq (R : ℕ) :
    orderedEulerCutActiveChildren R ⊆ Finset.range (R ^ 2) := by
  intro n hn
  exact Finset.mem_range.mpr (orderedEulerCutActiveChild_lt_root_sq hn)

/-- Summing the endpoint-charge field over any ambient prefix containing `R^2`
recovers exactly the active-child charge sum. -/
theorem signedBlockPrefix_childEndpointChargeReal_eq_activeChildSum
    (R K : ℕ) (hRK : R ^ 2 ≤ K) :
    signedBlockPrefix (orderedEulerCutChildEndpointChargeReal R) K =
      ∑ n ∈ orderedEulerCutActiveChildren R,
        orderedEulerCutChildChargeReal n := by
  unfold signedBlockPrefix orderedEulerCutChildEndpointChargeReal
  have hfilter :
      (Finset.range K).filter (fun n => n ∈ orderedEulerCutActiveChildren R) =
        orderedEulerCutActiveChildren R := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hn
      refine ⟨?_, hn⟩
      exact lt_of_lt_of_le (orderedEulerCutActiveChild_lt_root_sq hn) hRK
  rw [← Finset.sum_filter, hfilter]

/-! ## The signed line-event trajectory -/

/-- Endpoint change carried by one physical child line.  Internal transport of
a line present at both endpoints is already zero here. -/
def signedVerticalLineEventStep (a b n : ℕ) : ℝ :=
  orderedEulerCutChildEndpointChargeReal (b + 1) n -
    orderedEulerCutChildEndpointChargeReal a n

/-- Total real birth/death mass, evaluated on the physical child prefix large
enough to contain both endpoint carriers. -/
def signedVerticalLineRunMassReal (a b : ℕ) : ℝ :=
  signedBlockPrefix (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-- Diagonal energy of the physical line-event trajectory. -/
def signedVerticalLineRunDiagonal (a b : ℕ) : ℝ :=
  signedBlockEnergy (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-- Aggregate covariance over distinct physical birth/death lines.  This is a
signed pair sum; negative covariance helps and is never replaced by its
absolute value. -/
def signedVerticalLineRunCovariance (a b : ℕ) : ℝ :=
  signedBlockCrossCovariance (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-- The real line-event sum is exactly the difference of the two active-child
charge sums. -/
theorem signedVerticalLineRunMassReal_eq_activeChildChargeDifference
    (a b : ℕ) (hab : a ≤ b + 1) :
    signedVerticalLineRunMassReal a b =
      (∑ n ∈ orderedEulerCutActiveChildren (b + 1),
        orderedEulerCutChildChargeReal n) -
      ∑ n ∈ orderedEulerCutActiveChildren a,
        orderedEulerCutChildChargeReal n := by
  unfold signedVerticalLineRunMassReal signedVerticalLineEventStep
    signedBlockPrefix
  rw [Finset.sum_sub_distrib]
  have haSq : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left hab 2
  have hright :=
    signedBlockPrefix_childEndpointChargeReal_eq_activeChildSum
      (b + 1) ((b + 1) ^ 2) (le_refl _)
  have hleft :=
    signedBlockPrefix_childEndpointChargeReal_eq_activeChildSum
      a ((b + 1) ^ 2) haSq
  unfold signedBlockPrefix at hright hleft
  rw [hright, hleft]

/-- The line-event mass is literally the already-formalized complex vertical
run mass. -/
theorem signedVerticalLineRunMassReal_cast_eq_verticalMass
    (a b : ℕ) (hab : a ≤ b + 1) :
    ((signedVerticalLineRunMassReal a b : ℝ) : ℂ) =
      signedVerticalIntervalMass a b := by
  rw [signedVerticalLineRunMassReal_eq_activeChildChargeDifference a b hab,
    signedVerticalIntervalMass_eq_activeChildChargeDifference]
  push_cast
  simp_rw [orderedEulerCutChildChargeReal_cast]

/-! ## Green--Kubo before every magnitude estimate -/

/-- Exact square expansion of the complete signed physical line-event
population. -/
theorem signedVerticalLineRunMassReal_sq_eq_diagonal_add_two_mul_covariance
    (a b : ℕ) :
    signedVerticalLineRunMassReal a b ^ 2 =
      signedVerticalLineRunDiagonal a b +
        2 * signedVerticalLineRunCovariance a b := by
  exact signedBlockPrefix_sq_eq_energy_add_two_mul_cross
    (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-- Every physical line event has squared charge at most one.  This uses only
`mu(n) in {-1,0,1}` and keeps the birth/death sign intact. -/
theorem signedVerticalLineEventStep_sq_le_one
    (a b n : ℕ) :
    signedVerticalLineEventStep a b n ^ 2 ≤ 1 := by
  have hmu := realMoebiusStep_sq_le_one n
  by_cases hb : n ∈ orderedEulerCutActiveChildren (b + 1)
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · simp [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha]
    · simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha]
        using hmu
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha]
        using hmu
    · simp [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha]

/-- **Root-square diagonal bound.**  The entire birth/death diagonal is already
at RH energy scale.  No estimate of the unsigned number of Euler atoms is used. -/
theorem signedVerticalLineRunDiagonal_le_endpoint_sq
    (a b : ℕ) :
    signedVerticalLineRunDiagonal a b ≤ (((b + 1) ^ 2 : ℕ) : ℝ) := by
  unfold signedVerticalLineRunDiagonal signedBlockEnergy
  calc
    (∑ n ∈ Finset.range ((b + 1) ^ 2),
        signedVerticalLineEventStep a b n ^ 2) ≤
      ∑ _n ∈ Finset.range ((b + 1) ^ 2), (1 : ℝ) := by
        exact Finset.sum_le_sum
          (fun n _hn => signedVerticalLineEventStep_sq_le_one a b n)
    _ = (((b + 1) ^ 2 : ℕ) : ℝ) := by simp

/-- Norm-square of the original complex vertical mass is the ordinary square
of the real birth/death line sum. -/
theorem norm_signedVerticalIntervalMass_sq_eq_lineRunMassReal_sq
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 =
      signedVerticalLineRunMassReal a b ^ 2 := by
  rw [← signedVerticalLineRunMassReal_cast_eq_verticalMass a b hab,
    Complex.norm_real, Real.norm_eq_abs]
  exact sq_abs _

/-- Exact Green--Kubo identity stated directly on the complex vertical mass. -/
theorem norm_signedVerticalIntervalMass_sq_eq_lineDiagonal_add_two_mul_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 =
      signedVerticalLineRunDiagonal a b +
        2 * signedVerticalLineRunCovariance a b := by
  rw [norm_signedVerticalIntervalMass_sq_eq_lineRunMassReal_sq a b hab]
  exact signedVerticalLineRunMassReal_sq_eq_diagonal_add_two_mul_covariance a b

/-- **Actual unconditional one-sided inequality.**  The diagonal is root-square,
so only positive aggregate covariance can push the signed birth/death mass
above root scale. -/
theorem norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (((b + 1) ^ 2 : ℕ) : ℝ) +
        2 * signedVerticalLineRunCovariance a b := by
  have hid :=
    norm_signedVerticalIntervalMass_sq_eq_lineDiagonal_add_two_mul_covariance
      a b hab
  have hdiag := signedVerticalLineRunDiagonal_le_endpoint_sq a b
  linarith

/-- Negative line covariance is harmless.  This is the unconditional envelope
with only the positive part of the genuine signed pair sum remaining. -/
theorem norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_positiveCovariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (((b + 1) ^ 2 : ℕ) : ℝ) +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_covariance
      a b hab
  have hcov : signedVerticalLineRunCovariance a b ≤
      max 0 (signedVerticalLineRunCovariance a b) :=
    le_max_right _ _
  linarith

/-- Any proposed upper budget on the *one-sided signed covariance* immediately
bounds the whole birth/death population.  There is no absolute value on the
covariance hypothesis. -/
theorem norm_signedVerticalIntervalMass_sq_le_of_lineCovariance_le
    (a b : ℕ) (hab : a ≤ b + 1) (B : ℝ)
    (hcov : signedVerticalLineRunCovariance a b ≤ B) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (((b + 1) ^ 2 : ℕ) : ℝ) + 2 * B := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_covariance
      a b hab
  linarith

/-- Conversely, a super-root vertical mass forces positive covariance among
distinct birth/death lines.  This is the exact pressure inequality to attack
with the sequential Euler geometry. -/
theorem signedVerticalLineRunCovariance_ge_half_excess
    (a b : ℕ) (hab : a ≤ b + 1) :
    (‖signedVerticalIntervalMass a b‖ ^ 2 -
        (((b + 1) ^ 2 : ℕ) : ℝ)) / 2 ≤
      signedVerticalLineRunCovariance a b := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_covariance
      a b hab
  linarith

/-- **Subdoubling root-scale inequality.**  On the frozen horizon the physical
diagonal is at most `2*a^2`, so the exact remaining obstruction is only the
positive cross-line covariance. -/
theorem norm_signedVerticalIntervalMass_sq_le_subdoubling_root_sq_add_covariance
    (a b : ℕ) (hab : a ≤ b + 1)
    (hsub : (b + 1) ^ 2 < 2 * a ^ 2) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (((2 * a ^ 2 : ℕ) : ℝ)) +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_positiveCovariance
      a b hab
  have hsqNat : (b + 1) ^ 2 ≤ 2 * a ^ 2 := Nat.le_of_lt hsub
  have hsqReal :
      ((((b + 1) ^ 2 : ℕ) : ℝ)) ≤ (((2 * a ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hsqNat
  linarith

/-! ## Sequential Euler action on the covariance term

The birth/death event is a Möbius sign times a deterministic endpoint mask.
This exposes the exact two-coordinate Euler action on the *covariance itself*.
For a fresh prime, the four pair descendants still carry the `+,-,-,+`
Möbius pattern.  Hence every complete four-corner covariance cube cancels up to
the mixed finite difference of the endpoint mask and the physical order cutoff.

If the endpoint mask is stable under multiplication by that fresh prime, the
masked mixed cell collapses to the already-formalized global order cell.  After
swapping the two old coordinates, its two interior order shells cancel and only
the usual top escape remains.  Likewise the covariance strictly inside a
prime-family is an exact lower-scale copy of the same line covariance whenever
the mask is stable on that lower prefix.

Thus positive line covariance is no longer an opaque pair sum: prime-stable
families descend exactly, and the genuinely new obstruction is localized to
prime-instability of the physical birth/death mask plus the standard top escape.
No absolute covariance bound is introduced.
-/

/-- Deterministic endpoint-status mask multiplying the ordinary Möbius sign.
It is `+1` on deaths, `-1` on births, and `0` on persistent/absent lines. -/
def signedVerticalLineEventMask (a b n : ℕ) : ℝ :=
  (if n ∈ orderedEulerCutActiveChildren a then 1 else 0) -
    (if n ∈ orderedEulerCutActiveChildren (b + 1) then 1 else 0)

/-- The line event factors exactly as ordinary Möbius times its endpoint mask. -/
theorem signedVerticalLineEventStep_eq_moebius_mul_mask
    (a b n : ℕ) :
    signedVerticalLineEventStep a b n =
      realMoebiusStep n * signedVerticalLineEventMask a b n := by
  by_cases ha : n ∈ orderedEulerCutActiveChildren a <;>
    by_cases hb : n ∈ orderedEulerCutActiveChildren (b + 1) <;>
      simp [signedVerticalLineEventStep, signedVerticalLineEventMask,
        orderedEulerCutChildEndpointChargeReal, orderedEulerCutChildChargeReal,
        realMoebiusStep, ha, hb]

/-- The covariance term is literally the masked ordinary Möbius pair sum. -/
theorem signedVerticalLineRunCovariance_eq_masked_doubleSum
    (a b : ℕ) :
    signedVerticalLineRunCovariance a b =
      ∑ n ∈ Finset.range ((b + 1) ^ 2),
        ∑ m ∈ Finset.range n,
          realMoebiusStep m * realMoebiusStep n *
            (signedVerticalLineEventMask a b m *
              signedVerticalLineEventMask a b n) := by
  unfold signedVerticalLineRunCovariance
  rw [signedBlockCrossCovariance_eq_doubleSum]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro m _hm
  rw [signedVerticalLineEventStep_eq_moebius_mul_mask,
    signedVerticalLineEventStep_eq_moebius_mul_mask]
  ring

/-- Ordered physical pair cell with the line-event mask retained. -/
def signedVerticalLineMaskedPairIndicator
    (a b K m n : ℕ) : ℝ :=
  signedVerticalLineEventMask a b m *
    signedVerticalLineEventMask a b n *
      positiveLagPairIndicator K m n

/-- Mixed two-coordinate finite difference after adjoining one prime in either
physical child coordinate. -/
def signedVerticalLinePairMixedPrimeCell
    (a b p K m n : ℕ) : ℝ :=
  signedVerticalLineMaskedPairIndicator a b K m n -
    signedVerticalLineMaskedPairIndicator a b K (p * m) n -
    signedVerticalLineMaskedPairIndicator a b K m (p * n) +
    signedVerticalLineMaskedPairIndicator a b K (p * m) (p * n)

/-- Actual four-corner covariance mass of the line-event trajectory. -/
def signedVerticalLinePairFourCornerMass
    (a b p K m n : ℕ) : ℝ :=
  signedVerticalLineEventStep a b m * signedVerticalLineEventStep a b n *
      positiveLagPairIndicator K m n +
    signedVerticalLineEventStep a b (p * m) * signedVerticalLineEventStep a b n *
      positiveLagPairIndicator K (p * m) n +
    signedVerticalLineEventStep a b m * signedVerticalLineEventStep a b (p * n) *
      positiveLagPairIndicator K m (p * n) +
    signedVerticalLineEventStep a b (p * m) *
      signedVerticalLineEventStep a b (p * n) *
        positiveLagPairIndicator K (p * m) (p * n)

/-- **Fresh-prime covariance cube.**  All Möbius dependence factors into the
old pair weight.  The complete remaining defect is the mixed finite difference
of the physical line mask and order cutoff. -/
theorem signedVerticalLinePairFourCornerMass_eq_mixedPrimeCell
    {a b p K m n : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    signedVerticalLinePairFourCornerMass a b p K m n =
      realMoebiusStep m * realMoebiusStep n *
        signedVerticalLinePairMixedPrimeCell a b p K m n := by
  unfold signedVerticalLinePairFourCornerMass
  simp_rw [signedVerticalLineEventStep_eq_moebius_mul_mask]
  rw [realMoebiusStep_mul_prime_eq_neg hp hpm,
    realMoebiusStep_mul_prime_eq_neg hp hpn]
  unfold signedVerticalLinePairMixedPrimeCell
    signedVerticalLineMaskedPairIndicator
  ring

/-- If the physical endpoint mask is prime-stable in both old coordinates, the
masked covariance cell is exactly the old mask product times the ordinary
Möbius order cell. -/
theorem signedVerticalLinePairMixedPrimeCell_eq_mask_mul_positiveLag
    {a b p K m n : ℕ}
    (hm : signedVerticalLineEventMask a b (p * m) =
      signedVerticalLineEventMask a b m)
    (hn : signedVerticalLineEventMask a b (p * n) =
      signedVerticalLineEventMask a b n) :
    signedVerticalLinePairMixedPrimeCell a b p K m n =
      signedVerticalLineEventMask a b m *
        signedVerticalLineEventMask a b n *
          positiveLagPairMixedPrimeCell p K m n := by
  unfold signedVerticalLinePairMixedPrimeCell
    signedVerticalLineMaskedPairIndicator positiveLagPairMixedPrimeCell
  rw [hm, hn]
  ring

/-- **Stable swapped pair cancellation.**  On a prime-stable pair the same two
interior order-crossing shells as in the global Möbius covariance cancel after
swapping coordinates.  Only the standard top escape remains. -/
theorem signedVerticalLinePairMixedPrimeCell_add_swap_eq_topEscape_of_stable
    {a b p K m n : ℕ}
    (hp : p.Prime) (hmn : m < n) (hpn : ¬ p ∣ n)
    (hm : signedVerticalLineEventMask a b (p * m) =
      signedVerticalLineEventMask a b m)
    (hn : signedVerticalLineEventMask a b (p * n) =
      signedVerticalLineEventMask a b n) :
    signedVerticalLinePairMixedPrimeCell a b p K m n +
        signedVerticalLinePairMixedPrimeCell a b p K n m =
      signedVerticalLineEventMask a b m *
        signedVerticalLineEventMask a b n *
          (if n < K ∧ K ≤ p * m then 1 else 0) := by
  rw [signedVerticalLinePairMixedPrimeCell_eq_mask_mul_positiveLag hm hn,
    signedVerticalLinePairMixedPrimeCell_eq_mask_mul_positiveLag hn hm]
  have hcomm :
      signedVerticalLineEventMask a b n * signedVerticalLineEventMask a b m =
        signedVerticalLineEventMask a b m * signedVerticalLineEventMask a b n := by
    ring
  rw [hcomm, ← mul_add,
    positiveLagPairMixedPrimeCell_add_swap_eq_topEscape hp hmn hpn]

/-- Endpoint-membership stability implies mask stability.  Hence mask failure
must come from a genuine active-child boundary at at least one endpoint. -/
theorem signedVerticalLineEventMask_prime_stable_of_endpoint_stable
    {a b p n : ℕ}
    (ha : (p * n ∈ orderedEulerCutActiveChildren a) ↔
      n ∈ orderedEulerCutActiveChildren a)
    (hb : (p * n ∈ orderedEulerCutActiveChildren (b + 1)) ↔
      n ∈ orderedEulerCutActiveChildren (b + 1)) :
    signedVerticalLineEventMask a b (p * n) =
      signedVerticalLineEventMask a b n := by
  simp [signedVerticalLineEventMask, ha, hb]

/-- Therefore every prime-instability of the covariance mask is physically
owned by an endpoint active-set transition, rather than by Möbius signs. -/
theorem signedVerticalLineEventMask_prime_unstable_imp_endpoint_unstable
    {a b p n : ℕ}
    (h : signedVerticalLineEventMask a b (p * n) ≠
      signedVerticalLineEventMask a b n) :
    (¬ ((p * n ∈ orderedEulerCutActiveChildren a) ↔
      n ∈ orderedEulerCutActiveChildren a)) ∨
    (¬ ((p * n ∈ orderedEulerCutActiveChildren (b + 1)) ↔
      n ∈ orderedEulerCutActiveChildren (b + 1))) := by
  by_cases ha : (p * n ∈ orderedEulerCutActiveChildren a) ↔
      n ∈ orderedEulerCutActiveChildren a
  · by_cases hb : (p * n ∈ orderedEulerCutActiveChildren (b + 1)) ↔
        n ∈ orderedEulerCutActiveChildren (b + 1)
    · exact False.elim
        (h (signedVerticalLineEventMask_prime_stable_of_endpoint_stable ha hb))
    · exact Or.inr hb
  · exact Or.inl ha

/-- One prime-family prefix of the physical line-event trajectory. -/
def signedVerticalLinePrimeFamilyPrefix
    (a b p K : ℕ) : ℝ :=
  ∑ c ∈ Finset.range K, signedVerticalLineEventStep a b (p * c)

/-- Pair covariance carried strictly inside one prime-family. -/
def signedVerticalLinePrimeFamilyCovariance
    (a b p K : ℕ) : ℝ :=
  ∑ d ∈ Finset.range K,
    signedVerticalLineEventStep a b (p * d) *
      signedVerticalLinePrimeFamilyPrefix a b p d

/-- On a prime-stable child, adjoining a fresh larger prime reverses the line
event exactly.  The endpoint mask is preserved and the Möbius sign flips. -/
theorem signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable
    {a b p c : ℕ}
    (hp : p.Prime) (hc : c < p)
    (hstable : signedVerticalLineEventMask a b (p * c) =
      signedVerticalLineEventMask a b c) :
    signedVerticalLineEventStep a b (p * c) =
      -signedVerticalLineEventStep a b c := by
  rw [signedVerticalLineEventStep_eq_moebius_mul_mask,
    signedVerticalLineEventStep_eq_moebius_mul_mask,
    realMoebiusStep_prime_mul_of_lt hp hc, hstable]
  ring

/-- A complete stable prime-family reverses total mass and introduces no new
amplitude. -/
theorem signedVerticalLinePrimeFamilyPrefix_eq_neg
    {a b p K : ℕ}
    (hp : p.Prime) (hK : K ≤ p)
    (hstable : ∀ c : ℕ, c < K →
      signedVerticalLineEventMask a b (p * c) =
        signedVerticalLineEventMask a b c) :
    signedVerticalLinePrimeFamilyPrefix a b p K =
      -signedBlockPrefix (signedVerticalLineEventStep a b) K := by
  unfold signedVerticalLinePrimeFamilyPrefix signedBlockPrefix
  have hstep : ∀ c ∈ Finset.range K,
      signedVerticalLineEventStep a b (p * c) =
        -signedVerticalLineEventStep a b c := by
    intro c hcK
    have hcLt : c < K := Finset.mem_range.mp hcK
    exact signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable
      hp (hcLt.trans_le hK) (hstable c hcLt)
  rw [Finset.sum_congr rfl hstep]
  simp

/-- **Covariance descent on a stable fresh-prime family.**  Two sign reversals
cancel in every pair product, so the covariance inside the `p`-family is
*exactly* the same line covariance at the strictly lower prefix.  Any failure
of this descent is therefore mask-instability, already localized above to an
endpoint active-set transition. -/
theorem signedVerticalLinePrimeFamilyCovariance_eq_lower
    {a b p K : ℕ}
    (hp : p.Prime) (hK : K ≤ p)
    (hstable : ∀ c : ℕ, c < K →
      signedVerticalLineEventMask a b (p * c) =
        signedVerticalLineEventMask a b c) :
    signedVerticalLinePrimeFamilyCovariance a b p K =
      signedBlockCrossCovariance (signedVerticalLineEventStep a b) K := by
  unfold signedVerticalLinePrimeFamilyCovariance signedBlockCrossCovariance
  apply Finset.sum_congr rfl
  intro d hdKmem
  have hdK : d < K := Finset.mem_range.mp hdKmem
  have hdp : d < p := hdK.trans_le hK
  rw [signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable
      hp hdp (hstable d hdK),
    signedVerticalLinePrimeFamilyPrefix_eq_neg hp (hdK.le.trans hK)]
  · ring
  · intro c hc
    exact hstable c (hc.trans hdK)

end RHLean.Proof