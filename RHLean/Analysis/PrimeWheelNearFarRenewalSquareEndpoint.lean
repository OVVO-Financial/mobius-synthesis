import Mathlib
import RHLean.Analysis.PrimeWheelRecoveredMertensCriterion
import RHLean.Analysis.SquareRootTransportRealization
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# Prime-wheel near/far renewal at square-prefix endpoints

At `X_t = (t + 1)^2 - 1`, split the prime coordinates above `t` into the
near strip `t+1,...,t+8` and the far sector beginning at `t+9`.

The proper-multiple fibre is `M(floor (X_t / p)) - 1`.  This is deliberately
distinct from the existing survivor fibre, which includes the cofactor-one atom.
The doubled prime-comb contribution therefore exposes the exact signed pair
`2 * primeCount - 2 * renewal`.

No PNT or `Li` term is inserted, and no separate absolute estimate for the
renewal is asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

@[simp] theorem squareRootEndpoint_succ_eq_squarePrefixEndpoint (t : ℕ) :
    squareRootEndpoint (t + 1) = squarePrefixEndpoint t := by
  rfl

/-- Prime coordinates in the eight-position strip beginning at `t+1`. -/
def IsPrimeWheelSquareNearPrime (t p : ℕ) : Prop :=
  p.Prime ∧ t + 1 ≤ p ∧ p ≤ t + 8

/-- Prime coordinates in the far sector beginning at `t+9`. -/
def IsPrimeWheelSquareFarPrime (t p : ℕ) : Prop :=
  p.Prime ∧ t + 9 ≤ p ∧ p ≤ squarePrefixEndpoint t

instance instDecidableIsPrimeWheelSquareNearPrime (t p : ℕ) :
    Decidable (IsPrimeWheelSquareNearPrime t p) := by
  unfold IsPrimeWheelSquareNearPrime
  infer_instance

instance instDecidableIsPrimeWheelSquareFarPrime (t p : ℕ) :
    Decidable (IsPrimeWheelSquareFarPrime t p) := by
  unfold IsPrimeWheelSquareFarPrime
  infer_instance

/-- Every prime coordinate in `(t,X_t]` is either near or far. -/
theorem primeWheelSquare_near_or_far
    {t p : ℕ} (hp : p.Prime) (htp : t < p)
    (hpX : p ≤ squarePrefixEndpoint t) :
    IsPrimeWheelSquareNearPrime t p ∨ IsPrimeWheelSquareFarPrime t p := by
  by_cases hnear : p ≤ t + 8
  · left
    exact ⟨hp, by omega, hnear⟩
  · right
    exact ⟨hp, by omega, hpX⟩

/-- The near and far prime sectors are disjoint. -/
theorem primeWheelSquare_near_not_far
    {t p : ℕ} (hnear : IsPrimeWheelSquareNearPrime t p) :
    ¬ IsPrimeWheelSquareFarPrime t p := by
  rcases hnear with ⟨_, _, hnearUpper⟩
  rintro ⟨_, hfarLower, _⟩
  omega

/-- Proper-multiple Möbius fibre at one prime coordinate. -/
def primeWheelSquareProperFiber (t p : ℕ) : ℂ :=
  mertensSummatory (squarePrefixEndpoint t / p) - 1

/-- Every far fibre has the requested lower-scale Mertens normalization. -/
theorem primeWheelSquare_farFiber_eq_mertens_sub_one
    {t p : ℕ} (_hp : IsPrimeWheelSquareFarPrime t p) :
    primeWheelSquareProperFiber t p =
      mertensSummatory (squarePrefixEndpoint t / p) - 1 := by
  rfl

/-- Above the root cutoff, the reciprocal cofactor cutoff is at most `t`. -/
theorem squarePrefixEndpoint_div_le_root
    {t p : ℕ} (hpLower : t + 1 ≤ p) :
    squarePrefixEndpoint t / p ≤ t := by
  have hpPos : 0 < p := by omega
  by_contra hnot
  have hdiv : t + 1 ≤ squarePrefixEndpoint t / p := by omega
  have hmul : (t + 1) * p ≤ squarePrefixEndpoint t :=
    (Nat.le_div_iff_mul_le hpPos).1 hdiv
  have hsquare : (t + 1) * (t + 1) ≤ (t + 1) * p :=
    Nat.mul_le_mul_left (t + 1) hpLower
  have hXlt : squarePrefixEndpoint t < (t + 1) * (t + 1) := by
    rw [show (t + 1) * (t + 1) = (t + 1) ^ 2 by ring]
    exact Nat.sub_lt (by positivity) (by norm_num)
  omega

private theorem mertensSummatory_one : mertensSummatory 1 = 1 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]

/-- A proper fibre above the root has norm at most `t`. -/
theorem norm_primeWheelSquareProperFiber_le_root
    {t p : ℕ} (hpLower : t + 1 ≤ p)
    (hpX : p ≤ squarePrefixEndpoint t) :
    ‖primeWheelSquareProperFiber t p‖ ≤ (t : ℝ) := by
  have hpPos : 0 < p := by omega
  have hB1 : 1 ≤ squarePrefixEndpoint t / p := by
    apply (Nat.le_div_iff_mul_le hpPos).2
    simpa using hpX
  have hM := norm_mertensSummatory_sub_le
    1 (squarePrefixEndpoint t / p) hB1
  rw [mertensSummatory_one] at hM
  have hBt := squarePrefixEndpoint_div_le_root hpLower
  calc
    ‖primeWheelSquareProperFiber t p‖ =
        ‖mertensSummatory (squarePrefixEndpoint t / p) - 1‖ := rfl
    _ ≤ (((squarePrefixEndpoint t / p - 1 : ℕ) : ℝ)) := hM
    _ ≤ (t : ℝ) := by
      exact_mod_cast ((Nat.sub_le _ _).trans hBt)

/-- Near proper-fibre mass before the prime-comb factor `-2`. -/
def primeWheelSquareNearProperFiberMass (t : ℕ) : ℂ :=
  ∑ p ∈ Finset.Icc (t + 1) (t + 8),
    if p.Prime then primeWheelSquareProperFiber t p else 0

/-- The near T-prime comb contribution. -/
def primeWheelSquareNearCombMass (t : ℕ) : ℂ :=
  -2 * primeWheelSquareNearProperFiberMass t

/-- In the survivor range the eight near positions lie below the endpoint. -/
theorem nearStrip_upper_le_squarePrefixEndpoint
    {t : ℕ} (ht : 55 ≤ t) :
    t + 8 ≤ squarePrefixEndpoint t := by
  unfold squarePrefixEndpoint
  have hsq : t + 9 ≤ (t + 1) ^ 2 := by
    nlinarith
  omega

/-- Explicit root-scale estimate for the eight-position near strip. -/
theorem norm_primeWheelSquareNearCombMass_le_sixteen_mul
    (t : ℕ) (ht : 55 ≤ t) :
    ‖primeWheelSquareNearCombMass t‖ ≤ 16 * (t : ℝ) := by
  have hupper : t + 8 ≤ squarePrefixEndpoint t :=
    nearStrip_upper_le_squarePrefixEndpoint ht
  have hsum :
      ‖primeWheelSquareNearProperFiberMass t‖ ≤ 8 * (t : ℝ) := by
    unfold primeWheelSquareNearProperFiberMass
    calc
      ‖∑ p ∈ Finset.Icc (t + 1) (t + 8),
          if p.Prime then primeWheelSquareProperFiber t p else 0‖ ≤
        ∑ p ∈ Finset.Icc (t + 1) (t + 8),
          ‖if p.Prime then primeWheelSquareProperFiber t p else 0‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ _p ∈ Finset.Icc (t + 1) (t + 8), (t : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hprime : p.Prime
        · simp only [hprime, if_true]
          have hpData := Finset.mem_Icc.mp hp
          exact norm_primeWheelSquareProperFiber_le_root
            hpData.1 (hpData.2.trans hupper)
        · simp [hprime]
      _ = 8 * (t : ℝ) := by
        simp
  unfold primeWheelSquareNearCombMass
  calc
    ‖(-2 : ℂ) * primeWheelSquareNearProperFiberMass t‖ =
        2 * ‖primeWheelSquareNearProperFiberMass t‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ 2 * (8 * (t : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 16 * (t : ℝ) := by ring

/-- Indicator-sum form of `pi(X_t)-pi(t)`. -/
def primeWheelSquarePrimeCountMass (t : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
    if p.Prime then 1 else 0

/-- Lower-scale Mertens renewal on all prime coordinates in `(t,X_t]`. -/
def primeWheelSquareRenewal (t : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
    if p.Prime then
      mertensSummatory (squarePrefixEndpoint t / p)
    else 0

/-- Sum of all proper-multiple fibres in `(t,X_t]`. -/
def primeWheelSquareProperFiberMass (t : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
    if p.Prime then primeWheelSquareProperFiber t p else 0

/-- Removing the cofactor-one atom is renewal minus prime count. -/
theorem primeWheelSquareProperFiberMass_eq_renewal_sub_primeCount
    (t : ℕ) :
    primeWheelSquareProperFiberMass t =
      primeWheelSquareRenewal t - primeWheelSquarePrimeCountMass t := by
  unfold primeWheelSquareProperFiberMass primeWheelSquareRenewal
    primeWheelSquarePrimeCountMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp [hprime, primeWheelSquareProperFiber]
  · simp [hprime]

/-- Exact centered prime-count/renewal pair. -/
theorem two_primeCount_sub_two_renewal_eq_neg_two_properFiberMass
    (t : ℕ) :
    2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t =
      -2 * primeWheelSquareProperFiberMass t := by
  rw [primeWheelSquareProperFiberMass_eq_renewal_sub_primeCount]
  ring

/-- Far proper-fibre mass, with threshold exactly `t+9`. -/
def primeWheelSquareFarProperFiberMass (t : ℕ) : ℂ :=
  ∑ p ∈ Finset.Icc (t + 9) (squarePrefixEndpoint t),
    if p.Prime then primeWheelSquareProperFiber t p else 0

/-- Far T-prime comb contribution. -/
def primeWheelSquareFarCombMass (t : ℕ) : ℂ :=
  -2 * primeWheelSquareFarProperFiberMass t

/-- Exact near/far partition of the complete proper-fibre mass. -/
theorem primeWheelSquareProperFiberMass_eq_near_add_far
    (t : ℕ) (ht : 55 ≤ t) :
    primeWheelSquareProperFiberMass t =
      primeWheelSquareNearProperFiberMass t +
        primeWheelSquareFarProperFiberMass t := by
  have hupper : t + 8 ≤ squarePrefixEndpoint t :=
    nearStrip_upper_le_squarePrefixEndpoint ht
  have hset :
      Finset.Ioc t (squarePrefixEndpoint t) =
        Finset.Icc (t + 1) (t + 8) ∪
          Finset.Icc (t + 9) (squarePrefixEndpoint t) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_Ioc.mp hp with ⟨htp, hpX⟩
      by_cases hnearUpper : p ≤ t + 8
      · apply Finset.mem_union.mpr
        left
        exact Finset.mem_Icc.mpr ⟨by omega, hnearUpper⟩
      · apply Finset.mem_union.mpr
        right
        exact Finset.mem_Icc.mpr ⟨by omega, hpX⟩
    · intro hp
      rcases Finset.mem_union.mp hp with hpNear | hpFar
      · rcases Finset.mem_Icc.mp hpNear with ⟨hpLower, hpUpper⟩
        exact Finset.mem_Ioc.mpr ⟨by omega, hpUpper.trans hupper⟩
      · rcases Finset.mem_Icc.mp hpFar with ⟨hpLower, hpUpper⟩
        exact Finset.mem_Ioc.mpr ⟨by omega, hpUpper⟩
  have hdisjoint :
      Disjoint (Finset.Icc (t + 1) (t + 8))
        (Finset.Icc (t + 9) (squarePrefixEndpoint t)) := by
    rw [Finset.disjoint_left]
    intro p hpNear hpFar
    rcases Finset.mem_Icc.mp hpNear with ⟨_, hpNearUpper⟩
    rcases Finset.mem_Icc.mp hpFar with ⟨hpFarLower, _⟩
    omega
  unfold primeWheelSquareProperFiberMass
    primeWheelSquareNearProperFiberMass primeWheelSquareFarProperFiberMass
  rw [hset, Finset.sum_union hdisjoint]

/-- The centered pair is the exact far comb plus the explicit near comb. -/
theorem two_primeCount_sub_two_renewal_eq_near_add_farComb
    (t : ℕ) (ht : 55 ≤ t) :
    2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t =
      primeWheelSquareNearCombMass t + primeWheelSquareFarCombMass t := by
  rw [two_primeCount_sub_two_renewal_eq_neg_two_properFiberMass,
    primeWheelSquareProperFiberMass_eq_near_add_far t ht]
  unfold primeWheelSquareNearCombMass primeWheelSquareFarCombMass
  ring

/-- Root-scale error form of the exact near/far partition. -/
theorem exists_nearError_centeredPair_eq_farComb_add
    (t : ℕ) (ht : 55 ≤ t) :
    ∃ E : ℂ, ‖E‖ ≤ 16 * (t : ℝ) ∧
      2 * primeWheelSquarePrimeCountMass t -
          2 * primeWheelSquareRenewal t =
        primeWheelSquareFarCombMass t + E := by
  refine ⟨primeWheelSquareNearCombMass t,
    norm_primeWheelSquareNearCombMass_le_sixteen_mul t ht, ?_⟩
  rw [two_primeCount_sub_two_renewal_eq_near_add_farComb t ht]
  ring

/-- Prime-count weight above `t` at reciprocal cutoff `X_t/m`. -/
def primeWheelSquarePrimeFiberCountMass (t m : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t / m),
    if p.Prime then 1 else 0

private theorem mertens_eq_bounded_cofactor_sum
    {t p : ℕ} (hpLower : t < p) :
    mertensSummatory (squarePrefixEndpoint t / p) =
      ∑ m ∈ Finset.Icc 1 t,
        if m * p ≤ squarePrefixEndpoint t then canonicalMoebiusWeight m else 0 := by
  classical
  have hpPos : 0 < p := by omega
  have hBt : squarePrefixEndpoint t / p ≤ t :=
    squarePrefixEndpoint_div_le_root (by omega)
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  unfold cofactorMobiusPrefixMass
  have hset :
      (Finset.Icc 1 t).filter
          (fun m => m * p ≤ squarePrefixEndpoint t) =
        Finset.Icc 1 (squarePrefixEndpoint t / p) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm1, hmt⟩, hmul⟩
      exact ⟨hm1, (Nat.le_div_iff_mul_le hpPos).2 hmul⟩
    · rintro ⟨hm1, hmB⟩
      exact ⟨⟨hm1, hmB.trans hBt⟩,
        (Nat.le_div_iff_mul_le hpPos).1 hmB⟩
  rw [← hset, Finset.sum_filter]

/-- Pair form of the renewal before finite Fubini. -/
def primeWheelSquareRenewalPairMass (t : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
    if p.Prime then
      ∑ m ∈ Finset.Icc 1 t,
        if m * p ≤ squarePrefixEndpoint t then canonicalMoebiusWeight m else 0
    else 0

/-- The renewal is exactly its bounded `(m,p)` pair expansion. -/
theorem primeWheelSquareRenewal_eq_pairMass (t : ℕ) :
    primeWheelSquareRenewal t = primeWheelSquareRenewalPairMass t := by
  classical
  unfold primeWheelSquareRenewal primeWheelSquareRenewalPairMass
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp only [hprime, if_true]
    have hpData := Finset.mem_Ioc.mp hp
    exact mertens_eq_bounded_cofactor_sum hpData.1
  · simp [hprime]

private theorem primeIndicator_mul_condition_sum_eq_fiberCount
    {t m : ℕ} (hm : m ∈ Finset.Icc 1 t) :
    (∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
        if p.Prime ∧ m * p ≤ squarePrefixEndpoint t then (1 : ℂ) else 0) =
      primeWheelSquarePrimeFiberCountMass t m := by
  classical
  have hmPos : 0 < m := by
    have := (Finset.mem_Icc.mp hm).1
    omega
  unfold primeWheelSquarePrimeFiberCountMass
  have hset :
      (Finset.Ioc t (squarePrefixEndpoint t)).filter
          (fun p => p.Prime ∧ m * p ≤ squarePrefixEndpoint t) =
        (Finset.Ioc t (squarePrefixEndpoint t / m)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨htp, hpX⟩, hprime, hmul⟩
      have hpB : p ≤ squarePrefixEndpoint t / m := by
        apply (Nat.le_div_iff_mul_le hmPos).2
        simpa [Nat.mul_comm] using hmul
      exact ⟨⟨htp, hpB⟩, hprime⟩
    · rintro ⟨⟨htp, hpB⟩, hprime⟩
      have hpX : p ≤ squarePrefixEndpoint t :=
        hpB.trans (Nat.div_le_self _ _)
      have hmul : m * p ≤ squarePrefixEndpoint t := by
        have h := (Nat.le_div_iff_mul_le hmPos).1 hpB
        simpa [Nat.mul_comm] using h
      exact ⟨⟨htp, hpX⟩, hprime, hmul⟩
  calc
    (∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
        if p.Prime ∧ m * p ≤ squarePrefixEndpoint t then (1 : ℂ) else 0) =
      ∑ p ∈ (Finset.Ioc t (squarePrefixEndpoint t)).filter
          (fun p => p.Prime ∧ m * p ≤ squarePrefixEndpoint t), (1 : ℂ) := by
            rw [Finset.sum_filter]
    _ = ∑ p ∈ (Finset.Ioc t (squarePrefixEndpoint t / m)).filter Nat.Prime,
          (1 : ℂ) := by rw [hset]
    _ = ∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t / m),
          if p.Prime then (1 : ℂ) else 0 := by
            rw [Finset.sum_filter]

/-- Exact Möbius reindexing of the renewal. -/
theorem primeWheelSquareRenewal_eq_mobius_primeFiberCount
    (t : ℕ) :
    primeWheelSquareRenewal t =
      ∑ m ∈ Finset.Icc 1 t,
        canonicalMoebiusWeight m * primeWheelSquarePrimeFiberCountMass t m := by
  classical
  rw [primeWheelSquareRenewal_eq_pairMass]
  unfold primeWheelSquareRenewalPairMass
  calc
    (∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
        if p.Prime then
          ∑ m ∈ Finset.Icc 1 t,
            if m * p ≤ squarePrefixEndpoint t then canonicalMoebiusWeight m else 0
        else 0) =
      ∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
        ∑ m ∈ Finset.Icc 1 t,
          if p.Prime ∧ m * p ≤ squarePrefixEndpoint t then
            canonicalMoebiusWeight m
          else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hprime : p.Prime
            · simp [hprime]
            · simp [hprime]
    _ = ∑ m ∈ Finset.Icc 1 t,
        ∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
          if p.Prime ∧ m * p ≤ squarePrefixEndpoint t then
            canonicalMoebiusWeight m
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.Icc 1 t,
        canonicalMoebiusWeight m *
          (∑ p ∈ Finset.Ioc t (squarePrefixEndpoint t),
            if p.Prime ∧ m * p ≤ squarePrefixEndpoint t then (1 : ℂ) else 0) := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p hp
              by_cases hcond : p.Prime ∧ m * p ≤ squarePrefixEndpoint t
              · simp [hcond]
              · simp [hcond]
    _ = ∑ m ∈ Finset.Icc 1 t,
        canonicalMoebiusWeight m * primeWheelSquarePrimeFiberCountMass t m := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [primeIndicator_mul_condition_sum_eq_fiberCount hm]

/-- Existing square-root transport is the strict-`t+1` part of this renewal. -/
theorem squareRootTransportPrimeFirst_succ_eq_strictRenewal
    (t : ℕ) :
    squareRootTransportPrimeFirst (t + 1) =
      ∑ p ∈ Finset.Ioc (t + 1) (squarePrefixEndpoint t),
        if p.Prime then mertensSummatory (squarePrefixEndpoint t / p) else 0 := by
  have htPos : 0 < t + 1 := by omega
  simpa using squareRootTransportPrimeFirst_eq_mertensTransform (t + 1) htPos

/-- Final algebraic interface for any noncircular pre-T background `A`. -/
theorem squarePrefixMertens_eq_background_add_centeredRenewal_of_properFiber
    (t : ℕ) (A : ℂ)
    (hbackground : squarePrefixMertens t =
      A - 2 * primeWheelSquareProperFiberMass t) :
    squarePrefixMertens t =
      A + 2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t := by
  rw [primeWheelSquareProperFiberMass_eq_renewal_sub_primeCount] at hbackground
  calc
    squarePrefixMertens t =
        A - 2 * (primeWheelSquareRenewal t -
          primeWheelSquarePrimeCountMass t) := hbackground
    _ = A + 2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t := by ring

/-- The same interface with the near strip isolated as an explicit root-scale error. -/
theorem exists_nearError_squarePrefixMertens_eq_background_add_farComb
    (t : ℕ) (ht : 55 ≤ t) (A : ℂ)
    (hbackground : squarePrefixMertens t =
      A - 2 * primeWheelSquareProperFiberMass t) :
    ∃ E : ℂ, ‖E‖ ≤ 16 * (t : ℝ) ∧
      squarePrefixMertens t = A + primeWheelSquareFarCombMass t + E := by
  refine ⟨primeWheelSquareNearCombMass t,
    norm_primeWheelSquareNearCombMass_le_sixteen_mul t ht, ?_⟩
  rw [hbackground, primeWheelSquareProperFiberMass_eq_near_add_far t ht]
  unfold primeWheelSquareNearCombMass primeWheelSquareFarCombMass
  ring

end RHLean.Proof
