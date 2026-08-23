import Mathlib
import RHLean.Analysis.CorrectedConductorHighSectorGram

/-!
# Quantitative cutoff error for the signed high-conductor Gram

The hard conductor family itself is not estimated packetwise.  This file bounds
only the error created when the conductor cutoff is pushed through the complete
Moebius reindexing.

For `k >= 2`, every raw expansion divisor is an actual divisor of the minimal
torus.  Unique factorization makes the ternary expansion-divisor map injective.
The exact upper-Moebius collapse therefore contains at most one expansion layer
at a fixed boundary divisor `d`.  Its expansion weight has norm at most `d`, so
the corresponding upper-Moebius coefficient has norm at most the ambient torus
modulus.  After the common torus normalization, each small boundary divisor has
coefficient at most one.

A divisor boundary is periodic in its upper endpoint.  Reducing to one incomplete
`d`-period and using the existing short-interval estimate gives the deliberately
crude bound `2 d^2`.  Hence all reindexed raw boundary divisors `d <= R` contribute
at most `2 (R+1) R^2`.

Combining this with the already-proved `O(R^4)` low corrected-conductor sector
shows that the cutoff-reindexing error has norm at most `8 (R+1) R^3`.  If
`R^8 <= U`, its squared norm is at most `256 U`.  Consequently the original
`q=1` plus `q>R` signed Gram is bounded by twice the collapsed-core energy plus
`512 U`.  No absolute sum over the high conductors is used anywhere here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

private theorem high_rawExpansionDivisor_factorization
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S) :
    (primeWheelRawExpansionDivisor S e).factorization =
      ∑ p : {p // p ∈ S}, Finsupp.single p.val (e p).val := by
  unfold primeWheelRawExpansionDivisor
  rw [Nat.factorization_prod]
  · apply Fintype.sum_congr
    intro p
    exact (hprime p.val p.property).factorization_pow
  · intro p hp
    exact pow_ne_zero _ (hprime p.val p.property).ne_zero

private theorem high_rawExpansionDivisor_factorization_apply
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S)
    (p : {p // p ∈ S}) :
    (primeWheelRawExpansionDivisor S e).factorization p.val = (e p).val := by
  classical
  rw [high_rawExpansionDivisor_factorization S hprime e]
  simp [Finsupp.single_apply]
  calc
    (∑ x ∈ S.attach, if x.val = p.val then (e x).val else 0) =
        (if p.val = p.val then (e p).val else 0) := by
          apply Finset.sum_eq_single_of_mem p
          · simp
          · intro q _ hqp
            rw [if_neg]
            intro hval
            exact hqp (Subtype.ext hval)
    _ = (e p).val := by simp

private theorem high_rawExpansionDivisor_injective
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    Function.Injective (primeWheelRawExpansionDivisor S) := by
  intro c e hce
  funext p
  apply Fin.ext
  have hfac := congrArg Nat.factorization hce
  have happ := congrArg (fun f : ℕ →₀ ℕ => f p.val) hfac
  change
    (primeWheelRawExpansionDivisor S c).factorization p.val =
      (primeWheelRawExpansionDivisor S e).factorization p.val at happ
  rw [high_rawExpansionDivisor_factorization_apply S hprime c p,
    high_rawExpansionDivisor_factorization_apply S hprime e p] at happ
  exact happ

private theorem norm_localPrimeCombExpansionWeight_le_primePow
    (p : ℕ) (hp : Nat.Prime p) (e : Fin 3) :
    ‖localPrimeCombExpansionWeight e‖ ≤ (p : ℝ) ^ e.val := by
  fin_cases e
  · norm_num [localPrimeCombExpansionWeight]
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    simpa [localPrimeCombExpansionWeight] using hp2
  · have hpNat : 1 ≤ p := hp.one_le
    norm_num [localPrimeCombExpansionWeight]
    omega

private theorem norm_primeWheelRawExpansionWeight_le_divisor
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S) :
    ‖primeWheelRawExpansionWeight S e‖ ≤
      (primeWheelRawExpansionDivisor S e : ℝ) := by
  classical
  unfold primeWheelRawExpansionWeight primeWheelRawExpansionDivisor
  have hcast :
      ((∏ p : {p // p ∈ S}, p.val ^ (e p).val : ℕ) : ℝ) =
        ∏ p : {p // p ∈ S}, (p.val : ℝ) ^ (e p).val := by
    push_cast
    rfl
  rw [hcast, norm_prod]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    exact norm_localPrimeCombExpansionWeight_le_primePow
      p.val (hprime p.val p.property) (e p)

/-- At an actual primorial boundary divisor, the upper-Moebius raw coefficient
has norm at most the torus modulus.  This is the exact expansion-layer collapse
plus unique factorization; it is not a conductorwise Fourier estimate. -/
theorem norm_primorialRawUpperMobiusTransform_le_modulus
    (k d : ℕ) (hk : 2 ≤ k)
    (hdmem : d ∈ (primorialMinimalWheelSystem k).modulus.divisors) :
    ‖primeWheelRawUpperMobiusTransform
        (primorialWheelPrimes k)
        (primorialMinimalWheelSystem k).modulus d‖ ≤
      ((primorialMinimalWheelSystem k).modulus : ℝ) := by
  classical
  let S := primorialWheelPrimes k
  let Q := (primorialMinimalWheelSystem k).modulus
  have hQne : Q ≠ 0 := Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
  have hdvd : d ∣ Q := Nat.dvd_of_mem_divisors hdmem
  have hdiv : ∀ e : PrimeWheelRawExpansionPoint S,
      primeWheelRawExpansionDivisor S e ∣ Q := by
    intro e
    exact primorialRawExpansionDivisor_dvd_minimalModulus k hk e
  rw [primeWheelRawUpperMobiusTransform_eq_exactExpansionDivisor
    S Q d hQne hdpos hdiv]
  have hinj : Function.Injective (primeWheelRawExpansionDivisor S) :=
    high_rawExpansionDivisor_injective S
      (fun p hp => prime_of_mem_primesUpTo hp)
  by_cases hex : ∃ e : PrimeWheelRawExpansionPoint S,
      d = primeWheelRawExpansionDivisor S e
  · rcases hex with ⟨e0, he0⟩
    have hiff : ∀ e : PrimeWheelRawExpansionPoint S,
        d = primeWheelRawExpansionDivisor S e ↔ e = e0 := by
      intro e
      constructor
      · intro he
        apply hinj
        exact he.symm.trans he0
      · intro he
        subst e
        exact he0
    simp_rw [hiff]
    simp
    have hw0 := norm_primeWheelRawExpansionWeight_le_divisor
      S (fun p hp => prime_of_mem_primesUpTo hp) e0
    have hw : ‖primeWheelRawExpansionWeight S e0‖ ≤ (d : ℝ) := by
      simpa [← he0] using hw0
    have hprod : d * (Q / d) = Q := Nat.mul_div_cancel' hdvd
    calc
      ‖primeWheelRawExpansionWeight S e0‖ *
          ((Q / primeWheelRawExpansionDivisor S e0 : ℕ) : ℝ) =
          ‖primeWheelRawExpansionWeight S e0‖ * ((Q / d : ℕ) : ℝ) := by
            rw [← he0]
      _ ≤ (d : ℝ) * ((Q / d : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hw (by positivity)
      _ = (Q : ℝ) := by exact_mod_cast hprod
  · have hnone : ∀ e : PrimeWheelRawExpansionPoint S,
        d ≠ primeWheelRawExpansionDivisor S e := by
      intro e he
      exact hex ⟨e, he⟩
    simp [hnone]

private theorem divisorIntervalBoundary_eq_short_remainder
    {d : ℕ} (hd : 0 < d)
    (a lower upper : ℕ) (hlower : lower ≤ upper) :
    divisorIntervalBoundary d a lower upper =
      divisorIntervalBoundary d a lower
        (lower + ((upper - lower) % d)) := by
  let n := upper - lower
  let r := n % d
  let c := n / d
  have hupper : upper = lower + n := by
    dsimp [n]
    omega
  have hdivmod : n = c * d + r := by
    dsimp [c, r]
    calc
      upper - lower = d * ((upper - lower) / d) + (upper - lower) % d :=
        (Nat.div_add_mod (upper - lower) d).symm
      _ = ((upper - lower) / d) * d + (upper - lower) % d := by
        rw [Nat.mul_comm d ((upper - lower) / d)]
  have hre : lower ≤ lower + r := Nat.le_add_right _ _
  have harg : upper = (lower + r) + c * d := by
    rw [hupper, hdivmod]
    omega
  have hdcd : d ∣ c * d := by
    refine ⟨c, ?_⟩
    exact Nat.mul_comm c d
  calc
    divisorIntervalBoundary d a lower upper =
        divisorIntervalBoundary d a lower ((lower + r) + c * d) := by
          rw [harg]
    _ = divisorIntervalBoundary d a lower (lower + r) :=
      divisorIntervalBoundary_add_multiple
        d a lower (lower + r) (c * d) hd hdcd hre
    _ = divisorIntervalBoundary d a lower
        (lower + ((upper - lower) % d)) := by
          rfl

/-- A divisor boundary is uniformly quadratic in its modulus, independently of
the full prefix length.  Periodicity reduces the endpoint to one incomplete
period before the short-interval bound is used. -/
theorem abs_divisorIntervalBoundary_le_two_mul_sq
    (d a lower upper : ℕ)
    (hd : 0 < d) (hlower : lower ≤ upper) :
    |divisorIntervalBoundary d a lower upper| ≤
      2 * (d : ℤ) ^ 2 := by
  rw [divisorIntervalBoundary_eq_short_remainder hd a lower upper hlower]
  let r := (upper - lower) % d
  have hrlt : r < d := by
    dsimp [r]
    exact Nat.mod_lt _ hd
  exact abs_divisorIntervalBoundary_le_two_mul_sq_of_short
    d a lower (lower + r) d le_rfl
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))
    (by simpa using hrlt)

private def primorialSmallRawBoundaryDivisors
    (k R : ℕ) : Finset ℕ :=
  ((primorialMinimalWheelSystem k).modulus.divisors).filter fun d => d ≤ R

private def highPrimorialRawBoundarySummand
    (k x d : ℕ) : ℂ :=
  primeWheelRawUpperMobiusTransform
      (primorialWheelPrimes k)
      (primorialMinimalWheelSystem k).modulus d *
    (((divisorIntervalBoundary d 0
      (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))

/-- The normalized reindexed raw boundary supported on `d <= R` is `O(R^3)`.
This is the only new absolute summation in the high-sector reduction, and it is
performed after the full conductor Moebius collapse. -/
theorem norm_primorialNormalizedRawSmallBoundary_le
    (k x R : ℕ) (hk : 2 ≤ k)
    (hlower : (primorialMinimalWheelSystem k).lower ≤ x) :
    ‖primorialNormalizedRawSmallBoundary k x R‖ ≤
      2 * (R + 1 : ℝ) * (R : ℝ) ^ 2 := by
  classical
  let Q := (primorialMinimalWheelSystem k).modulus
  have hQpos : 0 < (Q : ℝ) := by
    exact_mod_cast (primorialMinimalWheelSystem k).modulus_pos
  have hsmall :
      primorialRawSmallCollapsedBoundaryPairing k x R =
        ∑ d ∈ primorialSmallRawBoundaryDivisors k R,
          highPrimorialRawBoundarySummand k x d := by
    unfold primorialRawSmallCollapsedBoundaryPairing
      primorialSmallRawBoundaryDivisors highPrimorialRawBoundarySummand
    rw [Finset.sum_filter]
    rfl
  unfold primorialNormalizedRawSmallBoundary
  rw [hsmall, norm_mul]
  have hQinv : ‖((Q : ℂ)⁻¹)‖ = (Q : ℝ)⁻¹ := by simp
  rw [hQinv]
  calc
    (Q : ℝ)⁻¹ *
        ‖∑ d ∈ primorialSmallRawBoundaryDivisors k R,
          highPrimorialRawBoundarySummand k x d‖ ≤
      (Q : ℝ)⁻¹ *
        ∑ d ∈ primorialSmallRawBoundaryDivisors k R,
          ‖highPrimorialRawBoundarySummand k x d‖ := by
            apply mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Q : ℝ)⁻¹ *
        ∑ _d ∈ primorialSmallRawBoundaryDivisors k R,
          ((Q : ℝ) * (2 * (R : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro d hdset
      have hddata := Finset.mem_filter.mp hdset
      have hdmem : d ∈ (primorialMinimalWheelSystem k).modulus.divisors := hddata.1
      have hdR : d ≤ R := hddata.2
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
      have hT := norm_primorialRawUpperMobiusTransform_le_modulus k d hk hdmem
      have hBint := abs_divisorIntervalBoundary_le_two_mul_sq
        d 0 (primorialMinimalWheelSystem k).lower x hdpos hlower
      have hB0 :
          ‖(((divisorIntervalBoundary d 0
            (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ ≤
            2 * (d : ℝ) ^ 2 := by
        exact_mod_cast hBint
      have hpow : (d : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdR) 2
      have hB :
          ‖(((divisorIntervalBoundary d 0
            (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ ≤
            2 * (R : ℝ) ^ 2 :=
        hB0.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      unfold highPrimorialRawBoundarySummand
      rw [norm_mul]
      exact mul_le_mul hT hB (norm_nonneg _) (by positivity)
    _ = ((primorialSmallRawBoundaryDivisors k R).card : ℝ) *
        (2 * (R : ℝ) ^ 2) := by
      have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      field_simp [hQne]
    _ ≤ (R + 1 : ℝ) * (2 * (R : ℝ) ^ 2) := by
      have hsubset :
          primorialSmallRawBoundaryDivisors k R ⊆ Finset.range (R + 1) := by
        intro d hdset
        have hddata := Finset.mem_filter.mp hdset
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hddata.2)
      have hcard0 := Finset.card_le_card hsubset
      have hcardNat : (primorialSmallRawBoundaryDivisors k R).card ≤ R + 1 := by
        simpa using hcard0
      have hcard : ((primorialSmallRawBoundaryDivisors k R).card : ℝ) ≤ R + 1 := by
        exact_mod_cast hcardNat
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * (R + 1 : ℝ) * (R : ℝ) ^ 2 := by ring

/-- The cutoff-reindexing error has the same `O(R^4)` scale as the already
controlled low conductor sector.  No high conductor packet is opened. -/
theorem norm_primorialHighConductorReindexError_le_eight
    (k x R : ℕ) (hk : 2 ≤ k) (hR : 1 ≤ R)
    (hlower : (primorialMinimalWheelSystem k).lower ≤ x)
    (hupper : x ≤ (primorialMinimalWheelSystem k).upper) :
    ‖primorialHighConductorReindexError k x R‖ ≤
      8 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := by
  have hbase := norm_primorialHighConductorReindexError_le k x R hlower hupper
  have hraw := norm_primorialNormalizedRawSmallBoundary_le k x R hk hlower
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hpow : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 3 := by
    calc
      (R : ℝ) ^ 2 = (R : ℝ) ^ 2 * 1 := by ring
      _ ≤ (R : ℝ) ^ 2 * (R : ℝ) :=
        mul_le_mul_of_nonneg_left hRreal (sq_nonneg (R : ℝ))
      _ = (R : ℝ) ^ 3 := by ring
  calc
    ‖primorialHighConductorReindexError k x R‖ ≤
        ‖primorialNormalizedRawSmallBoundary k x R‖ +
          6 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := hbase
    _ ≤ 2 * (R + 1 : ℝ) * (R : ℝ) ^ 2 +
          6 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := by
      exact add_le_add_right hraw _
    _ ≤ 2 * (R + 1 : ℝ) * (R : ℝ) ^ 3 +
          6 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) _
    _ = 8 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := by ring

/-- If the cutoff satisfies `R^8 <= U`, the entire cutoff-reindexing error is
already at square-root scale: its squared norm is at most `256 U`. -/
theorem norm_sq_primorialHighConductorReindexError_le_256_mul
    (k x R U : ℕ) (hk : 2 ≤ k) (hR : 1 ≤ R)
    (hlower : (primorialMinimalWheelSystem k).lower ≤ x)
    (hupper : x ≤ (primorialMinimalWheelSystem k).upper)
    (hscale : R ^ 8 ≤ U) :
    ‖primorialHighConductorReindexError k x R‖ ^ 2 ≤
      256 * (U : ℝ) := by
  have herr := norm_primorialHighConductorReindexError_le_eight
    k x R hk hR hlower hupper
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hsucc : (R : ℝ) + 1 ≤ 2 * (R : ℝ) := by
    linarith
  have hnorm :
      ‖primorialHighConductorReindexError k x R‖ ≤
        16 * (R : ℝ) ^ 4 := by
    calc
      ‖primorialHighConductorReindexError k x R‖ ≤
          8 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := herr
      _ ≤ 8 * (2 * (R : ℝ)) * (R : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsucc (by positivity)) (by positivity)
      _ = 16 * (R : ℝ) ^ 4 := by ring
  have hbound0 : 0 ≤ 16 * (R : ℝ) ^ 4 := by positivity
  have hnorm0 : 0 ≤ ‖primorialHighConductorReindexError k x R‖ := norm_nonneg _
  have hsq :
      ‖primorialHighConductorReindexError k x R‖ ^ 2 ≤
        (16 * (R : ℝ) ^ 4) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hnorm)
      (add_nonneg hbound0 hnorm0)
    nlinarith
  have hpow : (16 * (R : ℝ) ^ 4) ^ 2 = 256 * (R : ℝ) ^ 8 := by ring
  rw [hpow] at hsq
  have hscaleReal : (R : ℝ) ^ 8 ≤ (U : ℝ) := by exact_mod_cast hscale
  exact hsq.trans (mul_le_mul_of_nonneg_left hscaleReal (by positivity))

/-- **High-sector Gram reduction at the eighth-root cutoff.**  Once `R^8 <= U`,
the original signed family `J_1 + sum_{q>R} J_q` has energy at most twice the
energy of the single collapsed high core plus `512 U`.  The high conductors have
not been bounded absolutely. -/
theorem norm_sq_primorialHighConductorWithZeroSector_le_core_add_512_mul
    (k x R U : ℕ) (hk : 2 ≤ k) (hR : 1 ≤ R)
    (hlowerStrict : primorialBlockLower k < x)
    (hupperBlock : x ≤ primorialBlockUpper k)
    (hscale : R ^ 8 ≤ U) :
    ‖primorialHighConductorWithZeroSector k x R‖ ^ 2 ≤
      2 * ‖primorialHighCollapsedCore k x R‖ ^ 2 +
        512 * (U : ℝ) := by
  have hgram := norm_sq_primorialHighConductorWithZeroSector_le_core_add_error
    k hR hlowerStrict hupperBlock
  have hlower : (primorialMinimalWheelSystem k).lower ≤ x := by
    exact Nat.le_of_lt hlowerStrict
  have hupper : x ≤ (primorialMinimalWheelSystem k).upper := by
    simpa using hupperBlock
  have herr := norm_sq_primorialHighConductorReindexError_le_256_mul
    k x R U hk hR hlower hupper hscale
  calc
    ‖primorialHighConductorWithZeroSector k x R‖ ^ 2 ≤
        2 * ‖primorialHighCollapsedCore k x R‖ ^ 2 +
          2 * ‖primorialHighConductorReindexError k x R‖ ^ 2 := hgram
    _ ≤ 2 * ‖primorialHighCollapsedCore k x R‖ ^ 2 +
          2 * (256 * (U : ℝ)) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left herr (by positivity)) _
    _ = 2 * ‖primorialHighCollapsedCore k x R‖ ^ 2 +
          512 * (U : ℝ) := by ring

end RHLean.Analysis
