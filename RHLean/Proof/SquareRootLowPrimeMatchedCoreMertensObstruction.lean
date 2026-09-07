import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchedCoreBound
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling
import RHLean.Analysis.SquareRootPositiveSmoothCollapse

/-!
# Matched core as an exact Mertens-minus-middle obstruction

The structural reductions on the low-prime branch eventually expose the signed
core

`core R = bornSmooth R + farUpperSurvivor (R - 1)`.

The far-survivor bridge also gives

`matched R = core R - nearPrimeTransport R`,

while the original square-prefix identity gives

`M(R^2 - 1) = positiveSmooth R + matched R`.

Therefore the core is exactly

`core R = M(R^2 - 1) - (positiveSmooth R - nearPrimeTransport R)`.

The parenthesized term is named `squareRootLowPrimeMiddleMertensMass` below.
The second half of this file reindexes it to one literal canonical source
carrier:

`1 <= m <= R^2-1`, `P+(m) <= R+7`, `cofactor(m) < P+(m)`.

For every such nontrivial source, the last inequality is exactly the integer
orientation `m < P+(m)^2`, i.e. the canonical form of
`sqrt(m) < P+(m)`.

This module deliberately proves only exact identities and equivalences of bound
statements.  In particular, it does **not** assert that bounding the displayed
difference is equivalent to a standalone classical bound on `M(R^2 - 1)`:
the middle term is correlated with the square-prefix Mertens value and may carry
essential cancellation.

No asymptotic estimate, PNT input, Mertens hypothesis, or RH implication is
introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The exact signed middle term left when the seven-coordinate near-prime strip
is absorbed back into the positive-orientation square-prefix source mass. -/
def squareRootLowPrimeMiddleMertensMass (R : ℕ) : ℂ :=
  squareRootPositiveSmoothMass R - squareRootNearPrimeTransport R

/-- The predecessor square-prefix sample is literally `M(R^2 - 1)`. -/
theorem squarePrefixMertens_pred_eq_mertens_squareRootEndpoint
    (R : ℕ) (hR : 1 ≤ R) :
    RHLean.Analysis.squarePrefixMertens (R - 1) =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) := by
  unfold RHLean.Analysis.squarePrefixMertens
    RHLean.Analysis.squarePrefixEndpoint squareRootEndpoint
  rw [Nat.sub_add_cancel hR]

/-- **Exact obstruction identity in square-prefix coordinates.** -/
theorem squareRootLowPrimeMatchedCore_eq_squarePrefixMertens_sub_middleMertensMass
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootLowPrimeMatchedCore R =
      RHLean.Analysis.squarePrefixMertens (R - 1) -
        squareRootLowPrimeMiddleMertensMass R := by
  unfold squareRootLowPrimeMiddleMertensMass
  rw [squarePrefixMertens_eq_positiveSmooth_add_matched R (by omega)]
  rw [squareRootMatchedBornSmoothTransport_eq_core_sub_near R hR]
  ring

/-- **Exact obstruction identity in literal Mertens coordinates.**

With `X = R^2 - 1`, the matched core is exactly `M(X)` minus the signed middle
population. -/
theorem squareRootLowPrimeMatchedCore_eq_mertens_sub_middleMertensMass
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootLowPrimeMatchedCore R =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        squareRootLowPrimeMiddleMertensMass R := by
  rw [← squarePrefixMertens_pred_eq_mertens_squareRootEndpoint R (by omega)]
  exact squareRootLowPrimeMatchedCore_eq_squarePrefixMertens_sub_middleMertensMass
    R hR

/-- Norm-form Mertens-minus-middle target, with the constant left free. -/
def SquareRootLowPrimeMertensMiddleBound (C : ℝ) (R : ℕ) : Prop :=
  ‖RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
      squareRootLowPrimeMiddleMertensMass R‖ ≤ C * (R : ℝ)

/-- The matched-core norm bound is exactly the Mertens-minus-middle norm bound. -/
theorem squareRootLowPrimeMatchedCoreBound_iff_mertensMiddleBound
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R) :
    SquareRootLowPrimeMatchedCoreBound C R ↔
      SquareRootLowPrimeMertensMiddleBound C R := by
  unfold SquareRootLowPrimeMatchedCoreBound SquareRootLowPrimeMertensMiddleBound
  rw [squareRootLowPrimeMatchedCore_eq_mertens_sub_middleMertensMass R hR]

/-- Real-coordinate form of the same obstruction.  This is the minimal target
actually consumed by the terminal real imbalance. -/
def SquareRootLowPrimeMertensMiddleRealBound (C : ℝ) (R : ℕ) : Prop :=
  |(RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
      squareRootLowPrimeMiddleMertensMass R).re| ≤ C * (R : ℝ)

/-- The minimal matched-core real bound is exactly the corresponding
Mertens-minus-middle real bound. -/
theorem squareRootLowPrimeMatchedCoreRealBound_iff_mertensMiddleRealBound
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R) :
    SquareRootLowPrimeMatchedCoreRealBound C R ↔
      SquareRootLowPrimeMertensMiddleRealBound C R := by
  unfold SquareRootLowPrimeMatchedCoreRealBound
    SquareRootLowPrimeMertensMiddleRealBound
  rw [squareRootLowPrimeMatchedCore_eq_mertens_sub_middleMertensMass R hR]

/-! ## Literal source reindexing of the correlated middle term -/

/-- Positive-orientation sources whose canonical largest prime is in the first
seven coordinates strictly above the root. -/
def squareRootLowPrimeNearPositiveSourceSet (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun m =>
    R < canonicalLargestPrimeFactor m ∧
      canonicalLargestPrimeFactor m ≤ R + 7 ∧
      canonicalCofactor m < canonicalLargestPrimeFactor m

/-- Prime/cofactor coordinates for the same near-root source population. -/
def squareRootLowPrimeNearPositivePairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc R (R + 7)).product
      (Finset.Icc 1 (squareRootEndpoint R))).filter fun qc =>
    qc.1.Prime ∧ qc.2 * qc.1 ≤ squareRootEndpoint R

/-- Native Möbius mass of the near-root positive source population. -/
def squareRootLowPrimeNearPositiveSourceMass (R : ℕ) : ℂ :=
  ∑ m ∈ squareRootLowPrimeNearPositiveSourceSet R,
    canonicalMoebiusWeight m

/-- The same mass in prime/cofactor coordinates. -/
def squareRootLowPrimeNearPositivePairMass (R : ℕ) : ℂ :=
  ∑ qc ∈ squareRootLowPrimeNearPositivePairSet R,
    canonicalMoebiusWeight (qc.2 * qc.1)

private theorem one_lt_of_mem_nearPositiveSourceSet
    {R m : ℕ} (hm : m ∈ squareRootLowPrimeNearPositiveSourceSet R) :
    1 < m := by
  rcases Finset.mem_filter.mp hm with ⟨hmRange, hdata⟩
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmRange).1
  have hcq : canonicalCofactor m < canonicalLargestPrimeFactor m := hdata.2.2
  by_contra hnot
  have hmEq : m = 1 := by omega
  subst m
  simp [canonicalLargestPrimeFactor, canonicalCofactor] at hcq

private theorem nearPositiveSource_to_pair_mem
    {R m : ℕ} (hm : m ∈ squareRootLowPrimeNearPositiveSourceSet R) :
    (canonicalLargestPrimeFactor m, canonicalCofactor m) ∈
      squareRootLowPrimeNearPositivePairSet R := by
  rcases Finset.mem_filter.mp hm with ⟨hmRange, hdata⟩
  rcases hdata with ⟨hRq, hqUpper, hcq⟩
  have hmgt : 1 < m := one_lt_of_mem_nearPositiveSourceSet hm
  have hqPrime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hmgt
  have hprod :
      canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hmgt
  have hcPos : 0 < canonicalCofactor m := by
    by_contra hnot
    have hc0 : canonicalCofactor m = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hc0, zero_mul] at hprod
    omega
  have hcLeM : canonicalCofactor m ≤ m := by
    -- `rw [← hprod]` would rewrite the `m` inside `canonicalCofactor m` as well,
    -- so rewrite forward in a derived inequality instead.
    have hle :
        canonicalCofactor m ≤
          canonicalCofactor m * canonicalLargestPrimeFactor m :=
      Nat.le_mul_of_pos_right _ hqPrime.pos
    rw [hprod] at hle
    exact hle
  have hcX : canonicalCofactor m ≤ squareRootEndpoint R :=
    hcLeM.trans (Finset.mem_Icc.mp hmRange).2
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hRq, hqUpper⟩,
        Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hcPos, hcX⟩⟩
  · exact ⟨hqPrime, by simpa [hprod] using (Finset.mem_Icc.mp hmRange).2⟩

private theorem nearPositiveSource_pair_injective
    {R m n : ℕ}
    (hm : m ∈ squareRootLowPrimeNearPositiveSourceSet R)
    (hn : n ∈ squareRootLowPrimeNearPositiveSourceSet R)
    (hpair :
      (canonicalLargestPrimeFactor m, canonicalCofactor m) =
        (canonicalLargestPrimeFactor n, canonicalCofactor n)) :
    m = n := by
  have hmgt : 1 < m := one_lt_of_mem_nearPositiveSourceSet hm
  have hngt : 1 < n := one_lt_of_mem_nearPositiveSourceSet hn
  have hmprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  have hnprod := canonicalCofactor_mul_largestPrimeFactor hngt
  have hq : canonicalLargestPrimeFactor m = canonicalLargestPrimeFactor n :=
    congrArg Prod.fst hpair
  have hc : canonicalCofactor m = canonicalCofactor n :=
    congrArg Prod.snd hpair
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hmprod.symm
    _ = canonicalCofactor n * canonicalLargestPrimeFactor n := by rw [hc, hq]
    _ = n := hnprod

private theorem nearPositivePair_surjective
    {R : ℕ} (hR : 1 ≤ R) (qc : ℕ × ℕ)
    (hqc : qc ∈ squareRootLowPrimeNearPositivePairSet R) :
    ∃ m ∈ squareRootLowPrimeNearPositiveSourceSet R,
      (canonicalLargestPrimeFactor m, canonicalCofactor m) = qc := by
  rcases Finset.mem_filter.mp hqc with ⟨hbase, hdata⟩
  rcases Finset.mem_product.mp hbase with ⟨hqMem, hcMem⟩
  rcases Finset.mem_Ioc.mp hqMem with ⟨hRq, hqUpper⟩
  rcases Finset.mem_Icc.mp hcMem with ⟨hc1, _hcX⟩
  rcases hdata with ⟨hqPrime, hprodX⟩
  have hdivR : squareRootEndpoint R / qc.1 < R :=
    squareRootEndpoint_div_lt (by omega) hRq hqPrime.pos
  have hcDiv : qc.2 ≤ squareRootEndpoint R / qc.1 :=
    (Nat.le_div_iff_mul_le hqPrime.pos).2 hprodX
  have hcR : qc.2 < R := hcDiv.trans_lt hdivR
  have hcq : qc.2 < qc.1 := hcR.trans hRq
  have hcPos : 0 < qc.2 := by omega
  have hlargest : canonicalLargestPrimeFactor (qc.2 * qc.1) = qc.1 :=
    canonicalLargestPrimeFactor_mul_prime_eq hcPos hcq hqPrime
  have hcofactor : canonicalCofactor (qc.2 * qc.1) = qc.2 :=
    canonicalCofactor_mul_prime_eq hcPos hcq hqPrime
  have hm1 : 1 ≤ qc.2 * qc.1 :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt hcPos) hqPrime.ne_zero)
  refine ⟨qc.2 * qc.1, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨hm1, hprodX⟩
    · simpa only [hlargest, hcofactor] using
        And.intro hRq (And.intro hqUpper hcq)
  · exact Prod.ext hlargest hcofactor

/-- Reindex the first seven post-root positive sources by their unique
largest-prime/cofactor coordinates. -/
theorem squareRootLowPrimeNearPositiveSourceMass_eq_pairMass
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootLowPrimeNearPositiveSourceMass R =
      squareRootLowPrimeNearPositivePairMass R := by
  classical
  unfold squareRootLowPrimeNearPositiveSourceMass
    squareRootLowPrimeNearPositivePairMass
  refine Finset.sum_bij
    (fun m _hm => (canonicalLargestPrimeFactor m, canonicalCofactor m))
    (fun m hm => nearPositiveSource_to_pair_mem hm)
    (fun m hm n hn hmn => nearPositiveSource_pair_injective hm hn hmn)
    (fun qc hcq => by simpa using nearPositivePair_surjective hR qc hcq)
    ?_
  intro m hm
  have hmgt : 1 < m := one_lt_of_mem_nearPositiveSourceSet hm
  rw [canonicalCofactor_mul_largestPrimeFactor hmgt]

/-- One fixed post-root prime fibre is the negative reciprocal Mertens prefix. -/
private theorem nearPositivePrimeFibre_eq_neg_mertens
    {R q : ℕ} (hR : 1 ≤ R) (hqMem : q ∈ Finset.Ioc R (R + 7))
    (hqPrime : q.Prime) :
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        if c * q ≤ squareRootEndpoint R then
          canonicalMoebiusWeight (c * q)
        else 0) =
      -RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q) := by
  have hRq : R < q := (Finset.mem_Ioc.mp hqMem).1
  have hdivR : squareRootEndpoint R / q < R :=
    squareRootEndpoint_div_lt (by omega) hRq hqPrime.pos
  have hset :
      (Finset.Icc 1 (squareRootEndpoint R)).filter
          (fun c => c * q ≤ squareRootEndpoint R) =
        Finset.Icc 1 (squareRootEndpoint R / q) := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_filter.mp hc with ⟨hcRange, hmul⟩
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hcRange).1,
          (Nat.le_div_iff_mul_le hqPrime.pos).2 hmul⟩
    · intro hc
      rcases Finset.mem_Icc.mp hc with ⟨hc1, hcDiv⟩
      have hmul : c * q ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le hqPrime.pos).1 hcDiv
      have hcX : c ≤ squareRootEndpoint R :=
        hcDiv.trans (Nat.div_le_self _ _)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hc1, hcX⟩, hmul⟩
  rw [← Finset.sum_filter, hset]
  calc
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        canonicalMoebiusWeight (c * q)) =
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        -canonicalMoebiusWeight c := by
          apply Finset.sum_congr rfl
          intro c hc
          rcases Finset.mem_Icc.mp hc with ⟨hc1, hcUpper⟩
          have hcR : c < R := hcUpper.trans_lt hdivR
          have hcq : c < q := hcR.trans hRq
          exact canonicalMoebiusWeight_mul_prime_eq_neg (by omega) hcq hqPrime
    _ = -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        canonicalMoebiusWeight c := by simp
    _ = -cofactorMobiusPrefixMass (squareRootEndpoint R / q) := by rfl
    _ = -RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q) := by
      rw [cofactorMobiusPrefixMass_eq_mertensSummatory]

/-- The complete post-root pair mass is exactly the negative seven-coordinate
near-prime transport. -/
theorem squareRootLowPrimeNearPositivePairMass_eq_neg_nearPrimeTransport
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootLowPrimeNearPositivePairMass R =
      -squareRootNearPrimeTransport R := by
  classical
  unfold squareRootLowPrimeNearPositivePairMass
    squareRootLowPrimeNearPositivePairSet
  rw [Finset.sum_filter]
  calc
    (∑ qc ∈ (Finset.Ioc R (R + 7)).product
          (Finset.Icc 1 (squareRootEndpoint R)),
        if qc.1.Prime ∧ qc.2 * qc.1 ≤ squareRootEndpoint R then
          canonicalMoebiusWeight (qc.2 * qc.1)
        else 0) =
      ∑ q ∈ Finset.Ioc R (R + 7),
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          if q.Prime ∧ c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight (c * q)
          else 0 := by
            simpa only using
              (Finset.sum_product
                (s := Finset.Ioc R (R + 7))
                (t := Finset.Icc 1 (squareRootEndpoint R))
                (f := fun qc : ℕ × ℕ =>
                  if qc.1.Prime ∧ qc.2 * qc.1 ≤ squareRootEndpoint R then
                    canonicalMoebiusWeight (qc.2 * qc.1)
                  else 0))
    _ = ∑ q ∈ Finset.Ioc R (R + 7),
        if q.Prime then
          -RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
        else 0 := by
          apply Finset.sum_congr rfl
          intro q hqMem
          by_cases hqPrime : q.Prime
          · simp only [hqPrime, true_and, if_true]
            exact nearPositivePrimeFibre_eq_neg_mertens hR hqMem hqPrime
          · simp [hqPrime]
    _ = -squareRootNearPrimeTransport R := by
      unfold squareRootNearPrimeTransport
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q _hqMem
      by_cases hqPrime : q.Prime <;> simp [hqPrime]

/-- Source form of the same near-root identity. -/
theorem squareRootLowPrimeNearPositiveSourceMass_eq_neg_nearPrimeTransport
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootLowPrimeNearPositiveSourceMass R =
      -squareRootNearPrimeTransport R := by
  rw [squareRootLowPrimeNearPositiveSourceMass_eq_pairMass R hR,
    squareRootLowPrimeNearPositivePairMass_eq_neg_nearPrimeTransport R hR]

/-- Single canonical source carrier for the complete middle term. -/
def squareRootLowPrimeMiddleSourceSet (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun m =>
    canonicalLargestPrimeFactor m ≤ R + 7 ∧
      canonicalCofactor m < canonicalLargestPrimeFactor m

/-- Möbius mass of the single middle source carrier. -/
def squareRootLowPrimeMiddleSourceMass (R : ℕ) : ℂ :=
  ∑ m ∈ squareRootLowPrimeMiddleSourceSet R,
    canonicalMoebiusWeight m

/-- The middle source carrier is exactly the disjoint union of the old positive
smooth source and the first seven post-root largest-prime fibres. -/
theorem squareRootLowPrimeMiddleSourceSet_eq_positive_union_near
    (R : ℕ) :
    squareRootLowPrimeMiddleSourceSet R =
      squareRootPositiveSmoothSourceSet R ∪
        squareRootLowPrimeNearPositiveSourceSet R := by
  ext m
  constructor
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hmRange, hdata⟩
    rcases hdata with ⟨hqUpper, hcq⟩
    by_cases hqR : canonicalLargestPrimeFactor m ≤ R
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hmRange, ⟨hqR, hcq⟩⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr
          ⟨hmRange, ⟨Nat.lt_of_not_ge hqR, hqUpper, hcq⟩⟩
  · intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases Finset.mem_filter.mp hm with ⟨hmRange, hdata⟩
      exact Finset.mem_filter.mpr
        ⟨hmRange, ⟨hdata.1.trans (by omega : R ≤ R + 7), hdata.2⟩⟩
    · rcases Finset.mem_filter.mp hm with ⟨hmRange, hdata⟩
      exact Finset.mem_filter.mpr ⟨hmRange, ⟨hdata.2.1, hdata.2.2⟩⟩

/-- The two source populations are disjoint by their largest-prime cutoff. -/
theorem squareRootPositiveSmoothSourceSet_disjoint_nearPositive
    (R : ℕ) :
    Disjoint
      (squareRootPositiveSmoothSourceSet R)
      (squareRootLowPrimeNearPositiveSourceSet R) := by
  rw [Finset.disjoint_left]
  intro m hmPos hmNear
  have hqR := (Finset.mem_filter.mp hmPos).2.1
  have hRq := (Finset.mem_filter.mp hmNear).2.1
  omega

/-- **Literal source reindexing of the obstruction term.** -/
theorem squareRootLowPrimeMiddleSourceMass_eq_middleMertensMass
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootLowPrimeMiddleSourceMass R =
      squareRootLowPrimeMiddleMertensMass R := by
  unfold squareRootLowPrimeMiddleSourceMass
  rw [squareRootLowPrimeMiddleSourceSet_eq_positive_union_near R]
  rw [Finset.sum_union
    (squareRootPositiveSmoothSourceSet_disjoint_nearPositive R)]
  change squareRootPositiveSmoothSourceMass R +
      squareRootLowPrimeNearPositiveSourceMass R =
    squareRootLowPrimeMiddleMertensMass R
  rw [← squareRootPositiveSmoothMass_eq_sourceMass R hR,
    squareRootLowPrimeNearPositiveSourceMass_eq_neg_nearPrimeTransport R hR]
  unfold squareRootLowPrimeMiddleMertensMass
  ring

/-- **Final literal source form.**  The hard core is `M(R^2-1)` minus the
Möbius mass of the positive-orientation source integers with largest prime at
most `R+7`. -/
theorem squareRootLowPrimeMatchedCore_eq_mertens_sub_middleSourceMass
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootLowPrimeMatchedCore R =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        squareRootLowPrimeMiddleSourceMass R := by
  rw [squareRootLowPrimeMatchedCore_eq_mertens_sub_middleMertensMass R hR]
  rw [← squareRootLowPrimeMiddleSourceMass_eq_middleMertensMass R (by omega)]

/-- On every middle source, the canonical orientation is the exact integer
square-root inequality `m < P+(m)^2`. -/
theorem squareRootLowPrimeMiddleSource_lt_largestPrime_sq
    {R m : ℕ} (hm : m ∈ squareRootLowPrimeMiddleSourceSet R) :
    m < (canonicalLargestPrimeFactor m) ^ 2 := by
  rcases Finset.mem_filter.mp hm with ⟨hmRange, hdata⟩
  have hcq := hdata.2
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmRange).1
  have hmgt : 1 < m := by
    by_contra hnot
    have hmEq : m = 1 := by omega
    subst m
    simp [canonicalLargestPrimeFactor, canonicalCofactor] at hcq
  have hqPrime := canonicalLargestPrimeFactor_prime hmgt
  have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hprod.symm
    _ < canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m :=
      Nat.mul_lt_mul_of_pos_right hcq hqPrime.pos
    _ = (canonicalLargestPrimeFactor m) ^ 2 := by ring

end RHLean.Proof