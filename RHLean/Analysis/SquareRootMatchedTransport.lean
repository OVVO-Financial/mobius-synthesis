import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm
import RHLean.Proof.ConcreteLiCoreExtensionWeight
import RHLean.Proof.CanonicalGapAncestryBridge

/-!
# Matched born-smooth / transport cancellation

This module returns to the original square-root smooth/transport decomposition
and isolates the large cancellation visible in the `2ab` scale-transfer route.

For square cutoff `R`, the existing smooth mass is split by orientation into

* a positive-orientation part with canonical cofactor `c < q = P+(m)`;
* a born-smooth part with `q <= c`.

The existing high transport term is then rewritten exactly as the lower-scale
Mertens prime transform

`sum_{R < q <= R^2-1, q prime} M(floor((R^2-1)/q))`.

The analytic target is the signed matched difference

`bornSmooth - transport`,

not a separate absolute bound for the transport term.  No analytic estimate is
proved in this file; the RH-scale bound is exposed as an ordinary proposition.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Smooth sources already on the `q <= c` side of the canonical orientation
split at square-root cutoff `R`.  This is the born-smooth part of the original
smooth mass. -/
def squareRootBornSmoothMass (R : ℕ) : ℂ :=
  ∑ m ∈ cumulativeSquarePrefixSet (R - 1),
    if canonicalLargestPrimeFactor m ≤ R ∧
        canonicalLargestPrimeFactor m ≤ canonicalCofactor m then
      canonicalMoebiusWeight m
    else
      0

/-- Smooth sources on the complementary canonical orientation `c < q`. -/
def squareRootPositiveSmoothMass (R : ℕ) : ℂ :=
  ∑ m ∈ cumulativeSquarePrefixSet (R - 1),
    if canonicalLargestPrimeFactor m ≤ R ∧
        canonicalCofactor m < canonicalLargestPrimeFactor m then
      canonicalMoebiusWeight m
    else
      0

/-- Exact orientation split of the original square-root smooth mass. -/
theorem squareRootSmoothMass_eq_positive_add_bornSmooth
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootSmoothMass (R - 1) =
      squareRootPositiveSmoothMass R + squareRootBornSmoothMass R := by
  unfold squareRootSmoothMass squareRootPositiveSmoothMass
    squareRootBornSmoothMass
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  rw [hpred, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hsmooth : canonicalLargestPrimeFactor m ≤ R
  · by_cases horient : canonicalCofactor m < canonicalLargestPrimeFactor m
    · have hnotBorn :
        ¬ canonicalLargestPrimeFactor m ≤ canonicalCofactor m :=
        Nat.not_le.mpr horient
      simp [hsmooth, horient, hnotBorn]
    · have hborn :
        canonicalLargestPrimeFactor m ≤ canonicalCofactor m :=
        Nat.le_of_not_gt horient
      simp [hsmooth, horient, hborn]
  · simp [hsmooth]

/-- Every upper-prime transport fibre is exactly the lower-scale Mertens value
at the reciprocal cutoff. -/
theorem primeDilatedLowCofactorMass_eq_mertensSummatory
    (R q : ℕ) (hR : 0 < R) (hRq : R < q) (hq : 0 < q) :
    primeDilatedLowCofactorMass R q =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q) := by
  rw [primeDilatedLowCofactorMass_eq_cofactorMobiusPrefixMass
    R q hR hRq hq]
  exact cofactorMobiusPrefixMass_eq_mertensSummatory _

/-- Exact lower-triangular Mertens transform of the original high transport
term.  This is the same `T_R` used by the `2ab` scale-transfer analysis. -/
theorem squareRootTransportPrimeFirst_eq_mertensTransform
    (R : ℕ) (hR : 0 < R) :
    squareRootTransportPrimeFirst R =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if q.Prime then
          RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
        else
          0 := by
  unfold squareRootTransportPrimeFirst
  apply Finset.sum_congr rfl
  intro q hqmem
  by_cases hprime : q.Prime
  · have hRq : R < q := (Finset.mem_Ioc.mp hqmem).1
    simp only [hprime, if_true]
    exact primeDilatedLowCofactorMass_eq_mertensSummatory
      R q hR hRq hprime.pos
  · simp [hprime]

/-- The large cancellation object: born-smooth mass minus the original high
transport term, before any norm or triangle inequality is taken. -/
def squareRootMatchedBornSmoothTransport (R : ℕ) : ℂ :=
  squareRootBornSmoothMass R - squareRootTransportPrimeFirst R

/-- The matched object uses exactly the original cofactor-first transport term. -/
theorem squareRootMatchedBornSmoothTransport_eq_bornSmooth_sub_transport
    (R : ℕ) :
    squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothMass R - squareRootTransportCofactorFirst R := by
  unfold squareRootMatchedBornSmoothTransport
  rw [squareRootTransportCofactorFirst_eq_primeFirst]

/-- The same matched object written directly as a born-smooth term minus the
lower-scale Mertens prime transform. -/
theorem squareRootMatchedBornSmoothTransport_eq_mertensTransform
    (R : ℕ) (hR : 0 < R) :
    squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothMass R -
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime then
            RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
          else
            0 := by
  unfold squareRootMatchedBornSmoothTransport
  rw [squareRootTransportPrimeFirst_eq_mertensTransform R hR]

/-- Exact decomposition of `A - T` into the positive-orientation smooth part
plus the matched born-smooth / transport difference. -/
theorem squareRootSmooth_sub_transport_eq_positive_add_matched
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootSmoothMass (R - 1) - squareRootTransportPrimeFirst R =
      squareRootPositiveSmoothMass R +
        squareRootMatchedBornSmoothTransport R := by
  rw [squareRootSmoothMass_eq_positive_add_bornSmooth R hR]
  unfold squareRootMatchedBornSmoothTransport
  ring

/-- The direct RH-scale analytic target for the large born-smooth / transport
cancellation.  This proposition asserts the estimate but does not assume or
prove it. -/
def SquareRootMatchedTransportBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖squareRootMatchedBornSmoothTransport R‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-! ## Exact PNT centering of the cofactor-first transport -/

/-- Exact raw prime-fibre weight attached to a cofactor `c`.

On the positive cofactor support `1 <= c < R`, this is exactly
`pi(floor((R^2-1)/c)) - pi(R)`, represented as a finite prime-indicator sum.
The product-cutoff form is chosen so that the existing cofactor-first transport
unfolds directly against it. -/
def squareRootTransportRawWeight (R c : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
    if q.Prime ∧ c * q ≤ squareRootEndpoint R then 1 else 0

/-- The raw product-cutoff weight is exactly the reciprocal-cutoff prime count,
i.e. `pi(floor((R^2-1)/c)) - pi(R)`, for every positive cofactor. -/
theorem squareRootTransportRawWeight_eq_primeCountDifference
    {R c : ℕ} (hc : 1 ≤ c) :
    squareRootTransportRawWeight R c =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R / c),
        if q.Prime then (1 : ℂ) else 0 := by
  classical
  have hcpos : 0 < c := Nat.zero_lt_of_lt hc
  have hset :
      (Finset.Ioc R (squareRootEndpoint R)).filter
          (fun q => q.Prime ∧ c * q ≤ squareRootEndpoint R) =
        (Finset.Ioc R (squareRootEndpoint R / c)).filter Nat.Prime := by
    ext q
    constructor
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hqmem, hcond⟩
      rcases Finset.mem_Ioc.mp hqmem with ⟨hRq, _hqX⟩
      have hqdiv : q ≤ squareRootEndpoint R / c := by
        apply (Nat.le_div_iff_mul_le hcpos).2
        simpa [Nat.mul_comm] using hcond.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hRq, hqdiv⟩, hcond.1⟩
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hqmem, hprime⟩
      rcases Finset.mem_Ioc.mp hqmem with ⟨hRq, hqdiv⟩
      have hqmul : q * c ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le hcpos).1 hqdiv
      have hmul : c * q ≤ squareRootEndpoint R := by
        simpa [Nat.mul_comm] using hqmul
      have hqX : q ≤ squareRootEndpoint R :=
        hqdiv.trans (Nat.div_le_self _ _)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hRq, hqX⟩, ⟨hprime, hmul⟩⟩
  unfold squareRootTransportRawWeight
  calc
    (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if q.Prime ∧ c * q ≤ squareRootEndpoint R then 1 else 0) =
      ∑ q ∈ (Finset.Ioc R (squareRootEndpoint R)).filter
          (fun q => q.Prime ∧ c * q ≤ squareRootEndpoint R), (1 : ℂ) := by
        rw [Finset.sum_filter]
    _ = ∑ q ∈ (Finset.Ioc R (squareRootEndpoint R / c)).filter Nat.Prime,
          (1 : ℂ) := by rw [hset]
    _ = ∑ q ∈ Finset.Ioc R (squareRootEndpoint R / c),
          if q.Prime then (1 : ℂ) else 0 := by
        rw [Finset.sum_filter]

/-- Discrete logarithmic-integral weight evaluated at the exact integer reciprocal
cutoff `floor((R^2-1)/c)`. -/
def squareRootTransportLiDiscWeight (R c : ℕ) : ℂ :=
  ((RHLean.Analysis.logarithmicIntegralFromTwo
        ((squareRootEndpoint R / c : ℕ) : ℝ) -
      RHLean.Analysis.logarithmicIntegralFromTwo (R : ℝ) : ℝ) : ℂ)

/-- Smooth logarithmic-integral weight with the reciprocal cutoff before flooring. -/
def squareRootTransportLiSmoothWeight (R c : ℕ) : ℂ :=
  ((RHLean.Analysis.logarithmicIntegralFromTwo
        ((squareRootEndpoint R : ℝ) / (c : ℝ)) -
      RHLean.Analysis.logarithmicIntegralFromTwo (R : ℝ) : ℝ) : ℂ)

/-- Exact floor-rounding correction between the discrete and smooth Li weights. -/
def squareRootTransportRoundingWeight (R c : ℕ) : ℂ :=
  squareRootTransportLiDiscWeight R c -
    squareRootTransportLiSmoothWeight R c

/-- The discrete Li weight splits exactly into its smooth part plus floor correction. -/
theorem squareRootTransportLiDiscWeight_eq_smooth_add_rounding
    (R c : ℕ) :
    squareRootTransportLiDiscWeight R c =
      squareRootTransportLiSmoothWeight R c +
        squareRootTransportRoundingWeight R c := by
  unfold squareRootTransportRoundingWeight
  ring

/-- The raw prime count splits pointwise into smooth Li mass, floor correction,
and the remaining prime-counting discrepancy. -/
theorem squareRootTransportRawWeight_eq_smooth_add_rounding_add_error
    (R c : ℕ) :
    squareRootTransportRawWeight R c =
      squareRootTransportLiSmoothWeight R c +
        squareRootTransportRoundingWeight R c +
          (squareRootTransportRawWeight R c -
            squareRootTransportLiDiscWeight R c) := by
  unfold squareRootTransportRoundingWeight
  ring

/-- The existing cofactor-first transport is exactly the Mobius-weighted raw
prime-fibre count. -/
theorem squareRootTransportCofactorFirst_eq_rawWeightSum (R : ℕ) :
    squareRootTransportCofactorFirst R =
      ∑ c ∈ Finset.Ico 1 R,
        canonicalMoebiusWeight c * squareRootTransportRawWeight R c := by
  classical
  unfold squareRootTransportCofactorFirst squareRootTransportRawWeight
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : q.Prime ∧ c * q ≤ squareRootEndpoint R
  · simp [h]
  · simp [h]

/-- Discrete PNT main term using Li at the exact integer reciprocal cutoff. -/
def squareRootTransportDiscretePNTMain (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    canonicalMoebiusWeight c * squareRootTransportLiDiscWeight R c

/-- Smooth PNT main term using Li before reciprocal-cutoff flooring. -/
def squareRootTransportSmoothMain (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    canonicalMoebiusWeight c * squareRootTransportLiSmoothWeight R c

/-- Aggregate floor-rounding correction `Q_R`. -/
def squareRootTransportFloorCorrection (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    canonicalMoebiusWeight c * squareRootTransportRoundingWeight R c

/-- Aggregate exact prime-counting discrepancy `E_R`. -/
def squareRootTransportPNTError (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    canonicalMoebiusWeight c *
      (squareRootTransportRawWeight R c -
        squareRootTransportLiDiscWeight R c)

/-- Exact first centering: `T_R = T_R^disc + E_R`. -/
theorem squareRootTransportCofactorFirst_eq_discretePNT_add_error
    (R : ℕ) :
    squareRootTransportCofactorFirst R =
      squareRootTransportDiscretePNTMain R +
        squareRootTransportPNTError R := by
  rw [squareRootTransportCofactorFirst_eq_rawWeightSum]
  unfold squareRootTransportDiscretePNTMain squareRootTransportPNTError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-- Exact floor split: `T_R^disc = T_R^sm + Q_R`. -/
theorem squareRootTransportDiscretePNTMain_eq_smooth_add_floor
    (R : ℕ) :
    squareRootTransportDiscretePNTMain R =
      squareRootTransportSmoothMain R +
        squareRootTransportFloorCorrection R := by
  unfold squareRootTransportDiscretePNTMain squareRootTransportSmoothMain
    squareRootTransportFloorCorrection squareRootTransportRoundingWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-- Exact three-term transport decomposition:
`T_R = T_R^sm + Q_R + E_R`. -/
theorem squareRootTransportCofactorFirst_eq_smooth_add_floor_add_error
    (R : ℕ) :
    squareRootTransportCofactorFirst R =
      squareRootTransportSmoothMain R +
        squareRootTransportFloorCorrection R +
          squareRootTransportPNTError R := by
  rw [squareRootTransportCofactorFirst_eq_discretePNT_add_error,
    squareRootTransportDiscretePNTMain_eq_smooth_add_floor]

/-- Born-smooth mass paired against the smooth Li transport main term before
any norm is taken. -/
def squareRootMatchedBornSmoothPNTMain (R : ℕ) : ℂ :=
  squareRootBornSmoothMass R - squareRootTransportSmoothMain R

/-- Exact insertion of the PNT decomposition into the matched object:
`bornSmooth - T_R = (bornSmooth - T_R^sm) - Q_R - E_R`. -/
theorem squareRootMatchedBornSmoothTransport_eq_pntMain_sub_floor_sub_error
    (R : ℕ) :
    squareRootMatchedBornSmoothTransport R =
      squareRootMatchedBornSmoothPNTMain R -
        squareRootTransportFloorCorrection R -
          squareRootTransportPNTError R := by
  unfold squareRootMatchedBornSmoothTransport squareRootMatchedBornSmoothPNTMain
  rw [← squareRootTransportCofactorFirst_eq_primeFirst R]
  rw [squareRootTransportCofactorFirst_eq_smooth_add_floor_add_error]
  ring

/-! ## Exact ancestry coordinates for the born-smooth side -/

namespace SquareRootBornSmoothAncestry

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge

/-- The nonroot part of the native canonical source field.  For the concrete
ancestry flow, these are exactly the smooth-oriented sources `q < c`; roots are
the complementary transport-oriented sources. -/
noncomputable def smoothSourceField (B : ℕ) : SourceIndex B → ℤ := by
  classical
  exact fun s => if SmoothOriented s then sourceWeight s else 0

/-- Exact partition of the bounded canonical source field into transport roots
and smooth-oriented nonroots.  This is an identity of signed fields, before any
clock pushforward or norm. -/
theorem weight_eq_root_add_smooth (B : ℕ) :
    (boundedSourceFlow B).weight =
      (boundedSourceFlow B).rootField + smoothSourceField B := by
  funext s
  classical
  by_cases h : SmoothOriented s
  · have hp : sourceParent s = some (parentIndex s h) := smoothSource_has_parent s h
    simp [smoothSourceField, h, boundedSourceFlow, rootField, hp]
  · have hp : sourceParent s = none := (sourceParent_eq_none_iff s).2 h
    simp [smoothSourceField, h, boundedSourceFlow, rootField, hp]

/-- The smooth field is exactly the finite alternating ancestry tail generated
from the transport-oriented root field.  No analytic estimate is used: repeated
largest-core-prime stripping has already been proved nilpotent in the ancestry
bridge. -/
theorem smoothSourceField_eq_finite_root_tail (B : ℕ) :
    smoothSourceField B =
      alternatingPrefix (boundedSourceFlow B).successorOperator
          (boundedSourceFlow B).rootField (B + 1) -
        (boundedSourceFlow B).rootField := by
  have hsplit := weight_eq_root_add_smooth B
  have halt := boundedSource_weight_eq_finite_alternating B
  rw [← halt]
  rw [hsplit]
  abel

/-- Square-prefix clock pushforward of the smooth-oriented ancestry field.  The
ambient bound is the same exact endpoint `R^2 - 1` used by square-root transport. -/
noncomputable def squareRootSmoothAncestryClockMass (R : ℕ) : ℤ :=
  let B := squareRootEndpoint R
  clockPushforward (sourceClock B) (R - 1) (smoothSourceField B)

/-- Exact lower-scale/root-coordinate form of the smooth ancestry mass.  This is
the formal mechanism that moves smooth-oriented sources onto the finite
transport-root ancestry expansion without separating any PNT error terms. -/
theorem squareRootSmoothAncestryClockMass_eq_finite_root_tail (R : ℕ) :
    squareRootSmoothAncestryClockMass R =
      let B := squareRootEndpoint R
      clockPushforward (sourceClock B) (R - 1)
        (alternatingPrefix (boundedSourceFlow B).successorOperator
            (boundedSourceFlow B).rootField (B + 1) -
          (boundedSourceFlow B).rootField) := by
  dsimp [squareRootSmoothAncestryClockMass]
  rw [smoothSourceField_eq_finite_root_tail]

end SquareRootBornSmoothAncestry

/-- The exact PNT split preserves the signed Gram as one object.  No triangle
inequality or separate norm is taken on the floor or prime-counting errors. -/
theorem squareRootMatchedPNTCombinedGram_eq_matchedGram (R : ℕ) :
    ‖squareRootMatchedBornSmoothPNTMain R -
        squareRootTransportFloorCorrection R -
          squareRootTransportPNTError R‖ ^ 2 =
      ‖squareRootMatchedBornSmoothTransport R‖ ^ 2 := by
  rw [squareRootMatchedBornSmoothTransport_eq_pntMain_sub_floor_sub_error]

/-- Open joint analytic target for the exact signed combination above.  This is
a named proposition only; no estimate is asserted or assumed by the exact decomposition. -/
def SquareRootMatchedPNTJointBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖squareRootMatchedBornSmoothPNTMain R -
            squareRootTransportFloorCorrection R -
              squareRootTransportPNTError R‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

end RHLean.Proof
