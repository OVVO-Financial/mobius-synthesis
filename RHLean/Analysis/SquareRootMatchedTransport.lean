import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm

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

end RHLean.Proof
