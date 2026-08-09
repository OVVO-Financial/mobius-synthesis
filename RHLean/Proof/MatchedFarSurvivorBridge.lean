import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Analysis.SquareRootMatchedTransport
import RHLean.Proof.SurvivorFarUpperRigidity

/-!
# Matched transport as born-smooth plus far-upper survivor

The far-upper rigidity theorem identifies every `Lambda = 16` survivor fibre
with prime coordinate at least eight steps above the square root with the
negative reciprocal Mertens fibre.  This module splices that exact theorem back
into the square-root matched born-smooth / transport decomposition.

Write `R = t+1` and `X = R^2-1`.  For `R >= 56`, the full upper-prime transport
splits into

* the seven possible prime coordinates `R < q <= R+7`, and
* the far tail `R+8 <= q <= X`.

The far tail is exactly the negative far-upper survivor at stage `R-1`.
Consequently

```text
transport = nearTransport - farSurvivor
matched   = bornSmooth + farSurvivor - nearTransport.
```

The near transport is elementary: every reciprocal Mertens argument is
strictly below `R`, and there are only seven integer coordinates.  Hence its
norm is at most `7*R` without any prime-distribution input.

Thus the large matched cancellation is localized, up to an already
square-root-scale remainder, to the signed interaction

```text
bornSmooth + farSurvivor.
```

No power-saving hypothesis or RH implication is introduced here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- The bounded root strip omitted by the far-upper rigidity theorem. -/
def squareRootNearPrimeTransport (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc R (R + 7),
    if q.Prime then
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
    else 0

/-- The complementary far-upper reciprocal Mertens transport. -/
def squareRootFarPrimeTransport (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
    if q.Prime then
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
    else 0

/-- For `R >= 56`, the full square-root transport is the disjoint sum of the
seven-coordinate root strip and the far-upper tail. -/
theorem squareRootTransportPrimeFirst_eq_near_add_far
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootTransportPrimeFirst R =
      squareRootNearPrimeTransport R + squareRootFarPrimeTransport R := by
  have hRpos : 0 < R := by omega
  rw [squareRootTransportPrimeFirst_eq_mertensTransform R hRpos]
  unfold squareRootNearPrimeTransport squareRootFarPrimeTransport
  have hsqpos : 1 ≤ R ^ 2 := by nlinarith
  have hend : squareRootEndpoint R + 1 = R ^ 2 := by
    unfold squareRootEndpoint
    exact Nat.sub_add_cancel hsqpos
  have hX : R + 8 ≤ squareRootEndpoint R := by
    nlinarith
  let A := Finset.Ioc R (R + 7)
  let B := Finset.Icc (R + 8) (squareRootEndpoint R)
  have hset : Finset.Ioc R (squareRootEndpoint R) = A ∪ B := by
    ext q
    simp [A, B]
    omega
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro q hqA hqB
    simp [A] at hqA
    simp [B] at hqB
    omega
  rw [hset, Finset.sum_union hdisj]

/-- The merged far-upper rigidity theorem, rewritten on the square-root clock:
the far survivor is exactly the negative far transport. -/
theorem survivorSixteenFarUpperPrimeMass_pred_eq_neg_farTransport
    (R : ℕ) (hR : 56 ≤ R) :
    survivorSixteenFarUpperPrimeMass (R - 1) =
      -squareRootFarPrimeTransport R := by
  have ht : 55 ≤ R - 1 := by omega
  have hR1 : 1 ≤ R := by omega
  have hpred : R - 1 + 9 = R + 8 := by omega
  have hend :
      RHLean.Analysis.squarePrefixEndpoint (R - 1) =
        squareRootEndpoint R := by
    unfold RHLean.Analysis.squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel hR1]
  have h := survivorSixteenFarUpperPrimeMass_eq_neg_mertensTransform
    (R - 1) ht
  unfold squareRootFarPrimeTransport
  simpa [hpred, hend] using h

/-- Exact cross-region recombination: all but the bounded root strip of the
transport is already present with the opposite sign in the far-upper survivor. -/
theorem squareRootTransportPrimeFirst_eq_near_sub_farSurvivor
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootTransportPrimeFirst R =
      squareRootNearPrimeTransport R -
        survivorSixteenFarUpperPrimeMass (R - 1) := by
  rw [squareRootTransportPrimeFirst_eq_near_add_far R hR]
  have hfar := survivorSixteenFarUpperPrimeMass_pred_eq_neg_farTransport R hR
  rw [hfar]
  ring

/-- The matched born-smooth / transport object is, exactly, born-smooth plus
the far-upper survivor, minus only the seven-coordinate root strip. -/
theorem squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothMass R +
        survivorSixteenFarUpperPrimeMass (R - 1) -
          squareRootNearPrimeTransport R := by
  unfold squareRootMatchedBornSmoothTransport
  rw [squareRootTransportPrimeFirst_eq_near_sub_farSurvivor R hR]
  ring

/-- Every reciprocal Mertens value occurring in the seven-coordinate root strip
has norm at most `R`. -/
private theorem norm_nearPrimeTransportTerm_le
    (R q : ℕ) (hR : 0 < R) (hRq : R < q) :
    ‖if q.Prime then
        RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
      else 0‖ ≤ (R : ℝ) := by
  by_cases hqPrime : q.Prime
  · simp only [hqPrime, if_true]
    have hBlt : squareRootEndpoint R / q < R :=
      squareRootEndpoint_div_lt hR hRq hqPrime.pos
    have hm := RHLean.Analysis.norm_mertensSummatory_sub_le
      0 (squareRootEndpoint R / q) (Nat.zero_le _)
    rw [RHLean.Analysis.mertensSummatory_zero, sub_zero] at hm
    have hBle : ((squareRootEndpoint R / q : ℕ) : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast (Nat.le_of_lt hBlt)
    exact hm.trans hBle
  · simp [hqPrime]

/-- The entire omitted root strip is unconditionally square-root scale.  No
prime-density estimate is used: the interval contains only seven integers. -/
theorem norm_squareRootNearPrimeTransport_le
    (R : ℕ) (hR : 56 ≤ R) :
    ‖squareRootNearPrimeTransport R‖ ≤ 7 * (R : ℝ) := by
  have hRpos : 0 < R := by omega
  unfold squareRootNearPrimeTransport
  calc
    ‖∑ q ∈ Finset.Ioc R (R + 7),
        if q.Prime then
          RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
        else 0‖ ≤
      ∑ q ∈ Finset.Ioc R (R + 7),
        ‖if q.Prime then
            RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
          else 0‖ := by
        exact norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Ioc R (R + 7), (R : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact norm_nearPrimeTransportTerm_le R q hRpos
        (Finset.mem_Ioc.mp hq).1
    _ = 7 * (R : ℝ) := by simp

/-- Quantitative localization of the missing cancellation.  The matched object
differs from `bornSmooth + farSurvivor` by at most the elementary `7R` root
strip. -/
theorem norm_matched_sub_bornSmooth_add_farSurvivor_le
    (R : ℕ) (hR : 56 ≤ R) :
    ‖squareRootMatchedBornSmoothTransport R -
        (squareRootBornSmoothMass R +
          survivorSixteenFarUpperPrimeMass (R - 1))‖ ≤
      7 * (R : ℝ) := by
  calc
    ‖squareRootMatchedBornSmoothTransport R -
        (squareRootBornSmoothMass R +
          survivorSixteenFarUpperPrimeMass (R - 1))‖ =
      ‖-squareRootNearPrimeTransport R‖ := by
        rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
          R hR]
        congr 1
        ring
    _ = ‖squareRootNearPrimeTransport R‖ := by simp
    _ ≤ 7 * (R : ℝ) := norm_squareRootNearPrimeTransport_le R hR

end RHLean.Proof
