import RHLean.Proof.LowWheelFrozenSquareResidualRootFloored
import RHLean.Proof.LowWheelFrozenSecondContactRoughPrefix

/-!
# Root-anchor closure onto the historical matching transport

The q^2 parent reassembly leaves one explicit root-anchor column.  This is not a
new residual.  Combining the exact root-floored normal form with the already
compiled saturated source identity and the physical RoughPrefix mate identity
eliminates the moving root-floored column completely.

The result is an exact formula for the *existing* historical matching fixed
transport population:

`T_match = F_{R^-}(X_R) + sum_{q<R} F_{q^-}(R) - 1`.

Thus after an earlier layer and the parent-product Fubini step there is no hidden source
scale, interval-prime cube, or q^2 floor term left in that transport.  No norm
or estimate is taken.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-- The saturated frozen source itself is the global Euler upper-column
boundary minus the exact root-floored q^2 column. -/
theorem lowWheelFrozenSecondContactSourceMass_eq_one_sub_smooth_sub_rootFloored
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
        lowWheelTaggedDowncrossWeight y) =
      (((1 - frozenPrimeUniverseMass (primesUpTo (R - 1))
          (squareRootEndpoint R) -
        lowWheelFrozenSquareResidualRootFlooredColumn R : ℤ) : ℂ)) := by
  have hsource :=
    lowWheelFrozenSecondContactSource_sum_eq_rootBoundary_sub_goOrRoot R hR
  have hcolumn := lowWheelFrozenSecondContactRootFlooredColumn_eq_goOrRoot R
  unfold lowWheelFrozenSquareResidualRootFlooredColumn
  rw [hcolumn]
  simpa [lowWheelTaggedDowncrossWeight] using hsource

/-- **Historical transport closure.**  The actual matching fixed-transport mass
attached to represented source scales is exactly the old-root smooth mass plus
the common predecessor root anchor, minus the empty Euler face. -/
theorem lowWheelFrozenSecondContactMatchingFixedTransportMass_eq_smooth_add_anchor_sub_one
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFrozenSecondContactMatchingFixedTransportMass R =
      (((frozenPrimeUniverseMass (primesUpTo (R - 1))
          (squareRootEndpoint R) +
        lowWheelFrozenSquareResidualRootAnchorColumn R - 1 : ℤ) : ℂ)) := by
  have hcomp :=
    lowWheelFrozenSecondContactSource_add_matchingFixedTransport_eq_squareResidual R
  have hsource :=
    lowWheelFrozenSecondContactSourceMass_eq_one_sub_smooth_sub_rootFloored R hR
  have hresidual :=
    lowWheelFrozenSecondContactSquareResidualMass_eq_anchor_sub_rootFloored R
  calc
    lowWheelFrozenSecondContactMatchingFixedTransportMass R =
      lowWheelFrozenSecondContactSquareResidualMass R -
        (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
          lowWheelTaggedDowncrossWeight y) := by
            linear_combination hcomp
    _ = (((frozenPrimeUniverseMass (primesUpTo (R - 1))
          (squareRootEndpoint R) +
        lowWheelFrozenSquareResidualRootAnchorColumn R - 1 : ℤ) : ℂ)) := by
          rw [hresidual, hsource]
          push_cast
          ring

/-- Equivalent cancellation form: source plus matching transport contains no
moving q^2 root-floor column beyond the already identified square residual. -/
theorem lowWheelFrozenSecondContactSource_sub_anchor_eq_neg_smooth_add_one_sub_rootFloored
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
        lowWheelTaggedDowncrossWeight y) -
      ((lowWheelFrozenSquareResidualRootAnchorColumn R : ℤ) : ℂ) =
    (((1 - frozenPrimeUniverseMass (primesUpTo (R - 1))
        (squareRootEndpoint R) -
      lowWheelFrozenSquareResidualRootFlooredColumn R -
      lowWheelFrozenSquareResidualRootAnchorColumn R : ℤ) : ℂ)) := by
  rw [lowWheelFrozenSecondContactSourceMass_eq_one_sub_smooth_sub_rootFloored R hR]
  push_cast
  ring

end RHLean.Proof
