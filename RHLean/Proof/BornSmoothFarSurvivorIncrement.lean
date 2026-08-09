import Mathlib
import RHLean.Proof.CanonicalSignedParent
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# Born-smooth and far-survivor increment localization

The matched far-survivor bridge localizes the large square-root
born-smooth/transport cancellation to

```text
bornSmooth(R) + farSurvivor(R-1)
```

up to the seven-coordinate near-prime strip.  This module takes the discrete
square-root derivative of that identity.

The key exact point is that the born-smooth prefix has no old-source
reclassification.  If an old source `m < R^2` satisfies the born-smooth
orientation `P+(m) <= c_m`, then necessarily `P+(m) <= R`; increasing the
square-root cutoff from `R` to `R+1` cannot activate it for the first time.
Therefore

```text
bornSmooth(R+1) - bornSmooth(R)
```

is exactly the born-smooth mass of the newly entered square block
`[R^2,(R+1)^2)`.

Combining this with the previous bridge gives an increment-level identity:

```text
Delta matched
  = bornSmoothBlock
    + Delta farSurvivor
    - Delta nearTransport.
```

The last term is unconditionally `O(R)`: each near transport prefix is bounded
by `7R`.  Thus, up to an explicit square-root-scale remainder, the local matched
increment is exactly new born-smooth mass plus the change in the far-upper
survivor tail.  No cancellation estimate is asserted for that remaining signed
pair.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- One summand of the square-root born-smooth prefix at cutoff `R`. -/
def squareRootBornSmoothTerm (R m : ℕ) : ℂ :=
  if canonicalLargestPrimeFactor m ≤ R ∧
      canonicalLargestPrimeFactor m ≤ canonicalCofactor m then
    canonicalMoebiusWeight m
  else
    0

/-- Born-smooth mass carried by the newly entered square block
`[R^2,(R+1)^2)`, evaluated at the new cutoff `R+1`. -/
def squareRootBornSmoothBlockMass (R : ℕ) : ℂ :=
  ∑ m ∈ canonicalSquareBlock R, squareRootBornSmoothTerm (R + 1) m

/-- The existing born-smooth prefix is exactly the finite sum of the explicit
born-smooth term over the complete square prefix. -/
theorem squareRootBornSmoothMass_eq_sum_term (R : ℕ) :
    squareRootBornSmoothMass R =
      ∑ m ∈ cumulativeSquarePrefixSet (R - 1), squareRootBornSmoothTerm R m := by
  rfl

/-- A born-smooth-oriented integer below `(R+1)^2` has largest prime factor at
most `R`.  This is the arithmetic reason old sources cannot become newly
born-smooth when the square-root cutoff advances. -/
theorem canonicalLargestPrimeFactor_le_root_of_bornSmooth
    (R m : ℕ) (hR : 1 ≤ R) (hm : m < (R + 1) ^ 2)
    (horient : canonicalLargestPrimeFactor m ≤ canonicalCofactor m) :
    canonicalLargestPrimeFactor m ≤ R := by
  by_cases hmgt : 1 < m
  · have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
    by_contra hnot
    have hq : R + 1 ≤ canonicalLargestPrimeFactor m := by omega
    have hc : R + 1 ≤ canonicalCofactor m := hq.trans horient
    have hsquare :
        (R + 1) ^ 2 ≤
          canonicalCofactor m * canonicalLargestPrimeFactor m := by
      simpa [pow_two] using Nat.mul_le_mul hc hq
    have hmLower : (R + 1) ^ 2 ≤ m := by
      calc
        (R + 1) ^ 2 ≤
            canonicalCofactor m * canonicalLargestPrimeFactor m := hsquare
        _ = m := hprod
    exact (Nat.not_lt_of_ge hmLower) hm
  · have hq : canonicalLargestPrimeFactor m = 1 := by
      unfold canonicalLargestPrimeFactor
      rw [dif_neg hmgt]
    rw [hq]
    exact hR

/-- On the old prefix below `R^2`, the born-smooth term is unchanged when the
cutoff advances from `R` to `R+1`. -/
theorem squareRootBornSmoothTerm_succ_eq_of_lt_square
    (R m : ℕ) (hR : 1 ≤ R) (hm : m < R ^ 2) :
    squareRootBornSmoothTerm (R + 1) m = squareRootBornSmoothTerm R m := by
  unfold squareRootBornSmoothTerm
  by_cases horient : canonicalLargestPrimeFactor m ≤ canonicalCofactor m
  · have hm' : m < (R + 1) ^ 2 := by
      have hsq : R ^ 2 < (R + 1) ^ 2 := by nlinarith
      exact hm.trans hsq
    have hqR : canonicalLargestPrimeFactor m ≤ R :=
      canonicalLargestPrimeFactor_le_root_of_bornSmooth R m hR hm' horient
    have hqSucc : canonicalLargestPrimeFactor m ≤ R + 1 := by omega
    simp [horient, hqR, hqSucc]
  · simp [horient]

/-- Exact new-block law for born-smooth mass.  No previously resident source is
reclassified into the born-smooth population. -/
theorem squareRootBornSmoothMass_succ_eq_add_blockMass
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootBornSmoothMass (R + 1) =
      squareRootBornSmoothMass R + squareRootBornSmoothBlockMass R := by
  classical
  rw [squareRootBornSmoothMass_eq_sum_term,
    squareRootBornSmoothMass_eq_sum_term]
  unfold cumulativeSquarePrefixSet squareRootBornSmoothBlockMass
    canonicalSquareBlock
  simp only [Nat.add_sub_cancel]
  rw [Nat.sub_add_cancel hR]
  have hle : R ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  calc
    (∑ m ∈ Finset.range ((R + 1) ^ 2),
        squareRootBornSmoothTerm (R + 1) m) =
      (∑ m ∈ Finset.range (R ^ 2),
          squareRootBornSmoothTerm (R + 1) m) +
        ∑ m ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
          squareRootBornSmoothTerm (R + 1) m := by
            exact (Finset.sum_range_add_sum_Ico
              (fun m => squareRootBornSmoothTerm (R + 1) m) hle).symm
    _ =
      (∑ m ∈ Finset.range (R ^ 2), squareRootBornSmoothTerm R m) +
        ∑ m ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
          squareRootBornSmoothTerm (R + 1) m := by
            apply congrArg
              (fun z => z +
                ∑ m ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
                  squareRootBornSmoothTerm (R + 1) m)
            apply Finset.sum_congr rfl
            intro m hmMem
            exact squareRootBornSmoothTerm_succ_eq_of_lt_square
              R m hR (Finset.mem_range.mp hmMem)

/-- Difference form of the exact born-smooth new-block law. -/
theorem squareRootBornSmoothMass_succ_sub_eq_blockMass
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootBornSmoothMass (R + 1) - squareRootBornSmoothMass R =
      squareRootBornSmoothBlockMass R := by
  rw [squareRootBornSmoothMass_succ_eq_add_blockMass R hR]
  ring

/-- Exact discrete derivative of the matched far-survivor bridge.  The hard
increment is localized to the new born-smooth block plus the change of the
far-upper survivor tail; only the bounded near-prime strip remains outside. -/
theorem squareRootMatchedBornSmoothTransport_succ_sub_eq_block_add_farDiff_sub_nearDiff
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootMatchedBornSmoothTransport (R + 1) -
        squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothBlockMass R +
        (survivorSixteenFarUpperPrimeMass R -
          survivorSixteenFarUpperPrimeMass (R - 1)) -
        (squareRootNearPrimeTransport (R + 1) -
          squareRootNearPrimeTransport R) := by
  have hR1 : 1 ≤ R := by omega
  have hRs : 56 ≤ R + 1 := by omega
  rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
      (R + 1) hRs,
    squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
      R hR,
    squareRootBornSmoothMass_succ_eq_add_blockMass R hR1]
  have hpredSucc : R + 1 - 1 = R := by omega
  rw [hpredSucc]
  ring

/-- The change in the seven-coordinate near-prime strip is still elementary
square-root scale. -/
theorem norm_squareRootNearPrimeTransport_succ_sub_le
    (R : ℕ) (hR : 56 ≤ R) :
    ‖squareRootNearPrimeTransport (R + 1) -
        squareRootNearPrimeTransport R‖ ≤
      14 * (R : ℝ) + 7 := by
  have hRs : 56 ≤ R + 1 := by omega
  have hnext := norm_squareRootNearPrimeTransport_le (R + 1) hRs
  have hcur := norm_squareRootNearPrimeTransport_le R hR
  calc
    ‖squareRootNearPrimeTransport (R + 1) -
        squareRootNearPrimeTransport R‖ ≤
      ‖squareRootNearPrimeTransport (R + 1)‖ +
        ‖squareRootNearPrimeTransport R‖ := norm_sub_le _ _
    _ ≤ 7 * ((R + 1 : ℕ) : ℝ) + 7 * (R : ℝ) := add_le_add hnext hcur
    _ = 14 * (R : ℝ) + 7 := by
      push_cast
      ring

/-- Quantitative increment localization.  After removing the new born-smooth
block and the far-survivor increment, the complete matched increment has only
the explicit `14R+7` near-strip remainder. -/
theorem norm_matchedIncrement_sub_bornBlock_add_farDiff_le
    (R : ℕ) (hR : 56 ≤ R) :
    ‖(squareRootMatchedBornSmoothTransport (R + 1) -
          squareRootMatchedBornSmoothTransport R) -
        (squareRootBornSmoothBlockMass R +
          (survivorSixteenFarUpperPrimeMass R -
            survivorSixteenFarUpperPrimeMass (R - 1)))‖ ≤
      14 * (R : ℝ) + 7 := by
  calc
    ‖(squareRootMatchedBornSmoothTransport (R + 1) -
          squareRootMatchedBornSmoothTransport R) -
        (squareRootBornSmoothBlockMass R +
          (survivorSixteenFarUpperPrimeMass R -
            survivorSixteenFarUpperPrimeMass (R - 1)))‖ =
      ‖-(squareRootNearPrimeTransport (R + 1) -
          squareRootNearPrimeTransport R)‖ := by
        rw [squareRootMatchedBornSmoothTransport_succ_sub_eq_block_add_farDiff_sub_nearDiff
          R hR]
        congr 1
        ring
    _ = ‖squareRootNearPrimeTransport (R + 1) -
        squareRootNearPrimeTransport R‖ := by
      simp only [norm_neg]
    _ ≤ 14 * (R : ℝ) + 7 :=
      norm_squareRootNearPrimeTransport_succ_sub_le R hR

end RHLean.Proof
