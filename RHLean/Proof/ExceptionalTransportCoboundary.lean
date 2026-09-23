import RHLean.Proof.TwoWheelQ2GoCompatibility
import RHLean.Proof.StableFarWallRenewalTerminalPrimeCount
import RHLean.Proof.StableFarWallAdaptiveFourCornerBridge

/-!
# Exceptional scalar daughters and the prime-insertion coboundary

The chronological high column already is an exact prime coboundary. Its
potential is the frozen cube at the original cutoff, so completing the prime
chronology leaves the full Mertens value as the terminal potential.

For the exceptional owners `3,5,7` the predecessor cubes are finite, with
products `2,6,30`. They vanish identically after those cutoffs. Consequently,
at `X >= 1470` every scalar Go daughter in this owner set is zero and its
signed recovered daughter is entirely negative high transport. In particular,
the scalar `FF-FT-TF+TT` Gram has only its `TT` term left there.

These statements concern the scalar Go/high-column dictionary. They do not
identify the complete physical incidence packet with a scalar daughter, and
they do not assert an energy estimate or a failure of possible cancellation
inside the high-transport Gram.

The actual scalar daughters at `41^2-1` also give a finite obstruction to the
uniform two-thirds interpolated correlation comparison. This distinguishes a
numerically sufficient closure budget from an arithmetic Gram theorem.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-! ## Post-root adaptive boundary Fubini -/

/-- **The complete adaptive post-root boundary is an intact partner-incidence
column.**  This is the coefficient-weighted finite Fubini form needed after the
pointwise stable-far annihilation: the outer fresh prime `p > R` disappears
from the value, while every parent coefficient and every literal rough partner
is retained. -/
theorem squareRootCanonicalRoughAdaptiveRawBoundaryMass_eq_partnerIncidenceSum_of_rootPrime
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hp : p.Prime) (hRp : R < p) :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a =
      ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        ∑ _q ∈ squareRootCanonicalRoughPrimePartnerSet R c,
          a c * canonicalMoebiusWeight c := by
  unfold squareRootCanonicalRoughAdaptiveRawBoundaryMass
  apply Finset.sum_congr rfl
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, hcrough, _hcchild⟩
  exact
    weighted_squareRootCanonicalRoughFreshPrimeRawBoundary_eq_partnerIncidenceSum_of_rootPrime
      a hR hcpos hp hcrough hRp

/-- **There is no coefficient-mismatch cost at a post-root fresh prime.**  The
child raw response is identically zero for every legal parent, so the mismatch
ledger vanishes for arbitrary inherited coefficients, not just the special
stable-far coefficient field. -/
theorem squareRootCanonicalRoughAdaptiveRawMismatchMass_eq_zero_of_rootPrime
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hp : p.Prime) (hRp : R < p) :
    squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a = 0 := by
  unfold squareRootCanonicalRoughAdaptiveRawMismatchMass
  apply Finset.sum_eq_zero
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, hcrough, _hcchild⟩
  rw [squareRootCanonicalRoughRawCorrelationSummand_mul_freshPrime_eq_zero_of_rootPrime
    hR hcpos hp hcrough hRp]
  simp

/-- **Exact post-root adaptive transposition.**  One post-root prime step is
therefore the next adaptive carrier plus the intact partner-incidence column;
there is no additional mismatch population to estimate. -/
theorem adaptiveRawWeightedMass_eq_next_add_partnerIncidence_of_rootPrime
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hp : p.Prime) (hRp : R < p) :
    squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
      squareRootCanonicalRoughAdaptiveRawWeightedMass R
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a) +
      ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        ∑ _q ∈ squareRootCanonicalRoughPrimePartnerSet R c,
          a c * canonicalMoebiusWeight c := by
  rw [adaptiveRawWeightedMass_eq_next_add_boundary_add_mismatch
      R U a hR hp,
    squareRootCanonicalRoughAdaptiveRawBoundaryMass_eq_partnerIncidenceSum_of_rootPrime
      R U a hR hp hRp,
    squareRootCanonicalRoughAdaptiveRawMismatchMass_eq_zero_of_rootPrime
      R U a hR hp hRp,
    add_zero]

/-- The high-prime column in the exact recovered q-square daughter identity. -/
def q2DaughterHighTransport (q X : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (q - 1) (X / (q * q)),
    frozenPrimeUniverseMass (primesUpTo (p - 1)) ((X / (q * q)) / p)

/-- A finite prime-insertion coboundary, including its terminal potential.
The cutoff is `X/q²` on both potentials; it has not decreased further. -/
theorem q2DaughterHighTransport_eq_go_sub_mertens
    {q X : ℕ} (hcut : q - 1 ≤ X / (q * q)) :
    q2DaughterHighTransport q X =
      squareRootLowPrimeGoWallSquareResidual q X -
        mertensSummatoryInt (X / (q * q)) := by
  have h := mertensDaughter_eq_goDaughter_sub_highOwnerColumn
    (q := q) (X := X) hcut
  change mertensSummatoryInt (X / (q * q)) =
    squareRootLowPrimeGoWallSquareResidual q X - q2DaughterHighTransport q X at h
  linarith

/-- Completing the predecessor cube kills the frozen scalar daughter. -/
theorem q2GoDaughter_eq_zero_of_predecessorCube_complete
    {q X : ℕ} (hq : 2 < q)
    (hfit : primeFaceProduct (primesUpTo (q - 1)) ≤ X / (q * q)) :
    squareRootLowPrimeGoWallSquareResidual q X = 0 := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  apply frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
  · refine ⟨2, mem_primesUpTo_of_prime_le Nat.prime_two ?_⟩
    omega
  · intro p hp
    exact prime_of_mem_primesUpTo hp
  · exact hfit

/-- Beyond predecessor-cube completion the entire scalar daughter is carried
by high transport; the prime telescope retains the Mertens terminal value. -/
theorem q2DaughterHighTransport_eq_neg_mertens_of_predecessorCube_complete
    {q X : ℕ} (hq : 2 < q)
    (hfit : primeFaceProduct (primesUpTo (q - 1)) ≤ X / (q * q))
    (hcut : q - 1 ≤ X / (q * q)) :
    q2DaughterHighTransport q X =
      -mertensSummatoryInt (X / (q * q)) := by
  rw [q2DaughterHighTransport_eq_go_sub_mertens hcut,
    q2GoDaughter_eq_zero_of_predecessorCube_complete hq hfit, zero_sub]

/-- The owner-five predecessor cube fits precisely from daughter cutoff six. -/
theorem q2GoDaughter_five_eq_zero {X : ℕ} (hX : 150 ≤ X) :
    squareRootLowPrimeGoWallSquareResidual 5 X = 0 := by
  apply q2GoDaughter_eq_zero_of_predecessorCube_complete (by norm_num)
  have hprod : primeFaceProduct (primesUpTo (5 - 1)) = 6 := by native_decide
  rw [hprod]
  omega

/-- The owner-seven predecessor cube fits from daughter cutoff thirty. -/
theorem q2GoDaughter_seven_eq_zero {X : ℕ} (hX : 1470 ≤ X) :
    squareRootLowPrimeGoWallSquareResidual 7 X = 0 := by
  apply q2GoDaughter_eq_zero_of_predecessorCube_complete (by norm_num)
  have hprod : primeFaceProduct (primesUpTo (7 - 1)) = 30 := by native_decide
  rw [hprod]
  omega

/-- All three exceptional scalar frozen daughters vanish beyond one explicit
cutoff. This does not assert that their physical incidence operators vanish. -/
theorem exceptionalGoDaughter_eq_zero
    {q X : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) (hX : 1470 ≤ X) :
    squareRootLowPrimeGoWallSquareResidual q X = 0 := by
  rcases hq with rfl | rfl | rfl
  · exact squareRootLowPrimeGoWallSquareResidual_three_eq_zero (by omega)
  · exact q2GoDaughter_five_eq_zero (by omega)
  · exact q2GoDaughter_seven_eq_zero hX

/-- Exact signed exceptional high columns, with no norm taken. -/
theorem exceptionalHighTransport_eq_neg_mertens
    {q X : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) (hX : 1470 ≤ X) :
    q2DaughterHighTransport q X =
      -mertensSummatoryInt (X / (q * q)) := by
  have hcut : q - 1 ≤ X / (q * q) := by
    rcases hq with rfl | rfl | rfl <;> omega
  rw [q2DaughterHighTransport_eq_go_sub_mertens hcut,
    exceptionalGoDaughter_eq_zero hq hX, zero_sub]

/-- Each entry of the *scalar daughter* signed Gram has only its high/high
piece left after the exceptional predecessor cubes complete. This is not a
replacement for the still-unidentified physical packet Gram. -/
theorem exceptionalScalarDaughterGram_eq_highTransportGram
    {q r X : ℕ}
    (hq : q = 3 ∨ q = 5 ∨ q = 7)
    (hr : r = 3 ∨ r = 5 ∨ r = 7) (hX : 1470 ≤ X) :
    (squareRootLowPrimeGoWallSquareResidual q X - q2DaughterHighTransport q X) *
        (squareRootLowPrimeGoWallSquareResidual r X - q2DaughterHighTransport r X) =
      q2DaughterHighTransport q X * q2DaughterHighTransport r X := by
  rw [exceptionalGoDaughter_eq_zero hq hX, exceptionalGoDaughter_eq_zero hr hX]
  ring

/-- Actual scalar daughters at the square endpoint `41²-1`, after all three
predecessor cubes have completed. -/
theorem exceptionalScalarDaughters_at_1680 :
    mertensSummatoryInt (1680 / 9) = -4 ∧
      mertensSummatoryInt (1680 / 25) = -2 ∧
      mertensSummatoryInt (1680 / 49) = -2 := by
  native_decide

/-- The aggregate two-thirds correlation comparison that would suffice for
the restricted numerical budget fails on actual scalar Mertens daughters.
Any successful physical Gram comparison must therefore use more than their
three scalar values. No physical incidence operator is replaced here. -/
theorem exceptionalScalarDaughters_twoThirdsComparison_fails :
    let u3 : ℚ := mertensSummatoryInt (1680 / 9)
    let u5 : ℚ := mertensSummatoryInt (1680 / 25)
    let u7 : ℚ := mertensSummatoryInt (1680 / 49)
    (1 / 3 : ℚ) * (u3 ^ 2 + u5 ^ 2 + u7 ^ 2) +
        (2 / 3 : ℚ) * (1 / 3 + 1 / 5 + 1 / 7) *
          (3 * u3 ^ 2 + 5 * u5 ^ 2 + 7 * u7 ^ 2) <
      (u3 + u5 + u7) ^ 2 := by
  rcases exceptionalScalarDaughters_at_1680 with ⟨h3, h5, h7⟩
  norm_num [h3, h5, h7]

/-- At this actual endpoint, the interpolated scalar Gram comparison requires
correlation allowance at least `175/179`, much larger than two thirds. -/
theorem exceptionalScalarDaughters_at_1680_correlation_threshold (rho : ℚ) :
    let u3 : ℚ := mertensSummatoryInt (1680 / 9)
    let u5 : ℚ := mertensSummatoryInt (1680 / 25)
    let u7 : ℚ := mertensSummatoryInt (1680 / 49)
    ((u3 + u5 + u7) ^ 2 ≤
      (1 - rho) * (u3 ^ 2 + u5 ^ 2 + u7 ^ 2) +
        rho * (1 / 3 + 1 / 5 + 1 / 7) *
          (3 * u3 ^ 2 + 5 * u5 ^ 2 + 7 * u7 ^ 2)) ↔
      (175 : ℚ) / 179 ≤ rho := by
  rcases exceptionalScalarDaughters_at_1680 with ⟨h3, h5, h7⟩
  norm_num [h3, h5, h7]
  constructor <;> intro h <;> linarith

end RHLean.Proof
