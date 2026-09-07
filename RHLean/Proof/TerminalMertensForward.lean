import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Proof.TerminalMertensReduction

/-!
# Discharge the terminal forward Mertens criterion

The analytic continuation, identity theorem, and completed-zeta reflection now
construct the one direction of the classical Mertens criterion that the terminal
proof actually uses.  This file plugs that theorem into
`TerminalMertensReduction` and records the resulting unconditional implication
from the projected-renewal estimate to Mathlib's Riemann Hypothesis.

The reverse implication `RH → MertensEnergyBoundedStatement` is not needed by
this forward route and is not asserted here.

The final section records the first global consequence of the fresh-prime
rough-partner boundary law.  Along a single ancestry chain, signed
`Loss - Birth` boundaries telescope to endpoint capacities.  After root
crossing, births vanish edgewise, so the positive loss mass itself telescopes.
This removes ancestry depth as a source of multiplicity, but deliberately makes
no claim about multiplicity across distinct branches.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

namespace TerminalMertensForward

open RHLean.Analysis
open CanonicalGapAncestryQuadraticClosure
open TerminalMertensReduction

/-- The previously external forward Mertens criterion is now constructed from
the repository's Mellin continuation and completed-zeta reflection. -/
theorem mertensForwardCriterion : MertensForwardCriterion := by
  intro hM
  change RiemannHypothesis
  exact riemannHypothesis_of_mertensEnergy hM

/-- **Square-prefix terminal theorem.**  Once the exact square-prefix Mertens
energy estimate is proved, the existing square-to-global bridge and the
unconditional forward Mertens theorem give Mathlib's Riemann Hypothesis.  No
`ClassicalMertensRHCriterion` argument is used. -/
theorem riemannHypothesis_of_squarePrefixEnergy
    (hS : SquarePrefixEnergyBoundedStatement) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_squarePrefixEnergyBounded hS)

/-- Consequently the terminal implication no longer needs a classical
Mertens/RH criterion supplied by the caller. Once the projected-renewal
quadratic estimate is proved, RH follows outright. -/
theorem projectedRenewalQuadraticBounded_imp_riemannHypothesis_unconditional
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ProjectedRenewalQuadraticBoundedStatement Λ →
      RiemannHypothesisStatement :=
  projectedRenewalQuadraticBounded_imp_riemannHypothesis
    hΛ mertensForwardCriterion

end TerminalMertensForward

namespace CanonicalRoughPartnerAncestryBoundary

open RHLean.Analysis

private theorem complex_sum_range_forwardDifference
    (f : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Along any multiplicative ancestry chain, the complete signed finite
boundary `Loss - Birth` telescopes to the difference of endpoint rough-partner
capacities.  No root-crossing or primality hypothesis is needed for this purely
set-theoretic aggregation of the exact one-edge law. -/
theorem squareRootCanonicalRoughFreshBoundary_chain_telescope
    {R n : ℕ} (c p : ℕ → ℕ)
    (hstep : ∀ i, i < n → c (i + 1) = p i * c i) :
    (∑ i ∈ Finset.range n,
        (((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ))) =
      squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
  calc
    (∑ i ∈ Finset.range n,
        (((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ))) =
      ∑ i ∈ Finset.range n,
        (squareRootCanonicalRoughPrimePartnerCount R (c i) -
          squareRootCanonicalRoughPrimePartnerCount R (c (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hedge :=
          squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_loss_sub_birth
            (R := R) (c := c i) (p := p i)
        rw [← hstep i hin] at hedge
        exact hedge.symm
    _ = squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
      simpa using complex_sum_range_forwardDifference
        (fun i => squareRootCanonicalRoughPrimePartnerCount R (c i)) n

/-- On a chain segment whose fresh-prime children have all reached the root,
every birth boundary is empty. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_chain_sum_eq_zero_of_root_reached
    {R n : ℕ} (c p : ℕ → ℕ)
    (hR : 2 ≤ R)
    (hc : ∀ i, i < n → 0 < c i)
    (hp : ∀ i, i < n → (p i).Prime)
    (hfresh : ∀ i, i < n → canonicalLargestPrimeFactor (c i) < p i)
    (hroot : ∀ i, i < n → R ≤ p i * c i) :
    (∑ i ∈ Finset.range n,
        ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  rw [squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_root_reached
    (hR := hR) (hc := hc i hin) (hp := hp i hin)
    (hfresh := hfresh i hin) (hroot := hroot i hin)]
  simp

/-- **Post-root ancestry telescope.**  Along any fresh-prime chain segment for
which every child is at or beyond `R`, the positive sum of loss-boundary
cardinalities is exactly the difference of the endpoint rough-partner
capacities.  Hence ancestry depth contributes no extra post-root multiplicity
on a single branch. -/
theorem squareRootCanonicalRoughFreshLossBoundary_chain_telescope_of_root_reached
    {R n : ℕ} (c p : ℕ → ℕ)
    (hR : 2 ≤ R)
    (hc : ∀ i, i < n → 0 < c i)
    (hp : ∀ i, i < n → (p i).Prime)
    (hfresh : ∀ i, i < n → canonicalLargestPrimeFactor (c i) < p i)
    (hstep : ∀ i, i < n → c (i + 1) = p i * c i)
    (hroot : ∀ i, i < n → R ≤ p i * c i) :
    (∑ i ∈ Finset.range n,
        ((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ)) =
      squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
  calc
    (∑ i ∈ Finset.range n,
        ((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ)) =
      ∑ i ∈ Finset.range n,
        (squareRootCanonicalRoughPrimePartnerCount R (c i) -
          squareRootCanonicalRoughPrimePartnerCount R (c (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hedge :=
          squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_lossBoundary
            (R := R) (c := c i) (p := p i)
            hR (hc i hin) (hp i hin) (hfresh i hin) (hroot i hin)
        rw [← hstep i hin] at hedge
        exact hedge.symm
    _ = squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
      simpa using complex_sum_range_forwardDifference
        (fun i => squareRootCanonicalRoughPrimePartnerCount R (c i)) n

end CanonicalRoughPartnerAncestryBoundary

end RHLean.Proof
