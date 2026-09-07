import Mathlib
import RHLean.Arithmetic.BooleanCubeCancellation
import RHLean.Arithmetic.PrimeFaceMoebius
import RHLean.Proof.LifetimeRunCancellation
import RHLean.Proof.LowWheelCanonicalOrientedRunFibres

/-!
# Signed prefix event lifetimes

The physical cutoff grows through nested integer prefixes.  The oriented Euler
frontier at a later square root is therefore not a fresh signed sample: it is
the current residual after earlier arrivals and all Euler completions that have
already occurred.

This file puts that bookkeeping on the exact common physical-state carrier
already used by `LowWheelCanonicalOrientedRunFibres`, and then telescopes the
run one square-root step at a time using the existing trajectory theorem from
`LifetimeRunCancellation`.

For a run from root `a` to root `b + 1`:

* the upper endpoint fibre is the arrival-side event mass;
* the lower endpoint fibre is the completion-side event mass;
* their difference is the event lifetime residual;
* one-step event residuals telescope exactly over `a, ..., b`;
* summing those residuals is exactly `canonicalOrientedRunDifference a b`.

At the elementary Euler-pair level, a parent face `t` arrives when its prime
product enters the growing prefix and its fresh-`p` child completes at
`p * primeFaceProduct t`.  During the interval between those two times only the
parent sign is exposed.  Once the child has entered, the two Boolean-cube signs
cancel exactly and leave zero residual lifetime.

The final declaration `SignedPrefixLifetimeEnergyBound` is deliberately only a
`Prop`.  It is the RH-scale energy estimate on this lifetime coordinate, with an
existential constant and no assumed numerical value.  The theorem at the end
shows that it is exactly the already-exposed canonical oriented-run energy seam;
no new axiom or estimate is introduced here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Zero-extended signed mass of one physical state at one square-root endpoint.
This is the atomic endpoint event used in the lifetime bookkeeping. -/
def signedPrefixEndpointEventMass
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x

/-- Arrival-side event mass across the run: the upper endpoint ledger, extended
to the common run carrier. -/
def signedPrefixRunArrivalMass (a b : ℕ) : ℂ :=
  ∑ x ∈ canonicalOrientedRunStateCarrier a b,
    signedPrefixEndpointEventMass (b + 1) x

/-- Completion-side event mass across the run: the lower endpoint ledger,
extended to the same common run carrier. -/
def signedPrefixRunCompletionMass (a b : ℕ) : ℂ :=
  ∑ x ∈ canonicalOrientedRunStateCarrier a b,
    signedPrefixEndpointEventMass a x

/-- Net signed lifetime contribution of one physical state across the run. -/
def signedPrefixEventLifetimeResidual
    (a b : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  signedPrefixEndpointEventMass (b + 1) x -
    signedPrefixEndpointEventMass a x

/-- Total signed lifetime residual over the common physical-state carrier. -/
def signedPrefixLifetimeResidual (a b : ℕ) : ℂ :=
  signedPrefixRunArrivalMass a b - signedPrefixRunCompletionMass a b

/-- The arrival-side event mass is exactly the upper oriented Euler ledger. -/
theorem signedPrefixRunArrivalMass_eq_upperLedger (a b : ℕ) :
    signedPrefixRunArrivalMass a b =
      lowWheelCanonicalDowncrossOrientedLedger (b + 1) := by
  unfold signedPrefixRunArrivalMass signedPrefixEndpointEventMass
  symm
  exact lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_right a b

/-- The completion-side event mass is exactly the lower oriented Euler ledger. -/
theorem signedPrefixRunCompletionMass_eq_lowerLedger (a b : ℕ) :
    signedPrefixRunCompletionMass a b =
      lowWheelCanonicalDowncrossOrientedLedger a := by
  unfold signedPrefixRunCompletionMass signedPrefixEndpointEventMass
  symm
  exact lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_left a b

/-- **Event-level arrival/completion decomposition.**  The oriented run change
is exactly arrivals minus completions on one common physical-state carrier. -/
theorem canonicalOrientedRunDifference_eq_arrivals_sub_completions
    (a b : ℕ) :
    canonicalOrientedRunDifference a b =
      signedPrefixRunArrivalMass a b - signedPrefixRunCompletionMass a b := by
  rw [signedPrefixRunArrivalMass_eq_upperLedger,
    signedPrefixRunCompletionMass_eq_lowerLedger]
  rfl

/-- The same identity resolved state-by-state.  No norm or triangle inequality
has been applied. -/
theorem canonicalOrientedRunDifference_eq_sum_eventLifetimeResiduals
    (a b : ℕ) :
    canonicalOrientedRunDifference a b =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        signedPrefixEventLifetimeResidual a b x := by
  simpa [signedPrefixEventLifetimeResidual, signedPrefixEndpointEventMass] using
    canonicalOrientedRunDifference_eq_sum_frozenStateFibreDifferences a b

/-- The total lifetime residual is literally the canonical oriented run
difference.  Thus the lifetime coordinate is an exact reindexing, not a new
analytic assumption. -/
theorem signedPrefixLifetimeResidual_eq_canonicalOrientedRunDifference
    (a b : ℕ) :
    signedPrefixLifetimeResidual a b = canonicalOrientedRunDifference a b := by
  rw [canonicalOrientedRunDifference_eq_arrivals_sub_completions]
  rfl

/-! ## Sequential prefix events -/

/-- Arrival mass on one adjacent square-root step `R -> R+1`. -/
def signedPrefixStepArrivalMass (R : ℕ) : ℂ :=
  signedPrefixRunArrivalMass R R

/-- Completion mass on one adjacent square-root step `R -> R+1`. -/
def signedPrefixStepCompletionMass (R : ℕ) : ℂ :=
  signedPrefixRunCompletionMass R R

/-- Net event increment on one adjacent square-root step. -/
def signedPrefixStepIncrement (R : ℕ) : ℂ :=
  signedPrefixStepArrivalMass R - signedPrefixStepCompletionMass R

/-- One step of the growing-prefix process is exactly the increment of the
oriented Euler ledger. -/
theorem signedPrefixStepIncrement_eq_orientedLedgerIncrement (R : ℕ) :
    signedPrefixStepIncrement R =
      lowWheelCanonicalDowncrossOrientedLedger (R + 1) -
        lowWheelCanonicalDowncrossOrientedLedger R := by
  unfold signedPrefixStepIncrement signedPrefixStepArrivalMass
    signedPrefixStepCompletionMass
  rw [signedPrefixRunArrivalMass_eq_upperLedger,
    signedPrefixRunCompletionMass_eq_lowerLedger]

/-- **Sequential event telescope.**  The current boundary is a larger-prefix
state: the whole oriented run difference is the sum of the consecutive prefix
event increments, not a comparison of unrelated boundary samples. -/
theorem canonicalOrientedRunDifference_eq_sum_signedPrefixStepIncrements
    {a b : ℕ} (hab : a ≤ b + 1) :
    canonicalOrientedRunDifference a b =
      ∑ R ∈ Finset.Ico a (b + 1), signedPrefixStepIncrement R := by
  have htel := sum_increment_Ico
    (fun R => lowWheelCanonicalDowncrossOrientedLedger R) hab
  calc
    canonicalOrientedRunDifference a b =
        lowWheelCanonicalDowncrossOrientedLedger (b + 1) -
          lowWheelCanonicalDowncrossOrientedLedger a := rfl
    _ = ∑ R ∈ Finset.Ico a (b + 1),
        (lowWheelCanonicalDowncrossOrientedLedger (R + 1) -
          lowWheelCanonicalDowncrossOrientedLedger R) := htel.symm
    _ = ∑ R ∈ Finset.Ico a (b + 1), signedPrefixStepIncrement R := by
      apply Finset.sum_congr rfl
      intro R _hR
      exact (signedPrefixStepIncrement_eq_orientedLedgerIncrement R).symm

/-- The sequential telescope written literally as arrival events minus
completion events at each growing-prefix step. -/
theorem canonicalOrientedRunDifference_eq_sum_stepArrivals_sub_completions
    {a b : ℕ} (hab : a ≤ b + 1) :
    canonicalOrientedRunDifference a b =
      ∑ R ∈ Finset.Ico a (b + 1),
        (signedPrefixStepArrivalMass R - signedPrefixStepCompletionMass R) := by
  simpa [signedPrefixStepIncrement] using
    canonicalOrientedRunDifference_eq_sum_signedPrefixStepIncrements hab

/-! ## One completed Euler pair -/

/-- Prefix time at which an old Boolean face first enters the physical cutoff. -/
def signedPrefixEulerArrivalTime (t : Finset ℕ) : ℕ :=
  primeFaceProduct t

/-- Prefix time at which the fresh-`p` child of an old face enters. -/
def signedPrefixEulerCompletionTime (p : ℕ) (t : Finset ℕ) : ℕ :=
  p * primeFaceProduct t

/-- Signed residual of one parent/child Euler event at prefix cutoff `X`.
The child is represented by its actual Boolean-cube sign, so freshness is used
only when proving cancellation. -/
def signedPrefixEulerPairResidualAt
    (X p : ℕ) (t : Finset ℕ) : ℤ :=
  (if signedPrefixEulerArrivalTime t ≤ X then booleanCubeSign t else 0) +
    (if signedPrefixEulerCompletionTime p t ≤ X then
      booleanCubeSign (insert p t) else 0)

/-- During the exposed lifetime, after the parent has arrived but before its
fresh child completes, the event residual is exactly the parent sign. -/
theorem signedPrefixEulerPairResidualAt_eq_parent_of_exposed
    {X p : ℕ} {t : Finset ℕ}
    (hparent : signedPrefixEulerArrivalTime t ≤ X)
    (hchild : X < signedPrefixEulerCompletionTime p t) :
    signedPrefixEulerPairResidualAt X p t = booleanCubeSign t := by
  have hnotChild : ¬ signedPrefixEulerCompletionTime p t ≤ X :=
    Nat.not_le.mpr hchild
  simp [signedPrefixEulerPairResidualAt, hparent, hnotChild]

/-- A fresh Euler child has the opposite Boolean-cube sign of its parent. -/
theorem signedPrefixFreshEulerChildSign
    {p : ℕ} {t : Finset ℕ} (hpFresh : p ∉ t) :
    booleanCubeSign (insert p t) = -booleanCubeSign t := by
  unfold booleanCubeSign
  rw [Finset.card_insert_of_notMem hpFresh, pow_succ]
  ring

/-- **Completed Euler pairs leave no residual lifetime.**

Once the fresh-`p` child has entered the growing prefix, the parent is already
present as well and the two opposite Boolean-cube signs cancel pointwise. -/
theorem signedPrefixEulerPairResidualAt_eq_zero_of_completed
    {X p : ℕ} {t : Finset ℕ}
    (hpPrime : p.Prime) (hpFresh : p ∉ t)
    (hcomplete : signedPrefixEulerCompletionTime p t ≤ X) :
    signedPrefixEulerPairResidualAt X p t = 0 := by
  have hparentLeCompletion :
      signedPrefixEulerArrivalTime t ≤ signedPrefixEulerCompletionTime p t := by
    unfold signedPrefixEulerArrivalTime signedPrefixEulerCompletionTime
    have hpOne : 1 ≤ p := hpPrime.one_le
    have hmul := Nat.mul_le_mul_right (primeFaceProduct t) hpOne
    simpa using hmul
  have hparent : signedPrefixEulerArrivalTime t ≤ X :=
    hparentLeCompletion.trans hcomplete
  have hsign := signedPrefixFreshEulerChildSign hpFresh
  simp [signedPrefixEulerPairResidualAt, hparent, hcomplete, hsign]

/-- Abstract lifetime trajectories that are born and completed inside a run
contribute zero to the cumulative run, independently of lifetime length.  This
is the generic trajectory law used by the sequential prefix interpretation. -/
theorem signedPrefixInteriorLifetimeIncrement_eq_zero
    {β δ a b : ℕ} (hab : a ≤ b) (hborn : a < β) (hcaptured : δ ≤ b) :
    (∑ k ∈ Finset.Ico a b,
        (lifetimeActivity β δ (k + 1) - lifetimeActivity β δ k)) = 0 := by
  exact sum_lifetimeActivity_increment_Ico_eq_zero_of_interior
    hab hborn hcaptured

/-- The lifetime energy target on the exact event residual coordinate.

No constant is supplied or assumed: for each positive `ε` the statement asks
for the existence of a nonnegative constant, uniformly over all forward strict
subdoubling square runs. -/
def SignedPrefixLifetimeEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, 3 ≤ a → a ≤ b →
        (b + 1) ^ 2 < 2 * a ^ 2 →
        ‖signedPrefixLifetimeResidual a b‖ ^ 2 ≤
          C * Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)

/-- The lifetime-energy statement is exactly the existing oriented-run seam.
This proves that the new coordinate preserves the full difficulty while making
arrivals, exposed lifetimes, and irreversible completions explicit. -/
theorem signedPrefixLifetimeEnergyBound_iff_canonicalOrientedRunDifferenceEnergyBounded :
    SignedPrefixLifetimeEnergyBound ↔
      CanonicalOrientedRunDifferenceEnergyBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro a b ha hab hsub
    rw [← signedPrefixLifetimeResidual_eq_canonicalOrientedRunDifference]
    exact hbound a b ha hab hsub
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro a b ha hab hsub
    rw [signedPrefixLifetimeResidual_eq_canonicalOrientedRunDifference]
    exact hbound a b ha hab hsub

end RHLean.Proof
