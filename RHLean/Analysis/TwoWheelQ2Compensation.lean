import Mathlib
import RHLean.Analysis.PhysicalDaughterEnergyObstructions
import RHLean.Analysis.OutsidePrimeLeastSquareMaximalWheel

/-!
# Two-wheel q-square compensation

The finite CRT/least-owner wheel and the all-prime recovery wheel play different
roles.  This module keeps them separate and isolates the exact algebraic
compatibility at a fresh owner `q`.

For any arithmetic field `g`, the two successive first-power Euler responses
at `x` and `x/q` leave exactly the square-dilated daughter:

`g(x) - Delta_q g(x) - Delta_q g(x/q) = g(x/q^2)`.

Thus the physical square-deletion contribution must not be identified with the
daughter by itself.  The signed current-q response and its first-power child are
the compensation that converts the deletion into the q-square daughter.  This
identity is purely local and uses no prefix, CRT completeness, independence, or
relation between the blocker wheel and the recovery wheel.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- **Two-step Euler/q-square identity.**  Two consecutive first-power fresh
prime differences expose the exact q-square remainder.  No primality or
freshness hypothesis is needed for this algebraic floor identity. -/
theorem freshPrimeDifference_twoStep_q2_remainder
    {A : Type*} [CommRing A]
    (q x : ℕ) (g : ℕ → A) :
    g x - freshPrimeDifference q g x -
        freshPrimeDifference q g (x / q) =
      g (x / (q * q)) := by
  simp only [freshPrimeDifference_apply]
  rw [Nat.div_div_eq_div_mul]
  ring

/-- The same identity after any already-formed finite Möbius difference fibre.
The old coordinates remain inside the signed field while the new owner is
peeled twice. -/
theorem finiteDifferenceOperator_twoStep_q2_remainder
    {A : Type*} [CommRing A]
    (P : Finset ℕ) (q x : ℕ) (f : ℕ → A) :
    finiteDifferenceOperator P f x -
        freshPrimeDifference q (finiteDifferenceOperator P f) x -
        freshPrimeDifference q (finiteDifferenceOperator P f) (x / q) =
      finiteDifferenceOperator P f (x / (q * q)) := by
  exact freshPrimeDifference_twoStep_q2_remainder q x
    (finiteDifferenceOperator P f)

/-- The fully reconstructed prime-11 packet associated to a recovery wheel `S`
and an arbitrary already-formed finite difference fibre `T`.  This is kept
separate from any finite CRT blocker wheel. -/
def twoWheelRecoveredElevenPacket
    (S T : Finset ℕ) (upper : ℕ) : ℕ → ℤ :=
  finiteDifferenceOperator T
    (freshPrimeDifference 11 (fun y =>
      primeWheelRawPositivePrefix S y -
        2 * primeWheelSmoothPositivePrefix S upper y))

/-- **Local compensation on the recovered packet.**  The q-square daughter is
exactly what remains after the current q response and its first-power child are
subtracted from the parent packet.  This theorem does not mention the CRT
blocker wheel at all. -/
theorem twoWheelRecoveredElevenPacket_twoStep_q2_remainder
    (S T : Finset ℕ) (upper q x : ℕ) :
    twoWheelRecoveredElevenPacket S T upper x -
        freshPrimeDifference q (twoWheelRecoveredElevenPacket S T upper) x -
        freshPrimeDifference q (twoWheelRecoveredElevenPacket S T upper)
          (x / q) =
      twoWheelRecoveredElevenPacket S T upper (x / (q * q)) := by
  exact freshPrimeDifference_twoStep_q2_remainder q x
    (twoWheelRecoveredElevenPacket S T upper)

/-- Under the existing square-root recovery hypotheses, the q-square remainder
is the same object obtained by pushing the complete recovered packet through the
q-square shift.  This is the exact local composition of recovery and q-square
descent. -/
theorem twoWheelRecoveredElevenPacket_q2_remainder_eq_shifted
    (S T : Finset ℕ) (upper q x : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hx : x ≤ upper) :
    twoWheelRecoveredElevenPacket S T upper (x / (q * q)) =
      finiteDifferenceOperator T
        (freshPrimeDifference 11
          (shift (q * q) (fun y =>
            primeWheelRawPositivePrefix S y -
              2 * primeWheelSmoothPositivePrefix S upper y))) x := by
  symm
  exact recoveredPrimeWheelElevenPacket_q2_selfSimilar
    S T upper x q hprime hcover hx

/-- **LOCAL-INTERTWINE algebraic core.**  Combining the two-step Euler
compensation with recovered-packet self-similarity gives the commuting square in
one statement.  The remaining physical theorem is only to identify the three
left-hand terms with the parent, owner-response, and first-power mate carried by
a complete least-owner super-orbit. -/
theorem twoWheelRecoveredElevenPacket_localIntertwine_core
    (S T : Finset ℕ) (upper q x : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hx : x ≤ upper) :
    twoWheelRecoveredElevenPacket S T upper x -
        freshPrimeDifference q (twoWheelRecoveredElevenPacket S T upper) x -
        freshPrimeDifference q (twoWheelRecoveredElevenPacket S T upper)
          (x / q) =
      finiteDifferenceOperator T
        (freshPrimeDifference 11
          (shift (q * q) (fun y =>
            primeWheelRawPositivePrefix S y -
              2 * primeWheelSmoothPositivePrefix S upper y))) x := by
  rw [twoWheelRecoveredElevenPacket_twoStep_q2_remainder]
  exact twoWheelRecoveredElevenPacket_q2_remainder_eq_shifted
    S T upper q x hprime hcover hx

end RHLean.Analysis
