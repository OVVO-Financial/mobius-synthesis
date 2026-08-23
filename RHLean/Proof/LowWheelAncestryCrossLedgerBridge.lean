import Mathlib
import RHLean.Proof.SquareRootAncestryParentFibres
import RHLean.Proof.LowWheelDoubleCubeSequentialFold
import RHLean.Proof.LowWheelCanonicalDefectReduction

/-!
# Sequential low-wheel operator inside the ancestry cross ledger

The ancestry and square-root decompositions already identify the two scalar
factors of the legal root-successor cross term:

`root = positiveSmooth - transport`,
`successor = 1 - bornSmooth`.

The new transport realization rewrites `transport` as the full two-copy
low-prime Boolean cube.  Therefore the actual RH-critical ancestry cross ledger
contains the double-cube operator *exactly*, before any norm is taken.

At a prime root cutoff `R`, the sequential fresh-prime fold can then be
substituted as well: the transport factor is the geometrically localized
`R`-coordinate shell state built over the previously processed prime universe
`primesUpTo (R-1)`.

This module is only an exact bridge.  It asserts no RH-scale estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The ancestry root factor with the high transport replaced by the symmetric
low-wheel double cube. -/
theorem sourceRootPrefix_cast_eq_positiveSmooth_sub_lowWheelDoubleCube
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    ((sourceRootPrefix B (R - 1) : ℤ) : ℂ) =
      squareRootPositiveSmoothMass R -
        lowWheelDoubleCubeTransportLedger R := by
  rw [sourceRootPrefix_cast_eq_positiveSmooth_sub_transport hR hB]
  rw [← squareRootTransportCofactorFirst_eq_primeFirst]
  rw [squareRootTransportCofactorFirst_eq_lowWheelDoubleCube R hR]

/-- **Cross-ledger factorization through the low-wheel operator.**  The exact
root-successor cross term is the product of the positive-smooth correction minus
the two-cube transport operator and the born-smooth successor factor. -/
theorem squareRootRootSuccessorCrossLedger_cast_eq_lowWheelDoubleCube
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℂ) =
      (squareRootPositiveSmoothMass R -
          lowWheelDoubleCubeTransportLedger R) *
        (1 - squareRootBornSmoothMass R) := by
  rw [squareRootRootSuccessorCrossLedger_eq_mul]
  push_cast
  rw [sourceRootPrefix_cast_eq_positiveSmooth_sub_lowWheelDoubleCube hR hB,
    sourceSuccessorPrefix_cast_eq_one_sub_bornSmooth hR hB]

/-- At a prime root coordinate, the RH-critical cross ledger contains the
literal sequential fresh-prime shell state: every transport contribution is
indexed only by prime faces from the already-processed universe
`primesUpTo (R-1)` and lies on the two `R`-scaled geometric shells. -/
theorem squareRootRootSuccessorCrossLedger_cast_eq_sequentialShells_of_prime
    {B R : ℕ} (hR : 2 ≤ R) (hprime : R.Prime)
    (hB : squareRootEndpoint R ≤ B) :
    ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℂ) =
      (squareRootPositiveSmoothMass R -
        (∑ u ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
          ∑ t ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
              (RHLean.Arithmetic.booleanCubeSign u : ℂ) *
                (RHLean.Arithmetic.booleanCubeSign t : ℂ) *
                lowWheelSequentialShellDifferenceC R R (squareRootEndpoint R)
                  (RHLean.Arithmetic.primeFaceProduct t * k)
                  ((RHLean.Arithmetic.primeFaceProduct u *
                    RHLean.Arithmetic.primeFaceProduct t) * k))) *
        (1 - squareRootBornSmoothMass R) := by
  rw [squareRootRootSuccessorCrossLedger_cast_eq_lowWheelDoubleCube hR hB]
  have hshell :=
    squareRootTransportCofactorFirst_eq_sequentialShells_of_prime R hR hprime
  have hdouble :
      lowWheelDoubleCubeTransportLedger R =
        ∑ u ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
          ∑ t ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
              (RHLean.Arithmetic.booleanCubeSign u : ℂ) *
                (RHLean.Arithmetic.booleanCubeSign t : ℂ) *
                lowWheelSequentialShellDifferenceC R R (squareRootEndpoint R)
                  (RHLean.Arithmetic.primeFaceProduct t * k)
                  ((RHLean.Arithmetic.primeFaceProduct u *
                    RHLean.Arithmetic.primeFaceProduct t) * k) := by
    rw [← squareRootTransportCofactorFirst_eq_lowWheelDoubleCube R hR]
    exact hshell
  rw [hdouble]

/-! ## Fixed-amplification coercivity seam -/

/-- The actual lower coercivity band required from the signed root-successor
cross ledger at amplification `A`.  Unlike an absolute-value estimate, the
right side keeps the signed cross term intact. -/
def SquareRootSequentialCrossLedgerCoerciveAt
    (A K : ℝ) (B R : ℕ) : Prop :=
  squareRootLegalRootReal B R ^ 2 +
      squareRootLegalSuccessorReal B R ^ 2 -
      A * (R : ℝ) ^ 2 * K ≤
    2 * ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℝ)

/-- The requested lower cross-ledger band is exactly the legal ancestry Gram
bound at the same amplification.  There is no Cauchy--Schwarz loss here. -/
theorem squareRootSequentialCrossLedgerCoerciveAt_iff_gramBound
    (A K : ℝ) (B R : ℕ) :
    SquareRootSequentialCrossLedgerCoerciveAt A K B R ↔
      squareRootLegalAncestryGramDefect B R ≤
        A * (R : ℝ) ^ 2 * K := by
  unfold SquareRootSequentialCrossLedgerCoerciveAt
  rw [squareRootLegalAncestryGramDefect_eq_sourceLedger]
  constructor <;> intro h <;> linarith

/-- At a complete square endpoint the same coercivity band is literally the
fixed-amplification Mertens endpoint inequality. -/
theorem squareRootSequentialCrossLedgerCoerciveAt_iff_mertensEndpoint
    {A K : ℝ} {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    SquareRootSequentialCrossLedgerCoerciveAt A K B R ↔
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
        A * (R : ℝ) ^ 2 * K := by
  rw [squareRootSequentialCrossLedgerCoerciveAt_iff_gramBound,
    squareRootLegalAncestryGramDefect_eq_mertensNumerator hR hB]

/-- Global fixed-amplification formulation directly on the sequential signed
cross ledger. -/
def SquareRootSequentialCrossLedgerCoercivityStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ, ∀ B : ℕ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      squareRootEndpoint R ≤ B →
      SquareRootSequentialCrossLedgerCoerciveAt A K B R

/-- The sequential cross-ledger coercivity statement is exactly the existing
legal ancestry Gram amplification statement. -/
theorem squareRootSequentialCrossLedgerCoercivity_iff_legalAncestryGram :
    SquareRootSequentialCrossLedgerCoercivityStatement ↔
      SquareRootLegalAncestryGramAmplificationStatement := by
  constructor
  · rintro ⟨A, hA, hcoercive⟩
    refine ⟨A, hA, ?_⟩
    intro R K B hR hK hB
    exact
      (squareRootSequentialCrossLedgerCoerciveAt_iff_gramBound A K B R).1
        (hcoercive R K B hR hK hB)
  · rintro ⟨A, hA, hgram⟩
    refine ⟨A, hA, ?_⟩
    intro R K B hR hK hB
    exact
      (squareRootSequentialCrossLedgerCoerciveAt_iff_gramBound A K B R).2
        (hgram R K B hR hK hB)

/-- Consequently, proving fixed lower coercivity for this sequential operator is
neither weaker nor stronger than the scalar endpoint amplification theorem: it
is exactly the RH-critical quantitative seam already isolated by the repo. -/
theorem squareRootSequentialCrossLedgerCoercivity_iff_mertensEndpointAmplification :
    SquareRootSequentialCrossLedgerCoercivityStatement ↔
      SquareRootMertensEndpointAmplificationStatement := by
  calc
    SquareRootSequentialCrossLedgerCoercivityStatement ↔
        SquareRootLegalAncestryGramAmplificationStatement :=
      squareRootSequentialCrossLedgerCoercivity_iff_legalAncestryGram
    _ ↔ SquareRootMertensEndpointAmplificationStatement :=
      squareRootMertensEndpointAmplification_iff_legalAncestryGram.symm

/-- Algebraic coercivity margin.  Its nonnegativity is exactly the desired
lower cross-ledger band. -/
def squareRootSequentialCrossLedgerCoercivityMargin
    (A K : ℝ) (B R : ℕ) : ℝ :=
  2 * ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℝ) -
    (squareRootLegalRootReal B R ^ 2 +
      squareRootLegalSuccessorReal B R ^ 2 -
      A * (R : ℝ) ^ 2 * K)

/-- The sign of the coercivity margin is precisely the signed anti-alignment
condition; no orientation information is lost. -/
theorem squareRootSequentialCrossLedgerCoercivityMargin_nonneg_iff
    (A K : ℝ) (B R : ℕ) :
    0 ≤ squareRootSequentialCrossLedgerCoercivityMargin A K B R ↔
      SquareRootSequentialCrossLedgerCoerciveAt A K B R := by
  unfold squareRootSequentialCrossLedgerCoercivityMargin
    SquareRootSequentialCrossLedgerCoerciveAt
  constructor <;> intro h <;> linarith

/-- At the complete square endpoint the margin is exactly the available
amplification budget minus the endpoint Mertens energy.  This identity prevents
a local shell or pairing estimate from silently discarding the RH-strength
boundary term. -/
theorem squareRootSequentialCrossLedgerCoercivityMargin_eq_endpointSlack
    {A K : ℝ} {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    squareRootSequentialCrossLedgerCoercivityMargin A K B R =
      A * (R : ℝ) ^ 2 * K -
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) := by
  have hledger := squareRootLegalAncestryGramDefect_eq_sourceLedger B R
  have hendpoint :=
    squareRootLegalAncestryGramDefect_eq_mertensNumerator hR hB
  unfold squareRootSequentialCrossLedgerCoercivityMargin
  nlinarith

/-- The opposite inequality is automatic from square nonnegativity.  This is
useful as a direction check: the open theorem is the *lower* cross-ledger band,
not this universal upper wall. -/
theorem squareRootRootSuccessorCrossLedger_two_mul_le_diagonal
    (B R : ℕ) :
    2 * ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℝ) ≤
      squareRootLegalRootReal B R ^ 2 +
        squareRootLegalSuccessorReal B R ^ 2 := by
  have hnonneg : 0 ≤ squareRootLegalAncestryGramDefect B R := by
    unfold squareRootLegalAncestryGramDefect
    positivity
  rw [squareRootLegalAncestryGramDefect_eq_sourceLedger] at hnonneg
  linarith

/-! ## Real operator and prime-shell specialization -/

/-- Real value of the exact low-wheel root-successor operator, before any norm
is taken. -/
def lowWheelSequentialRootSuccessorCrossOperatorReal (R : ℕ) : ℝ :=
  ((squareRootPositiveSmoothMass R -
      lowWheelDoubleCubeTransportLedger R) *
    (1 - squareRootBornSmoothMass R)).re

/-- The integer ancestry cross ledger is exactly the real value of the low-wheel
operator. -/
theorem squareRootRootSuccessorCrossLedger_real_eq_lowWheelOperator
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℝ) =
      lowWheelSequentialRootSuccessorCrossOperatorReal R := by
  have h :=
    squareRootRootSuccessorCrossLedger_cast_eq_lowWheelDoubleCube hR hB
  have hre := congrArg Complex.re h
  simpa [lowWheelSequentialRootSuccessorCrossOperatorReal] using hre

/-- The fixed-amplification coercivity target can therefore be stated directly
on the real sequential low-wheel operator. -/
theorem squareRootSequentialCrossLedgerCoerciveAt_iff_lowWheelOperator
    {A K : ℝ} {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    SquareRootSequentialCrossLedgerCoerciveAt A K B R ↔
      squareRootLegalRootReal B R ^ 2 +
          squareRootLegalSuccessorReal B R ^ 2 -
          A * (R : ℝ) ^ 2 * K ≤
        2 * lowWheelSequentialRootSuccessorCrossOperatorReal R := by
  unfold SquareRootSequentialCrossLedgerCoerciveAt
  rw [squareRootRootSuccessorCrossLedger_real_eq_lowWheelOperator hR hB]

/-- The prime-root fresh-shell transport as a named operator. -/
def lowWheelSequentialPrimeShellTransport (R : ℕ) : ℂ :=
  ∑ u ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
    ∑ t ∈ (RHLean.Arithmetic.primesUpTo (R - 1)).powerset,
      ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        (RHLean.Arithmetic.booleanCubeSign u : ℂ) *
          (RHLean.Arithmetic.booleanCubeSign t : ℂ) *
          lowWheelSequentialShellDifferenceC R R (squareRootEndpoint R)
            (RHLean.Arithmetic.primeFaceProduct t * k)
            ((RHLean.Arithmetic.primeFaceProduct u *
              RHLean.Arithmetic.primeFaceProduct t) * k)

/-- At a prime root, the complete low-wheel transport is literally its fresh
`R`-coordinate shell operator over the previously processed prime prefix. -/
theorem lowWheelDoubleCubeTransportLedger_eq_sequentialPrimeShellTransport
    (R : ℕ) (hR : 2 ≤ R) (hprime : R.Prime) :
    lowWheelDoubleCubeTransportLedger R =
      lowWheelSequentialPrimeShellTransport R := by
  rw [← squareRootTransportCofactorFirst_eq_lowWheelDoubleCube R hR]
  exact squareRootTransportCofactorFirst_eq_sequentialShells_of_prime R hR hprime

/-- Real cross-ledger operator with the prime-root fresh shell substituted. -/
def lowWheelSequentialPrimeShellCrossOperatorReal (R : ℕ) : ℝ :=
  ((squareRootPositiveSmoothMass R -
      lowWheelSequentialPrimeShellTransport R) *
    (1 - squareRootBornSmoothMass R)).re

/-- Prime roots make the sequential chronology literal inside the real cross
operator. -/
theorem lowWheelSequentialRootSuccessorCrossOperatorReal_eq_primeShells
    (R : ℕ) (hR : 2 ≤ R) (hprime : R.Prime) :
    lowWheelSequentialRootSuccessorCrossOperatorReal R =
      lowWheelSequentialPrimeShellCrossOperatorReal R := by
  unfold lowWheelSequentialRootSuccessorCrossOperatorReal
    lowWheelSequentialPrimeShellCrossOperatorReal
  rw [lowWheelDoubleCubeTransportLedger_eq_sequentialPrimeShellTransport
    R hR hprime]

/-- Final prime-root form of the open lower coercivity band: every occurrence of
the high transport has been replaced by the literal fresh-prime shell state. -/
theorem squareRootSequentialCrossLedgerCoerciveAt_iff_primeShellOperator
    {A K : ℝ} {B R : ℕ} (hR : 2 ≤ R) (hprime : R.Prime)
    (hB : squareRootEndpoint R ≤ B) :
    SquareRootSequentialCrossLedgerCoerciveAt A K B R ↔
      squareRootLegalRootReal B R ^ 2 +
          squareRootLegalSuccessorReal B R ^ 2 -
          A * (R : ℝ) ^ 2 * K ≤
        2 * lowWheelSequentialPrimeShellCrossOperatorReal R := by
  rw [squareRootSequentialCrossLedgerCoerciveAt_iff_lowWheelOperator hR hB,
    lowWheelSequentialRootSuccessorCrossOperatorReal_eq_primeShells R hR hprime]

end RHLean.Proof
