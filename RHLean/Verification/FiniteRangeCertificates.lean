import Mathlib
import RHLean.Proof.JointGramControl

open scoped BigOperators

namespace RHLean.Verification

/-- Metadata that a generated finite-range certificate must carry. -/
structure FiniteRangeCertificateMetadata where
  codeVersion : String
  sourceCommit : String
  dataChecksum : String
  payloadChecksum : ℕ
  deriving DecidableEq, Repr

/-- The metadata expected by the trusted checker invocation. -/
structure FiniteRangeCertificateExpectation where
  codeVersion : String
  sourceCommit : String
  dataChecksum : String
  deriving DecidableEq, Repr

/--
An exact decomposition checkpoint. All coordinates are integer numerators with the
common positive denominator stored by the enclosing certificate.
-/
structure ExactDecompositionCheckpoint where
  resonantReal : ℤ
  resonantImag : ℤ
  nonresonantReal : ℤ
  nonresonantImag : ℤ
  totalReal : ℤ
  totalImag : ℤ
  deriving DecidableEq, Repr

/-- The decomposition checkpoint recombines exactly in both coordinates. -/
def ExactDecompositionCheckpoint.Valid
    (checkpoint : ExactDecompositionCheckpoint) : Prop :=
  checkpoint.totalReal = checkpoint.resonantReal + checkpoint.nonresonantReal ∧
    checkpoint.totalImag = checkpoint.resonantImag + checkpoint.nonresonantImag

instance instDecidableExactDecompositionCheckpointValid
    (checkpoint : ExactDecompositionCheckpoint) : Decidable checkpoint.Valid := by
  unfold ExactDecompositionCheckpoint.Valid
  infer_instance

/-- Prime and residue-class counts recorded at one checked scale. -/
structure PrimeResidueCheckpoint where
  residueModulus : ℕ
  primeCount : ℕ
  residueClasses : List ℕ
  residueClassCounts : List ℕ
  deriving DecidableEq, Repr

/--
The residue checkpoint has a positive modulus, distinct in-range classes, one
count per class, and class counts summing to the recorded prime count.
-/
def PrimeResidueCheckpoint.Valid
    (checkpoint : PrimeResidueCheckpoint) : Prop :=
  0 < checkpoint.residueModulus ∧
    checkpoint.residueClasses.length = checkpoint.residueClassCounts.length ∧
    checkpoint.residueClasses.Nodup ∧
    (∀ index : Fin checkpoint.residueClasses.length,
      checkpoint.residueClasses.get index < checkpoint.residueModulus) ∧
    checkpoint.residueClassCounts.sum = checkpoint.primeCount

instance instDecidablePrimeResidueCheckpointValid
    (checkpoint : PrimeResidueCheckpoint) : Decidable checkpoint.Valid := by
  unfold PrimeResidueCheckpoint.Valid
  infer_instance

/--
The exact signed joint-Gram payload at one scale. The diagonal and off-diagonal
lists retain every term of the complete shell/cofactor/mode/row enumeration.
-/
structure JointGramCertificateCheckpoint where
  shellCount : ℕ
  cofactorCount : ℕ
  denominatorModeCount : ℕ
  jointCard : ℕ
  diagonalTerms : List ℤ
  offDiagonalTerms : List ℤ
  claimedJointEnergy : ℤ
  parentJointEnergy : ℤ
  forcing : ℤ
  deriving DecidableEq, Repr

/-- One generated finite-range row. -/
structure FiniteRangeCertificateRow where
  scale : ℕ
  parentScale : ℕ
  decomposition : ExactDecompositionCheckpoint
  primeResidues : PrimeResidueCheckpoint
  jointGram : JointGramCertificateCheckpoint
  deriving DecidableEq, Repr

/--
A complete generated certificate. All integer-valued analytic quantities use the
same positive `valueDenominator`. The contraction coefficient is represented by
`rhoNumerator / rhoDenominator`.
-/
structure FiniteRangeCertificate where
  metadata : FiniteRangeCertificateMetadata
  rangeStart : ℕ
  rangeEnd : ℕ
  valueDenominator : ℕ
  rhoNumerator : ℕ
  rhoDenominator : ℕ
  rows : List FiniteRangeCertificateRow
  deriving DecidableEq, Repr

/-- Injectively encode an integer as a natural-number checksum word. -/
def integerChecksumWord : ℤ → ℕ
  | .ofNat value => 2 * value
  | .negSucc value => 2 * value + 1

/-- A simple exact rolling checksum step for generated numeric payloads. -/
def payloadChecksumStep (accumulator word : ℕ) : ℕ :=
  accumulator * 65599 + word + 1

/-- Deterministic checksum of a finite list of natural-number words. -/
def payloadChecksumWords (words : List ℕ) : ℕ :=
  words.foldl payloadChecksumStep 2166136261

/-- Numeric payload words for an exact decomposition checkpoint. -/
def decompositionPayloadWords
    (checkpoint : ExactDecompositionCheckpoint) : List ℕ :=
  [ integerChecksumWord checkpoint.resonantReal,
    integerChecksumWord checkpoint.resonantImag,
    integerChecksumWord checkpoint.nonresonantReal,
    integerChecksumWord checkpoint.nonresonantImag,
    integerChecksumWord checkpoint.totalReal,
    integerChecksumWord checkpoint.totalImag ]

/-- Numeric payload words for a residue-count checkpoint. -/
def primeResiduePayloadWords
    (checkpoint : PrimeResidueCheckpoint) : List ℕ :=
  [ checkpoint.residueModulus,
    checkpoint.primeCount,
    checkpoint.residueClasses.length,
    checkpoint.residueClassCounts.length ] ++
    checkpoint.residueClasses ++ checkpoint.residueClassCounts

/-- Numeric payload words for one complete signed joint-Gram checkpoint. -/
def jointGramPayloadWords
    (checkpoint : JointGramCertificateCheckpoint) : List ℕ :=
  [ checkpoint.shellCount,
    checkpoint.cofactorCount,
    checkpoint.denominatorModeCount,
    checkpoint.jointCard,
    checkpoint.diagonalTerms.length,
    checkpoint.offDiagonalTerms.length,
    integerChecksumWord checkpoint.claimedJointEnergy,
    integerChecksumWord checkpoint.parentJointEnergy,
    integerChecksumWord checkpoint.forcing ] ++
    checkpoint.diagonalTerms.map integerChecksumWord ++
    checkpoint.offDiagonalTerms.map integerChecksumWord

/-- Numeric payload words for one generated finite-range row. -/
def finiteRangeRowPayloadWords
    (row : FiniteRangeCertificateRow) : List ℕ :=
  [row.scale, row.parentScale] ++
    decompositionPayloadWords row.decomposition ++
    primeResiduePayloadWords row.primeResidues ++
    jointGramPayloadWords row.jointGram

/--
Recompute the exact payload checksum from every numeric certificate field. The
external string checksum remains independently matched against the expectation.
-/
def finiteRangeCertificatePayloadChecksum
    (certificate : FiniteRangeCertificate) : ℕ :=
  payloadChecksumWords
    ([ certificate.rangeStart,
       certificate.rangeEnd,
       certificate.valueDenominator,
       certificate.rhoNumerator,
       certificate.rhoDenominator,
       certificate.rows.length ] ++
      certificate.rows.flatMap finiteRangeRowPayloadWords)

/-- Number of strict off-diagonal pairs in a complete joint index. -/
def expectedOffDiagonalCount (jointCard : ℕ) : ℕ :=
  jointCard * (jointCard - 1) / 2

/--
The exact joint energy reconstructed from every diagonal term and every signed
off-diagonal term in the generated row.
-/
def reconstructedJointEnergy
    (checkpoint : JointGramCertificateCheckpoint) : ℤ :=
  checkpoint.diagonalTerms.sum + 2 * checkpoint.offDiagonalTerms.sum

/--
Validity of one generated row at its expected scale. No componentwise smallness
condition is imposed: the recurrence check uses only the reconstructed full
signed joint-Gram energy.
-/
def FiniteRangeCertificateRow.Valid
    (certificate : FiniteRangeCertificate)
    (expectedScale : ℕ)
    (row : FiniteRangeCertificateRow) : Prop :=
  row.scale = expectedScale ∧
    row.parentScale < row.scale ∧
    row.decomposition.Valid ∧
    row.primeResidues.Valid ∧
    row.jointGram.jointCard =
      row.jointGram.shellCount * row.jointGram.cofactorCount *
        row.jointGram.denominatorModeCount * 2 ∧
    row.jointGram.diagonalTerms.length = row.jointGram.jointCard ∧
    row.jointGram.offDiagonalTerms.length =
      expectedOffDiagonalCount row.jointGram.jointCard ∧
    row.jointGram.claimedJointEnergy =
      reconstructedJointEnergy row.jointGram ∧
    0 ≤ row.jointGram.claimedJointEnergy ∧
    0 ≤ row.jointGram.parentJointEnergy ∧
    0 ≤ row.jointGram.forcing ∧
    (certificate.rhoDenominator : ℤ) * row.jointGram.claimedJointEnergy ≤
      (certificate.rhoNumerator : ℤ) * row.jointGram.parentJointEnergy +
        (certificate.rhoDenominator : ℤ) * row.jointGram.forcing

instance instDecidableFiniteRangeCertificateRowValid
    (certificate : FiniteRangeCertificate)
    (expectedScale : ℕ)
    (row : FiniteRangeCertificateRow) : Decidable (row.Valid certificate expectedScale) := by
  unfold FiniteRangeCertificateRow.Valid
  infer_instance

/--
The trusted semantic proposition checked for a complete finite-range
certificate. Rows must cover the declared interval exactly and in order.
-/
def FiniteRangeCertificate.Valid
    (expectation : FiniteRangeCertificateExpectation)
    (certificate : FiniteRangeCertificate) : Prop :=
  certificate.metadata.codeVersion = expectation.codeVersion ∧
    certificate.metadata.sourceCommit = expectation.sourceCommit ∧
    certificate.metadata.dataChecksum = expectation.dataChecksum ∧
    certificate.metadata.payloadChecksum =
      finiteRangeCertificatePayloadChecksum certificate ∧
    certificate.rangeStart ≤ certificate.rangeEnd ∧
    0 < certificate.valueDenominator ∧
    0 < certificate.rhoDenominator ∧
    certificate.rhoNumerator < certificate.rhoDenominator ∧
    certificate.rows.length =
      certificate.rangeEnd - certificate.rangeStart + 1 ∧
    ∀ index : Fin certificate.rows.length,
      (certificate.rows.get index).Valid certificate
        (certificate.rangeStart + index)

instance instDecidableFiniteRangeCertificateValid
    (expectation : FiniteRangeCertificateExpectation)
    (certificate : FiniteRangeCertificate) : Decidable (certificate.Valid expectation) := by
  unfold FiniteRangeCertificate.Valid
  infer_instance

/-- Executable checker used at the generated-data import boundary. -/
def checkFiniteRangeCertificate
    (expectation : FiniteRangeCertificateExpectation)
    (certificate : FiniteRangeCertificate) : Bool :=
  decide (certificate.Valid expectation)

/-- The executable checker is sound for the trusted validity proposition. -/
theorem checkFiniteRangeCertificate_sound
    (expectation : FiniteRangeCertificateExpectation)
    (certificate : FiniteRangeCertificate)
    (hchecked : checkFiniteRangeCertificate expectation certificate = true) :
    certificate.Valid expectation := by
  apply of_decide_eq_true
  simpa [checkFiniteRangeCertificate] using hchecked

/--
Only certificates accompanied by a proof that the executable checker returned
`true` cross the trusted import boundary.
-/
structure AcceptedFiniteRangeCertificate
    (expectation : FiniteRangeCertificateExpectation) where
  certificate : FiniteRangeCertificate
  checked : checkFiniteRangeCertificate expectation certificate = true

/-- Every accepted generated certificate satisfies the trusted proposition. -/
theorem AcceptedFiniteRangeCertificate.valid
    {expectation : FiniteRangeCertificateExpectation}
    (accepted : AcceptedFiniteRangeCertificate expectation) :
    accepted.certificate.Valid expectation :=
  checkFiniteRangeCertificate_sound expectation accepted.certificate accepted.checked

/--
An accepted certificate has the exact expected code version, source commit, and
external data checksum.
-/
theorem AcceptedFiniteRangeCertificate.metadata_eq
    {expectation : FiniteRangeCertificateExpectation}
    (accepted : AcceptedFiniteRangeCertificate expectation) :
    accepted.certificate.metadata.codeVersion = expectation.codeVersion ∧
      accepted.certificate.metadata.sourceCommit = expectation.sourceCommit ∧
      accepted.certificate.metadata.dataChecksum = expectation.dataChecksum := by
  rcases accepted.valid with
    ⟨hcode, hsource, hdata, _hpayload, _hrange, _hvalueDenominator,
      _hrhoDenominator, _hrho, _hlength, _hrows⟩
  exact ⟨hcode, hsource, hdata⟩

/-- The numeric payload checksum of every accepted certificate was recomputed. -/
theorem AcceptedFiniteRangeCertificate.payloadChecksum_eq
    {expectation : FiniteRangeCertificateExpectation}
    (accepted : AcceptedFiniteRangeCertificate expectation) :
    accepted.certificate.metadata.payloadChecksum =
      finiteRangeCertificatePayloadChecksum accepted.certificate := by
  rcases accepted.valid with
    ⟨_hcode, _hsource, _hdata, hpayload, _hrange, _hvalueDenominator,
      _hrhoDenominator, _hrho, _hlength, _hrows⟩
  exact hpayload

/-- Every row of an accepted certificate satisfies its exact checked obligations. -/
theorem AcceptedFiniteRangeCertificate.row_valid
    {expectation : FiniteRangeCertificateExpectation}
    (accepted : AcceptedFiniteRangeCertificate expectation)
    (index : Fin accepted.certificate.rows.length) :
    (accepted.certificate.rows.get index).Valid accepted.certificate
      (accepted.certificate.rangeStart + index) := by
  rcases accepted.valid with
    ⟨_hcode, _hsource, _hdata, _hpayload, _hrange, _hvalueDenominator,
      _hrhoDenominator, _hrho, _hlength, hrows⟩
  exact hrows index

end RHLean.Verification
