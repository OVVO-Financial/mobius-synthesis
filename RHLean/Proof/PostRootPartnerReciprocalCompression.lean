import Mathlib
import RHLean.Proof.ExceptionalTransportCoboundary
import RHLean.Proof.CanonicalRoughAdaptiveWeightedIteration

/-!
# Post-root partner columns on the reciprocal compression carrier

An earlier layer identifies every post-root adaptive raw boundary with the intact
partner-incidence column of its parent.  The reciprocal Euler machinery lives
on the same arithmetic response with one factor of the cofactor removed.
This file makes that conversion exact before any norm is taken.

There are two complementary statements.

* A post-root raw boundary is exactly a cofactor-weighted reciprocal parent
  mass.  Dividing the inherited coefficient by the cofactor gives the literal
  reciprocal parent mass, which can be fed directly to the already-compiled
  actual-carrier many-prime compression.
* More importantly for the actual zero-factor chronology, multiplying the
  evolved raw coefficient by the cofactor does not create a new reciprocal
  mismatch on a complete descending prefix.  If the current child has a later
  larger-prime extension, the four-corner theorem has already zeroed both raw
  coefficients; if it has none, its reciprocal response is zero.  Hence the
  cofactor-weighted reciprocal Euler step is exact on the evolved raw carrier.

The scaled reciprocal defect has an exact exchange rate with the raw signed
boundary: multiplying the cofactor-weighted reciprocal defect layer by the
current prime recovers the raw loss/birth boundary mass.  Thus the raw boundary
is a literal scaled drop of the reciprocal-compressed state, not an additional
error term.

No norm, asymptotic estimate, or RH-scale hypothesis is used here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- A raw weighted mass is exactly the same state written in the reciprocal
coordinate with the coefficient multiplied by the cofactor. -/
theorem adaptiveRawWeightedMass_eq_cofactorWeightedReciprocalMass
    (R : ℕ) (U : Finset ℕ) (a : ℕ → ℂ)
    (hpos : ∀ n ∈ U, 0 < n) :
    squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
      squareRootCanonicalRoughAdaptiveWeightedMass R U
        (fun n => (n : ℂ) * a n) := by
  unfold squareRootCanonicalRoughAdaptiveRawWeightedMass
    squareRootCanonicalRoughAdaptiveWeightedMass
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos := hpos n hn
  calc
    a n * squareRootCanonicalRoughRawCorrelationSummand R n =
        a n * ((n : ℂ) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R n) := by
      unfold squareRootCanonicalRoughRawCorrelationSummand
      rw [natCast_mul_squareRootCanonicalRoughCorrelationReciprocalSummand
        R hnpos]
    _ = ((n : ℂ) * a n) *
        squareRootCanonicalRoughCorrelationReciprocalSummand R n := by ring

/-- **Post-root raw boundary -> cofactor-weighted reciprocal parent mass.**
The partner column is therefore already on the reciprocal carrier after
one exact coefficient change. -/
theorem postRootAdaptiveRawBoundary_eq_cofactorWeightedReciprocalParents
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hp : p.Prime) (hRp : R < p) :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a =
      ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        ((c : ℂ) * a c) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R c := by
  unfold squareRootCanonicalRoughAdaptiveRawBoundaryMass
  apply Finset.sum_congr rfl
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, hcrough, _hcchild⟩
  calc
    a c * canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) =
      a c *
        (canonicalMoebiusWeight c *
          (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
            ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ))) := by ring
    _ = a c * squareRootCanonicalRoughRawCorrelationSummand R c := by
      rw [squareRootCanonicalRoughFreshPrimeRawBoundary_eq_parentRaw_of_rootPrime
        hR hcpos hp hcrough hRp]
    _ = a c * ((c : ℂ) *
        squareRootCanonicalRoughCorrelationReciprocalSummand R c) := by
      unfold squareRootCanonicalRoughRawCorrelationSummand
      rw [natCast_mul_squareRootCanonicalRoughCorrelationReciprocalSummand
        R hcpos]
    _ = ((c : ℂ) * a c) *
        squareRootCanonicalRoughCorrelationReciprocalSummand R c := by ring

/-- Dividing the post-root inherited coefficient by the cofactor removes the
cofactor weight exactly and exposes the literal reciprocal parent mass. -/
theorem postRootAdaptiveRawBoundary_reciprocalNormalized_eq_parentMass
    (R : ℕ) {p : ℕ} (U : Finset ℕ)
    (hR : 2 ≤ R) (hp : p.Prime) (hRp : R < p) :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U
        (fun c => 1 / (c : ℂ)) =
      ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R c := by
  rw [postRootAdaptiveRawBoundary_eq_cofactorWeightedReciprocalParents
    R U (fun c => 1 / (c : ℂ)) hR hp hRp]
  apply Finset.sum_congr rfl
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, _hcrough, _hcchild⟩
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcpos)
  field_simp [hc0]

/-- **Literal -> composition.**  The reciprocal-normalized post-root
partner column can be fed, without any intermediate norm, into the existing
actual-parent-carrier many-prime compression.  The only terms produced are the
Euler-scaled final parents, the transported signed physical defect ledger, and
the transported survivor ledger already named by an earlier layer. -/
theorem postRootReciprocalNormalizedBoundary_eq_manyPrimeCompression
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (ps : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime) (hRp : R < p)
    (hprime : ∀ q ∈ ps, q.Prime) :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U
        (fun c => 1 / (c : ℂ)) =
      (canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps
            (squareRootCanonicalRoughFreshPrimeParentsOn p U)) : ℂ) *
        (∑ n ∈ squareRootCanonicalRoughCompressionFinalParents ps
            (squareRootCanonicalRoughFreshPrimeParentsOn p U),
          squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
      squareRootCanonicalRoughTransportedDefectLedger R
        (squareRootCanonicalRoughCompressionRunSteps ps
          (squareRootCanonicalRoughFreshPrimeParentsOn p U)) +
      squareRootCanonicalRoughCorrelationTransportedSurvivorLedger R ps
        (squareRootCanonicalRoughFreshPrimeParentsOn p U) := by
  rw [postRootAdaptiveRawBoundary_reciprocalNormalized_eq_parentMass
    R U hR hp hRp]
  exact
    sum_squareRootCanonicalRoughCorrelationReciprocal_eq_manyPrimeCompression
      R hR ps (squareRootCanonicalRoughFreshPrimeParentsOn p U) hprime

/-- Multiplying the reciprocal physical defect by both the current prime and
its parent cofactor reconstructs the unweighted signed loss/birth boundary.
This is the exact exchange rate between the zero-factor raw descent and the
Euler-factor reciprocal descent. -/
theorem natCast_mul_cofactorWeightedReciprocalDefect_eq_rawBoundary
    {R c p : ℕ} (a : ℕ → ℂ) (hc : 0 < c) (hp : p.Prime) :
    (p : ℂ) *
        (((c : ℂ) * a c) *
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) =
      a c * canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) := by
  have hscaled :=
    natCast_mul_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
      (R := R) hc hp
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hc)
  calc
    (p : ℂ) *
        (((c : ℂ) * a c) *
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) =
      ((c : ℂ) * a c) *
        ((p : ℂ) * squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) := by
          ring
    _ = ((c : ℂ) * a c) *
        (squareRootCanonicalRoughParityReciprocalSummand c *
          squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar R c p) := by
          rw [hscaled]
    _ = a c * canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) := by
      unfold squareRootCanonicalRoughParityReciprocalSummand
        squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar
      rw [squareRootCanonicalRoughFreshLossBoundary_card_eq_threshold_add_topEscape]
      push_cast
      field_simp [hc0]

/-- Carrier-level form of the exact exchange rate. -/
theorem natCast_mul_adaptiveCofactorWeightedPhysicalDefectMass_eq_rawBoundaryMass
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ)
    (hp : p.Prime) :
    (p : ℂ) *
        squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U
          (fun c => (c : ℂ) * a c) =
      squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a := by
  unfold squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass
    squareRootCanonicalRoughAdaptiveRawBoundaryMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, _hcrough, _hcchild⟩
  exact natCast_mul_cofactorWeightedReciprocalDefect_eq_rawBoundary
    (R := R) a hcpos hp

/-- **Cofactor weighting does not recreate the mismatch on the actual evolved
raw chronology.**  This is the crucial compatibility missing from a naive
raw-to-reciprocal substitution.

After a complete descending prefix above `p`, either the child `c*p` still has
a larger physical extension, in which case the four-corner theorem has already
zeroed the evolved raw coefficients of both `c` and `c*p`, or it has no such
extension, in which case its reciprocal response is zero.  Multiplication of
the raw coefficient by the cofactor therefore leaves the entire reciprocal
coefficient-mismatch mass identically zero. -/
theorem cofactorWeighted_evolvedMismatch_eq_zero_of_completeDescendingPrefix
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p
        (squareRootCanonicalRoughAdaptiveCarrier qs
          (Finset.Icc 1 (squareRootEndpoint R)))
        (fun n => (n : ℂ) *
          squareRootCanonicalRoughAdaptiveRawCoefficient qs
            (Finset.Icc 1 (squareRootEndpoint R))
            (fun _ => (1 : ℂ)) n) = 0 := by
  unfold squareRootCanonicalRoughAdaptiveCoefficientMismatchMass
  apply Finset.sum_eq_zero
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcV, hcpos, hrough, _hcpV⟩
  by_cases hchild :
      squareRootCanonicalRoughHasPrimeExtensionAbove R p (c * p)
  · rcases hchild with ⟨q, hqPrime, hpq, hupper⟩
    have hcpPos : 0 < c * p := Nat.mul_pos hcpos hp.pos
    have hqProd : q ≤ q * (c * p) := Nat.le_mul_of_pos_right q hcpPos
    have hqUpper : q ≤ squareRootEndpoint R := by
      have hqProd' : q ≤ (c * p) * q := by
        simpa [Nat.mul_comm] using hqProd
      exact hqProd'.trans hupper
    rcases hcomplete.2 q hqPrime hpq hqUpper with
      ⟨pre, post, hsplit, hprePrime, hpreLarger⟩
    have hzero :=
      squareRootCanonicalRoughAdaptiveRawCoefficient_pair_eq_zero_of_larger_extension_split
        pre post hcpos hp hqPrime hrough hpq hupper hprePrime hpreLarger
    rw [← hsplit] at hzero
    simp [hzero.1, hzero.2]
  · have hcpPos : 0 < c * p := Nat.mul_pos hcpos hp.pos
    have hraw :=
      squareRootCanonicalRoughRawCorrelationSummand_mul_freshPrime_eq_zero_of_no_extension
        hR hcpos hp hrough hchild
    have hrecip :
        squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) = 0 := by
      rw [squareRootCanonicalRoughCorrelationReciprocalSummand_eq_weighted_response_div
        R hcpPos]
      unfold squareRootCanonicalRoughRawCorrelationSummand at hraw
      rw [hraw]
      simp
    rw [hrecip]
    simp

/-- The previous theorem removes the only coefficient obstruction in the
weighted reciprocal Euler step on the actual evolved raw carrier. -/
theorem cofactorWeighted_evolvedMass_eq_next_add_physicalDefect_of_completeDescendingPrefix
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    let U := squareRootCanonicalRoughAdaptiveCarrier qs
      (Finset.Icc 1 (squareRootEndpoint R))
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs
      (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))
    let b := fun n : ℕ => (n : ℂ) * a n
    squareRootCanonicalRoughAdaptiveWeightedMass R U b =
      squareRootCanonicalRoughAdaptiveWeightedMass R
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveNextCoefficient p U b) +
      squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U b := by
  dsimp
  have hstep :=
    adaptiveWeightedMass_eq_next_add_physicalDefect_add_mismatch
      R
      (squareRootCanonicalRoughAdaptiveCarrier qs
        (Finset.Icc 1 (squareRootEndpoint R)))
      (fun n : ℕ => (n : ℂ) *
        squareRootCanonicalRoughAdaptiveRawCoefficient qs
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ)) n)
      hR hp
  rw [cofactorWeighted_evolvedMismatch_eq_zero_of_completeDescendingPrefix
    R qs hR hp hcomplete] at hstep
  simpa using hstep

/-- **Signed scaled-drop form.**  On the actual evolved raw carrier, the current
raw boundary is exactly `p` times the drop from the current raw mass to the
Euler-compressed reciprocal next state.  This is a discrete Stokes identity on
the physical carrier; it is an equality, not an energy estimate. -/
theorem evolvedRawBoundary_eq_scaledReciprocalDrop_of_completeDescendingPrefix
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
      (fun _ => (1 : ℂ))
    let b := fun n : ℕ => (n : ℂ) * a n
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a =
      (p : ℂ) *
        (squareRootCanonicalRoughAdaptiveRawWeightedMass R U a -
          squareRootCanonicalRoughAdaptiveWeightedMass R
            (squareRootCanonicalRoughAdaptiveNextCarrier p U)
            (squareRootCanonicalRoughAdaptiveNextCoefficient p U b)) := by
  dsimp
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  let U : Finset ℕ := squareRootCanonicalRoughAdaptiveCarrier qs U0
  let a : ℕ → ℂ := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
    (fun _ => (1 : ℂ))
  let b : ℕ → ℂ := fun n => (n : ℂ) * a n
  have hpos : ∀ n ∈ U, 0 < n := by
    intro n hn
    have hn0 : n ∈ U0 :=
      squareRootCanonicalRoughAdaptiveCarrier_subset qs U0 hn
    have hnRange := Finset.mem_Icc.mp hn0
    omega
  have hcoord :
      squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
        squareRootCanonicalRoughAdaptiveWeightedMass R U b := by
    exact adaptiveRawWeightedMass_eq_cofactorWeightedReciprocalMass R U a hpos
  have hstep :=
    cofactorWeighted_evolvedMass_eq_next_add_physicalDefect_of_completeDescendingPrefix
      R qs hR hp hcomplete
  dsimp [U0, U, a, b] at hstep
  have hdef :=
    natCast_mul_adaptiveCofactorWeightedPhysicalDefectMass_eq_rawBoundaryMass
      R (p := p) U a hp
  change (p : ℂ) *
      squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U b =
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a at hdef
  rw [hcoord]
  rw [hstep]
  rw [← hdef]
  ring

end RHLean.Proof
