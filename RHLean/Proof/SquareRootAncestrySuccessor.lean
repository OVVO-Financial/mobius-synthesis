import Mathlib
import RHLean.Analysis.SquareRootTransportRealization
import RHLean.Proof.SquareRootAncestryRoot

/-!
# The ancestry successor is exactly the born-smooth correction

The square-root transport and canonical ancestry routes are now compared term
by term.  The previous root theorem identifies every transport-oriented ancestry
root with a lower-triangular prime transform.  Here we identify the other half
of the renewal.

A smooth-oriented ancestry source has a unique parent, and the existing exact
sign-reversal theorem says that the successor operator evaluates to the negative
of the child Möbius weight.  Reindexing active smooth sources by their represented
integer therefore gives exactly the born-smooth population, except for the
special integer `m = 1`, which has no ancestry source.

Thus, at the square endpoint `X = R^2 - 1`,

`successor = 1 - bornSmooth`.

Combining this with the two already-proved total identities forces the root
identity

`root = positiveSmooth - transport`.

So the ancestry renewal and square-root smooth/transport decomposition are not
merely equivalent because both sum to Mertens: their root and successor pieces
are literally the same signed arithmetic populations.

No norm estimate or analytic contraction is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

/-- Clock-pushed successor term in the canonical ancestry renewal. -/
def sourceSuccessorPrefix (B x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x
    ((boundedSourceFlow B).successorOperator (boundedSourceFlow B).weight)

/-- Active smooth-oriented canonical sources under the native square-root clock. -/
def activeSmoothSourceSet (B x : ℕ) : Finset (SourceIndex B) := by
  classical
  exact Finset.univ.filter fun s =>
    SmoothOriented s ∧ sourceClock B s ≤ x

/-- The successor operator is pointwise the negative child weight on every
active smooth source, and zero on roots. -/
theorem sourceSuccessorPrefix_eq_neg_activeSmooth_sum (B x : ℕ) :
    sourceSuccessorPrefix B x =
      -∑ s ∈ activeSmoothSourceSet B x, sourceWeight s := by
  classical
  unfold sourceSuccessorPrefix activeSmoothSourceSet clockPushforward
  rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hclock : sourceClock B s ≤ x
  · by_cases hsmooth : SmoothOriented s
    · have hparent : sourceParent s = some (parentIndex s hsmooth) :=
        smoothSource_has_parent s hsmooth
      have hsign := sourceWeight_parentIndex s hsmooth
      have hparentWeight :
          sourceWeight (parentIndex s hsmooth) = -sourceWeight s := by
        linarith
      simp [boundedSourceFlow, ParentFlow.successorOperator, hparent,
        hclock, hsmooth, hparentWeight]
    · have hparent : sourceParent s = none :=
        (sourceParent_eq_none_iff s).2 hsmooth
      simp [boundedSourceFlow, ParentFlow.successorOperator, hparent,
        hclock, hsmooth]
  · simp [hclock]

/-- Squarefree integers larger than one whose canonical largest-prime
orientation is smooth at square-root cutoff `R`. -/
def squareRootAncestrySmoothIntegerSet (R : ℕ) : Finset ℕ := by
  classical
  exact (cumulativeSquarePrefixSet (R - 1)).filter fun m =>
    2 ≤ m ∧ Squarefree m ∧
      canonicalLargestPrimeFactor m < canonicalCofactor m

/-- Integer Möbius mass of the nontrivial born-smooth population. -/
def squareRootAncestrySmoothMassInt (R : ℕ) : ℤ :=
  ∑ m ∈ squareRootAncestrySmoothIntegerSet R, (μ m : ℤ)

/-- Active smooth ancestry sources are exactly the native squarefree integers
in smooth canonical orientation. -/
theorem activeSmoothSource_sum_eq_smoothIntegerMass
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    (∑ s ∈ activeSmoothSourceSet B (R - 1), sourceWeight s) =
      squareRootAncestrySmoothMassInt R := by
  classical
  unfold squareRootAncestrySmoothMassInt
  refine Finset.sum_bij (fun s _hs => sourceProduct s) ?_ ?_ ?_ ?_
  · intro s hs
    have hsdata : SmoothOriented s ∧ sourceClock B s ≤ R - 1 := by
      simpa [activeSmoothSourceSet] using hs
    have hadm : SourceAdmissible s := hsdata.1.1
    have hprodle : sourceProduct s ≤ squareRootEndpoint R := by
      have hclock :=
        (sourceClock_le_iff_sourceProduct_le_endpoint
          (x := R - 1) s).1 hsdata.2
      simpa [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)] using hclock
    have hprodgt : 1 < sourceProduct s :=
      one_lt_sourceProduct_of_admissible hadm
    have hprod2 : 2 ≤ sourceProduct s := by omega
    have hsq : Squarefree (sourceProduct s) :=
      sourceProduct_squarefree_of_admissible hadm
    have horient :
        canonicalLargestPrimeFactor (sourceProduct s) <
          canonicalCofactor (sourceProduct s) := by
      rw [← sourcePrime_eq_canonicalLargestPrimeFactor s hadm,
        ← sourceCore_eq_canonicalCofactor s hadm]
      exact hsdata.1.2
    apply Finset.mem_filter.mpr
    refine ⟨?_, hprod2, hsq, horient⟩
    unfold cumulativeSquarePrefixSet
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
    have hXlt : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      have hsqpos : 0 < R ^ 2 := by positivity
      omega
    exact Finset.mem_range.mpr (lt_of_le_of_lt hprodle hXlt)
  · intro s₁ hs₁ s₂ hs₂ heq
    have h₁ : SmoothOriented s₁ ∧ sourceClock B s₁ ≤ R - 1 := by
      simpa [activeSmoothSourceSet] using hs₁
    have h₂ : SmoothOriented s₂ ∧ sourceClock B s₂ ≤ R - 1 := by
      simpa [activeSmoothSourceSet] using hs₂
    exact sourceProduct_injective_on_admissible h₁.1.1 h₂.1.1 heq
  · intro m hm
    have hmdata :
        m ∈ cumulativeSquarePrefixSet (R - 1) ∧
          2 ≤ m ∧ Squarefree m ∧
            canonicalLargestPrimeFactor m < canonicalCofactor m := by
      simpa [squareRootAncestrySmoothIntegerSet] using hm
    have hmgt : 1 < m := by omega
    have hm_lt_sq : m < R ^ 2 := by
      simpa [cumulativeSquarePrefixSet,
        Nat.sub_add_cancel (by omega : 1 ≤ R)] using hmdata.1
    have hmend : m ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      have hsqpos : 0 < R ^ 2 := by positivity
      omega
    have hmB : m ≤ B := hmend.trans hB
    let s := canonicalSourceIndex B m hmdata.2.2.1 hmgt hmB
    have hadm : SourceAdmissible s :=
      canonicalSourceIndex_admissible hmdata.2.2.1 hmgt hmB
    have hprod : sourceProduct s = m :=
      canonicalSourceIndex_product hmdata.2.2.1 hmgt hmB
    have hqeq := sourcePrime_eq_canonicalLargestPrimeFactor s hadm
    have hceq := sourceCore_eq_canonicalCofactor s hadm
    rw [hprod] at hqeq hceq
    have hsmooth : SmoothOriented s := by
      refine ⟨hadm, ?_⟩
      rw [hqeq, hceq]
      exact hmdata.2.2.2
    have hclock : sourceClock B s ≤ R - 1 := by
      apply (sourceClock_le_iff_sourceProduct_le_endpoint
        (x := R - 1) s).2
      rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega), hprod]
      exact hmend
    refine ⟨s, ?_, hprod⟩
    simp [activeSmoothSourceSet, hsmooth, hclock]
  · intro s hs
    have hsdata : SmoothOriented s ∧ sourceClock B s ≤ R - 1 := by
      simpa [activeSmoothSourceSet] using hs
    exact sourceWeight_of_admissible s hsdata.1.1

/-- Integer version of the square-root born-smooth mass. -/
def squareRootBornSmoothMassInt (R : ℕ) : ℤ :=
  ∑ m ∈ cumulativeSquarePrefixSet (R - 1),
    if canonicalLargestPrimeFactor m ≤ R ∧
        canonicalLargestPrimeFactor m ≤ canonicalCofactor m then
      (μ m : ℤ)
    else
      0

/-- The integer born-smooth mass casts to the existing complex-valued object. -/
theorem squareRootBornSmoothMassInt_cast (R : ℕ) :
    ((squareRootBornSmoothMassInt R : ℤ) : ℂ) =
      squareRootBornSmoothMass R := by
  unfold squareRootBornSmoothMassInt squareRootBornSmoothMass
    canonicalMoebiusWeight
  push_cast
  rfl

/-- On every nontrivial squarefree source below `R^2`, the born-smooth
predicate is exactly strict smooth orientation. -/
private theorem bornSmooth_iff_smoothOrientation
    {R m : ℕ} (hR : 2 ≤ R)
    (hm : m ∈ cumulativeSquarePrefixSet (R - 1))
    (hm2 : 2 ≤ m) (hsq : Squarefree m) :
    (canonicalLargestPrimeFactor m ≤ R ∧
      canonicalLargestPrimeFactor m ≤ canonicalCofactor m) ↔
      canonicalLargestPrimeFactor m < canonicalCofactor m := by
  have hmgt : 1 < m := by omega
  constructor
  · rintro ⟨_hqR, hqc⟩
    have hne : canonicalLargestPrimeFactor m ≠ canonicalCofactor m := by
      intro heq
      apply canonicalLargestPrimeFactor_not_dvd_cofactor hsq hmgt
      rw [heq]
    exact lt_of_le_of_ne hqc hne
  · intro hqc
    refine ⟨?_, hqc.le⟩
    have hm_lt : m < R * R := by
      simpa [cumulativeSquarePrefixSet,
        Nat.sub_add_cancel (by omega : 1 ≤ R), pow_two] using hm
    have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
    by_contra hnot
    have hRq : R < canonicalLargestPrimeFactor m := Nat.lt_of_not_ge hnot
    nlinarith

/-- The sole difference between born-smooth mass and the smooth ancestry source
population is the exceptional Möbius term `m = 1`. -/
theorem squareRootBornSmoothMassInt_eq_one_add_smoothMassInt
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootBornSmoothMassInt R =
      1 + squareRootAncestrySmoothMassInt R := by
  classical
  let S := cumulativeSquarePrefixSet (R - 1)
  let bornTerm : ℕ → ℤ := fun m =>
    if canonicalLargestPrimeFactor m ≤ R ∧
        canonicalLargestPrimeFactor m ≤ canonicalCofactor m then
      (μ m : ℤ)
    else 0
  let smoothTerm : ℕ → ℤ := fun m =>
    if 2 ≤ m ∧ Squarefree m ∧
        canonicalLargestPrimeFactor m < canonicalCofactor m then
      (μ m : ℤ)
    else 0
  have h1mem : 1 ∈ S := by
    dsimp [S, cumulativeSquarePrefixSet]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
    simp
    nlinarith
  have hR1 : 1 ≤ R := by omega
  have hborn1 : bornTerm 1 = 1 := by
    simp [bornTerm, canonicalLargestPrimeFactor, canonicalCofactor, hR1]
  have hsmooth1 : smoothTerm 1 = 0 := by
    simp [smoothTerm]
  have hterms : ∀ m ∈ S.erase 1, bornTerm m = smoothTerm m := by
    intro m hm
    have hmS : m ∈ S := (Finset.mem_erase.mp hm).2
    have hmne : m ≠ 1 := (Finset.mem_erase.mp hm).1
    by_cases hm2 : 2 ≤ m
    · by_cases hsq : Squarefree m
      · have hiff := bornSmooth_iff_smoothOrientation hR hmS hm2 hsq
        simp [bornTerm, smoothTerm, hm2, hsq, hiff]
      · have hzero : (μ m : ℤ) = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        simp [bornTerm, smoothTerm, hsq, hzero]
    · have hm0 : m = 0 := by omega
      subst m
      simp [bornTerm, smoothTerm, canonicalLargestPrimeFactor,
        canonicalCofactor]
  have hbornSplit :
      (∑ m ∈ S, bornTerm m) =
        1 + ∑ m ∈ S.erase 1, smoothTerm m := by
    calc
      (∑ m ∈ S, bornTerm m) =
          bornTerm 1 + ∑ m ∈ S.erase 1, bornTerm m :=
        (Finset.add_sum_erase S bornTerm h1mem).symm
      _ = 1 + ∑ m ∈ S.erase 1, smoothTerm m := by
        rw [hborn1]
        apply congrArg (fun z : ℤ => 1 + z)
        apply Finset.sum_congr rfl
        exact hterms
  have hsmoothErase :
      (∑ m ∈ S.erase 1, smoothTerm m) = ∑ m ∈ S, smoothTerm m := by
    have h := Finset.add_sum_erase S smoothTerm h1mem
    rw [hsmooth1, zero_add] at h
    exact h
  unfold squareRootBornSmoothMassInt squareRootAncestrySmoothMassInt
    squareRootAncestrySmoothIntegerSet
  change (∑ m ∈ S, bornTerm m) =
    1 + ∑ m ∈ S.filter (fun m =>
      2 ≤ m ∧ Squarefree m ∧
        canonicalLargestPrimeFactor m < canonicalCofactor m), (μ m : ℤ)
  rw [hbornSplit, hsmoothErase]
  congr 1
  unfold smoothTerm
  rw [Finset.sum_filter]

/-- Exact successor identification.  The `+1` is the source `m=1`, which is
present in the square-root smooth mass but intentionally absent from the
canonical ancestry universe. -/
theorem sourceSuccessorPrefix_cast_eq_one_sub_bornSmooth
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    ((sourceSuccessorPrefix B (R - 1) : ℤ) : ℂ) =
      1 - squareRootBornSmoothMass R := by
  rw [sourceSuccessorPrefix_eq_neg_activeSmooth_sum,
    activeSmoothSource_sum_eq_smoothIntegerMass hR hB]
  have hborn := squareRootBornSmoothMassInt_eq_one_add_smoothMassInt R hR
  have hcast := squareRootBornSmoothMassInt_cast R
  rw [← hcast, hborn]
  push_cast
  ring_nf

/-- The ancestry root is literally the positive-orientation smooth mass minus
the square-root transport mass.  This follows by comparing the exact renewals,
now that the successor pieces have been identified. -/
theorem sourceRootPrefix_cast_eq_positiveSmooth_sub_transport
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    ((sourceRootPrefix B (R - 1) : ℤ) : ℂ) =
      squareRootPositiveSmoothMass R - squareRootTransportPrimeFirst R := by
  have hrenew := sourcePrefix_renewal B (R - 1)
  have hsource := sourcePrefix_add_one_eq_squarePrefixMertens
    (B := B) (x := R - 1) (by omega)
    (by simpa [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)] using hB)
  have hsucc := sourceSuccessorPrefix_cast_eq_one_sub_bornSmooth hR hB
  have hsquare := squarePrefixMertens_eq_positiveSmooth_add_matched R (by omega)
  have hmatched :
      squareRootMatchedBornSmoothTransport R =
        squareRootBornSmoothMass R - squareRootTransportPrimeFirst R := rfl
  have hrenew' :
      ((sourcePrefix B (R - 1) : ℤ) : ℂ) =
        ((sourceRootPrefix B (R - 1) : ℤ) : ℂ) -
          ((sourceSuccessorPrefix B (R - 1) : ℤ) : ℂ) := by
    change ((sourcePrefix B (R - 1) : ℤ) : ℂ) =
      ((clockPushforward (sourceClock B) (R - 1)
        (boundedSourceFlow B).rootField : ℤ) : ℂ) -
      ((clockPushforward (sourceClock B) (R - 1)
        ((boundedSourceFlow B).successorOperator
          (boundedSourceFlow B).weight) : ℤ) : ℂ)
    rw [← Int.cast_sub]
    exact_mod_cast hrenew
  rw [hmatched] at hsquare
  rw [hrenew', hsucc] at hsource
  rw [hsquare] at hsource
  linear_combination hsource

/-- Final term-by-term identification of the two exact decompositions. -/
theorem squareRootAncestryRenewal_terms
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    ((sourceRootPrefix B (R - 1) : ℤ) : ℂ) =
        squareRootPositiveSmoothMass R - squareRootTransportPrimeFirst R ∧
    ((sourceSuccessorPrefix B (R - 1) : ℤ) : ℂ) =
        1 - squareRootBornSmoothMass R :=
  ⟨sourceRootPrefix_cast_eq_positiveSmooth_sub_transport hR hB,
    sourceSuccessorPrefix_cast_eq_one_sub_bornSmooth hR hB⟩

end RHLean.Proof
