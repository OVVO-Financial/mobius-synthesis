import RHLean.Proof.WheelToLedgerEquivariance
import RHLean.Proof.LowWheelHighPrimeSurvivor

/-!
# Pushforward of the ancestry cross ledger to ordered wheel edges

The equivariance module identifies the precise wheel move that commutes with the
canonical ancestry parent: a fresh core prime must be inserted above every prime
already present in the core.  This file proves the converse realization and then
reindexes the full root-successor cross ledger through those ordered moves.
Thus the final identity is a transport theorem on finite signed configurations,
not an analytic estimate.

No norm, asymptotic estimate, Strong Mertens input, or RH hypothesis appears.
The only operation is an exact finite reindexing before absolute values.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

/-- Read an admissible ancestry source back as its bounded wheel factor pair. -/
def sourceToWheelFactor {B : ℕ} (s : SourceIndex B)
    (h : SourceAdmissible s) : WheelFactorConfiguration B where
  q := sourcePrime s
  c := sourceCore s
  data := h
  q_lt := s.1.2
  c_lt := s.2.2

/-- The factor carrier is lossless on admissible ancestry sources. -/
@[simp] theorem wheelToSource_sourceToWheelFactor {B : ℕ}
    (s : SourceIndex B) (h : SourceAdmissible s) :
    wheelToSource (sourceToWheelFactor s h) = s := by
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Fin.ext
    rfl

/-- Reverse one canonical ancestry parent edge into the corresponding wheel
fresh-prime insertion.  The inserted prime is exactly the largest prime stripped
from the child core by `sourceParent`. -/
noncomputable def ancestryParentWheelMove {B : ℕ}
    (s : SourceIndex B) (h : SmoothOriented s) : WheelFreshPrimeMove B := by
  have hcgt : 1 < sourceCore s := lt_trans h.1.1.one_lt h.2
  exact
    { parent := sourceToWheelFactor (parentIndex s h) (parentIndex_admissible s h)
      child := sourceToWheelFactor s h.1
      freshPrime := canonicalLargestPrimeFactor (sourceCore s)
      freshPrime_prime := canonicalLargestPrimeFactor_prime hcgt
      same_distinguished := by
        simp [sourceToWheelFactor]
      child_core := by
        change sourceCore s =
          sourceCore (parentIndex s h) *
            canonicalLargestPrimeFactor (sourceCore s)
        rw [sourceCore_parentIndex]
        exact (canonicalCofactor_mul_largestPrimeFactor hcgt).symm
      fresh := by
        change ¬ canonicalLargestPrimeFactor (sourceCore s) ∣
          sourceCore (parentIndex s h)
        rw [sourceCore_parentIndex]
        exact canonicalLargestPrimeFactor_not_dvd_cofactor h.1.2.2.1 hcgt
      child_smooth := by
        simpa [sourceToWheelFactor] using h.2 }

/-- Every canonical ancestry parent edge is an ordered wheel insertion. -/
theorem ancestryParentWheelMove_ordered {B : ℕ}
    (s : SourceIndex B) (h : SmoothOriented s) :
    WheelFreshPrimeMove.Ordered (ancestryParentWheelMove s h) := by
  apply (WheelFreshPrimeMove.inserted_is_top_iff_ordered
    (ancestryParentWheelMove s h)).1
  rfl

/-- The reverse construction recovers the original child carrier. -/
@[simp] theorem ancestryParentWheelMove_child_source {B : ℕ}
    (s : SourceIndex B) (h : SmoothOriented s) :
    wheelToSource (ancestryParentWheelMove s h).child = s := by
  simp [ancestryParentWheelMove]

/-- The reverse construction recovers the original ancestry parent. -/
@[simp] theorem ancestryParentWheelMove_parent_source {B : ℕ}
    (s : SourceIndex B) (h : SmoothOriented s) :
    wheelToSource (ancestryParentWheelMove s h).parent = parentIndex s h := by
  simp [ancestryParentWheelMove]

/-- **Converse equivariance.**  Every legal ancestry parent edge is literally
the image of an ordered fresh-prime wheel move. -/
theorem smoothSource_parentEdge_is_orderedWheelMove {B : ℕ}
    (s : SourceIndex B) (h : SmoothOriented s) :
    ∃ m : WheelFreshPrimeMove B,
      WheelFreshPrimeMove.Ordered m ∧
      wheelToSource m.child = s ∧
      wheelToSource m.parent = parentIndex s h := by
  exact ⟨ancestryParentWheelMove s h,
    ancestryParentWheelMove_ordered s h,
    ancestryParentWheelMove_child_source s h,
    ancestryParentWheelMove_parent_source s h⟩

/-- Finite root-by-child carrier set.  Each second coordinate is an active
smooth child and hence, by `smoothSource_parentEdge_is_orderedWheelMove`, carries
one canonical ordered fresh-prime wheel edge. -/
def orderedWheelCrossConfigurationSet (B R : ℕ) :
    Finset (SourceIndex B × SourceIndex B) :=
  (activeRootSourceSet B (R - 1)).product
    (activeSmoothSourceSet B (R - 1))

/-- Signed contribution attached to one transported root/ordered-edge pair.
The negative child weight is exactly the parent weight along that edge. -/
def orderedWheelCrossSignedContribution {B : ℕ}
    (x : SourceIndex B × SourceIndex B) : ℤ :=
  sourceWeight x.1 * (-sourceWeight x.2)

/-- Total signed wheel-side cross ledger after transport to the common `(q,c)`
carrier. -/
def orderedWheelCrossLedger (B R : ℕ) : ℤ :=
  ∑ x ∈ orderedWheelCrossConfigurationSet B R,
    orderedWheelCrossSignedContribution x

/-- Every configuration in the transported finite set really does carry an
ordered wheel edge; no extra or nonchronological child is introduced by the
pushforward. -/
theorem orderedWheelCrossConfiguration_has_orderedMove
    {B R : ℕ} {x : SourceIndex B × SourceIndex B}
    (hx : x ∈ orderedWheelCrossConfigurationSet B R) :
    ∃ h : SmoothOriented x.2,
      WheelFreshPrimeMove.Ordered (ancestryParentWheelMove x.2 h) := by
  have hs : x.2 ∈ activeSmoothSourceSet B (R - 1) :=
    (Finset.mem_product.mp hx).2
  have hsdata : SmoothOriented x.2 ∧ sourceClock B x.2 ≤ R - 1 := by
    simpa [activeSmoothSourceSet] using hs
  exact ⟨hsdata.1, ancestryParentWheelMove_ordered x.2 hsdata.1⟩

/-- On an active smooth child, the transported wheel-parent weight is exactly
`-sourceWeight child`, so the cross contribution above is genuinely the
root-by-parent contribution used by the source ledger. -/
theorem orderedWheelParentWeight_eq_neg_childWeight
    {B : ℕ} (s : SourceIndex B) (h : SmoothOriented s) :
    wheelSignedWeight (ancestryParentWheelMove s h).parent =
      -sourceWeight s := by
  have hparent : sourceParent s = some (parentIndex s h) :=
    smoothSource_has_parent s h
  have hsign := sourceWeight_signReversal s (parentIndex s h) hparent
  have hparentWeight : sourceWeight (parentIndex s h) = -sourceWeight s := by
    linarith
  calc
    wheelSignedWeight (ancestryParentWheelMove s h).parent =
        sourceWeight
          (wheelToSource (ancestryParentWheelMove s h).parent) :=
      (sourceWeight_wheelToSource _).symm
    _ = sourceWeight (parentIndex s h) := by
      rw [ancestryParentWheelMove_parent_source]
    _ = -sourceWeight s := hparentWeight

/-- **Pushforward ledger identity.**  The complete parent-fibre cross ledger is
exactly the signed sum over root configurations crossed with the canonical
ordered fresh-prime wheel edges.  The equality is taken before any norm or
absolute value. -/
theorem squareRootRootSuccessorCrossLedger_eq_orderedWheelCrossLedger
    (B R : ℕ) :
    squareRootRootSuccessorCrossLedger B R =
      orderedWheelCrossLedger B R := by
  rw [squareRootRootSuccessorCrossLedger_eq_mul,
    sourceRootPrefix_eq_activeRoot_sum,
    sourceSuccessorPrefix_eq_neg_activeSmooth_sum]
  unfold orderedWheelCrossLedger orderedWheelCrossConfigurationSet
    orderedWheelCrossSignedContribution
  simp [Finset.sum_product, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_neg_distrib]
  exact Finset.sum_comm

end RHLean.Proof