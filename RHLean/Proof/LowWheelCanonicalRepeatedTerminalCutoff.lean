import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification
import RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell

/-!
# Exact cutoff split of the repeated-parent terminal boundary

The repository's `primesUpTo R` convention is inclusive at `R`.  Consequently
a terminal repeated-parent state with fresh pivot `p = R` can still move `p`
into the Boolean face.  The actual outside-wheel obstruction is therefore
`R < p`, not `R <= p`.

This file records that endpoint exactly before any mate ledger is formed.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Terminal states whose fresh pivot is still an available low-wheel Boolean
coordinate.  Equality `p = R` belongs here because `primesUpTo R` is inclusive. -/
def lowWheelCanonicalRepeatedTerminalInternalPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedTerminalBoundary R).filter fun y =>
    lowWheelTaggedDowncrossPivot y ≤ R

/-- Literal terminal states whose fresh pivot lies outside the low-wheel cube. -/
def lowWheelCanonicalRepeatedTerminalExternalPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedTerminalBoundary R).filter fun y =>
    R < lowWheelTaggedDowncrossPivot y

/-- The terminal boundary splits exactly at the inclusive low-wheel cutoff. -/
theorem lowWheelCanonicalRepeatedTerminal_eq_internal_union_external
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalBoundary R =
      lowWheelCanonicalRepeatedTerminalInternalPart R ∪
        lowWheelCanonicalRepeatedTerminalExternalPart R := by
  ext y
  constructor
  · intro hy
    by_cases hle : lowWheelTaggedDowncrossPivot y ≤ R
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hy, hle⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, Nat.lt_of_not_ge hle⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · exact (Finset.mem_filter.mp hy).1

/-- The two terminal cutoff pieces are disjoint. -/
theorem lowWheelCanonicalRepeatedTerminalInternal_disjoint_external
    (R : ℕ) :
    Disjoint
      (lowWheelCanonicalRepeatedTerminalInternalPart R)
      (lowWheelCanonicalRepeatedTerminalExternalPart R) := by
  rw [Finset.disjoint_left]
  intro y hyI hyE
  have hle := (Finset.mem_filter.mp hyI).2
  have hlt := (Finset.mem_filter.mp hyE).2
  omega

/-- Every internal terminal pivot is literally a coordinate of `primesUpTo R`.
In particular the endpoint `p = R` is internal whenever `R` is prime. -/
theorem lowWheelCanonicalRepeatedTerminalInternal_pivot_mem_primesUpTo
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelTaggedDowncrossPivot y ∈ primesUpTo R := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have hle := (Finset.mem_filter.mp hy).2
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  exact mem_primesUpTo.mpr ⟨hgeom.2.2.1, hle⟩

/-- Conversely every external terminal pivot is absent from `primesUpTo R`. -/
theorem lowWheelCanonicalRepeatedTerminalExternal_pivot_not_mem_primesUpTo
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalExternalPart R) :
    lowWheelTaggedDowncrossPivot y ∉ primesUpTo R := by
  intro hmem
  have hle := (mem_primesUpTo.mp hmem).2
  have hlt := (Finset.mem_filter.mp hy).2
  omega

/-- The external terminal population is a literal native first-failure boundary
for the fresh prime `p`, with no unnamed remainder. -/
theorem lowWheelCanonicalRepeatedTerminalExternal_mem_firstFailureBoundary
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalExternalPart R) :
    y.1 ∈ primeProductFirstFailureBoundary
      (insert (lowWheelTaggedDowncrossPivot y) (primesUpTo R)) R
      (lowWheelTaggedDowncrossPivot y) := by
  let p := lowWheelTaggedDowncrossPivot y
  have hterminal := (Finset.mem_filter.mp hy).1
  have hlt : R < p := by simpa [p] using (Finset.mem_filter.mp hy).2
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  have hp : p.Prime := by simpa [p] using hgeom.2.2.1
  have hpNot : p ∉ primesUpTo R := by
    intro hmem
    have hpLe := (mem_primesUpTo.mp hmem).2
    omega
  have herase : (insert p (primesUpTo R)).erase p = primesUpTo R := by
    simp [hpNot]
  have hfrozen := (Finset.mem_filter.mp hterminal).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier
  have htSub : y.1 ⊆ primesUpTo R := Finset.mem_powerset.mp htag.1
  rw [mem_primeProductFirstFailureBoundary, herase]
  refine ⟨htSub, hgeom.2.2.2.2.1, ?_⟩
  exact hgeom.2.2.2.2.2

end RHLean.Proof
