import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalCutoff
import RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger

/-!
# Existing physical mate for the internal repeated-parent terminal boundary

For a terminal state `y = (t,(1,p))` with `p <= R`, the prime `p` is still a
literal coordinate of the inclusive low-wheel cube.  Move that fresh prime into
the Boolean face and collapse the quotient:

`(t,(1,p)) -> (insert p t,(1,1))`.

The first-crossing inequalities are exactly what is needed for the mate to lie
in the already-existing physical transport ledger.  The cofactor remains one
and the Boolean sign flips once.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Terminal low-wheel mate obtained by moving the fresh prime into the Boolean
face. -/
def lowWheelCanonicalRepeatedTerminalInternalMate
    (y : LowWheelTaggedDowncrossState) : LowWheelTaggedCofactorQuotientState :=
  (insert (lowWheelTaggedDowncrossPivot y) y.1, (1, 1))

/-- On the internal terminal part, the fresh pivot is absent from the old face. -/
theorem lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelTaggedDowncrossPivot y ∉ y.1 := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  intro hpMem
  have hlt := hgeom.2.2.2.1 _ hpMem
  exact Nat.lt_irrefl _ hlt

/-- The terminal mate is a literal occurrence of the existing physical
transport ledger. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_mem_transport
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelCanonicalRepeatedTerminalInternalMate y ∈
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  let p := lowWheelTaggedDowncrossPivot y
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  have hp : p.Prime := by simpa [p] using hgeom.2.2.1
  have hpMem : p ∈ primesUpTo R := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_mem_primesUpTo hy
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  have hfrozen := (Finset.mem_filter.mp hterminal).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hfaceMate : insert p y.1 ∈ (primesUpTo R).powerset := by
    apply Finset.mem_powerset.mpr
    exact Finset.insert_subset hpMem (Finset.mem_powerset.mp htag.1)
  have hphysSource := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hsourceCarrier :=
    (mem_lowWheelCanonicalPhysicalStateSet.mp hphysSource).2.2.2
  have hRgt : 1 < R := by
    have hcR := hsourceCarrier.2.1
    simpa [hgeom.1] using hcR
  have hprodInsert : primeFaceProduct (insert p y.1) = p * primeFaceProduct y.1 := by
    simp [primeFaceProduct, hpNotFace]
  have hmateCarrier : LowWheelTransportPairCarrier R (insert p y.1) (1, 1) := by
    refine ⟨by simp, hRgt, ?_, ?_⟩
    · rw [hprodInsert]
      simpa [Nat.mul_comm] using hgeom.2.2.2.2.2
    · have htop := hsourceCarrier.2.2.2
      rw [hgeom.1, hgeom.2.1] at htop
      rw [hprodInsert]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htop
  have hranges := lowWheelTransportPairCarrier_mem_ranges hmateCarrier
  have hmatePhysical : (1, 1) ∈
      lowWheelCanonicalPhysicalStateSet R (insert p y.1) := by
    exact mem_lowWheelCanonicalPhysicalStateSet.mpr
      ⟨hranges.1, hranges.2, squarefree_one, hmateCarrier⟩
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  simpa [lowWheelCanonicalRepeatedTerminalInternalMate, p] using
    And.intro hfaceMate hmatePhysical

/-- Moving the fresh prime into the Boolean face reverses exactly one Boolean
sign, hence the terminal source and existing mate have opposite weights. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_weight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelTaggedCanonicalWeight
        (lowWheelCanonicalRepeatedTerminalInternalMate y) =
      -lowWheelTaggedCanonicalWeight (y.1, y.2) := by
  let p := lowWheelTaggedDowncrossPivot y
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  have hc : y.2.1 = 1 := hgeom.1
  have hsign : booleanCubeSign (insert p y.1) = -booleanCubeSign y.1 := by
    simp [booleanCubeSign, hpNotFace, pow_succ]
  simp [lowWheelTaggedCanonicalWeight,
    lowWheelCanonicalRepeatedTerminalInternalMate, hc, p, hsign]

/-- The mate is pointwise distinct from the terminal source because the fresh
prime was not already in the old Boolean face. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_ne
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelCanonicalRepeatedTerminalInternalMate y ≠ (y.1, y.2) := by
  let p := lowWheelTaggedDowncrossPivot y
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  intro heq
  have hface := congrArg Prod.fst heq
  change insert p y.1 = y.1 at hface
  have hpInsert : p ∈ insert p y.1 := Finset.mem_insert_self p y.1
  rw [hface] at hpInsert
  exact hpNotFace hpInsert

end RHLean.Proof
