import Mathlib
import RHLean.Proof.CreationResponseOthelloInvolution
import RHLean.Proof.SquareRootLowPrimeResponseForest

/-!
# Response-forest Othello involution

Internal response atoms are not independent residuals.  An internal born atom
`z = (c,q)` has arithmetic child `c*q`, which is another owned response
cofactor.  Pair the atom with that child cofactor and leave every other tagged
state fixed.

The generic creation/response Othello involution already supplies the matching
kernel.  This file instantiates it on the actual response forest and identifies
its stable set exactly as

* born exit atoms;
* post-root response atoms;
* response-root cofactors with no incoming internal born edge.

No estimate or new arithmetic carrier is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Tagged atom/cofactor universe of the response forest. -/
def squareRootLowPrimeResponseForestOthelloCarrier
    (R K U : ℕ) : Finset (Sum (ℕ × ℕ) ℕ) :=
  creationResponseOthelloCarrier
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    (squareRootLowPrimeOwnedResponseCofactors R K U)

/-- Atom side is oriented against its arithmetic child; cofactor side keeps its
native Möbius orientation. -/
def squareRootLowPrimeResponseForestOthelloWeight :
    Sum (ℕ × ℕ) ℕ → ℤ
  | .inl z => -μ (squareRootLowPrimeBadAtomChild z)
  | .inr c => μ c

/-- Internal born atom to its unique arithmetic child cofactor. -/
def squareRootLowPrimeResponseForestOthelloMate
    (R K U : ℕ) : Sum (ℕ × ℕ) ℕ → Sum (ℕ × ℕ) ℕ :=
  creationResponseOthelloMate
    (squareRootLowPrimeBornInternalAtoms R K U)
    squareRootLowPrimeBadAtomChild

/-- The response-forest mate preserves its tagged carrier. -/
theorem squareRootLowPrimeResponseForestOthelloMate_mem
    {R K U : ℕ} (hUR : U < R)
    {x : Sum (ℕ × ℕ) ℕ}
    (hx : x ∈ squareRootLowPrimeResponseForestOthelloCarrier R K U) :
    squareRootLowPrimeResponseForestOthelloMate R K U x ∈
      squareRootLowPrimeResponseForestOthelloCarrier R K U := by
  unfold squareRootLowPrimeResponseForestOthelloCarrier
    squareRootLowPrimeResponseForestOthelloMate
  apply creationResponseOthelloMate_mem
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    (squareRootLowPrimeBornInternalAtoms R K U)
    (squareRootLowPrimeOwnedResponseCofactors R K U)
    squareRootLowPrimeBadAtomChild
  · intro z hz
    exact (mem_squareRootLowPrimeBornInternalAtoms.mp hz).1
  · intro z hz
    exact squareRootLowPrimeBornInternalChildren_subset_ownedResponseCofactors
      hUR (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  · exact hx

/-- The response-forest mate is involutive. -/
theorem squareRootLowPrimeResponseForestOthelloMate_involutive
    {R K U : ℕ} (hUR : U < R) (x : Sum (ℕ × ℕ) ℕ) :
    squareRootLowPrimeResponseForestOthelloMate R K U
        (squareRootLowPrimeResponseForestOthelloMate R K U x) = x := by
  unfold squareRootLowPrimeResponseForestOthelloMate
  exact creationResponseOthelloMate_involutive
    (squareRootLowPrimeBornInternalAtoms R K U)
    squareRootLowPrimeBadAtomChild
    (squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms hUR) x

/-- Every moved response-forest edge reverses the tagged integer weight. -/
theorem squareRootLowPrimeResponseForestOthelloMate_weight_neg
    {R K U : ℕ} (hUR : U < R)
    (x : Sum (ℕ × ℕ) ℕ)
    (hne : squareRootLowPrimeResponseForestOthelloMate R K U x ≠ x) :
    squareRootLowPrimeResponseForestOthelloWeight
        (squareRootLowPrimeResponseForestOthelloMate R K U x) =
      -squareRootLowPrimeResponseForestOthelloWeight x := by
  have hne' :
      creationResponseOthelloMate
          (squareRootLowPrimeBornInternalAtoms R K U)
          squareRootLowPrimeBadAtomChild x ≠ x := by
    simpa [squareRootLowPrimeResponseForestOthelloMate] using hne
  have h := creationResponseOthelloMate_weight_neg
    (squareRootLowPrimeBornInternalAtoms R K U)
    squareRootLowPrimeBadAtomChild
    (fun z => -μ (squareRootLowPrimeBadAtomChild z))
    (fun c => μ c)
    (squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms hUR)
    (by
      intro z _hz
      simp)
    x hne'
  have hweight :
      squareRootLowPrimeResponseForestOthelloWeight =
        creationResponseOthelloWeight
          (fun z => -μ (squareRootLowPrimeBadAtomChild z))
          (fun c => μ c) := by
    funext y
    rcases y with z | c <;> rfl
  rw [hweight]
  simpa only [squareRootLowPrimeResponseForestOthelloMate] using h

/-- Explicit stable boundary of the response forest. -/
def squareRootLowPrimeResponseForestOthelloBoundary
    (R K U : ℕ) : Finset (Sum (ℕ × ℕ) ℕ) :=
  ((squareRootLowPrimeBornFrontierAtoms R K U ∪
      squareRootLowPrimePostRootResponseAtoms R K U).map
        ⟨Sum.inl, Sum.inl_injective⟩) ∪
    (squareRootLowPrimeResponseRootCofactors R K U).map
      ⟨Sum.inr, Sum.inr_injective⟩

private theorem squareRootLowPrimeOwnedResponseAtoms_sdiff_internal_eq_boundaryAtoms
    (R K U : ℕ) :
    squareRootLowPrimeOwnedResponseAtoms R K U \
        squareRootLowPrimeBornInternalAtoms R K U =
      squareRootLowPrimeBornFrontierAtoms R K U ∪
        squareRootLowPrimePostRootResponseAtoms R K U := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_sdiff.mp hz with ⟨hzOwned, hzNotInternal⟩
    rw [squareRootLowPrimeOwnedResponseAtoms_eq_born_union_postRoot] at hzOwned
    rcases Finset.mem_union.mp hzOwned with hzBorn | hzPost
    · rw [squareRootLowPrimeBornResponseAtoms_eq_internal_union_frontier]
        at hzBorn
      rcases Finset.mem_union.mp hzBorn with hzInternal | hzFront
      · exact (hzNotInternal hzInternal).elim
      · exact Finset.mem_union.mpr (Or.inl hzFront)
    · exact Finset.mem_union.mpr (Or.inr hzPost)
  · intro hz
    rcases Finset.mem_union.mp hz with hzFront | hzPost
    · have hzFrontData := mem_squareRootLowPrimeBornFrontierAtoms.mp hzFront
      have hzBorn : z ∈ squareRootLowPrimeBornResponseAtoms R K U :=
        mem_squareRootLowPrimeBornResponseAtoms.mpr
          ⟨hzFrontData.1, hzFrontData.2.1⟩
      apply Finset.mem_sdiff.mpr
      constructor
      · rw [squareRootLowPrimeOwnedResponseAtoms_eq_born_union_postRoot]
        exact Finset.mem_union.mpr (Or.inl hzBorn)
      · intro hzInternal
        exact (Finset.disjoint_left.mp
          (squareRootLowPrimeBornInternalAtoms_disjoint_frontier R K U))
          hzInternal hzFront
    · apply Finset.mem_sdiff.mpr
      constructor
      · rw [squareRootLowPrimeOwnedResponseAtoms_eq_born_union_postRoot]
        exact Finset.mem_union.mpr (Or.inr hzPost)
      · intro hzInternal
        have hzBorn : z ∈ squareRootLowPrimeBornResponseAtoms R K U :=
          mem_squareRootLowPrimeBornResponseAtoms.mpr
            ⟨(mem_squareRootLowPrimeBornInternalAtoms.mp hzInternal).1,
              (mem_squareRootLowPrimeBornInternalAtoms.mp hzInternal).2.1⟩
        exact (Finset.disjoint_left.mp
          (squareRootLowPrimeBornResponseAtoms_disjoint_postRoot R K U))
          hzBorn hzPost

/-- **Stable-disc identification.**  The fixed set of the response-forest
Othello mate is exactly the three explicit endpoint classes. -/
theorem finiteOthelloStablePart_responseForest_eq_boundary
    {R K U : ℕ} (hUR : U < R) :
    finiteOthelloStablePart
        (squareRootLowPrimeResponseForestOthelloCarrier R K U)
        (squareRootLowPrimeResponseForestOthelloMate R K U) =
      squareRootLowPrimeResponseForestOthelloBoundary R K U := by
  unfold squareRootLowPrimeResponseForestOthelloCarrier
    squareRootLowPrimeResponseForestOthelloMate
  rw [finiteOthelloStablePart_creationResponse_eq_frontier
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    (squareRootLowPrimeBornInternalAtoms R K U)
    (squareRootLowPrimeOwnedResponseCofactors R K U)
    squareRootLowPrimeBadAtomChild]
  · unfold squareRootLowPrimeResponseForestOthelloBoundary
      creationResponseTaggedFrontier
      creationResponseMatchedImage
      squareRootLowPrimeResponseRootCofactors
    rw [squareRootLowPrimeOwnedResponseAtoms_sdiff_internal_eq_boundaryAtoms]
    rfl
  · intro z hz
    exact (mem_squareRootLowPrimeBornInternalAtoms.mp hz).1
  · exact squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms hUR

/-- The complete tagged forest mass is exactly the signed mass of its stable
root/exit boundary. -/
theorem squareRootLowPrimeResponseForestOthello_mass_eq_boundary
    {R K U : ℕ} (hUR : U < R) :
    (∑ x ∈ squareRootLowPrimeResponseForestOthelloCarrier R K U,
        squareRootLowPrimeResponseForestOthelloWeight x) =
      ∑ x ∈ squareRootLowPrimeResponseForestOthelloBoundary R K U,
        squareRootLowPrimeResponseForestOthelloWeight x := by
  rw [← finiteOthelloStablePart_responseForest_eq_boundary hUR]
  exact sum_finiteOthelloRegion_eq_stable
    (squareRootLowPrimeResponseForestOthelloCarrier R K U)
    (squareRootLowPrimeResponseForestOthelloMate R K U)
    squareRootLowPrimeResponseForestOthelloWeight
    (fun x hx => squareRootLowPrimeResponseForestOthelloMate_mem hUR hx)
    (fun x _hx => squareRootLowPrimeResponseForestOthelloMate_involutive hUR x)
    (fun x _hx hne =>
      squareRootLowPrimeResponseForestOthelloMate_weight_neg hUR x hne)

end RHLean.Proof
