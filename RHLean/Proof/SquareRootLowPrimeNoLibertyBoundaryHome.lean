import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary
import RHLean.Proof.SquareRootLowPrimeNoTogglePopulationBound
import RHLean.Proof.SquareRootLowPrimePartialPacketBoundary

/-!
# Canonical homes for the terminal no-liberty boundary

The square-root terminal normal form has four already-existing endpoint classes:

* one distinguished head;
* the compressed partial crossing packet;
* born response atoms with no successor;
* the exact Go root-equality boundary left after every strict crossing has its
  existing global transport mate.

The last class is the cross-coordinate point.  A root-equality incidence
`((r,q),d)` is not charged by its two prime owners.  The theorem
`squareRootLowPrimeGoRootEquality_parentProjection_injOn` proves that its parent
`d < R` recovers the complete incidence.  Thus the root endpoint contributes at
most one unit per canonical parent home.

No analytic input and no new arithmetic carrier occur below.  Both the terminal
normal form and its home space are tagged disjoint unions of endpoint carriers
already present in the repository.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Root homes are the integer parent slots strictly below `R`.  The zero slot
is harmless and keeps the cardinality definitionally equal to `R`; actual Go
root-equality incidences occupy positive parent slots. -/
def squareRootLowPrimeNoLibertyFailureRoots (R : ℕ) : Finset ℕ :=
  Finset.range R

/-- The requested tagged home type

`Head ⊔ PartialSeats ⊔ BornExit ⊔ FailureRoots`.
-/
abbrev SquareRootLowPrimeNoLibertyBoundaryHome :=
  Sum Unit (Sum ℕ (Sum (ℕ × ℕ) ℕ))

/-- The finite set of available canonical homes. -/
def squareRootLowPrimeNoLibertyBoundaryHomeSpace
    (R K j : ℕ) : Finset SquareRootLowPrimeNoLibertyBoundaryHome :=
  ({()} : Finset Unit).disjSum
    ((squareRootLowPrimePartialPacketBoundary R K j).disjSum
      ((squareRootLowPrimeBornNoSuccessorAtoms R K
          (squareRootBornPostTailLowPrimeCutoff R)).disjSum
        (squareRootLowPrimeNoLibertyFailureRoots R)))

/-- Exact cardinality of the tagged home space. -/
theorem card_squareRootLowPrimeNoLibertyBoundaryHomeSpace
    (R K j : ℕ) :
    (squareRootLowPrimeNoLibertyBoundaryHomeSpace R K j).card =
      1 +
        (squareRootLowPrimePartialPacketBoundary R K j).card +
        (squareRootLowPrimeBornNoSuccessorAtoms R K
          (squareRootBornPostTailLowPrimeCutoff R)).card + R := by
  simp [squareRootLowPrimeNoLibertyBoundaryHomeSpace,
    squareRootLowPrimeNoLibertyFailureRoots]
  omega

/-- **The four canonical home classes have total cardinality at most `4*R`.** -/
theorem squareRootLowPrimeNoLibertyBoundaryHomeSpace_card_le_four_root
    {R K j : ℕ} (hR : 1 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    (squareRootLowPrimeNoLibertyBoundaryHomeSpace R K j).card ≤ 4 * R := by
  have hpacket :=
    squareRootLowPrimePartialPacketBoundary_card_lt_depth
      (R := R) (K := K) (j := j) hV0 hVK
  have hborn :=
    squareRootLowPrimeBornNoSuccessorAtoms_card_le_two_root R K hR
  rw [card_squareRootLowPrimeNoLibertyBoundaryHomeSpace]
  omega

/-- Post-rematching processed-seat normal form.  The first three summands are
already literal terminal endpoints.  The last summand retains the complete Go
root-equality incidence until the home projection below forgets its redundant
prime-owner coordinates. -/
abbrev SquareRootLowPrimeProcessedSeatNoLibertyState :=
  Sum Unit (Sum ℕ (Sum (ℕ × ℕ) ((ℕ × ℕ) × ℕ)))

/-- The terminal no-liberty boundary after all strict Go crossings have been
reattached to their existing global transport mates.  Nothing is estimated in
this definition: it is the tagged union of the four surviving endpoint
populations. -/
def squareRootLowPrimeProcessedSeatNoLibertyBoundary
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedSeatNoLibertyState :=
  ({()} : Finset Unit).disjSum
    ((squareRootLowPrimePartialPacketBoundary R K j).disjSum
      ((squareRootLowPrimeBornNoSuccessorAtoms R K U).disjSum
        (squareRootLowPrimeGoRootEqualityDefectCarrier R)))

/-- Native real weight of one tagged no-liberty boundary endpoint.

This equips the exact four-class carrier above with the signed orientation
needed for the eventual second-involution mass theorem, without asserting that
mass theorem here. -/
def squareRootLowPrimeNoLibertyBoundaryWeight :
    SquareRootLowPrimeProcessedSeatNoLibertyState → ℝ
  | .inl _ => 1
  | .inr (.inl _) => -1
  | .inr (.inr (.inl z)) =>
      ((μ (squareRootLowPrimeBadAtomChild z) : ℤ) : ℝ)
  | .inr (.inr (.inr z)) =>
      ((μ (z.1.2 * z.2) : ℤ) : ℝ)

@[simp] theorem squareRootLowPrimeNoLibertyBoundaryWeight_head
    (u : Unit) :
    squareRootLowPrimeNoLibertyBoundaryWeight (.inl u) = 1 := rfl

@[simp] theorem squareRootLowPrimeNoLibertyBoundaryWeight_partial
    (s : ℕ) :
    squareRootLowPrimeNoLibertyBoundaryWeight (.inr (.inl s)) = -1 := rfl

@[simp] theorem squareRootLowPrimeNoLibertyBoundaryWeight_born
    (z : ℕ × ℕ) :
    squareRootLowPrimeNoLibertyBoundaryWeight (.inr (.inr (.inl z))) =
      ((μ (squareRootLowPrimeBadAtomChild z) : ℤ) : ℝ) := rfl

@[simp] theorem squareRootLowPrimeNoLibertyBoundaryWeight_rootEquality
    (z : (ℕ × ℕ) × ℕ) :
    squareRootLowPrimeNoLibertyBoundaryWeight (.inr (.inr (.inr z))) =
      ((μ (z.1.2 * z.2) : ℤ) : ℝ) := rfl

/-- Canonical home of one terminal unit.  Only the root-equality case forgets
coordinates: `((r,q),d)` is sent to `d`. -/
def squareRootLowPrimeNoLibertyBoundaryHome
    (_R _K _j : ℕ) :
    SquareRootLowPrimeProcessedSeatNoLibertyState →
      SquareRootLowPrimeNoLibertyBoundaryHome
  | .inl u => .inl u
  | .inr (.inl s) => .inr (.inl s)
  | .inr (.inr (.inl z)) => .inr (.inr (.inl z))
  | .inr (.inr (.inr z)) => .inr (.inr (.inr z.2))

/-- Every canonical terminal unit lands in the finite home space. -/
theorem squareRootLowPrimeNoLibertyBoundaryHome_mem
    {R K j : ℕ} {x : SquareRootLowPrimeProcessedSeatNoLibertyState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary
      R K j (squareRootBornPostTailLowPrimeCutoff R)) :
    squareRootLowPrimeNoLibertyBoundaryHome R K j x ∈
      squareRootLowPrimeNoLibertyBoundaryHomeSpace R K j := by
  rcases x with u | x
  · simp [squareRootLowPrimeProcessedSeatNoLibertyBoundary,
      squareRootLowPrimeNoLibertyBoundaryHome,
      squareRootLowPrimeNoLibertyBoundaryHomeSpace] at hx ⊢
  · rcases x with s | x
    · simpa [squareRootLowPrimeProcessedSeatNoLibertyBoundary,
        squareRootLowPrimeNoLibertyBoundaryHome,
        squareRootLowPrimeNoLibertyBoundaryHomeSpace] using hx
    · rcases x with z | w
      · simpa [squareRootLowPrimeProcessedSeatNoLibertyBoundary,
          squareRootLowPrimeNoLibertyBoundaryHome,
          squareRootLowPrimeNoLibertyBoundaryHomeSpace] using hx
      · have hw : w ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R := by
          simpa [squareRootLowPrimeProcessedSeatNoLibertyBoundary] using hx
        rcases w with ⟨⟨r, q⟩, d⟩
        rcases mem_squareRootLowPrimeGoRootEqualityDefectCarrier.mp hw with
          ⟨_hrR, _hqR, hdR, _hr, _hq, _hrq, _heq, _hcube, _hd⟩
        simp [squareRootLowPrimeNoLibertyBoundaryHome,
          squareRootLowPrimeNoLibertyBoundaryHomeSpace,
          squareRootLowPrimeNoLibertyFailureRoots, hdR]

/-- **Final canonical-home injectivity.**

Different terminal units cannot occupy the same canonical home.  The first
three tagged classes are injective by construction.  In the only nontrivial
case, equality of failure-root homes is equality of the Go parent coordinate;
the already-proved root-equality ownership theorem recovers both prime owners
and hence the complete incidence.
-/
theorem squareRootLowPrimeNoLibertyBoundaryHome_injOn
    (R K j : ℕ) :
    Set.InjOn
      (squareRootLowPrimeNoLibertyBoundaryHome R K j)
      (squareRootLowPrimeProcessedSeatNoLibertyBoundary
        R K j (squareRootBornPostTailLowPrimeCutoff R)) := by
  intro x hx y hy hxy
  rcases x with xu | x
  · rcases y with yu | y
    · cases xu
      cases yu
      rfl
    · rcases y with ys | y
      · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
      · rcases y with yz | yw
        · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
        · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
  · rcases x with xs | x
    · rcases y with yu | y
      · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
      · rcases y with ys | y
        · have hs : xs = ys := by
            simpa [squareRootLowPrimeNoLibertyBoundaryHome] using hxy
          subst ys
          rfl
        · rcases y with yz | yw
          · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
          · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
    · rcases x with xz | xw
      · rcases y with yu | y
        · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
        · rcases y with ys | y
          · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
          · rcases y with yz | yw
            · have hz : xz = yz := by
                simpa [squareRootLowPrimeNoLibertyBoundaryHome] using hxy
              subst yz
              rfl
            · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
      · rcases y with yu | y
        · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
        · rcases y with ys | y
          · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
          · rcases y with yz | yw
            · simp [squareRootLowPrimeNoLibertyBoundaryHome] at hxy
            · have hxw : xw ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R := by
                simpa [squareRootLowPrimeProcessedSeatNoLibertyBoundary] using hx
              have hyw : yw ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R := by
                simpa [squareRootLowPrimeProcessedSeatNoLibertyBoundary] using hy
              have hparent : xw.2 = yw.2 := by
                simpa [squareRootLowPrimeNoLibertyBoundaryHome] using hxy
              have hroot : xw = yw :=
                squareRootLowPrimeGoRootEquality_parentProjection_injOn
                  R hxw hyw hparent
              subst yw
              rfl

/-- The injective home map immediately transfers the `4*R` home budget to the
post-rematching no-liberty boundary. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyBoundary_card_le_four_root
    {R K j : ℕ} (hR : 1 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    (squareRootLowPrimeProcessedSeatNoLibertyBoundary
      R K j (squareRootBornPostTailLowPrimeCutoff R)).card ≤ 4 * R := by
  let B := squareRootLowPrimeProcessedSeatNoLibertyBoundary
    R K j (squareRootBornPostTailLowPrimeCutoff R)
  let H := squareRootLowPrimeNoLibertyBoundaryHomeSpace R K j
  let home := squareRootLowPrimeNoLibertyBoundaryHome R K j
  have hinj : Set.InjOn home B := by
    simpa [B, home] using
      squareRootLowPrimeNoLibertyBoundaryHome_injOn R K j
  have himage : B.image home ⊆ H := by
    intro h hh
    rcases Finset.mem_image.mp hh with ⟨x, hx, rfl⟩
    simpa [B, H, home] using
      squareRootLowPrimeNoLibertyBoundaryHome_mem (R := R) (K := K) (j := j) hx
  have hcardImage : (B.image home).card = B.card :=
    Finset.card_image_iff.mpr hinj
  have hhome :=
    squareRootLowPrimeNoLibertyBoundaryHomeSpace_card_le_four_root
      hR hKR hV0 hVK
  calc
    B.card = (B.image home).card := hcardImage.symm
    _ ≤ H.card := Finset.card_le_card himage
    _ ≤ 4 * R := by simpa [H] using hhome

end RHLean.Proof
