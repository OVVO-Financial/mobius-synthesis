import Mathlib
import RHLean.Arithmetic.PrimeSquareCollisionCRT
import RHLean.Arithmetic.PrimeWheelFiniteSystem

noncomputable section

open scoped BigOperators

namespace RHLean.Arithmetic

/-!
# Collision labels and the local exponent-state flip

Two different three-element sets occur in the collision analysis and must not
be identified without proof.

First, one local prime comb has three exponent states:

* `0`: no prime hit, with local value `+1`;
* `1`: first-power hit, with local value `-1`;
* `2`: square hit, with local value `0`.

Second, one three-slot cell has three collision labels, recording which active
slot contains a prime-square hit.  Both sets can be represented by `Fin 3`, but
their arithmetic meanings are different.  In particular, the exponent states
have unequal residue multiplicities modulo `p^2`, while the nine CRT collision
classes are the three current slot labels crossed with the three next-cell slot
labels.

This file therefore keeps the two copies of `Fin 3` logically separate.  The
local exponent-state flip proves only the pointwise sign identity for
`localPrimeCombStateValue`.  The collision-slot involution is a candidate
pairing on the nine CRT labels; any physical `R - 2H` weight must still prove a
separate sign-reversal theorem before `Finset.sum_involution` may cancel it.
-/

/-! ## Local prime-comb exponent states -/

/-- The three local prime-comb exponent states. -/
abbrev PrimeCombExponentState := Fin 3

/-- Two independent local exponent states.  This is an abstract state space,
not the nine physical CRT collision classes. -/
abbrev TwoPrimeCombExponentState :=
  PrimeCombExponentState × PrimeCombExponentState

/-- The exact local comb value attached to an exponent state. -/
def localPrimeCombStateValue (a : PrimeCombExponentState) : ℤ :=
  if a = 0 then 1 else if a = 1 then -1 else 0

/-- The exponent state read directly from divisibility by `p` and `p^2`. -/
def localPrimeExponentState (p n : ℕ) : PrimeCombExponentState :=
  if p ^ 2 ∣ n then 2 else if p ∣ n then 1 else 0

/-- `localPrimeComb` is exactly the three-state value map. -/
theorem localPrimeComb_eq_stateValue (p n : ℕ) :
    localPrimeComb p n =
      localPrimeCombStateValue (localPrimeExponentState p n) := by
  by_cases hsq : p ^ 2 ∣ n
  · simp [localPrimeComb, localPrimeExponentState,
      localPrimeCombStateValue, hsq]
  · by_cases hp : p ∣ n
    · simp [localPrimeComb, localPrimeExponentState,
        localPrimeCombStateValue, hsq, hp]
    · simp [localPrimeComb, localPrimeExponentState,
        localPrimeCombStateValue, hsq, hp]

/-- Flip first-power parity while leaving the square-kill state fixed. -/
def primeCombExponentFlip (a : PrimeCombExponentState) :
    PrimeCombExponentState :=
  if a = 0 then 1 else if a = 1 then 0 else 2

@[simp] theorem primeCombExponentFlip_involutive
    (a : PrimeCombExponentState) :
    primeCombExponentFlip (primeCombExponentFlip a) = a := by
  fin_cases a <;> simp [primeCombExponentFlip]

/-- The local comb value changes sign under the exponent-state flip.  The
square state is fixed only because its value is already zero. -/
@[simp] theorem localPrimeCombStateValue_flip
    (a : PrimeCombExponentState) :
    localPrimeCombStateValue (primeCombExponentFlip a) =
      -localPrimeCombStateValue a := by
  fin_cases a <;>
    simp [primeCombExponentFlip, localPrimeCombStateValue]

/-- The only fixed exponent state is the square-kill state. -/
theorem primeCombExponentFlip_eq_self_iff
    (a : PrimeCombExponentState) :
    primeCombExponentFlip a = a ↔ a = 2 := by
  fin_cases a <;> simp [primeCombExponentFlip]

/-- Product-state involution for the abstract local comb value algebra. -/
def primeCombPairStateInvolution
    (s : TwoPrimeCombExponentState) : TwoPrimeCombExponentState :=
  (primeCombExponentFlip s.1, s.2)

@[simp] theorem primeCombPairStateInvolution_involutive
    (s : TwoPrimeCombExponentState) :
    primeCombPairStateInvolution (primeCombPairStateInvolution s) = s := by
  rcases s with ⟨a, b⟩
  simp [primeCombPairStateInvolution]

/-- A generic local product value on the abstract exponent-state space. -/
def localPrimeCombPairWeight (s : TwoPrimeCombExponentState) : ℤ :=
  localPrimeCombStateValue s.1 * localPrimeCombStateValue s.2

/-- The abstract local product value reverses sign under the exponent flip. -/
@[simp] theorem localPrimeCombPairWeight_involution
    (s : TwoPrimeCombExponentState) :
    localPrimeCombPairWeight (primeCombPairStateInvolution s) =
      -localPrimeCombPairWeight s := by
  simp [localPrimeCombPairWeight, primeCombPairStateInvolution]

/-- Fixed points of the abstract exponent-state involution have zero product
value because their first coordinate is the square-kill state. -/
theorem localPrimeCombPairWeight_eq_zero_of_fixed
    (s : TwoPrimeCombExponentState)
    (hs : primeCombPairStateInvolution s = s) :
    localPrimeCombPairWeight s = 0 := by
  have hfirst : s.1 = 2 := by
    rcases s with ⟨a, b⟩
    simp only [primeCombPairStateInvolution, Prod.mk.injEq] at hs
    exact (primeCombExponentFlip_eq_self_iff a).mp hs.1
  simp [localPrimeCombPairWeight, localPrimeCombStateValue, hfirst]

/-- Abstract three-by-three state-value cancellation.  This theorem deliberately
sums one copy of each exponent-state label.  It is **not** a complete residue
sum modulo `p^2*q^2`, because the three exponent states have unequal residue
multiplicities. -/
theorem sum_localPrimeCombPairWeight_eq_zero :
    ∑ s : TwoPrimeCombExponentState, localPrimeCombPairWeight s = 0 := by
  classical
  exact Finset.sum_involution
    (s := (Finset.univ : Finset TwoPrimeCombExponentState))
    (f := localPrimeCombPairWeight)
    (fun s _hs => primeCombPairStateInvolution s)
    (fun s _hs => by
      rw [localPrimeCombPairWeight_involution]
      simp)
    (fun s _hs hne hfix =>
      hne (localPrimeCombPairWeight_eq_zero_of_fixed s hfix))
    (fun _s _hs => Finset.mem_univ _)
    (fun s _hs => primeCombPairStateInvolution_involutive s)

/-! ## The nine physical CRT collision labels -/

/-- One of the three active slots in a four-cell collision. -/
abbrev CollisionSlotLabel := Fin 3

/-- The nine labelled current-slot/next-slot collision classes. -/
abbrev TwoPrimeCollisionState := CollisionSlotLabel × CollisionSlotLabel

/-- A fixed combinatorial matching of collision slots: swap the first two slot
labels and leave the third fixed.  This has the same finite permutation shape
as the exponent flip, but no arithmetic sign claim is attached to it. -/
def collisionSlotFlip (a : CollisionSlotLabel) : CollisionSlotLabel :=
  if a = 0 then 1 else if a = 1 then 0 else 2

@[simp] theorem collisionSlotFlip_involutive (a : CollisionSlotLabel) :
    collisionSlotFlip (collisionSlotFlip a) = a := by
  fin_cases a <;> simp [collisionSlotFlip]

/-- The only fixed slot label for the chosen matching is the third slot. -/
theorem collisionSlotFlip_eq_self_iff (a : CollisionSlotLabel) :
    collisionSlotFlip a = a ↔ a = 2 := by
  fin_cases a <;> simp [collisionSlotFlip]

/-- Candidate involution on the nine physical collision labels.  The historical
name is retained on this branch, but the coordinates are slot labels, not local
prime-comb exponent states. -/
def collisionExponentStateInvolution
    (s : TwoPrimeCollisionState) : TwoPrimeCollisionState :=
  (collisionSlotFlip s.1, s.2)

@[simp] theorem collisionExponentStateInvolution_involutive
    (s : TwoPrimeCollisionState) :
    collisionExponentStateInvolution
        (collisionExponentStateInvolution s) = s := by
  rcases s with ⟨a, b⟩
  simp [collisionExponentStateInvolution]

/-- Fixed collision labels are exactly those whose current collision is in the
third active slot. -/
theorem collisionExponentStateInvolution_eq_self_iff
    (s : TwoPrimeCollisionState) :
    collisionExponentStateInvolution s = s ↔ s.1 = 2 := by
  rcases s with ⟨a, b⟩
  simp [collisionExponentStateInvolution, collisionSlotFlip_eq_self_iff]

/-- There are exactly nine symbolic collision-slot labels. -/
theorem twoPrimeCollisionState_card :
    Fintype.card TwoPrimeCollisionState = 9 := by
  simp [TwoPrimeCollisionState, CollisionSlotLabel]

/-- The fixed-point set for the chosen slot matching. -/
def collisionExponentFixedPoints : Finset TwoPrimeCollisionState :=
  Finset.univ.filter (fun s => collisionExponentStateInvolution s = s)

/-- The non-fixed labels on which a separately proved sign-reversing weight can
be paired. -/
def collisionExponentPairedStates : Finset TwoPrimeCollisionState :=
  Finset.univ.filter (fun s => collisionExponentStateInvolution s ≠ s)

/-- Exactly three slot-pair labels are fixed by the chosen matching. -/
theorem collisionExponentFixedPoints_card :
    collisionExponentFixedPoints.card = 3 := by
  native_decide

/-- Current-cell CRT offset attached to a collision slot label. -/
def currentCollisionStateOffset (a : CollisionSlotLabel) : ℕ :=
  a.1 + 1

/-- Next-cell CRT offset attached to a collision slot label. -/
def nextCollisionStateOffset (b : CollisionSlotLabel) : ℕ :=
  b.1 + 5

/-- CRT realization of a labelled current-slot/next-slot collision pair. -/
def collisionExponentStateResidue
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    (s : TwoPrimeCollisionState) :
    ZMod ((p ^ 2) * (q ^ 2)) :=
  (ZMod.chineseRemainder hcop).symm
    (collisionRoot (p ^ 2) (currentCollisionStateOffset s.1),
      collisionRoot (q ^ 2) (nextCollisionStateOffset s.2))

/-- Every labelled slot pair realizes one of the existing nine CRT collision
classes. -/
theorem collisionExponentStateResidue_mem
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    (s : TwoPrimeCollisionState) :
    collisionExponentStateResidue p q hcop s ∈
      collisionCRTResidues p q hcop := by
  rcases s with ⟨a, b⟩
  unfold collisionExponentStateResidue collisionCRTResidues
  apply Finset.mem_image.mpr
  refine ⟨(collisionRoot (p ^ 2) (currentCollisionStateOffset a),
    collisionRoot (q ^ 2) (nextCollisionStateOffset b)), ?_, rfl⟩
  apply Finset.mem_product.mpr
  constructor
  · fin_cases a <;>
      simp [currentCollisionStateOffset, currentCollisionRoots]
  · fin_cases b <;>
      simp [nextCollisionStateOffset, nextCollisionRoots]

/-- The nine slot-pair labels realized as a finite residue set. -/
def collisionExponentStateResidues
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2)) :
    Finset (ZMod ((p ^ 2) * (q ^ 2))) :=
  Finset.univ.image (collisionExponentStateResidue p q hcop)

/-- The labelled realization is contained in the existing CRT collision set. -/
theorem collisionExponentStateResidues_subset
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2)) :
    collisionExponentStateResidues p q hcop ⊆
      collisionCRTResidues p q hcop := by
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨s, _hs, rfl⟩
  exact collisionExponentStateResidue_mem p q hcop s

/-- For odd primes, the slot-pair CRT realization is injective.  Thus the nine
labels are genuinely nine distinct residue classes, rather than a merely
nine-element indexing type. -/
theorem collisionExponentStateResidue_injective
    (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpgt : 2 < p) (hqgt : 2 < q)
    (hcop : Nat.Coprime (p ^ 2) (q ^ 2)) :
    Function.Injective (collisionExponentStateResidue p q hcop) := by
  intro s t hst
  rcases s with ⟨a, b⟩
  rcases t with ⟨c, d⟩
  unfold collisionExponentStateResidue at hst
  have hpair := (ZMod.chineseRemainder hcop).symm.injective hst
  have hfirst :
      collisionRoot (p ^ 2) (currentCollisionStateOffset a) =
        collisionRoot (p ^ 2) (currentCollisionStateOffset c) :=
    congrArg Prod.fst hpair
  have hsecond :
      collisionRoot (q ^ 2) (nextCollisionStateOffset b) =
        collisionRoot (q ^ 2) (nextCollisionStateOffset d) :=
    congrArg Prod.snd hpair
  have hp4 := four_coprime_primeSquare p hp hpgt
  have hq4 := four_coprime_primeSquare q hq hqgt
  have hp_sq_ge : 9 ≤ p ^ 2 := by nlinarith
  have hq_sq_ge : 9 ≤ q ^ 2 := by nlinarith
  have ha_lt : currentCollisionStateOffset a < p ^ 2 := by
    have ha := a.isLt
    unfold currentCollisionStateOffset
    omega
  have hc_lt : currentCollisionStateOffset c < p ^ 2 := by
    have hc := c.isLt
    unfold currentCollisionStateOffset
    omega
  have hb_lt : nextCollisionStateOffset b < q ^ 2 := by
    have hb := b.isLt
    unfold nextCollisionStateOffset
    omega
  have hd_lt : nextCollisionStateOffset d < q ^ 2 := by
    have hd := d.isLt
    unfold nextCollisionStateOffset
    omega
  have hacOffset := collisionRoot_injective_of_lt
    (p ^ 2) (currentCollisionStateOffset a)
      (currentCollisionStateOffset c) hp4 ha_lt hc_lt hfirst
  have hbdOffset := collisionRoot_injective_of_lt
    (q ^ 2) (nextCollisionStateOffset b)
      (nextCollisionStateOffset d) hq4 hb_lt hd_lt hsecond
  have hac : a = c := by
    apply Fin.ext
    unfold currentCollisionStateOffset at hacOffset
    omega
  have hbd : b = d := by
    apply Fin.ext
    unfold nextCollisionStateOffset at hbdOffset
    omega
  exact Prod.ext hac hbd

/-- For distinct odd primes, the labelled realization is exactly the existing
nine-class CRT collision set. -/
theorem collisionExponentStateResidues_eq_collisionCRTResidues
    (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpgt : 2 < p) (hqgt : 2 < q)
    (hpq : p ≠ q) :
    collisionExponentStateResidues p q
        (primeSquare_coprime_primeSquare p q hp hq hpq) =
      collisionCRTResidues p q
        (primeSquare_coprime_primeSquare p q hp hq hpq) := by
  let hcop := primeSquare_coprime_primeSquare p q hp hq hpq
  apply Finset.eq_of_subset_of_card_le
    (collisionExponentStateResidues_subset p q hcop)
  rw [collisionCRTResidues_card p q hp hq hpgt hqgt hpq]
  unfold collisionExponentStateResidues
  rw [Finset.card_image_of_injective _
    (collisionExponentStateResidue_injective p q hp hq hpgt hqgt hcop)]
  simp [TwoPrimeCollisionState, CollisionSlotLabel]

end RHLean.Arithmetic
