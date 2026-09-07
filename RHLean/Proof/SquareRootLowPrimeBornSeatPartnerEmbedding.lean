import Mathlib
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome
import RHLean.Proof.SquareRootLowPrimeFirstOwnerFalloutWidth
import RHLean.Proof.SquareRootLowPrimeProcessedSeatCarrier
import RHLean.Proof.SquareRootLowPrimeSequentialDissipation

/-!
# Born-partner coordinate change for the no-liberty embedding

The no-liberty closure needs an actual
`SquareRootLowPrimeDescendingBoundaryWeightEmbedding`: a weight-preserving
injection from the descending processed-seat frontier into the four tagged
endpoint homes.  Source and target are stated in different coordinates, and
that mismatch is the first thing any classifier has to cross.

* A processed seat is `(c, s)` with `s` an **index**,
  `s < squareRootLowPrimeCombinedFreshResponse R K j c`, and real weight
  `-mu c`.
* A born endpoint is `(c, q)` with `q` an actual **prime partner**,
  `q ∈ squareRootBornPartnerSet R c`, and real weight
  `mu (squareRootLowPrimeBadAtomChild (c,q)) = mu (c * q)`.

This file builds that coordinate change and proves it is exactly weight
preserving, which is what the `weight_eq` field of the embedding demands.

## What is proved

* `squareRootLowPrimeSeatBornPartner` sends a seat index below
  `squareRootBornPartnerCount R c` to the corresponding born partner prime, in
  increasing order.  It lands in `squareRootBornPartnerSet R c`
  (`squareRootLowPrimeSeatBornPartner_mem`) and is injective in the index
  (`squareRootLowPrimeSeatBornPartner_injOn`).

* `moebius_mul_squareRootLowPrimeSeatBornPartner`: `mu (c * q) = - mu c` for the
  enumerated partner, because a born partner is prime and strictly above the
  canonical largest prime factor of `c`, hence fresh.

* `squareRootLowPrimeNoLibertyBoundaryWeight_bornSeat`: the born endpoint weight
  of the image equals the processed-seat weight of the source, in the exact
  form the embedding's `weight_eq` field asks for.  The born home is therefore
  weight-compatible with the seat carrier by arithmetic, not by convention.

* `squareRootLowPrimeBornSeatHome_injOn`: the resulting home map is injective on
  seats whose index is in born range.

## What this does not yet give, stated exactly

Two obligations remain before these pieces assemble into the embedding, and
neither is an estimate:

1. *No-successor membership.*  The target is
   `squareRootLowPrimeBornNoSuccessorAtoms`, not the full born atom set, so a
   stable seat must additionally satisfy
   `squareRootLowPrimeBadAtomChild (c,q) ∉ squareRootLowPrimeOwnedResponseCofactors R K U`.

2. *The complementary index range.*  The born coordinate change is defined only
   for `s < squareRootBornPartnerCount R c`.
   `squareRootLowPrimeSeat_lt_root_of_not_bornRange` proves that every seat
   outside that range has `c ≤ R - 1`: the uncovered seats are exactly the
   post-tail high-response seats, and they all sit below the root.  Whether a
   stable such seat always has a partial-packet or Go-root-equality home is the
   remaining classification question, and a stable seat with none would be the
   fifth geometry the four-home split omits.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## Enumerating the born partners of one cofactor -/

/-- Increasing enumeration of the born partner primes of `c`. -/
def squareRootLowPrimeBornPartnerEnum (R c : ℕ) :
    Fin (squareRootBornPartnerCount R c) ↪o ℕ :=
  (squareRootBornPartnerSet R c).orderEmbOfFin rfl

/-- The born partner prime named by one processed-seat index.  Outside born
range the value is irrelevant and set to zero. -/
def squareRootLowPrimeSeatBornPartner (R c s : ℕ) : ℕ :=
  if h : s < squareRootBornPartnerCount R c then
    squareRootLowPrimeBornPartnerEnum R c ⟨s, h⟩
  else 0

/-- A born-range seat index names an actual born partner. -/
theorem squareRootLowPrimeSeatBornPartner_mem
    {R c s : ℕ} (hs : s < squareRootBornPartnerCount R c) :
    squareRootLowPrimeSeatBornPartner R c s ∈ squareRootBornPartnerSet R c := by
  unfold squareRootLowPrimeSeatBornPartner squareRootLowPrimeBornPartnerEnum
  rw [dif_pos hs]
  exact Finset.orderEmbOfFin_mem _ _ _

/-- Distinct born-range seat indices name distinct partners. -/
theorem squareRootLowPrimeSeatBornPartner_injOn
    {R c s t : ℕ}
    (hs : s < squareRootBornPartnerCount R c)
    (ht : t < squareRootBornPartnerCount R c)
    (h : squareRootLowPrimeSeatBornPartner R c s =
      squareRootLowPrimeSeatBornPartner R c t) :
    s = t := by
  unfold squareRootLowPrimeSeatBornPartner at h
  rw [dif_pos hs, dif_pos ht] at h
  have hfin : (⟨s, hs⟩ : Fin (squareRootBornPartnerCount R c)) = ⟨t, ht⟩ :=
    (squareRootLowPrimeBornPartnerEnum R c).injective h
  simpa using congrArg Fin.val hfin

/-! ## Arithmetic of the coordinate change -/

/-- The enumerated partner is prime. -/
theorem squareRootLowPrimeSeatBornPartner_prime
    {R c s : ℕ} (hs : s < squareRootBornPartnerCount R c) :
    (squareRootLowPrimeSeatBornPartner R c s).Prime :=
  (Finset.mem_filter.mp (squareRootLowPrimeSeatBornPartner_mem hs)).2.1

/-- The enumerated partner is strictly above the canonical largest prime factor
of the cofactor, so it is a genuinely fresh coordinate. -/
theorem squareRootLowPrimeSeatBornPartner_rough
    {R c s : ℕ} (hs : s < squareRootBornPartnerCount R c) :
    canonicalLargestPrimeFactor c < squareRootLowPrimeSeatBornPartner R c s :=
  (Finset.mem_filter.mp (squareRootLowPrimeSeatBornPartner_mem hs)).2.2.1

/-- Adjoining the born partner reverses the Möbius sign of the cofactor. -/
theorem moebius_mul_squareRootLowPrimeSeatBornPartner
    {R c s : ℕ} (hc : 0 < c) (hs : s < squareRootBornPartnerCount R c) :
    μ (c * squareRootLowPrimeSeatBornPartner R c s) = - μ c := by
  have hq := squareRootLowPrimeSeatBornPartner_prime hs
  have hrough := squareRootLowPrimeSeatBornPartner_rough hs
  have hnd : ¬ squareRootLowPrimeSeatBornPartner R c s ∣ c :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hc hq hrough
  rw [Nat.mul_comm]
  exact moebius_prime_mul hq hnd

/-! ## Weight compatibility with the born home -/

/-- The born-range seat home. -/
def squareRootLowPrimeBornSeatHome (R : ℕ) (z : ℕ × ℕ) :
    SquareRootLowPrimeProcessedSeatNoLibertyState :=
  Sum.inr (Sum.inr (Sum.inl (z.1, squareRootLowPrimeSeatBornPartner R z.1 z.2)))

/-- **Exact weight preservation of the born coordinate change.**  This is the
`weight_eq` obligation of `SquareRootLowPrimeDescendingBoundaryWeightEmbedding`
for a born-range seat, discharged by arithmetic alone. -/
theorem squareRootLowPrimeNoLibertyBoundaryWeight_bornSeat
    {R c s : ℕ} (hc : 0 < c) (hs : s < squareRootBornPartnerCount R c) :
    squareRootLowPrimeNoLibertyBoundaryWeight
        (squareRootLowPrimeBornSeatHome R (c, s)) =
      squareRootLowPrimeProcessedSeatWeightReal (some (c, s)) := by
  have hmu := moebius_mul_squareRootLowPrimeSeatBornPartner hc hs
  have hchild :
      squareRootLowPrimeBadAtomChild
          (c, squareRootLowPrimeSeatBornPartner R c s) =
        c * squareRootLowPrimeSeatBornPartner R c s := rfl
  unfold squareRootLowPrimeBornSeatHome
  show squareRootLowPrimeNoLibertyBoundaryWeight
      (Sum.inr (Sum.inr (Sum.inl
        (c, squareRootLowPrimeSeatBornPartner R c s)))) =
    squareRootLowPrimeProcessedSeatWeightReal (some (c, s))
  rw [squareRootLowPrimeNoLibertyBoundaryWeight_born, hchild, hmu]
  rfl

/-- The born-range home map is injective. -/
theorem squareRootLowPrimeBornSeatHome_injOn
    {R : ℕ} {z w : ℕ × ℕ}
    (hz : z.2 < squareRootBornPartnerCount R z.1)
    (hw : w.2 < squareRootBornPartnerCount R w.1)
    (h : squareRootLowPrimeBornSeatHome R z = squareRootLowPrimeBornSeatHome R w) :
    z = w := by
  unfold squareRootLowPrimeBornSeatHome at h
  have hpair :
      (z.1, squareRootLowPrimeSeatBornPartner R z.1 z.2) =
        (w.1, squareRootLowPrimeSeatBornPartner R w.1 w.2) :=
    Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))
  rw [Prod.mk.injEq] at hpair
  obtain ⟨hfirst, hsecond⟩ := hpair
  have hwz : w.2 < squareRootBornPartnerCount R z.1 := by
    rw [hfirst]; exact hw
  have hsecond' :
      squareRootLowPrimeSeatBornPartner R z.1 z.2 =
        squareRootLowPrimeSeatBornPartner R z.1 w.2 := by
    rw [hsecond, hfirst]
  have hindex : z.2 = w.2 :=
    squareRootLowPrimeSeatBornPartner_injOn hz hwz hsecond'
  exact Prod.ext hfirst hindex

/-! ## The complementary index range -/

/-- **The seats the born coordinate change does not reach all lie below the
root.**  A processed seat outside born index range must be drawing on the
post-tail high response, which is available only for `c ≤ R - 1`.  So the
residual classification problem for the no-liberty embedding is confined to
sub-root cofactors, where the partial-packet and Go-root-equality homes live. -/
theorem squareRootLowPrimeSeat_lt_root_of_not_bornRange
    {R K j c s : ℕ}
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c) :
    c ≤ R - 1 := by
  by_contra hc
  unfold squareRootLowPrimeCombinedFreshResponse at hs
  rw [if_neg hc] at hs
  omega

/-! ## Canonical terminal first-owner geometry -/

/-- **Every assigned canonical terminal has only the two literal carrier-wall
geometries at its first owner.**

The square-wall branch is completely shallow: its parent owner is at most `K`,
the parent cofactor has reached the root, and its complete response is therefore
purely born.  In the complementary branch the child stays under the square
wall and the inherited seat index lies beyond the child's response fibre.

This is a disjoint arithmetic classification of the canonical terminal
survivor; no mutable-row displacement residual remains. -/
theorem squareRootLowPrimeCanonicalAssigned_firstOwner_wall_or_seatTail
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hx : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p) :
    (squareRootEndpoint R < p * c ∧
        canonicalLargestPrimeFactor c ≤ K ∧
        R ≤ c ∧
        squareRootLowPrimeCombinedFreshResponse R K j c =
          squareRootBornPartnerCount R c) ∨
      (p * c ≤ squareRootEndpoint R ∧
        squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s) := by
  have hxTerminal : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U :=
    (Finset.mem_sdiff.mp hx).1
  have hfall :=
    squareRootLowPrimeProcessedSeatCanonicalTerminal_firstOwnerAbove_mem_falloff
      hxTerminal (by simp) hfirst
  have hpList := squareRootLowPrimeFirstOwnerAbove_mem_freshPrimeList hfirst
  have hpSet : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hpList
  have hpData := Finset.mem_filter.mp hpSet
  have hpPrime : p.Prime := hpData.2
  have hpU : p ≤ U := (Finset.mem_Ioc.mp hpData.1).2
  have hobstruction :=
    squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_carrierObstruction
      hpPrime hpU hfall
  by_cases hwall : squareRootEndpoint R < p * c
  · left
    have hlow :=
      squareRootLowPrimeFirstOwnerFalloff_productWall_forces_lowOwner
        (by omega) hUR hfirst hfall hwall
    have hcR :=
      squareRootLowPrimeFirstOwnerWall_forces_root_le_cofactor
        hR hUR hfirst hwall
    have hborn :=
      squareRootLowPrimeCombinedFreshResponse_eq_born_of_root_le
        (K := K) (j := j) (by omega) hcR
    exact ⟨hwall, hlow, hcR, hborn⟩
  · right
    have hinside : p * c ≤ squareRootEndpoint R := Nat.le_of_not_gt hwall
    rcases hobstruction with hwall' | hseat
    · exact (hwall hwall').elim
    · exact ⟨hinside, hseat⟩

/-- **A square-wall assigned terminal is a shallow born seat, and its actual
born partner is an old prime.** -/
theorem squareRootLowPrimeCanonicalAssigned_wall_bornSeat_oldPartner
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hx : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c) :
    s < squareRootBornPartnerCount R c ∧
      squareRootLowPrimeSeatBornPartner R c s ≤ K := by
  have hxTerminal : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U :=
    (Finset.mem_sdiff.mp hx).1
  have hxCarrier : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_subset
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U) hxTerminal
  have hseat : s < squareRootLowPrimeCombinedFreshResponse R K j c := by
    have hatom : (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hxCarrier
    exact (mem_squareRootLowPrimeProcessedSeatAtoms.mp hatom).2
  have hcR := squareRootLowPrimeFirstOwnerWall_forces_root_le_cofactor
    hR hUR hfirst hwall
  have hborn := squareRootLowPrimeCombinedFreshResponse_eq_born_of_root_le
    (K := K) (j := j) (by omega) hcR
  have hsBorn : s < squareRootBornPartnerCount R c := by
    simpa [hborn] using hseat
  refine ⟨hsBorn, ?_⟩
  exact squareRootLowPrimeFirstOwnerWall_bornPartner_le_shallowCutoff
    hfirst hwall (squareRootLowPrimeSeatBornPartner_mem hsBorn)

/-- Every assigned terminal outside born-seat range lies strictly below the
root.  Combined with the preceding dichotomy, the only uncovered terminal
sector is therefore the sub-root seat-tail sector. -/
theorem squareRootLowPrimeCanonicalAssigned_not_bornRange_lt_root
    {R K j U c s : ℕ}
    (hx : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U)
    (hnb : ¬ s < squareRootBornPartnerCount R c) :
    c ≤ R - 1 := by
  have hxTerminal : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U :=
    (Finset.mem_sdiff.mp hx).1
  have hxCarrier : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_subset
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U) hxTerminal
  have hseat : s < squareRootLowPrimeCombinedFreshResponse R K j c := by
    have hatom : (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hxCarrier
    exact (mem_squareRootLowPrimeProcessedSeatAtoms.mp hatom).2
  exact squareRootLowPrimeSeat_lt_root_of_not_bornRange hseat hnb

end RHLean.Proof