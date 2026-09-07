import Mathlib
import RHLean.Proof.SquareRootLowPrimeBornSeatPartnerEmbedding
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty
import RHLean.Proof.SquareRootLowPrimeStructuralKey

/-!
# Non-born first-owner fallout is an inherited response tail

The born-partner coordinate change covers processed seats with
`s < squareRootBornPartnerCount R c`, and
`squareRootLowPrimeSeat_lt_root_of_not_bornRange` shows every other seat has
`c ≤ R - 1`.  This file uses that to remove the product-wall branch from the
first-owner fallout dichotomy entirely.

The exact fallout-seat interval theorem already splits a canonical owner
fallout into two alternatives,

`squareRootEndpoint R < p * c`  or  `Combined R K j (p*c) ≤ s`.

The first is a product wall: the proposed child `p*c` has left the square
window.  But the canonical schedule cutoff is
`squareRootBornPostTailLowPrimeCutoff R = R - Nat.sqrt R`, so every scheduled
owner satisfies `p ≤ R - 1`; a cofactor with `c ≤ R - 1` therefore has
`p * c ≤ (R-1)^2 ≤ R^2 - 1`, and the wall cannot occur.

So on the complement of born index range the fallout is never a wall.  What
survives is exactly the inherited tail of the parent response fibre:

`Combined R K j (p*c) ≤ s < Combined R K j c`.

The unclassified seats are therefore not a new state family.  They are the
parent/child response-window difference the tree already decomposes.

Nothing here is an estimate; the wall branch is killed by the arithmetic of the
cutoff alone.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Every fresh-prime coordinate is at most the schedule cutoff. -/
theorem squareRootLowPrimeFreshPrimeList_le_cutoff
    {K U p : ℕ} (hp : p ∈ squareRootLowPrimeFreshPrimeList K U) :
    p ≤ U := by
  have hset : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hp
  have hdata := Finset.mem_filter.mp hset
  exact (Finset.mem_Ioc.mp hdata.1).2

/-- **The product wall cannot fire below the root.**  A scheduled owner is at
most `R - Nat.sqrt R`, hence at most `R - 1`; against a cofactor at most `R - 1`
the child product stays inside the square window. -/
theorem squareRootLowPrimeProductWall_impossible_of_lt_root
    {R p c : ℕ} (hR : 1 ≤ R)
    (hpU : p ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hc : c ≤ R - 1) :
    ¬ squareRootEndpoint R < p * c := by
  intro hwall
  have hsqrt : 1 ≤ Nat.sqrt R := Nat.sqrt_pos.mpr hR
  have hcut : squareRootBornPostTailLowPrimeCutoff R = R - Nat.sqrt R := rfl
  rw [hcut] at hpU
  have hpR : p ≤ R - 1 := by omega
  obtain ⟨d, hd⟩ : ∃ d, R = d + 1 := ⟨R - 1, by omega⟩
  subst hd
  have hpd : p ≤ d := by omega
  have hcd : c ≤ d := by omega
  have hmul : p * c ≤ d * d := Nat.mul_le_mul hpd hcd
  have hend : squareRootEndpoint (d + 1) = d * d + 2 * d := by
    unfold squareRootEndpoint
    have hsq : (d + 1) ^ 2 = d * d + 2 * d + 1 := by ring
    rw [hsq, Nat.add_sub_cancel]
  rw [hend] at hwall
  exact absurd
    (lt_of_le_of_lt (Nat.le_add_right (d * d) (2 * d))
      (lt_of_lt_of_le hwall hmul))
    (lt_irrefl _)

/-- **Non-born fallout is a response tail.**  Outside born index range the
canonical owner fallout dichotomy loses its product-wall alternative, so the
seat index sits in the inherited parent/child response window. -/
theorem squareRootLowPrimeNonBornFirstOwnerFalloff_is_responseTail
    {R K j U p c s : ℕ} (hR : 1 ≤ R)
    (hp : p.Prime) (hpU : p ≤ U)
    (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s ∧
      s < squareRootLowPrimeCombinedFreshResponse R K j c := by
  have hcR := squareRootLowPrimeSeat_lt_root_of_not_bornRange hs hnb
  rcases squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_carrierObstruction
      hp hpU hfall with hwall | hseat
  · exact absurd hwall
      (squareRootLowPrimeProductWall_impossible_of_lt_root hR (hpU.trans hUR) hcR)
  · exact ⟨hseat, hs⟩

/-- The same conclusion in the repository's own fallout seat-window language. -/
theorem squareRootLowPrimeNonBornFirstOwnerFalloff_mem_responseTailWindow
    {R K j U p c s : ℕ} (hR : 1 ≤ R)
    (hp : p.Prime) (hpU : p ≤ U)
    (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    s ∈ Finset.Ico
      (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
      (squareRootLowPrimeCombinedFreshResponse R K j c) := by
  have htail := squareRootLowPrimeNonBornFirstOwnerFalloff_is_responseTail
    hR hp hpU hUR hs hnb hfall
  exact Finset.mem_Ico.mpr htail

/-- The canonical-schedule form: the owner is produced by
`squareRootLowPrimeFirstOwnerAbove` on the actual fresh-prime list, so its
primality and cutoff bound come from the schedule itself. -/
theorem squareRootLowPrimeNonBornCanonicalFalloff_is_responseTail
    {R K j c s p : ℕ} (hR : 1 ≤ R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K
        (squareRootBornPostTailLowPrimeCutoff R))
      (canonicalLargestPrimeFactor c) = some p)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j
        (squareRootBornPostTailLowPrimeCutoff R)) p) :
    squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s ∧
      s < squareRootLowPrimeCombinedFreshResponse R K j c := by
  obtain ⟨pre, post, hsplit, _hpre, _hLp⟩ :=
    squareRootLowPrimeFirstOwnerAbove_some_split hfirst
  have hpMem : p ∈ squareRootLowPrimeFreshPrimeList K
      (squareRootBornPostTailLowPrimeCutoff R) := by
    rw [hsplit]
    simp
  have hp := (squareRootLowPrimeFreshPrimeList_prime_and_above hpMem).1
  have hpU := squareRootLowPrimeFreshPrimeList_le_cutoff hpMem
  exact squareRootLowPrimeNonBornFirstOwnerFalloff_is_responseTail
    hR hp hpU le_rfl hs hnb hfall

end RHLean.Proof
