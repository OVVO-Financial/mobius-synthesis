import Mathlib
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Proof.SquareRootLowPrimeBornSquareBoundary
import RHLean.Proof.SquareRootLowPrimeHighResponseMonotone
import RHLean.Proof.SquareRootLowPrimeNonBornFalloutResponseTail

/-!
# Re-entry of a non-born response tail forces a newly born prime

`squareRootLowPrimeNonBornFirstOwnerFalloff_is_responseTail` puts a non-born
first-owner fallout seat in the inherited window `C(p*c) <= s < C(c)`, where
`C` is `squareRootLowPrimeCombinedFreshResponse`.  Suppose that seat is *not*
terminal, because a later scheduled prime `q > p` can still pair it.  Then its
`q`-child is present, so `s < C(q*c)`, and therefore `C(p*c) < C(q*c)`.

Split the response into its two channels, `C = B + E`, with
`B = squareRootBornPartnerCount` and `E` the honest high suffix.  The high
response is antitone in the cofactor and `p*c <= q*c`, so `E(q*c) <= E(p*c)`.
The high channel therefore cannot produce the increase:

`B(p*c) < B(q*c)`.

Strict born growth supplies an actual new partner
`r ∈ BornPartnerSet (q*c) \ BornPartnerSet (p*c)`, and the born conditions pin
it down.  Since `p` and `q` are fresh over `c`, `lpf (p*c) = p` and
`lpf (q*c) = q`, so `q < r`; and if `r` were at most `p*c` every born condition
at `p*c` would already hold (`p < q < r`, the same range and primality, and
`p*c*r <= q*c*r <= R^2-1`), contradicting `r ∉ BornPartnerSet (p*c)`.  Hence

`p*c < r`, so in particular `c < r`,

which is exactly membership in `squareRootBornPartnerBirthBoundary R c (q*c)`.
The repository already proves that boundary is the unique failure of downward
born support, so the escape is charged to a known object, not a new one.

The dynamic law is therefore: a non-born seat can evade its first owner only by
forcing a strictly larger prime `r > q > p` to be newly born at `q*c`.  The
owner prime strictly increases, so the ascent cannot cycle.

`..._window_card_le_birthBoundary` is the quantitative form: the whole re-entry
seat window is bounded by the birth boundary it creates.

No estimate appears; every step is born/high channel arithmetic.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## The two channels of the combined response -/

/-- The honest high suffix of the combined fresh response, including its
sub-root cutoff. -/
def squareRootLowPrimeHonestHighResponse (R K j c : ℕ) : ℕ :=
  if c ≤ R - 1 then squareRootBornPostTailHighResponse R K j c else 0

/-- The combined response is exactly born count plus honest high suffix. -/
theorem squareRootLowPrimeCombinedFreshResponse_eq_born_add_honestHigh
    (R K j c : ℕ) :
    squareRootLowPrimeCombinedFreshResponse R K j c =
      squareRootBornPartnerCount R c +
        squareRootLowPrimeHonestHighResponse R K j c := rfl

/-- The honest high suffix inherits antitonicity from the high response. -/
theorem squareRootLowPrimeHonestHighResponse_antitone
    {R K j a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    squareRootLowPrimeHonestHighResponse R K j b ≤
      squareRootLowPrimeHonestHighResponse R K j a := by
  unfold squareRootLowPrimeHonestHighResponse
  by_cases hb : b ≤ R - 1
  · have haR : a ≤ R - 1 := hab.trans hb
    rw [if_pos hb, if_pos haR]
    exact squareRootBornPostTailHighResponse_antitone ha hab
  · rw [if_neg hb]
    exact Nat.zero_le _

/-! ## Re-entry forces born growth -/

/-- **The high channel cannot cause a re-entry.**  If a seat has run out of
response at the earlier child but is still alive at the larger child, the born
partner count must have strictly increased. -/
theorem squareRootLowPrimeResponseReentry_forces_bornGrowth
    {R K j p q c s : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hpq : p < q)
    (hpGone : squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s)
    (hqAlive : s < squareRootLowPrimeCombinedFreshResponse R K j (q * c)) :
    squareRootBornPartnerCount R (p * c) <
      squareRootBornPartnerCount R (q * c) := by
  have hpcPos : 0 < p * c := Nat.mul_pos hp hc
  have hle : p * c ≤ q * c := Nat.mul_le_mul (le_of_lt hpq) (le_refl c)
  have hE := squareRootLowPrimeHonestHighResponse_antitone
    (R := R) (K := K) (j := j) hpcPos hle
  rw [squareRootLowPrimeCombinedFreshResponse_eq_born_add_honestHigh]
    at hpGone hqAlive
  omega

/-! ## The new born partner is above the earlier child -/

/-- A born partner of the larger child that is not one of the smaller child
must exceed the smaller child outright. -/
theorem squareRootLowPrimeResponseReentry_newBornPartner_gt
    {R p q c r : ℕ}
    (hc : 0 < c) (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q)
    (hrq : r ∈ squareRootBornPartnerSet R (q * c))
    (hrp : r ∉ squareRootBornPartnerSet R (p * c)) :
    p * c < r := by
  have hrData := Finset.mem_filter.mp hrq
  have hlpfP : canonicalLargestPrimeFactor (p * c) = p := by
    rw [Nat.mul_comm]
    exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hrough
  have hlpfQ : canonicalLargestPrimeFactor (q * c) = q := by
    rw [Nat.mul_comm]
    exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hq
      (lt_trans hrough hpq)
  have hqr : q < r := by
    have hlt := hrData.2.2.1
    rw [hlpfQ] at hlt
    exact hlt
  have hpcLe : p * c ≤ q * c := Nat.mul_le_mul (le_of_lt hpq) (le_refl c)
  by_contra hcon
  push_neg at hcon
  apply hrp
  refine Finset.mem_filter.mpr ⟨hrData.1, hrData.2.1, ?_, hcon, ?_⟩
  · rw [hlpfP]
    omega
  · calc p * c * r ≤ q * c * r := Nat.mul_le_mul hpcLe (le_refl r)
      _ ≤ squareRootEndpoint R := hrData.2.2.2.2

/-- Every newly available born partner lies in the birth boundary over `c`. -/
theorem squareRootLowPrimeResponseReentry_sdiff_subset_birthBoundary
    {R p q c : ℕ}
    (hc : 0 < c) (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q) :
    squareRootBornPartnerSet R (q * c) \ squareRootBornPartnerSet R (p * c) ⊆
      squareRootBornPartnerBirthBoundary R c (q * c) := by
  intro r hr
  rcases Finset.mem_sdiff.mp hr with ⟨hrq, hrp⟩
  have hpcr := squareRootLowPrimeResponseReentry_newBornPartner_gt
    hc hp hq hrough hpq hrq hrp
  have hcLe : c ≤ p * c := Nat.le_mul_of_pos_left c hp.pos
  exact mem_squareRootBornPartnerBirthBoundary.mpr ⟨hrq, by omega⟩

/-- **Birth witness.**  Strict born growth produces an actual prime that is
newly born at the larger child and sits above the earlier one. -/
theorem squareRootLowPrimeResponseReentry_birthWitness
    {R p q c : ℕ}
    (hc : 0 < c) (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q)
    (hgrowth : squareRootBornPartnerCount R (p * c) <
      squareRootBornPartnerCount R (q * c)) :
    ∃ r, r ∈ squareRootBornPartnerSet R (q * c) ∧
      r ∉ squareRootBornPartnerSet R (p * c) ∧
      p * c < r ∧
      r ∈ squareRootBornPartnerBirthBoundary R c (q * c) := by
  have hnotsub : ¬ squareRootBornPartnerSet R (q * c) ⊆
      squareRootBornPartnerSet R (p * c) := by
    intro hsub
    have hcard : squareRootBornPartnerCount R (q * c) ≤
        squareRootBornPartnerCount R (p * c) := Finset.card_le_card hsub
    omega
  obtain ⟨r, hrq, hrp⟩ := Finset.not_subset.mp hnotsub
  have hpcr := squareRootLowPrimeResponseReentry_newBornPartner_gt
    hc hp hq hrough hpq hrq hrp
  have hbirth := squareRootLowPrimeResponseReentry_sdiff_subset_birthBoundary
    hc hp hq hrough hpq (Finset.mem_sdiff.mpr ⟨hrq, hrp⟩)
  exact ⟨r, hrq, hrp, hpcr, hbirth⟩

/-! ## Quantitative form -/

/-- **The whole re-entry seat window is charged to the birth boundary.** -/
theorem squareRootLowPrimeResponseReentry_window_card_le_birthBoundary
    {R K j p q c : ℕ}
    (hc : 0 < c) (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q) :
    squareRootLowPrimeCombinedFreshResponse R K j (q * c) -
        squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤
      (squareRootBornPartnerBirthBoundary R c (q * c)).card := by
  have hpcPos : 0 < p * c := Nat.mul_pos hp.pos hc
  have hle : p * c ≤ q * c := Nat.mul_le_mul (le_of_lt hpq) (le_refl c)
  have hE := squareRootLowPrimeHonestHighResponse_antitone
    (R := R) (K := K) (j := j) hpcPos hle
  have hsdiff :
      (squareRootBornPartnerSet R (q * c) \
        squareRootBornPartnerSet R (p * c)).card ≤
        (squareRootBornPartnerBirthBoundary R c (q * c)).card :=
    Finset.card_le_card
      (squareRootLowPrimeResponseReentry_sdiff_subset_birthBoundary
        hc hp hq hrough hpq)
  have hsub : squareRootBornPartnerSet R (q * c) ⊆
      (squareRootBornPartnerSet R (q * c) \
        squareRootBornPartnerSet R (p * c)) ∪
        squareRootBornPartnerSet R (p * c) := by
    intro x hx
    by_cases hxB : x ∈ squareRootBornPartnerSet R (p * c)
    · exact Finset.mem_union_right _ hxB
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
  have hcardsub :
      squareRootBornPartnerCount R (q * c) ≤
        (squareRootBornPartnerSet R (q * c) \
          squareRootBornPartnerSet R (p * c)).card +
          squareRootBornPartnerCount R (p * c) := by
    calc squareRootBornPartnerCount R (q * c)
        ≤ ((squareRootBornPartnerSet R (q * c) \
            squareRootBornPartnerSet R (p * c)) ∪
            squareRootBornPartnerSet R (p * c)).card :=
          Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
  rw [squareRootLowPrimeCombinedFreshResponse_eq_born_add_honestHigh,
    squareRootLowPrimeCombinedFreshResponse_eq_born_add_honestHigh]
  omega

/-! ## Wrapping the actual fallout hypothesis -/

/-- **The dynamic law.**  A non-born first-owner fallout seat that survives to
be paired by a later scheduled prime forces a strictly larger prime to be newly
born at the later child. -/
theorem squareRootLowPrimeNonBornFalloutReentry_birthWitness
    {R K j U p q c s : ℕ} (hR : 1 ≤ R) (hc : 0 < c)
    (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hqAlive : s < squareRootLowPrimeCombinedFreshResponse R K j (q * c)) :
    ∃ r, r ∈ squareRootBornPartnerBirthBoundary R c (q * c) ∧
      q < r ∧ p * c < r := by
  have htail := squareRootLowPrimeNonBornFirstOwnerFalloff_is_responseTail
    hR hp hpU hUR hs hnb hfall
  have hgrowth := squareRootLowPrimeResponseReentry_forces_bornGrowth
    hc hp.pos hpq htail.1 hqAlive
  obtain ⟨r, hrq, _hrp, hpcr, hbirth⟩ :=
    squareRootLowPrimeResponseReentry_birthWitness hc hp hq hrough hpq hgrowth
  refine ⟨r, hbirth, ?_, hpcr⟩
  have hlpfQ : canonicalLargestPrimeFactor (q * c) = q := by
    rw [Nat.mul_comm]
    exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hq
      (lt_trans hrough hpq)
  have hlt := (Finset.mem_filter.mp hrq).2.2.1
  rw [hlpfQ] at hlt
  exact hlt

end RHLean.Proof
