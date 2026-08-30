import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty
import RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms

/-!
# Exact fixed-owner fallout widths

After the canonical Euler matching of `SquareRootLowPrimeCanonicalLiberty`, a
terminal non-head state is assigned to the first chronological prime `p` for
which its `p`-child is intrinsically absent from the original processed carrier.
This file opens that intrinsic absence completely at one fixed owner.

For a processed cofactor `c` with `P⁺(c) < p`, every parent seat has the form
`some (c,s)`, `0 <= s < CombinedFreshResponse(c)`.  There are exactly two ways
its canonical `p`-child can be absent from the original carrier:

* the cofactor itself crosses the square wall, `X_R < p*c`; or
* the child remains under the square wall but its response fibre ends before
  the inherited seat index `s`.

Consequently the literal fallout fibre over `c` is an interval of seat indices.
Its width is exactly

```text
CombinedFreshResponse(c)                         if X_R < p*c,
CombinedFreshResponse(c) - CombinedFreshResponse(p*c) otherwise.
```

The complete fixed-owner fallout is the disjoint union of these cofactor
fibres, so its signed mass is one cofactor sum with this exact width.  No
absolute value, asymptotic estimate, PNT input, Mertens bound, or chain-parity
argument is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Processed cofactors which can genuinely be extended in the canonical
Euler direction at owner `p`. -/
def squareRootLowPrimeCanonicalOwnerParentCofactors
    (R U p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeProcessedSignedCofactors R U).filter fun c =>
    canonicalLargestPrimeFactor c < p

@[simp] theorem mem_squareRootLowPrimeCanonicalOwnerParentCofactors
    {R U p c : ℕ} :
    c ∈ squareRootLowPrimeCanonicalOwnerParentCofactors R U p ↔
      c ∈ squareRootLowPrimeProcessedSignedCofactors R U ∧
        canonicalLargestPrimeFactor c < p := by
  simp [squareRootLowPrimeCanonicalOwnerParentCofactors]

/-- Exact number of inherited parent seats which have no `p`-child in the
original processed carrier. -/
def squareRootLowPrimeCanonicalOwnerFalloutWidth
    (R K j p c : ℕ) : ℕ :=
  if squareRootEndpoint R < p * c then
    squareRootLowPrimeCombinedFreshResponse R K j c
  else
    squareRootLowPrimeCombinedFreshResponse R K j c -
      squareRootLowPrimeCombinedFreshResponse R K j (p * c)

/-- Literal inherited seat indices lost at owner `p` over one cofactor `c`. -/
def squareRootLowPrimeCanonicalOwnerFalloutSeatIndices
    (R K j p c : ℕ) : Finset ℕ :=
  if squareRootEndpoint R < p * c then
    Finset.range (squareRootLowPrimeCombinedFreshResponse R K j c)
  else
    Finset.Ico
      (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
      (squareRootLowPrimeCombinedFreshResponse R K j c)

@[simp] theorem card_squareRootLowPrimeCanonicalOwnerFalloutSeatIndices
    (R K j p c : ℕ) :
    (squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c).card =
      squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c := by
  by_cases hwall : squareRootEndpoint R < p * c <;>
    simp [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices,
      squareRootLowPrimeCanonicalOwnerFalloutWidth, hwall]

/-- One cofactor's literal fixed-owner fallout states. -/
def squareRootLowPrimeCanonicalOwnerFalloutFiber
    (R K j p c : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c).image
    fun s => some (c, s)

@[simp] theorem mem_squareRootLowPrimeCanonicalOwnerFalloutFiber
    {R K j p c s : ℕ} :
    some (c, s) ∈ squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p c ↔
      s ∈ squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c := by
  simp [squareRootLowPrimeCanonicalOwnerFalloutFiber]

/-- A prime strictly above the largest prime factor of a positive integer is
fresh for that integer. -/
theorem squareRootLowPrimePrime_fresh_of_lpf_lt
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    ¬ p ∣ c := by
  intro hdiv
  by_cases hcOne : c = 1
  · subst c
    exact hp.not_dvd_one hdiv
  · have hcGt : 1 < c := by omega
    have hmem : p ∈ c.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdiv, by omega⟩
    have hle : p ≤ canonicalLargestPrimeFactor c := by
      unfold canonicalLargestPrimeFactor
      rw [dif_pos hcGt]
      exact Finset.le_max' c.primeFactors p hmem
    omega

/-- **Pointwise fallout = exact seat tail.**

Under canonical arithmetic legality of the parent, membership in the intrinsic
fixed-owner fallout set is equivalent to membership in the explicit lost-seat
interval. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_iff_seatIndex
    {R K j U p c s : ℕ}
    (hp : p.Prime) (hpU : p ≤ U)
    (hcSigned : c ∈ squareRootLowPrimeProcessedSignedCofactors R U)
    (hrough : canonicalLargestPrimeFactor c < p) :
    some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p ↔
      s ∈ squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c := by
  have hcRange := (Finset.mem_filter.mp hcSigned).1
  have hcOne : 1 ≤ c := (Finset.mem_Icc.mp hcRange).1
  have hcPos : 0 < c := by omega
  have hpFresh : ¬ p ∣ c :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hcPos hp hrough
  constructor
  · intro hfall
    rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
      ⟨hparent, _hhead, _hpFresh, _hmissing, _hrough⟩
    have hparentAtom :
        (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
    have hsParent :
        s < squareRootLowPrimeCombinedFreshResponse R K j c :=
      (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).2
    have hobs :=
      squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_carrierObstruction
        hp hpU hfall
    by_cases hwall : squareRootEndpoint R < p * c
    · simpa [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices, hwall]
        using hsParent
    · have hseat :
          squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s :=
        hobs.resolve_left hwall
      simpa [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices, hwall] using
        (Finset.mem_Ico.mpr ⟨hseat, hsParent⟩)
  · intro hsLost
    by_cases hwall : squareRootEndpoint R < p * c
    · have hsParent :
          s < squareRootLowPrimeCombinedFreshResponse R K j c := by
        simpa [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices, hwall]
          using hsLost
      have hparentAtom :
          (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
        mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hcSigned, hsParent⟩
      have hparent :
          some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
        unfold squareRootLowPrimeProcessedSeatCarrier
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨(c, s), hparentAtom, rfl⟩)
      have hchildMissing :
          squareRootLowPrimeProcessedSeatExtend p (some (c, s)) ∉
            squareRootLowPrimeProcessedSeatCarrier R K j U := by
        intro hchild
        have hchild' :
            some (p * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
          simpa [squareRootLowPrimeProcessedSeatExtend] using hchild
        have hchildAtom :
            (p * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
          simpa [squareRootLowPrimeProcessedSeatCarrier] using hchild'
        have hpcSigned :=
          (mem_squareRootLowPrimeProcessedSeatAtoms.mp hchildAtom).1
        have hpcRange := (Finset.mem_filter.mp hpcSigned).1
        have hpcUpper := (Finset.mem_Icc.mp hpcRange).2
        omega
      exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
        ⟨hparent, by simp, by simpa [squareRootLowPrimeProcessedStateCofactor],
          hchildMissing,
          by simpa [squareRootLowPrimeProcessedStateCofactor]⟩
    · have hsData :
          squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s ∧
            s < squareRootLowPrimeCombinedFreshResponse R K j c := by
        simpa [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices, hwall]
          using hsLost
      have hparentAtom :
          (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
        mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hcSigned, hsData.2⟩
      have hparent :
          some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
        unfold squareRootLowPrimeProcessedSeatCarrier
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨(c, s), hparentAtom, rfl⟩)
      have hchildMissing :
          squareRootLowPrimeProcessedSeatExtend p (some (c, s)) ∉
            squareRootLowPrimeProcessedSeatCarrier R K j U := by
        intro hchild
        have hchild' :
            some (p * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
          simpa [squareRootLowPrimeProcessedSeatExtend] using hchild
        have hchildAtom :
            (p * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
          simpa [squareRootLowPrimeProcessedSeatCarrier] using hchild'
        have hsChild :
            s < squareRootLowPrimeCombinedFreshResponse R K j (p * c) :=
          (mem_squareRootLowPrimeProcessedSeatAtoms.mp hchildAtom).2
        omega
      exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
        ⟨hparent, by simp, by simpa [squareRootLowPrimeProcessedStateCofactor],
          hchildMissing,
          by simpa [squareRootLowPrimeProcessedStateCofactor]⟩

/-- Fallout fibres over distinct cofactors are disjoint. -/
theorem squareRootLowPrimeCanonicalOwnerFalloutFiber_pairwiseDisjoint
    (R K j U p : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeCanonicalOwnerParentCofactors R U p))
      (squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p) := by
  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p c)
    (squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p d)
  rw [Finset.disjoint_left]
  intro x hxc hxd
  rcases Finset.mem_image.mp hxc with ⟨s, _hs, hsx⟩
  rcases Finset.mem_image.mp hxd with ⟨t, _ht, htx⟩
  have hpair : (c, s) = (d, t) :=
    Option.some.inj (hsx.trans htx.symm)
  exact hcd (congrArg Prod.fst hpair)

/-- **The complete fixed-owner fallout is the disjoint union of its exact
cofactor seat tails.** -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_eq_biUnion
    {R K j U p : ℕ} (hp : p.Prime) (hpU : p ≤ U) :
    squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p =
      (squareRootLowPrimeCanonicalOwnerParentCofactors R U p).biUnion
        (squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p) := by
  ext x
  constructor
  · intro hfall
    rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
      ⟨hparent, hhead, _hpFresh, _hmissing, hrough0⟩
    rcases x with _ | z
    · exact (hhead rfl).elim
    · rcases z with ⟨c, s⟩
      have hparentAtom :
          (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
        simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
      have hcSigned :=
        (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).1
      have hrough : canonicalLargestPrimeFactor c < p := by
        simpa [squareRootLowPrimeProcessedStateCofactor] using hrough0
      have hsLost :=
        (squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_iff_seatIndex
          hp hpU hcSigned hrough).mp hfall
      apply Finset.mem_biUnion.mpr
      refine ⟨c,
        mem_squareRootLowPrimeCanonicalOwnerParentCofactors.mpr
          ⟨hcSigned, hrough⟩, ?_⟩
      exact mem_squareRootLowPrimeCanonicalOwnerFalloutFiber.mpr hsLost
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, hcEligible, hxc⟩
    rcases Finset.mem_image.mp hxc with ⟨s, hsLost, hsx⟩
    have hcData :=
      mem_squareRootLowPrimeCanonicalOwnerParentCofactors.mp hcEligible
    rw [← hsx]
    exact
      (squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_iff_seatIndex
        hp hpU hcData.1 hcData.2).mpr hsLost

/-- Signed mass of one cofactor fallout fibre. -/
theorem squareRootLowPrimeCanonicalOwnerFalloutFiber_weight_sum
    (R K j p c : ℕ) :
    (∑ x ∈ squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p c,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c : ℝ) := by
  unfold squareRootLowPrimeCanonicalOwnerFalloutFiber
  calc
    (∑ x ∈
        (squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c).image
          (fun s => some (c, s)),
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ s ∈ squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c,
        squareRootLowPrimeProcessedSeatWeightReal (some (c, s)) := by
      apply Finset.sum_image
      intro a _ha b _hb hab
      simpa using hab
    _ = ∑ _s ∈ squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c,
        ((-μ c : ℤ) : ℝ) := by
      rfl
    _ = ((-μ c : ℤ) : ℝ) *
        ((squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c).card : ℝ) := by
      simp
      ring
    _ = ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c : ℝ) := by
      rw [card_squareRootLowPrimeCanonicalOwnerFalloutSeatIndices]

/-- **Exact fixed-owner signed fallout mass.**  Literal seat multiplicity has
been compressed to one arithmetic width per canonical parent cofactor. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_weight_sum
    {R K j U p : ℕ} (hp : p.Prime) (hpU : p ≤ U) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ c ∈ squareRootLowPrimeCanonicalOwnerParentCofactors R U p,
        ((-μ c : ℤ) : ℝ) *
          (squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c : ℝ) := by
  rw [squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_eq_biUnion hp hpU]
  rw [Finset.sum_biUnion
    (squareRootLowPrimeCanonicalOwnerFalloutFiber_pairwiseDisjoint R K j U p)]
  apply Finset.sum_congr rfl
  intro c _hc
  exact squareRootLowPrimeCanonicalOwnerFalloutFiber_weight_sum R K j p c

/-- Every chronological first-owner slice is contained in the corresponding
fixed-owner fallout set.  Thus the exact width formula above is the ambient
horizontal carrier for the disjoint terminal slices. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_subset_falloff
    {ps : List ℕ} {S T : Finset SquareRootLowPrimeProcessedState} {p : ℕ} :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p ⊆
      squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p := by
  intro x hx
  have howner :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hx).2
  exact (squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_some_mem howner).2

/-! ## First-owner wall fallout is confined to the low-owner boundary -/

/-- The first listed owner above `L` is no larger than any other listed
coordinate above `L`.  This packages the fact that the fresh-prime list is
sorted increasingly. -/
theorem squareRootLowPrimeFirstOwnerAbove_le_of_mem
    {K U L p q : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L = some p)
    (hq : q ∈ squareRootLowPrimeFreshPrimeList K U)
    (hLq : L < q) :
    p ≤ q := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, hpre, _hLp⟩
  have hsorted :
      List.Sorted (fun a b : ℕ => a ≤ b)
        (squareRootLowPrimeFreshPrimeList K U) := by
    unfold squareRootLowPrimeFreshPrimeList
    exact Finset.sort_sorted (· ≤ ·) _
  rw [hsplit] at hq hsorted
  rcases List.mem_append.mp hq with hqPre | hqTail
  · have hqLe := hpre q hqPre
    omega
  · rcases List.mem_cons.mp hqTail with rfl | hqPost
    · exact le_rfl
    · have htailSorted :
          List.Sorted (fun a b : ℕ => a ≤ b) (p :: post) :=
        (List.pairwise_append.mp hsorted).2.1
      exact (List.pairwise_cons.mp htailSorted).1 q hqPost

/-- A first scheduled owner is itself one of the fresh scheduled primes. -/
theorem squareRootLowPrimeFirstOwnerAbove_mem_freshPrimeList
    {K U L p : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L = some p) :
    p ∈ squareRootLowPrimeFreshPrimeList K U := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, _hpre, _hLp⟩
  rw [hsplit]
  simp

/-- **Deep-owner first fallout cannot cross the square wall.**

Assume the canonical owner of `c` is already beyond the shallow cutoff `K` and
`p` is the first scheduled prime above that owner.  Any parent seat gives a
literal deep partner prime `q > P⁺(c)` with `c*q <= X_R`.  Firstness of `p`
forces `p <= q` (whether `q` lies inside the processed list or beyond `U`), so
`p*c <= c*q <= X_R`. -/
theorem squareRootLowPrimeFirstOwnerFalloff_product_le_of_deepOwner
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R) (hUR : U < R)
    (hKOwner : K < canonicalLargestPrimeFactor c)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    p * c ≤ squareRootEndpoint R := by
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hparent, _hhead, _hpFresh, _hmissing, _hrough⟩
  have hparentAtom :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
  have hcSigned :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).1
  have hsParent :
      s < squareRootLowPrimeCombinedFreshResponse R K j c :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).2
  have hcData := Finset.mem_filter.mp hcSigned
  have hcOne : 1 ≤ c := (Finset.mem_Icc.mp hcData.1).1
  have hcPos : 0 < c := by omega
  have hcOwnerU : canonicalLargestPrimeFactor c ≤ U := hcData.2.1
  have hKc : K < c := by
    by_cases hcEq : c = 1
    · subst c
      simpa [canonicalLargestPrimeFactor] using hKOwner
    · have hcGt : 1 < c := by omega
      have hdiv := canonicalLargestPrimeFactor_dvd hcGt
      have hle : canonicalLargestPrimeFactor c ≤ c :=
        Nat.le_of_dvd hcPos hdiv
      exact hKOwner.trans_le hle
  have hresponsePos :
      0 < squareRootLowPrimeCombinedFreshResponse R K j c := by
    omega
  have hcard :=
    card_squareRootLowPrimeDeepPartnerSet_eq_combinedFreshResponse
      (R := R) (K := K) (j := j) (c := c) hR hcPos hKc
  have hcardPos : 0 < (squareRootLowPrimeDeepPartnerSet R c).card := by
    rw [hcard]
    exact hresponsePos
  rcases Finset.card_pos.mp hcardPos with ⟨q, hqPartner⟩
  have hqPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hqPartner
  have hqProduct :=
    mul_le_squareRootEndpoint_of_mem_deepPartnerSet hqPartner
  have hOwnerQ : canonicalLargestPrimeFactor c < q := by
    rcases Finset.mem_union.mp hqPartner with hqBorn | hqPost
    · exact (Finset.mem_filter.mp hqBorn).2.2.1
    · have hRq : R < q :=
        (Finset.mem_Ioc.mp (Finset.mem_filter.mp hqPost).1).1
      exact lt_of_le_of_lt hcOwnerU (hUR.trans hRq)
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, _hpre, _hLp⟩
  have hpList : p ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hsplit]
    simp
  have hpSet : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hpList
  have hpIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpSet).1
  have hpU : p ≤ U := hpIoc.2
  have hpq : p ≤ q := by
    by_cases hqU : q ≤ U
    · have hqSet : q ∈ squareRootLowPrimeFreshPrimeSet K U := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Ioc.mpr
          ⟨hKOwner.trans hOwnerQ, hqU⟩, hqPrime⟩
      have hqList : q ∈ squareRootLowPrimeFreshPrimeList K U := by
        simpa [squareRootLowPrimeFreshPrimeList] using hqSet
      exact squareRootLowPrimeFirstOwnerAbove_le_of_mem hfirst hqList hOwnerQ
    · have hUq : U < q := Nat.lt_of_not_ge hqU
      exact hpU.trans (Nat.le_of_lt hUq)
  calc
    p * c ≤ q * c := Nat.mul_le_mul_right c hpq
    _ = c * q := by ring
    _ ≤ squareRootEndpoint R := hqProduct

/-- Equivalently, a genuine first-owner square-wall event can occur only while
the parent's canonical owner is still at or below the shallow cutoff `K`. -/
theorem squareRootLowPrimeFirstOwnerFalloff_productWall_forces_lowOwner
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hwall : squareRootEndpoint R < p * c) :
    canonicalLargestPrimeFactor c ≤ K := by
  by_contra hnot
  have hdeep : K < canonicalLargestPrimeFactor c := Nat.lt_of_not_ge hnot
  have hinside :=
    squareRootLowPrimeFirstOwnerFalloff_product_le_of_deepOwner
      hR hUR hdeep hfirst hfall
  omega

/-- **A first-owner square-wall crossing forces the parent cofactor to have
reached the root.** -/
theorem squareRootLowPrimeFirstOwnerWall_forces_root_le_cofactor
    {R K U p c : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c) :
    R ≤ c := by
  have hpList := squareRootLowPrimeFirstOwnerAbove_mem_freshPrimeList hfirst
  have hpSet : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hpList
  have hpData := Finset.mem_filter.mp hpSet
  have hpPrime : p.Prime := hpData.2
  have hpU : p ≤ U := (Finset.mem_Ioc.mp hpData.1).2
  have hpR : p < R := hpU.trans_lt hUR
  by_contra hnot
  have hcR : c < R := Nat.lt_of_not_ge hnot
  have hcPos : 0 < c := by
    by_contra hc0
    have hcZero : c = 0 := Nat.eq_zero_of_not_pos hc0
    rw [hcZero, Nat.mul_zero] at hwall
    omega
  have hprod : p * c < R * R := by
    calc
      p * c < R * c := Nat.mul_lt_mul_of_pos_right hpR hcPos
      _ < R * R := Nat.mul_lt_mul_of_pos_left hcR (by omega)
  have hprod' : p * c < R ^ 2 := by
    simpa [pow_two] using hprod
  unfold squareRootEndpoint at hwall
  omega

/-- At or beyond the root the processed combined response is purely born: the
honest high channel has already ended. -/
theorem squareRootLowPrimeCombinedFreshResponse_eq_born_of_root_le
    {R K j c : ℕ} (hR : 1 ≤ R) (hcR : R ≤ c) :
    squareRootLowPrimeCombinedFreshResponse R K j c =
      squareRootBornPartnerCount R c := by
  unfold squareRootLowPrimeCombinedFreshResponse
  have hnot : ¬ c ≤ R - 1 := by omega
  simp [hnot]

/-- **Every born partner on a first-owner wall is an old prime `q <= K`.**

The born product satisfies `c*q <= X_R`, whereas the first scheduled owner has
`X_R < c*p`; hence `q < p`.  If `q` were also fresh (`K < q`), it would appear
in the increasing schedule before `p`, contradicting firstness. -/
theorem squareRootLowPrimeFirstOwnerWall_bornPartner_le_shallowCutoff
    {R K U p c q : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c)
    (hq : q ∈ squareRootBornPartnerSet R c) :
    q ≤ K := by
  rcases Finset.mem_filter.mp hq with
    ⟨_hqRange, hqPrime, hrough, hqc, hqProduct⟩
  have hcPos : 0 < c := lt_of_lt_of_le hqPrime.pos hqc
  have hqp : q < p := by
    by_contra hnot
    have hpq : p ≤ q := Nat.le_of_not_gt hnot
    have hmul : p * c ≤ q * c := Nat.mul_le_mul_right c hpq
    have hmul' : p * c ≤ c * q := by
      simpa [Nat.mul_comm] using hmul
    omega
  by_contra hnotK
  have hKq : K < q := Nat.lt_of_not_ge hnotK
  have hpList := squareRootLowPrimeFirstOwnerAbove_mem_freshPrimeList hfirst
  have hpSet : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hpList
  have hpU : p ≤ U := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpSet).1).2
  have hqU : q ≤ U := (Nat.le_of_lt hqp).trans hpU
  have hqSet : q ∈ squareRootLowPrimeFreshPrimeSet K U := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hKq, hqU⟩, hqPrime⟩
  have hqList : q ∈ squareRootLowPrimeFreshPrimeList K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hqSet
  have hpq := squareRootLowPrimeFirstOwnerAbove_le_of_mem
    hfirst hqList hrough
  omega

/-- The full born partner set of a first-owner wall is supported on the old
prime interval `[2,K]`. -/
theorem squareRootLowPrimeFirstOwnerWall_bornPartnerSet_subset_Icc
    {R K U p c : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c) :
    squareRootBornPartnerSet R c ⊆ Finset.Icc 2 K := by
  intro q hq
  have hqRange := (Finset.mem_filter.mp hq).1
  have hqTwo : 2 ≤ q := (Finset.mem_Icc.mp hqRange).1
  exact Finset.mem_Icc.mpr
    ⟨hqTwo,
      squareRootLowPrimeFirstOwnerWall_bornPartner_le_shallowCutoff
        hfirst hwall hq⟩

/-- **Exact wall width = old-prime born multiplicity.** -/
theorem squareRootLowPrimeFirstOwnerWall_falloutWidth_eq_born
    {R K j U p c : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c) :
    squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c =
      squareRootBornPartnerCount R c := by
  have hcR := squareRootLowPrimeFirstOwnerWall_forces_root_le_cofactor
    hR hUR hfirst hwall
  unfold squareRootLowPrimeCanonicalOwnerFalloutWidth
  rw [if_pos hwall,
    squareRootLowPrimeCombinedFreshResponse_eq_born_of_root_le (by omega) hcR]

end RHLean.Proof
