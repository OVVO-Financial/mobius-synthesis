import RHLean.Proof.StableFarWallOwnedCensus
import RHLean.Proof.StableFarPrimeWallTransport
import RHLean.Proof.CanonicalGapAncestryBridge

/-!
# Crossing survivors are genuine lower-cofactor stable-wall occurrences

After the exact census of an earlier layer, a strict `q^2` crossing is represented by a
true product `(q, d*p)`, where `p` is the original far prime and `d` is the
cofactor left after stripping the fresh low prime `q`.

This file records the next signed-reassembly fact without taking a norm:
forgetting the stripped owner does not create an artificial arithmetic object.
The lower state `(d,p)` is itself a literal member of the original stable far
wall, and its native physical weight is the opposite of the crossing product's
Möbius weight.

The owner tag is deliberately retained in the sum.  Different crossing owners
may descend to the same lower stable-wall state, so no injectivity across owners
is asserted or used.  This is the renewal form needed for any subsequent
frontier cancellation: every surviving crossing is an actual signed return to
the same physical wall, with exact multiplicity.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom LowWheelCanonicalDowncrossOwnership
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The stable-wall state reached after forgetting only the crossing owner tag. -/
def lowWheelFarPrimeCrossingStableState
    (x : ℕ × ℕ) : LowWheelFullTaggedPhysicalState :=
  (∅, (canonicalCofactor x.2, canonicalLargestPrimeFactor x.2))

/-- Every strict crossing product returns to a literal state of the original
stable far wall.  No owner multiplicity is forgotten by this membership
statement. -/
theorem lowWheelFarPrimeCrossingStableState_mem
    {R : ℕ} (hR : 2 ≤ R) {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    lowWheelFarPrimeCrossingStableState x ∈ stableFarWallCarrier R := by
  rcases Finset.mem_image.mp hx with ⟨t, htCross, rfl⟩
  have ht : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htCross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hq, hqR, hd1, hp, hpR, hdsq, hdq, hcut⟩
  have hcoords := lowWheelFarPrimeProduct_coordinates ht
  have hlpf :
      canonicalLargestPrimeFactor (t.2.1 * t.2.2) = t.2.2 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.1
  have hcofactor :
      canonicalCofactor (t.2.1 * t.2.2) = t.2.1 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.2
  have hq1 : 1 ≤ t.1 := hq.one_le
  have hdpCut : t.2.1 * t.2.2 ≤ squareRootEndpoint R := by
    have hle : t.2.1 * t.2.2 ≤ t.1 * (t.2.1 * t.2.2) := by
      simpa using Nat.mul_le_mul_right (t.2.1 * t.2.2) hq1
    exact hle.trans (by simpa [Nat.mul_assoc] using hcut)
  have hRpos : 0 < R := by omega
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  have hpGeR : R ≤ t.2.2 := by omega
  have hdR : t.2.1 < R := by
    by_contra hnot
    have hRd : R ≤ t.2.1 := Nat.le_of_not_gt hnot
    have hR2 : R * R ≤ t.2.1 * t.2.2 := Nat.mul_le_mul hRd hpGeR
    exact (Nat.not_lt_of_ge (hR2.trans hdpCut)) hXlt
  apply (mem_stableFarWallCarrier_iff_primeInsertion hR).2
  change
    (∅ : Finset ℕ) = ∅ ∧
      (canonicalLargestPrimeFactor (t.2.1 * t.2.2)).Prime ∧
      R + 8 ≤ canonicalLargestPrimeFactor (t.2.1 * t.2.2) ∧
      canonicalLargestPrimeFactor (t.2.1 * t.2.2) ≤ squareRootEndpoint R ∧
      canonicalCofactor (t.2.1 * t.2.2) ∈ Finset.Ico 1 R ∧
      Squarefree (canonicalCofactor (t.2.1 * t.2.2)) ∧
      canonicalCofactor (t.2.1 * t.2.2) *
          canonicalLargestPrimeFactor (t.2.1 * t.2.2) ≤ squareRootEndpoint R
  rw [hlpf, hcofactor]
  refine ⟨rfl, hp, hpR, ?_, Finset.mem_Ico.mpr ⟨hd1, hdR⟩, hdsq, hdpCut⟩
  have hle : t.2.2 ≤ t.2.1 * t.2.2 := by
    simpa using Nat.mul_le_mul_right t.2.2 hd1
  exact hle.trans hdpCut

/-- Pointwise renewal sign: the returned stable-wall occurrence has exactly the
opposite weight of the crossing product. -/
theorem lowWheelFarPrimeCrossingStableState_weight_eq_neg_product
    {R : ℕ} (hR : 2 ≤ R) {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    lowWheelFullTaggedPhysicalWeight
        (lowWheelFarPrimeCrossingStableState x) =
      -canonicalMoebiusWeight x.2 := by
  have hmem := lowWheelFarPrimeCrossingStableState_mem hR hx
  have hweight := stableFarWall_singleInsertion_weight hR hmem
  have hxgt : 1 < x.2 := by
    rcases Finset.mem_image.mp hx with ⟨t, htCross, htx⟩
    have ht := (Finset.mem_filter.mp htCross).1
    have hfar := (lowWheelFarPrimeProduct_geometry ht).2.1
    have hfarx : R + 8 ≤ x.2 := by
      simpa [htx] using hfar
    omega
  have hprod := canonicalCofactor_mul_largestPrimeFactor hxgt
  unfold lowWheelFarPrimeCrossingStableState at hweight
  rw [hprod] at hweight
  exact hweight

/-- **Exact crossing-renewal mass identity.**  Every crossing survivor is the
negative of a genuine lower stable-wall occurrence.  The sum is still indexed
by the tagged crossing carrier, so repeated owners landing on the same lower
state remain repeated occurrences rather than being silently collapsed. -/
theorem lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        canonicalMoebiusWeight x.2) =
      -∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [lowWheelFarPrimeCrossingStableState_weight_eq_neg_product hR hx]
  ring

/-- The descended triples may be regrouped by every possible prime owner below
`R` without losing an occurrence.  This is finite Fubini only. -/
theorem lowWheelFarPrimeQ2DescendedMass_eq_ownerFibers (R : ℕ) :
    lowWheelFarPrimeQ2DescendedMass R =
      ∑ q ∈ primesUpTo (R - 1),
        ∑ t ∈ lowWheelFarPrimeQ2DescendedOwnerTriples R q,
          canonicalMoebiusWeight t.2.1 := by
  let S := lowWheelFarPrimeQ2DescendedTriples R
  let O := primesUpTo (R - 1)
  let owner : ℕ × (ℕ × ℕ) → ℕ := Prod.fst
  have hmaps : ∀ t ∈ S, owner t ∈ O := by
    intro t ht
    have hdata := lowWheelFarPrimeLowCofactorTriple_data
      (Finset.mem_filter.mp ht).1
    exact mem_primesUpTo.mpr ⟨hdata.1, Nat.le_pred_of_lt hdata.2.1⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := O) (g := owner) hmaps
    (fun t => canonicalMoebiusWeight t.2.1)
  have hraw :
      (∑ t ∈ S, canonicalMoebiusWeight t.2.1) =
        ∑ q ∈ O,
          ∑ t ∈ S with owner t = q,
            canonicalMoebiusWeight t.2.1 := hfiber.symm
  unfold lowWheelFarPrimeQ2DescendedMass
  change (∑ t ∈ S, canonicalMoebiusWeight t.2.1) =
    ∑ q ∈ O,
      ∑ t ∈ lowWheelFarPrimeQ2DescendedOwnerTriples R q,
        canonicalMoebiusWeight t.2.1
  rw [hraw]
  apply Finset.sum_congr rfl
  intro q hq
  rfl

/-- **Global descended-child identification.**  The complete stripped descended
mass is exactly the sum of the literal far-prime high-transport slices at every
q² child cutoff. -/
theorem lowWheelFarPrimeQ2DescendedMass_eq_sum_childFarSlices (R : ℕ) :
    lowWheelFarPrimeQ2DescendedMass R =
      ∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1 := by
  rw [lowWheelFarPrimeQ2DescendedMass_eq_ownerFibers R]
  apply Finset.sum_congr rfl
  intro q hq
  have hdata := mem_primesUpTo.mp hq
  have hRpos : 0 < R := by
    have := hdata.1.two_le
    omega
  have hqR : q < R := Nat.lt_of_le_pred hRpos hdata.2
  exact lowWheelFarPrimeQ2DescendedOwner_mass_eq_childFarSlice hdata.1 hqR

/-- Reattaching the original far prime reverses the child-far sign, so the true
descended product packet is the negative of the global child high-transport
slice sum. -/
theorem lowWheelFarPrimeDescendedProductMass_eq_neg_sum_childFarSlices
    (R : ℕ) :
    (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
        canonicalMoebiusWeight x.2) =
      -∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1 := by
  have hprod := lowWheelFarPrimeQ2DescendedMass_eq_neg_productMass R
  have hchild := lowWheelFarPrimeQ2DescendedMass_eq_sum_childFarSlices R
  rw [hchild] at hprod
  have hneg := congrArg Neg.neg hprod
  simpa using hneg.symm

/-- The four-term boundary in renewal form: all strict crossing mass is now
shown on the literal stable far wall, while the already-owned terminal product
population remains explicit.  This is still a signed identity, not an estimate. -/
theorem lowWheelFarWall_remainingBoundary_eq_neg_stableRenewal_sub_terminal
    {R : ℕ} (hR : 2 ≤ R) :
    lowWheelFarPrimeUnitFaceMass R - lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      -(∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
          lowWheelFullTaggedPhysicalWeight
            (lowWheelFarPrimeCrossingStableState x)) -
        ∑ n ∈ lowWheelFarWallTerminalProducts R,
          canonicalMoebiusWeight n := by
  rw [lowWheelFarWall_remainingBoundary_eq_signed_products R,
    lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass hR]

/-- **Complete residual in renewal normal form.**  The old hard far
residual is now the genuine descended q² product packet minus the literal
stable-wall renewal occurrences minus the terminal product carrier.  Every
crossing-owner multiplicity is still present in the middle sum, and no norm has
been taken. -/
theorem lowWheelFrozenTopFarResidual_eq_descended_sub_stableRenewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
        canonicalMoebiusWeight x.2) -
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) -
      ∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n := by
  rw [lowWheelFrozenTopFarResidual_eq_descended_add_crossing_sub_terminal R hR,
    lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass (by omega)]
  ring

/-- The same hard residual with its descended term rewritten ownerwise as the
literal lower-scale child far-transport slices from an earlier layer. -/
theorem lowWheelFrozenTopFarResidual_eq_neg_childFarSlices_sub_stableRenewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      -(∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) -
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) -
      ∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n := by
  rw [lowWheelFrozenTopFarResidual_eq_descended_sub_stableRenewal_sub_terminal R hR,
    lowWheelFarPrimeDescendedProductMass_eq_neg_sum_childFarSlices R]

/-! ## Strict crossing renewal has depth one

A strict `q^2` crossing has already stripped the largest prime `q` from a
nonunit low cofactor `q*d`.  If the returned cofactor `d` is nonunit, write
`d = r*e` with `r = P⁺(d)`.  Since `r < q`, the original inequality
`q*d*p ≤ X_R` implies `r^2*e*p ≤ X_R`.  Thus the return is descended at its
next canonical owner and cannot cross again. -/

/-- **Depth-one renewal.**  A nonunit strict crossing, after forgetting its
outer owner, is automatically descended at the returned cofactor's own
canonical largest-prime owner. -/
theorem lowWheelFarPrimeQ2Crossing_returned_nonUnit_descends
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (hd : 1 < d) :
    (canonicalLargestPrimeFactor d, (canonicalCofactor d, p)) ∈
      lowWheelFarPrimeQ2DescendedTriples R := by
  have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp ht).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
    ⟨hqPrime, hqR, _hd1, hpPrime, hpR, hdsq, hdq, hcut⟩
  let r := canonicalLargestPrimeFactor d
  let e := canonicalCofactor d
  have hrPrime : r.Prime := by
    dsimp [r]
    exact canonicalLargestPrimeFactor_prime hd
  have he1 : 1 ≤ e := by
    dsimp [e]
    exact canonicalCofactor_pos hd
  have hesq : Squarefree e := by
    dsimp [e]
    exact squarefree_canonicalCofactor hdsq hd
  have hrq : r < q := by
    simpa [r] using hdq
  have hrR : r < R := hrq.trans hqR
  have her : canonicalLargestPrimeFactor e < r := by
    dsimp [r, e]
    exact canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hd hdsq
  have hprod : r * e = d := by
    dsimp [r, e]
    simpa [Nat.mul_comm] using canonicalCofactor_mul_largestPrimeFactor hd
  have hnextCut : r * e * p ≤ squareRootEndpoint R := by
    rw [hprod]
    have hq1 : 1 ≤ q := hqPrime.one_le
    have hle : d * p ≤ q * (d * p) := by
      simpa using Nat.mul_le_mul_right (d * p) hq1
    exact hle.trans (by simpa [Nat.mul_assoc] using hcut)
  have hnextBase :
      (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    lowWheelFarPrimeLowCofactorTriple_mem_of_data
      hrPrime hrR he1 hpPrime hpR hesq her hnextCut
  apply Finset.mem_filter.mpr
  refine ⟨hnextBase, ?_⟩
  have hrleq : r ≤ q := Nat.le_of_lt hrq
  calc
    r * r * e * p = r * (r * e) * p := by ring
    _ = r * d * p := by rw [hprod]
    _ ≤ q * d * p := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (d * p) hrleq
    _ ≤ squareRootEndpoint R := hcut

/-- The returned nonunit state therefore lands in the literal next-owner
child-far slice consumed by the q-square recursion. -/
theorem lowWheelFarPrimeQ2Crossing_returned_nonUnit_mem_nextChildFarSlice
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (hd : 1 < d) :
    (canonicalCofactor d, p) ∈
      lowWheelFarPrimeQ2ChildFarSlice R (canonicalLargestPrimeFactor d) := by
  have hdesc := lowWheelFarPrimeQ2Crossing_returned_nonUnit_descends ht hd
  have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp ht).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
    ⟨_hqPrime, hqR, _hd1, _hpPrime, _hpR, _hdsq, hdq, _hcut⟩
  have hrPrime : (canonicalLargestPrimeFactor d).Prime :=
    canonicalLargestPrimeFactor_prime hd
  have hrR : canonicalLargestPrimeFactor d < R := hdq.trans hqR
  have howner :
      (canonicalLargestPrimeFactor d, (canonicalCofactor d, p)) ∈
        lowWheelFarPrimeQ2DescendedOwnerTriples R (canonicalLargestPrimeFactor d) :=
    Finset.mem_filter.mpr ⟨hdesc, rfl⟩
  have himage :
      (canonicalCofactor d, p) ∈
        (lowWheelFarPrimeQ2DescendedOwnerTriples R
          (canonicalLargestPrimeFactor d)).image Prod.snd :=
    Finset.mem_image.mpr
      ⟨(canonicalLargestPrimeFactor d, (canonicalCofactor d, p)), howner, rfl⟩
  rw [lowWheelFarPrimeQ2DescendedOwner_image_eq_childFarSlice hrPrime hrR] at himage
  exact himage

/-- A returned strict crossing has no second strict crossing at its next
canonical owner. -/
theorem lowWheelFarPrimeQ2Crossing_returned_nonUnit_not_crossing
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (hd : 1 < d) :
    (canonicalLargestPrimeFactor d, (canonicalCofactor d, p)) ∉
      lowWheelFarPrimeQ2CrossingTriples R := by
  have hdesc := lowWheelFarPrimeQ2Crossing_returned_nonUnit_descends ht hd
  intro hcross
  have hle := (Finset.mem_filter.mp hdesc).2
  have hgt := (Finset.mem_filter.mp hcross).2
  omega

/-- Every strict crossing return is therefore either the unit terminal state or
one literal next-owner child-far state. -/
theorem lowWheelFarPrimeQ2Crossing_returned_terminal_or_nextChild
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R) :
    d = 1 ∨
      (canonicalCofactor d, p) ∈
        lowWheelFarPrimeQ2ChildFarSlice R (canonicalLargestPrimeFactor d) := by
  by_cases hdone : d = 1
  · exact Or.inl hdone
  · right
    have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp ht).1
    have hd1 := (lowWheelFarPrimeLowCofactorTriple_data hbase).2.2.1
    have hdgt : 1 < d := lt_of_le_of_ne hd1 (Ne.symm hdone)
    exact lowWheelFarPrimeQ2Crossing_returned_nonUnit_mem_nextChildFarSlice ht hdgt

/-- **Pointwise signed cancellation currency.**  On a nonunit return, the
stable-wall cofactor weight is exactly the negative of the next child-far
cofactor weight. -/
theorem lowWheelFarPrimeQ2Crossing_returnedWeight_eq_neg_nextChildWeight
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (hd : 1 < d) :
    lowWheelFullTaggedPhysicalWeight ((∅ : Finset ℕ), (d, p)) =
      -canonicalMoebiusWeight (canonicalCofactor d) := by
  have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp ht).1
  have hsq := (lowWheelFarPrimeLowCofactorTriple_data hbase).2.2.2.2.2.1
  have hmu := canonicalSignedParent_moebius hsq hd
  unfold lowWheelFullTaggedPhysicalWeight canonicalMoebiusWeight
  simp only [booleanCubeSign, Finset.card_empty, pow_zero, Int.cast_one, mul_one]
  rw [hmu]
  push_cast
  ring

/-! ## One-generation multiplicity reindex

The preceding depth-one theorem allows every nonunit renewal occurrence to be
reindexed onto an actual descended child state.  Repeated outer owners are not
discarded: they become an explicit integer multiplicity on that child. -/

/-- Strict crossing triples whose returned cofactor has another canonical owner. -/
def lowWheelFarPrimeQ2NonUnitCrossingTriples (R : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeQ2CrossingTriples R).filter fun t => 1 < t.2.1

/-- The unique next-owner child reached from a nonunit crossing return. -/
def lowWheelFarPrimeQ2CrossingNextChild
    (t : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  (canonicalLargestPrimeFactor t.2.1,
    (canonicalCofactor t.2.1, t.2.2))

/-- The next child of every nonunit crossing is a literal descended state. -/
theorem lowWheelFarPrimeQ2CrossingNextChild_mem_descended
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R) :
    lowWheelFarPrimeQ2CrossingNextChild t ∈
      lowWheelFarPrimeQ2DescendedTriples R := by
  rcases t with ⟨q, ⟨d, p⟩⟩
  rcases Finset.mem_filter.mp ht with ⟨hcross, hd⟩
  simpa [lowWheelFarPrimeQ2CrossingNextChild] using
    lowWheelFarPrimeQ2Crossing_returned_nonUnit_descends hcross hd

/-- Number of outer crossing owners returning to one descended child state. -/
def lowWheelFarPrimeQ2CrossingNextMultiplicity
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : ℕ :=
  ((lowWheelFarPrimeQ2NonUnitCrossingTriples R).filter fun t =>
    lowWheelFarPrimeQ2CrossingNextChild t = y).card

/-- Nonunit returned stable-wall mass, still indexed by every crossing occurrence. -/
def lowWheelFarPrimeQ2NonUnitReturnedRenewalMass (R : ℕ) : ℂ :=
  ∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R,
    lowWheelFullTaggedPhysicalWeight ((∅ : Finset ℕ), (t.2.1, t.2.2))

/-- The same occurrences read in their next-child cofactor coordinate. -/
def lowWheelFarPrimeQ2NextChildIncidenceMass (R : ℕ) : ℂ :=
  ∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R,
    canonicalMoebiusWeight (canonicalCofactor t.2.1)

/-- Pointwise sign reversal turns the nonunit renewal mass into the negative
next-child incidence mass. -/
theorem lowWheelFarPrimeQ2NonUnitReturnedRenewalMass_eq_neg_nextChildIncidence
    (R : ℕ) :
    lowWheelFarPrimeQ2NonUnitReturnedRenewalMass R =
      -lowWheelFarPrimeQ2NextChildIncidenceMass R := by
  unfold lowWheelFarPrimeQ2NonUnitReturnedRenewalMass
    lowWheelFarPrimeQ2NextChildIncidenceMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rcases t with ⟨q, ⟨d, p⟩⟩
  rcases Finset.mem_filter.mp ht with ⟨hcross, hd⟩
  simpa using
    lowWheelFarPrimeQ2Crossing_returnedWeight_eq_neg_nextChildWeight hcross hd

/-- **Finite Fubini onto the descended carrier.**  The only price of forgetting
outer crossing owners is their exact multiplicity at each next child. -/
theorem lowWheelFarPrimeQ2NextChildIncidenceMass_eq_multiplicity
    (R : ℕ) :
    lowWheelFarPrimeQ2NextChildIncidenceMass R =
      ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ) *
          canonicalMoebiusWeight y.2.1 := by
  have hmaps : ∀ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R,
      lowWheelFarPrimeQ2CrossingNextChild t ∈
        lowWheelFarPrimeQ2DescendedTriples R := by
    intro t ht
    exact lowWheelFarPrimeQ2CrossingNextChild_mem_descended ht
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := lowWheelFarPrimeQ2NonUnitCrossingTriples R)
    (t := lowWheelFarPrimeQ2DescendedTriples R)
    (g := lowWheelFarPrimeQ2CrossingNextChild) hmaps
    (fun t => canonicalMoebiusWeight (canonicalCofactor t.2.1))
  have hraw :
      (∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R,
          canonicalMoebiusWeight (canonicalCofactor t.2.1)) =
        ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
          ∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R with
              lowWheelFarPrimeQ2CrossingNextChild t = y,
            canonicalMoebiusWeight (canonicalCofactor t.2.1) := hfiber.symm
  unfold lowWheelFarPrimeQ2NextChildIncidenceMass
  rw [hraw]
  apply Finset.sum_congr rfl
  intro y hy
  calc
    (∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R with
        lowWheelFarPrimeQ2CrossingNextChild t = y,
        canonicalMoebiusWeight (canonicalCofactor t.2.1)) =
      ∑ _t ∈ (lowWheelFarPrimeQ2NonUnitCrossingTriples R).filter
          (fun t => lowWheelFarPrimeQ2CrossingNextChild t = y),
        canonicalMoebiusWeight y.2.1 := by
          apply Finset.sum_congr rfl
          intro t ht
          have heq := (Finset.mem_filter.mp ht).2
          have hc := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1) heq
          simpa [lowWheelFarPrimeQ2CrossingNextChild] using
            congrArg canonicalMoebiusWeight hc
    _ = (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ) *
        canonicalMoebiusWeight y.2.1 := by
          simp [lowWheelFarPrimeQ2CrossingNextMultiplicity]

/-- The nonunit renewal is therefore an explicit negative multiplicity-weighted
copy of the existing descended child carrier. -/
theorem lowWheelFarPrimeQ2NonUnitReturnedRenewalMass_eq_neg_multiplicityChildMass
    (R : ℕ) :
    lowWheelFarPrimeQ2NonUnitReturnedRenewalMass R =
      -∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ) *
          canonicalMoebiusWeight y.2.1 := by
  rw [lowWheelFarPrimeQ2NonUnitReturnedRenewalMass_eq_neg_nextChildIncidence,
    lowWheelFarPrimeQ2NextChildIncidenceMass_eq_multiplicity]

/-- **Centered one-generation incidence identity.**  Adding the genuine
q-square descended child packet to all nonunit renewal returns leaves exactly
the coefficient `1 - multiplicity` on each descended child.  No recursive
renewal remains. -/
theorem lowWheelFarPrimeQ2DescendedMass_add_nonUnitRenewal_eq_centeredMultiplicity
    (R : ℕ) :
    lowWheelFarPrimeQ2DescendedMass R +
        lowWheelFarPrimeQ2NonUnitReturnedRenewalMass R =
      ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
          canonicalMoebiusWeight y.2.1 := by
  rw [lowWheelFarPrimeQ2NonUnitReturnedRenewalMass_eq_neg_multiplicityChildMass]
  unfold lowWheelFarPrimeQ2DescendedMass
  calc
    (∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        canonicalMoebiusWeight y.2.1) +
        -(∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
          (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ) *
            canonicalMoebiusWeight y.2.1) =
      (∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        canonicalMoebiusWeight y.2.1) -
        ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
          (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ) *
            canonicalMoebiusWeight y.2.1 := by ring
    _ = ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        (canonicalMoebiusWeight y.2.1 -
          (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ) *
            canonicalMoebiusWeight y.2.1) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
          canonicalMoebiusWeight y.2.1 := by
          apply Finset.sum_congr rfl
          intro y hy
          ring

/-- Child-far-slice form of the same centered identity. -/
theorem lowWheelFarPrimeChildFarSlices_add_nonUnitRenewal_eq_centeredMultiplicity
    (R : ℕ) :
    (∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) +
        lowWheelFarPrimeQ2NonUnitReturnedRenewalMass R =
      ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
          canonicalMoebiusWeight y.2.1 := by
  rw [← lowWheelFarPrimeQ2DescendedMass_eq_sum_childFarSlices R]
  exact lowWheelFarPrimeQ2DescendedMass_add_nonUnitRenewal_eq_centeredMultiplicity R

end RHLean.Proof
