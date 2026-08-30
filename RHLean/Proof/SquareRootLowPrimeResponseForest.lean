import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseFrontier
import RHLean.Proof.CanonicalGapAncestryBridge

/-!
# Internal closure of the signed low-prime response forest

Every complete response atom is a fresh prime extension `(c,q)` with
`P+(c) < q`.  If the partner `q` is still inside the processed prime interval,
then the child `c*q` is itself an owned response cofactor at the later owner
`q`, and its Möbius orientation is the opposite of the parent orientation.
Thus the born response is not a collection of unrelated weighted errors: it is
a finite directed forest.

The only children that leave this forest are

* born frontier atoms with `q > U`; and
* post-root atoms with `q > R`.

The first class is already bounded by `2R` at the canonical terminal cutoff in
`SquareRootLowPrimeResponseFrontier`.  The second class is exactly the native
transport-root orientation of the repository's canonical ancestry flow.  This
file proves those identifications and an exact forest-boundary identity before
any norm is taken.

No estimate for the post-root transport roots, no PNT input, no covariance
normalization, and no energy decrement is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The complete cofactor carrier underlying the signed response forest. -/
def squareRootLowPrimeOwnedResponseCofactors
    (R K U : ℕ) : Finset ℕ :=
  squareRootLowPrimeOwnedBadCofactors R K U ∪
    squareRootLowPrimeOwnedDeletionCofactors R K U

@[simp] theorem mem_squareRootLowPrimeOwnedResponseCofactors
    {R K U c : ℕ} :
    c ∈ squareRootLowPrimeOwnedResponseCofactors R K U ↔
      c ∈ squareRootLowPrimeOwnedBadCofactors R K U ∨
        c ∈ squareRootLowPrimeOwnedDeletionCofactors R K U := by
  simp [squareRootLowPrimeOwnedResponseCofactors]

/-- A bad cofactor is owned by its canonical largest prime in the selected
fresh-prime interval. -/
theorem canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedBadCofactors
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedBadCofactors R K U) :
    canonicalLargestPrimeFactor c ∈ squareRootLowPrimeFreshPrimeSet K U := by
  unfold squareRootLowPrimeOwnedBadCofactors at hc
  rcases Finset.mem_biUnion.mp hc with ⟨p, hp, hcp⟩
  have hlpf : canonicalLargestPrimeFactor c = p :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hcp).1).2
  simpa [hlpf] using hp

/-- A deletion cofactor is owned by its canonical largest prime in the selected
fresh-prime interval. -/
theorem canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedDeletionCofactors
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedDeletionCofactors R K U) :
    canonicalLargestPrimeFactor c ∈ squareRootLowPrimeFreshPrimeSet K U := by
  unfold squareRootLowPrimeOwnedDeletionCofactors at hc
  rcases Finset.mem_biUnion.mp hc with ⟨p, hp, hcp⟩
  have hlpf : canonicalLargestPrimeFactor c = p :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hcp).1).2
  simpa [hlpf] using hp

/-- Every response cofactor is owned by one actual prime in `(K,U]`. -/
theorem canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedResponseCofactors
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U) :
    canonicalLargestPrimeFactor c ∈ squareRootLowPrimeFreshPrimeSet K U := by
  rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hc with hc | hc
  · exact
      canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedBadCofactors hc
  · exact
      canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedDeletionCofactors hc

/-- The cofactor coordinate of every response atom lies in the complete owned
cofactor carrier. -/
theorem squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors
    {R K U : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeOwnedResponseAtoms R K U) :
    z.1 ∈ squareRootLowPrimeOwnedResponseCofactors R K U := by
  unfold squareRootLowPrimeOwnedResponseAtoms at hz
  rcases Finset.mem_union.mp hz with hzBad | hzDeletion
  · unfold squareRootLowPrimeOwnedBadAtoms at hzBad
    rcases Finset.mem_biUnion.mp hzBad with ⟨c, hc, hzc⟩
    have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
    apply mem_squareRootLowPrimeOwnedResponseCofactors.mpr
    left
    simpa [hzcData.1] using hc
  · unfold squareRootLowPrimeOwnedDeletionAtoms at hzDeletion
    rcases Finset.mem_biUnion.mp hzDeletion with ⟨c, hc, hzc⟩
    have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
    apply mem_squareRootLowPrimeOwnedResponseCofactors.mpr
    right
    simpa [hzcData.1] using hc

/-- The owner of an atom's cofactor is an actual fresh prime in `(K,U]`. -/
theorem squareRootLowPrimeOwnedResponseAtom_owner_mem_freshPrimeSet
    {R K U : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeOwnedResponseAtoms R K U) :
    canonicalLargestPrimeFactor z.1 ∈
      squareRootLowPrimeFreshPrimeSet K U :=
  canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedResponseCofactors
    (squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors hz)

/-- Every response cofactor has nonzero Möbius orientation. -/
theorem squareRootLowPrimeOwnedResponseCofactor_moebius_eq_one_or_neg_one
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U) :
    μ c = 1 ∨ μ c = -1 := by
  rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hc with hc | hc
  · exact Or.inl (squareRootLowPrimeOwnedBadCofactor_data hc).2.2.2
  · exact Or.inr (squareRootLowPrimeOwnedDeletionCofactor_data hc).2.2.2

/-- An internal born atom advances to a later prime owner and flips from the bad
orientation to the deletion orientation, or conversely. -/
theorem squareRootLowPrimeBornInternalAtom_child_mem_oppositeCofactorCarrier
    {R K U : ℕ} (hUR : U < R) {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeBornInternalAtoms R K U) :
    (z ∈ squareRootLowPrimeOwnedBadAtoms R K U ∧
        squareRootLowPrimeBadAtomChild z ∈
          squareRootLowPrimeOwnedDeletionCofactors R K U) ∨
      (z ∈ squareRootLowPrimeOwnedDeletionAtoms R K U ∧
        squareRootLowPrimeBadAtomChild z ∈
          squareRootLowPrimeOwnedBadCofactors R K U) := by
  rcases mem_squareRootLowPrimeBornInternalAtoms.mp hz with
    ⟨hzResponse, hzBorn, hqU⟩
  have howner :=
    squareRootLowPrimeOwnedResponseAtom_owner_mem_freshPrimeSet hzResponse
  have hownerData := Finset.mem_filter.mp howner
  have hKowner := (Finset.mem_Ioc.mp hownerData.1).1
  have hbornData := Finset.mem_filter.mp hzBorn
  have hqPrime : z.2.Prime := hbornData.2.1
  have hrough : canonicalLargestPrimeFactor z.1 < z.2 :=
    hbornData.2.2.1
  have hKq : K < z.2 := hKowner.trans hrough
  have hqFresh : z.2 ∈ squareRootLowPrimeFreshPrimeSet K U :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hKq, hqU⟩, hqPrime⟩
  have hzData := squareRootLowPrimeOwnedResponseAtom_data hzResponse
  have hchildRange :
      squareRootLowPrimeBadAtomChild z ∈
        Finset.Icc 1 (squareRootEndpoint R) := by
    unfold squareRootLowPrimeBadAtomChild
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (Nat.ne_of_gt hzData.1) hqPrime.ne_zero),
        hbornData.2.2.2.2⟩
  have hlpfChild :
      canonicalLargestPrimeFactor (squareRootLowPrimeBadAtomChild z) = z.2 := by
    unfold squareRootLowPrimeBadAtomChild
    exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hzData.1 hqPrime hrough
  have hchildFresh :
      squareRootLowPrimeBadAtomChild z ∈
        squareRootLowPrimeBornFreshCofactors R z.2 := by
    unfold squareRootLowPrimeBornFreshCofactors
    exact Finset.mem_filter.mpr ⟨hchildRange, hlpfChild⟩
  unfold squareRootLowPrimeOwnedResponseAtoms at hzResponse
  rcases Finset.mem_union.mp hzResponse with hzBad | hzDeletion
  · have hweight :=
      squareRootLowPrimeOwnedBadAtomChild_moebiusWeight_eq_neg_one
        hUR hzBad
    have hmu : μ (squareRootLowPrimeBadAtomChild z) = -1 := by
      unfold canonicalMoebiusWeight at hweight
      exact_mod_cast hweight
    have hchildDeletion :
        squareRootLowPrimeBadAtomChild z ∈
          squareRootLowPrimeDeletionCofactors R z.2 := by
      unfold squareRootLowPrimeDeletionCofactors
      exact Finset.mem_filter.mpr ⟨hchildFresh, hmu⟩
    left
    refine ⟨hzBad, ?_⟩
    unfold squareRootLowPrimeOwnedDeletionCofactors
    exact Finset.mem_biUnion.mpr
      ⟨z.2, hqFresh, hchildDeletion⟩
  · have hweight :=
      squareRootLowPrimeOwnedDeletionAtomChild_moebiusWeight_eq_one
        hUR hzDeletion
    have hmu : μ (squareRootLowPrimeBadAtomChild z) = 1 := by
      unfold canonicalMoebiusWeight at hweight
      exact_mod_cast hweight
    have hchildBad :
        squareRootLowPrimeBadAtomChild z ∈
          squareRootLowPrimeBadCofactors R z.2 := by
      unfold squareRootLowPrimeBadCofactors
      exact Finset.mem_filter.mpr ⟨hchildFresh, hmu⟩
    right
    refine ⟨hzDeletion, ?_⟩
    unfold squareRootLowPrimeOwnedBadCofactors
    exact Finset.mem_biUnion.mpr ⟨z.2, hqFresh, hchildBad⟩

/-- Arithmetic children of the internal born response forest. -/
def squareRootLowPrimeBornInternalChildren
    (R K U : ℕ) : Finset ℕ :=
  (squareRootLowPrimeBornInternalAtoms R K U).image
    squareRootLowPrimeBadAtomChild

/-- **Internal closure.**  Every internal born child is another owned response
cofactor with the opposite Möbius orientation. -/
theorem squareRootLowPrimeBornInternalChildren_subset_ownedResponseCofactors
    {R K U : ℕ} (hUR : U < R) :
    squareRootLowPrimeBornInternalChildren R K U ⊆
      squareRootLowPrimeOwnedResponseCofactors R K U := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
  rcases
      squareRootLowPrimeBornInternalAtom_child_mem_oppositeCofactorCarrier
        hUR hz with h | h
  · exact mem_squareRootLowPrimeOwnedResponseCofactors.mpr (Or.inr h.2)
  · exact mem_squareRootLowPrimeOwnedResponseCofactors.mpr (Or.inl h.2)

/-- The internal child map remains injective. -/
theorem squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms
    {R K U : ℕ} (hUR : U < R) :
    Set.InjOn squareRootLowPrimeBadAtomChild
      (squareRootLowPrimeBornInternalAtoms R K U) := by
  intro z hz w hw hchild
  exact squareRootLowPrimeBadAtomChild_injOn_ownedResponseAtoms hUR
    (mem_squareRootLowPrimeBornInternalAtoms.mp hz).1
    (mem_squareRootLowPrimeBornInternalAtoms.mp hw).1 hchild

/-- Reindexing internal atoms by their arithmetic children loses no cardinality. -/
theorem card_squareRootLowPrimeBornInternalChildren
    {R K U : ℕ} (hUR : U < R) :
    (squareRootLowPrimeBornInternalChildren R K U).card =
      (squareRootLowPrimeBornInternalAtoms R K U).card := by
  unfold squareRootLowPrimeBornInternalChildren
  exact Finset.card_image_iff.mpr
    (squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms hUR)

/-- Response cofactors with no incoming internal born edge. -/
def squareRootLowPrimeResponseRootCofactors
    (R K U : ℕ) : Finset ℕ :=
  squareRootLowPrimeOwnedResponseCofactors R K U \
    squareRootLowPrimeBornInternalChildren R K U

/-- The owned cofactor carrier is the disjoint union of roots and internal
children. -/
theorem squareRootLowPrimeOwnedResponseCofactors_eq_roots_union_internalChildren
    {R K U : ℕ} (hUR : U < R) :
    squareRootLowPrimeOwnedResponseCofactors R K U =
      squareRootLowPrimeResponseRootCofactors R K U ∪
        squareRootLowPrimeBornInternalChildren R K U := by
  have hsub :
      squareRootLowPrimeBornInternalChildren R K U ⊆
        squareRootLowPrimeOwnedResponseCofactors R K U :=
    squareRootLowPrimeBornInternalChildren_subset_ownedResponseCofactors
      (R := R) (K := K) (U := U) hUR
  ext c
  unfold squareRootLowPrimeResponseRootCofactors
  constructor
  · intro hc
    by_cases hchild : c ∈ squareRootLowPrimeBornInternalChildren R K U
    · exact Finset.mem_union.mpr (Or.inr hchild)
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hc, hchild⟩))
  · intro hc
    rcases Finset.mem_union.mp hc with hroot | hchild
    · exact (Finset.mem_sdiff.mp hroot).1
    · exact hsub hchild

/-- Roots and incoming internal children are disjoint. -/
theorem squareRootLowPrimeResponseRootCofactors_disjoint_internalChildren
    (R K U : ℕ) :
    Disjoint (squareRootLowPrimeResponseRootCofactors R K U)
      (squareRootLowPrimeBornInternalChildren R K U) := by
  unfold squareRootLowPrimeResponseRootCofactors
  exact Finset.sdiff_disjoint

/-- Response atoms whose partner lies in the post-root transport range. -/
def squareRootLowPrimePostRootResponseAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeOwnedResponseAtoms R K U).filter fun z =>
    z.2 ∈ squareRootPostRootPrimePartnerSet R z.1

@[simp] theorem mem_squareRootLowPrimePostRootResponseAtoms
    {R K U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimePostRootResponseAtoms R K U ↔
      z ∈ squareRootLowPrimeOwnedResponseAtoms R K U ∧
        z.2 ∈ squareRootPostRootPrimePartnerSet R z.1 := by
  simp [squareRootLowPrimePostRootResponseAtoms]

/-- Every response atom is either born or post-root. -/
theorem squareRootLowPrimeOwnedResponseAtoms_eq_born_union_postRoot
    (R K U : ℕ) :
    squareRootLowPrimeOwnedResponseAtoms R K U =
      squareRootLowPrimeBornResponseAtoms R K U ∪
        squareRootLowPrimePostRootResponseAtoms R K U := by
  ext z
  simp only [Finset.mem_union, mem_squareRootLowPrimeBornResponseAtoms,
    mem_squareRootLowPrimePostRootResponseAtoms]
  constructor
  · intro hz
    have hzData := squareRootLowPrimeOwnedResponseAtom_data hz
    rcases Finset.mem_union.mp hzData.2.2.2 with hborn | hpost
    · exact Or.inl ⟨hz, hborn⟩
    · exact Or.inr ⟨hz, hpost⟩
  · rintro (hz | hz)
    · exact hz.1
    · exact hz.1

/-- Born and post-root response atoms are disjoint. -/
theorem squareRootLowPrimeBornResponseAtoms_disjoint_postRoot
    (R K U : ℕ) :
    Disjoint (squareRootLowPrimeBornResponseAtoms R K U)
      (squareRootLowPrimePostRootResponseAtoms R K U) := by
  rw [Finset.disjoint_left]
  intro z hzBorn hzPost
  have hb := mem_squareRootLowPrimeBornResponseAtoms.mp hzBorn
  have hp := mem_squareRootLowPrimePostRootResponseAtoms.mp hzPost
  exact
    (Finset.disjoint_left.mp
      (squareRootLowPrimeBornPartnerSet_disjoint_postRootPartnerSet R z.1))
      hb.2 hp.2

/-- Post-root response atoms are native canonical ancestry roots: the partner is
prime, the cofactor is positive and squarefree, every cofactor prime is smaller,
and the cofactor lies strictly below the partner. -/
theorem squareRootLowPrimePostRootResponseAtom_canonicalSourceData
    {R K U : ℕ} (hK : 1 ≤ K) (hUR : U < R) {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimePostRootResponseAtoms R K U) :
    CanonicalSourceData z.2 z.1 ∧ z.1 < z.2 := by
  rcases mem_squareRootLowPrimePostRootResponseAtoms.mp hz with
    ⟨hzResponse, hzPost⟩
  have hzData := squareRootLowPrimeOwnedResponseAtom_data hzResponse
  rcases Finset.mem_filter.mp hzPost with
    ⟨hqIoc, hqPrime, hproduct⟩
  have hRq : R < z.2 := (Finset.mem_Ioc.mp hqIoc).1
  have hrough :=
    canonicalLargestPrimeFactor_lt_partner_of_ownedResponseAtom hUR hzResponse
  have hcgt : 1 < z.1 := by omega
  have hcCarrier :=
    squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors hzResponse
  have hmuCases :=
    squareRootLowPrimeOwnedResponseCofactor_moebius_eq_one_or_neg_one hcCarrier
  have hmu0 : μ z.1 ≠ 0 := by
    rcases hmuCases with hmu | hmu <;> omega
  have hsq : Squarefree z.1 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu0
  have hnotdvd : ¬ z.2 ∣ z.1 := by
    intro hdiv
    have hle := prime_dvd_le_canonicalLargestPrimeFactor
      hcgt hqPrime hdiv
    omega
  have hcop : Nat.Coprime z.2 z.1 :=
    hqPrime.coprime_iff_not_dvd.mpr hnotdvd
  have hdom : ∀ p : ℕ, p.Prime → p ∣ z.1 → p < z.2 := by
    intro p hp hpc
    have hle := prime_dvd_le_canonicalLargestPrimeFactor hcgt hp hpc
    omega
  have hcDiv : z.1 ≤ squareRootEndpoint R / z.2 :=
    (Nat.le_div_iff_mul_le hqPrime.pos).2 hproduct
  have hRpos : 0 < R := by omega
  have hXltSquare : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsqpos : 0 < R ^ 2 := by positivity
    omega
  have hSquareLt : R ^ 2 < R * z.2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hRq hRpos
  have hXlt : squareRootEndpoint R < R * z.2 :=
    hXltSquare.trans hSquareLt
  have hdivlt : squareRootEndpoint R / z.2 < R :=
    (Nat.div_lt_iff_lt_mul hqPrime.pos).2 hXlt
  have hcR : z.1 < R := hcDiv.trans_lt hdivlt
  have hcq : z.1 < z.2 := hcR.trans hRq
  exact
    ⟨⟨hqPrime, Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hzData.1),
        hsq, hcop, hdom⟩,
      hcq⟩

/-- Signed Möbius mass of the complete owned cofactor carrier. -/
def squareRootLowPrimeOwnedResponseCofactorMass
    (R K U : ℕ) : ℂ :=
  ∑ c ∈ squareRootLowPrimeOwnedResponseCofactors R K U,
    canonicalMoebiusWeight c

/-- Signed Möbius mass of response roots. -/
def squareRootLowPrimeResponseRootCofactorMass
    (R K U : ℕ) : ℂ :=
  ∑ c ∈ squareRootLowPrimeResponseRootCofactors R K U,
    canonicalMoebiusWeight c

/-- Signed Möbius mass of internal born children. -/
def squareRootLowPrimeBornInternalChildMass
    (R K U : ℕ) : ℂ :=
  ∑ n ∈ squareRootLowPrimeBornInternalChildren R K U,
    canonicalMoebiusWeight n

/-- Signed Möbius mass of post-root response children. -/
def squareRootLowPrimePostRootChildMass
    (R K U : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimePostRootResponseAtoms R K U,
    canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)

/-- Internal atom mass is unchanged by injective reindexing to its child set. -/
theorem squareRootLowPrimeBornInternalChildMass_eq_atomMass
    {R K U : ℕ} (hUR : U < R) :
    squareRootLowPrimeBornInternalChildMass R K U =
      ∑ z ∈ squareRootLowPrimeBornInternalAtoms R K U,
        canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) := by
  unfold squareRootLowPrimeBornInternalChildMass
    squareRootLowPrimeBornInternalChildren
  apply Finset.sum_image
  intro z hz w hw hchild
  exact squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms hUR
    hz hw hchild

/-- The owned cofactor mass splits into root mass and incoming internal-child
mass. -/
theorem squareRootLowPrimeOwnedResponseCofactorMass_eq_root_add_internal
    {R K U : ℕ} (hUR : U < R) :
    squareRootLowPrimeOwnedResponseCofactorMass R K U =
      squareRootLowPrimeResponseRootCofactorMass R K U +
        squareRootLowPrimeBornInternalChildMass R K U := by
  have hsub :
      squareRootLowPrimeBornInternalChildren R K U ⊆
        squareRootLowPrimeOwnedResponseCofactors R K U :=
    squareRootLowPrimeBornInternalChildren_subset_ownedResponseCofactors
      (R := R) (K := K) (U := U) hUR
  unfold squareRootLowPrimeOwnedResponseCofactorMass
    squareRootLowPrimeResponseRootCofactorMass
    squareRootLowPrimeBornInternalChildMass
    squareRootLowPrimeResponseRootCofactors
  exact (Finset.sum_sdiff hsub).symm

/-- The complete signed child mass splits into internal born, born frontier,
and post-root populations. -/
theorem squareRootLowPrimeOwnedResponseAtomChildMass_eq_internal_add_frontier_add_postRoot
    (R K U : ℕ) :
    (∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
        canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)) =
      (∑ z ∈ squareRootLowPrimeBornInternalAtoms R K U,
          canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)) +
        squareRootLowPrimeBornFrontierChildMass R K U +
          squareRootLowPrimePostRootChildMass R K U := by
  have hBornPost :=
    squareRootLowPrimeBornResponseAtoms_disjoint_postRoot R K U
  have hIntFront :=
    squareRootLowPrimeBornInternalAtoms_disjoint_frontier R K U
  rw [squareRootLowPrimeOwnedResponseAtoms_eq_born_union_postRoot,
    Finset.sum_union hBornPost,
    squareRootLowPrimeBornResponseAtoms_eq_internal_union_frontier,
    Finset.sum_union hIntFront]
  rfl

/-- **Exact response-forest boundary identity.**  The negative complete child
mass is the root cofactor mass minus the complete cofactor mass, minus the born
exit frontier and the post-root transport-root mass. -/
theorem neg_squareRootLowPrimeOwnedResponseAtomChildMass_eq_forestBoundary
    {R K U : ℕ} (hUR : U < R) :
    -(∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
        canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)) =
      squareRootLowPrimeResponseRootCofactorMass R K U -
        squareRootLowPrimeOwnedResponseCofactorMass R K U -
          squareRootLowPrimeBornFrontierChildMass R K U -
            squareRootLowPrimePostRootChildMass R K U := by
  rw [squareRootLowPrimeOwnedResponseAtomChildMass_eq_internal_add_frontier_add_postRoot,
    ← squareRootLowPrimeBornInternalChildMass_eq_atomMass hUR]
  have hsplit :=
    squareRootLowPrimeOwnedResponseCofactorMass_eq_root_add_internal
      (R := R) (K := K) (U := U) hUR
  rw [hsplit]
  ring

/-- **Fresh response as a forest boundary.**  The exact sequential response on
`(K,U]` consists only of its bottom roots, complete cofactor mass, born exit
frontier, and post-root ancestry roots. -/
theorem squareRootLowPrimeFreshIncrement_sum_eq_responseForestBoundary
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrement R K j p) =
      squareRootLowPrimeResponseRootCofactorMass R K U -
        squareRootLowPrimeOwnedResponseCofactorMass R K U -
          squareRootLowPrimeBornFrontierChildMass R K U -
            squareRootLowPrimePostRootChildMass R K U := by
  rw [squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseAtomChildMass
    hR hUR]
  exact neg_squareRootLowPrimeOwnedResponseAtomChildMass_eq_forestBoundary
    (R := R) (K := K) (U := U) hUR

end RHLean.Proof
