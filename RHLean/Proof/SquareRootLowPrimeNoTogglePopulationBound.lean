import Mathlib
import RHLean.Proof.CanonicalSignedParent
import RHLean.Proof.SquareRootLowPrimeResponseForest

/-!
# Direct bounds for two genuine low-prime no-toggle populations

This file begins the quantitative residual attack after the exact carrier
infrastructure.  It does not introduce another weighted reindexing.

There are two distinct ways a literal response atom can fail to continue along
its canonical Euler edge.

* A born atom `(c,q)` has no later owned cofactor exactly when its partner prime
  has left the processed interval.  Thus its no-successor population is the
  already-bounded born exit frontier, of cardinality at most `2*R` at the
  canonical terminal cutoff.
* A post-root atom `(c,q)` has canonical predecessor
  `(canonicalCofactor c,q)`.  Whenever the predecessor still has an owner prime
  in `(K,U]`, downward closure of the hyperbolic condition keeps that
  predecessor inside the post-root response carrier.  Hence the interior high
  no-toggle population is empty.  Any high no-toggle is therefore supported at
  the lower owner cutoff, not throughout the processed prime interval.

These are direct population theorems.  They do not bound the unstable-pivot
population or finish the six-way residual estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Born response atoms whose arithmetic child has no later owned cofactor. -/
def squareRootLowPrimeBornNoSuccessorAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeBornResponseAtoms R K U).filter fun z =>
    squareRootLowPrimeBadAtomChild z ∉
      squareRootLowPrimeOwnedResponseCofactors R K U

@[simp] theorem mem_squareRootLowPrimeBornNoSuccessorAtoms
    {R K U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U ↔
      z ∈ squareRootLowPrimeBornResponseAtoms R K U ∧
        squareRootLowPrimeBadAtomChild z ∉
          squareRootLowPrimeOwnedResponseCofactors R K U := by
  simp [squareRootLowPrimeBornNoSuccessorAtoms]

/-- **Born no-toggle = born exit frontier.**  Internal born atoms always advance
into the opposite owned cofactor orientation; frontier atoms cannot do so
because their new largest prime exceeds `U`. -/
theorem squareRootLowPrimeBornNoSuccessorAtoms_eq_frontier
    {R K U : ℕ} (hUR : U < R) :
    squareRootLowPrimeBornNoSuccessorAtoms R K U =
      squareRootLowPrimeBornFrontierAtoms R K U := by
  ext z
  constructor
  · intro hz
    rcases mem_squareRootLowPrimeBornNoSuccessorAtoms.mp hz with
      ⟨hzBornResponse, hzNoChild⟩
    by_cases hqU : z.2 ≤ U
    · have hzInternal : z ∈ squareRootLowPrimeBornInternalAtoms R K U :=
        mem_squareRootLowPrimeBornInternalAtoms.mpr
          ⟨(mem_squareRootLowPrimeBornResponseAtoms.mp hzBornResponse).1,
            (mem_squareRootLowPrimeBornResponseAtoms.mp hzBornResponse).2,
            hqU⟩
      exact (hzNoChild
        (squareRootLowPrimeBornInternalChildren_subset_ownedResponseCofactors
          hUR (Finset.mem_image.mpr ⟨z, hzInternal, rfl⟩))).elim
    · exact mem_squareRootLowPrimeBornFrontierAtoms.mpr
        ⟨(mem_squareRootLowPrimeBornResponseAtoms.mp hzBornResponse).1,
          (mem_squareRootLowPrimeBornResponseAtoms.mp hzBornResponse).2,
          Nat.lt_of_not_ge hqU⟩
  · intro hz
    rcases mem_squareRootLowPrimeBornFrontierAtoms.mp hz with
      ⟨hzResponse, hzBorn, hUq⟩
    apply mem_squareRootLowPrimeBornNoSuccessorAtoms.mpr
    refine ⟨mem_squareRootLowPrimeBornResponseAtoms.mpr
      ⟨hzResponse, hzBorn⟩, ?_⟩
    intro hchild
    have howner :=
      canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedResponseCofactors
        hchild
    have hownerData := Finset.mem_filter.mp howner
    have hownerU := (Finset.mem_Ioc.mp hownerData.1).2
    have hzData := squareRootLowPrimeOwnedResponseAtom_data hzResponse
    have hqData := Finset.mem_filter.mp hzBorn
    have hlpfChild :
        canonicalLargestPrimeFactor (squareRootLowPrimeBadAtomChild z) = z.2 := by
      unfold squareRootLowPrimeBadAtomChild
      exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        hzData.1 hqData.2.1 hqData.2.2.1
    rw [hlpfChild] at hownerU
    omega

/-- **Direct terminal born no-toggle bound.** -/
theorem squareRootLowPrimeBornNoSuccessorAtoms_card_le_two_root
    (R K : ℕ) (hR : 1 ≤ R) :
    (squareRootLowPrimeBornNoSuccessorAtoms R K
      (squareRootBornPostTailLowPrimeCutoff R)).card ≤ 2 * R := by
  have hcut : squareRootBornPostTailLowPrimeCutoff R < R := by
    unfold squareRootBornPostTailLowPrimeCutoff
    have hsqrtPos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 (by omega)
    omega
  rw [squareRootLowPrimeBornNoSuccessorAtoms_eq_frontier hcut]
  exact squareRootLowPrimeBornFrontierAtoms_card_le_two_root R K

/-- Delete the canonical largest prime from the cofactor coordinate while
retaining the post-root partner. -/
def squareRootLowPrimePostRootCanonicalParentAtom
    (z : ℕ × ℕ) : ℕ × ℕ :=
  (canonicalCofactor z.1, z.2)

/-- Downward closure of the post-root hyperbolic partner condition. -/
theorem squareRootPostRootPrimePartnerSet_canonicalCofactor
    {R c q : ℕ} (hc : 1 < c)
    (hq : q ∈ squareRootPostRootPrimePartnerSet R c) :
    q ∈ squareRootPostRootPrimePartnerSet R (canonicalCofactor c) := by
  unfold squareRootPostRootPrimePartnerSet at hq ⊢
  rcases Finset.mem_filter.mp hq with ⟨hqRange, hqPrime, hcq⟩
  have hprod := canonicalCofactor_mul_largestPrimeFactor hc
  have hlpfPos : 0 < canonicalLargestPrimeFactor c :=
    (canonicalLargestPrimeFactor_prime hc).pos
  have hparentLe : canonicalCofactor c ≤ c := by
    calc
      canonicalCofactor c ≤
          canonicalCofactor c * canonicalLargestPrimeFactor c :=
        Nat.le_mul_of_pos_right _ hlpfPos
      _ = c := hprod
  exact Finset.mem_filter.mpr
    ⟨hqRange, hqPrime,
      (Nat.mul_le_mul_right q hparentLe).trans hcq⟩

/-- Rebuild an owned response atom from an owned cofactor and one admitted deep
partner. -/
theorem squareRootLowPrimeOwnedResponseAtom_of_cofactor_partner
    {R K U c q : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U)
    (hq : q ∈ squareRootLowPrimeDeepPartnerSet R c) :
    (c, q) ∈ squareRootLowPrimeOwnedResponseAtoms R K U := by
  rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hc with hcBad | hcDel
  · apply Finset.mem_union.mpr
    left
    unfold squareRootLowPrimeOwnedBadAtoms
    exact Finset.mem_biUnion.mpr
      ⟨c, hcBad, mem_squareRootLowPrimeBadAtomFiber.mpr ⟨rfl, hq⟩⟩
  · apply Finset.mem_union.mpr
    right
    unfold squareRootLowPrimeOwnedDeletionAtoms
    exact Finset.mem_biUnion.mpr
      ⟨c, hcDel, mem_squareRootLowPrimeBadAtomFiber.mpr ⟨rfl, hq⟩⟩

/-- If the canonical parent still has an owner in `(K,U]`, then it is itself an
owned signed response cofactor. -/
theorem squareRootLowPrimeCanonicalParent_mem_ownedResponseCofactors
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U)
    (hparentOwner : canonicalLargestPrimeFactor (canonicalCofactor c) ∈
      squareRootLowPrimeFreshPrimeSet K U) :
    canonicalCofactor c ∈
      squareRootLowPrimeOwnedResponseCofactors R K U := by
  have hcOwner :=
    canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedResponseCofactors hc
  have hcOwnerPrime := (Finset.mem_filter.mp hcOwner).2
  have hcSign := squareRootLowPrimeOwnedResponseCofactor_moebius_eq_one_or_neg_one hc
  have hcMuNe : μ c ≠ 0 := by
    rcases hcSign with h | h <;> omega
  have hsq : Squarefree c :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hcMuNe
  have hcPos : 0 < c := by
    rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hc with hcBad | hcDel
    · exact (squareRootLowPrimeOwnedBadCofactor_data hcBad).1
    · exact (squareRootLowPrimeOwnedDeletionCofactor_data hcDel).1
  have hcGt : 1 < c := by
    by_contra h
    have hcEq : c = 1 := by omega
    subst c
    norm_num [canonicalLargestPrimeFactor] at hcOwnerPrime
  have hflip := canonicalSignedParent_moebius hsq hcGt
  have hparentSign :
      μ (canonicalCofactor c) = 1 ∨ μ (canonicalCofactor c) = -1 := by
    rcases hcSign with hpos | hneg
    · right
      omega
    · left
      omega
  have hprod := canonicalCofactor_mul_largestPrimeFactor hcGt
  have hparentPos : 0 < canonicalCofactor c := by
    by_contra h
    have hzero : canonicalCofactor c = 0 := by omega
    rw [hzero, zero_mul] at hprod
    omega
  have hparentLe : canonicalCofactor c ≤ c := by
    calc
      canonicalCofactor c ≤
          canonicalCofactor c * canonicalLargestPrimeFactor c :=
        Nat.le_mul_of_pos_right _ hcOwnerPrime.pos
      _ = c := hprod
  have hcUpper : c ≤ squareRootEndpoint R := by
    rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hc with hcBad | hcDel
    · unfold squareRootLowPrimeOwnedBadCofactors at hcBad
      rcases Finset.mem_biUnion.mp hcBad with ⟨p, _hp, hcp⟩
      exact (Finset.mem_Icc.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hcp).1).1).2
    · unfold squareRootLowPrimeOwnedDeletionCofactors at hcDel
      rcases Finset.mem_biUnion.mp hcDel with ⟨p, _hp, hcp⟩
      exact (Finset.mem_Icc.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hcp).1).1).2
  have hparentFresh :
      canonicalCofactor c ∈ squareRootLowPrimeBornFreshCofactors R
        (canonicalLargestPrimeFactor (canonicalCofactor c)) := by
    unfold squareRootLowPrimeBornFreshCofactors
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hparentPos),
          hparentLe.trans hcUpper⟩,
        rfl⟩
  rcases hparentSign with hpos | hneg
  · apply mem_squareRootLowPrimeOwnedResponseCofactors.mpr
    left
    unfold squareRootLowPrimeOwnedBadCofactors
    exact Finset.mem_biUnion.mpr
      ⟨canonicalLargestPrimeFactor (canonicalCofactor c), hparentOwner,
        Finset.mem_filter.mpr ⟨hparentFresh, hpos⟩⟩
  · apply mem_squareRootLowPrimeOwnedResponseCofactors.mpr
    right
    unfold squareRootLowPrimeOwnedDeletionCofactors
    exact Finset.mem_biUnion.mpr
      ⟨canonicalLargestPrimeFactor (canonicalCofactor c), hparentOwner,
        Finset.mem_filter.mpr ⟨hparentFresh, hneg⟩⟩

/-- **Interior post-root downward closure.**  If the canonical parent still has
an owner prime in the processed interval, the literal parent atom remains in
the post-root response carrier. -/
theorem squareRootLowPrimePostRootCanonicalParentAtom_mem
    {R K U : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimePostRootResponseAtoms R K U)
    (hparentOwner :
      canonicalLargestPrimeFactor (canonicalCofactor z.1) ∈
        squareRootLowPrimeFreshPrimeSet K U) :
    squareRootLowPrimePostRootCanonicalParentAtom z ∈
      squareRootLowPrimePostRootResponseAtoms R K U := by
  rcases mem_squareRootLowPrimePostRootResponseAtoms.mp hz with
    ⟨hzResponse, hzPost⟩
  have hcOwned :=
    squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors hzResponse
  have hcOwner :=
    canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedResponseCofactors
      hcOwned
  have hcPrime := (Finset.mem_filter.mp hcOwner).2
  have hcPos := (squareRootLowPrimeOwnedResponseAtom_data hzResponse).1
  have hcGt : 1 < z.1 := by
    by_contra h
    have hcEq : z.1 = 1 := by omega
    rw [hcEq] at hcPrime
    norm_num [canonicalLargestPrimeFactor] at hcPrime
  have hparentOwned :=
    squareRootLowPrimeCanonicalParent_mem_ownedResponseCofactors
      hcOwned hparentOwner
  have hparentPost :=
    squareRootPostRootPrimePartnerSet_canonicalCofactor hcGt hzPost
  apply mem_squareRootLowPrimePostRootResponseAtoms.mpr
  refine ⟨?_, hparentPost⟩
  exact squareRootLowPrimeOwnedResponseAtom_of_cofactor_partner
    hparentOwned (Finset.mem_union.mpr (Or.inr hparentPost))

/-- Interior post-root atoms whose canonical predecessor is allegedly absent. -/
def squareRootLowPrimePostRootInteriorNoToggleAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimePostRootResponseAtoms R K U).filter fun z =>
    canonicalLargestPrimeFactor (canonicalCofactor z.1) ∈
        squareRootLowPrimeFreshPrimeSet K U ∧
      squareRootLowPrimePostRootCanonicalParentAtom z ∉
        squareRootLowPrimePostRootResponseAtoms R K U

/-- **The genuine interior high no-toggle population is empty.** -/
theorem squareRootLowPrimePostRootInteriorNoToggleAtoms_eq_empty
    (R K U : ℕ) :
    squareRootLowPrimePostRootInteriorNoToggleAtoms R K U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzPost, howner, hmissing⟩
  exact hmissing
    (squareRootLowPrimePostRootCanonicalParentAtom_mem hzPost howner)

/-- Direct cardinality form of the preceding vanishing theorem. -/
@[simp] theorem squareRootLowPrimePostRootInteriorNoToggleAtoms_card
    (R K U : ℕ) :
    (squareRootLowPrimePostRootInteriorNoToggleAtoms R K U).card = 0 := by
  rw [squareRootLowPrimePostRootInteriorNoToggleAtoms_eq_empty]
  simp

/-- The two directly controlled no-toggle populations have total cardinality at
most `2*R` at the canonical terminal cutoff. -/
theorem squareRootLowPrimeDirectNoTogglePopulations_card_le_two_root
    (R K : ℕ) (hR : 1 ≤ R) :
    (squareRootLowPrimeBornNoSuccessorAtoms R K
        (squareRootBornPostTailLowPrimeCutoff R)).card +
      (squareRootLowPrimePostRootInteriorNoToggleAtoms R K
        (squareRootBornPostTailLowPrimeCutoff R)).card ≤ 2 * R := by
  rw [squareRootLowPrimePostRootInteriorNoToggleAtoms_card]
  simpa using squareRootLowPrimeBornNoSuccessorAtoms_card_le_two_root R K hR

/-- Therefore absence of the post-root canonical predecessor can occur only
when the parent owner has left the processed prime interval. -/
theorem squareRootLowPrimePostRoot_noToggle_supported_at_owner_cutoff
    {R K U : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimePostRootResponseAtoms R K U)
    (hmissing : squareRootLowPrimePostRootCanonicalParentAtom z ∉
      squareRootLowPrimePostRootResponseAtoms R K U) :
    canonicalLargestPrimeFactor (canonicalCofactor z.1) ∉
      squareRootLowPrimeFreshPrimeSet K U := by
  intro howner
  exact hmissing
    (squareRootLowPrimePostRootCanonicalParentAtom_mem hz howner)

end RHLean.Proof
