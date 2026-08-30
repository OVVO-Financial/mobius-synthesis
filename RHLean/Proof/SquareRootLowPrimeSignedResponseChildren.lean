import Mathlib
import RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms

/-!
# Complete deep response as a signed canonical child mass

`SquareRootLowPrimeDeepResponseAtoms` expands every unit of the positive
orientation mass into a literal prime-extension atom `(c,q)`.  This file makes
the symmetric construction for the deletion orientation and then reunites the
two signs before taking any estimate.

For a deep prime interval `(K,U]` with `U < R`, every response atom satisfies

`P+(c) < q`,

so the arithmetic child `n = c*q` canonically recovers both coordinates:

`P+(n) = q` and `canonicalCofactor(n) = c`.

The child map is therefore injective on the union of the bad and deletion atom
carriers.  Since adjoining the fresh prime reverses the Möbius sign, the exact
signed interval response is

`sum_p Delta_p = - sum_{n in ResponseChildren} mu(n)`.

This identifies the complete weighted bad/deletion excess with one restricted
signed child set below `R^2-1`.  It does not bound that signed sum, prove an
energy decrement, or identify it with the earlier transition-seat shell.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The literal union of all negative-orientation cofactors in a fresh-prime
interval.  Distinct fibres are disjoint because the canonical largest prime is
unique. -/
def squareRootLowPrimeOwnedDeletionCofactors
    (R L U : ℕ) : Finset ℕ :=
  (squareRootLowPrimeFreshPrimeSet L U).biUnion
    (squareRootLowPrimeDeletionCofactors R)

/-- Deletion cofactor fibres over distinct fresh primes are pairwise disjoint. -/
theorem squareRootLowPrimeDeletionCofactors_pairwiseDisjoint
    (R L U : ℕ) :
    Set.PairwiseDisjoint (↑(squareRootLowPrimeFreshPrimeSet L U))
      (squareRootLowPrimeDeletionCofactors R) := by
  intro p _hp q _hq hpq
  change Disjoint (squareRootLowPrimeDeletionCofactors R p)
    (squareRootLowPrimeDeletionCofactors R q)
  rw [Finset.disjoint_left]
  intro c hcp hcq
  have hlpfp : canonicalLargestPrimeFactor c = p :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hcp).1).2
  have hlpfq : canonicalLargestPrimeFactor c = q :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hcq).1).2
  exact hpq (hlpfp.symm.trans hlpfq)

/-- The global deletion mass is one sum on its canonically owned cofactor
support. -/
theorem squareRootLowPrimeGlobalDeletionMass_eq_ownedCofactorSum
    (R K j L U : ℕ) :
    squareRootLowPrimeGlobalDeletionMass R K j L U =
      ∑ c ∈ squareRootLowPrimeOwnedDeletionCofactors R L U,
        squareRootLowPrimeCombinedFreshResponse R K j c := by
  unfold squareRootLowPrimeGlobalDeletionMass
    squareRootLowPrimeDeletionMass
    squareRootLowPrimeOwnedDeletionCofactors
  rw [← Finset.sum_biUnion
    (squareRootLowPrimeDeletionCofactors_pairwiseDisjoint R L U)]

/-- Arithmetic data forced by membership in the globally owned deletion
carrier. -/
theorem squareRootLowPrimeOwnedDeletionCofactor_data
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedDeletionCofactors R K U) :
    0 < c ∧ K < c ∧
      canonicalLargestPrimeFactor c ≤ U ∧ μ c = -1 := by
  unfold squareRootLowPrimeOwnedDeletionCofactors at hc
  rcases Finset.mem_biUnion.mp hc with ⟨p, hpSet, hcp⟩
  rcases Finset.mem_filter.mp hpSet with ⟨hpIoc, hpPrime⟩
  rcases Finset.mem_Ioc.mp hpIoc with ⟨hKp, hpU⟩
  unfold squareRootLowPrimeDeletionCofactors at hcp
  rcases Finset.mem_filter.mp hcp with ⟨hcFresh, hmu⟩
  unfold squareRootLowPrimeBornFreshCofactors at hcFresh
  rcases Finset.mem_filter.mp hcFresh with ⟨hcIcc, hlpf⟩
  rcases Finset.mem_Icc.mp hcIcc with ⟨hc1, _hcX⟩
  have hcne : c ≠ 1 := by
    intro hcEq
    subst c
    have hlpfOne : canonicalLargestPrimeFactor 1 = 1 := by
      simp [canonicalLargestPrimeFactor]
    rw [hlpfOne] at hlpf
    exact hpPrime.ne_one hlpf.symm
  have hcgt : 1 < c := by omega
  have hpDvd : p ∣ c := by
    rw [← hlpf]
    exact canonicalLargestPrimeFactor_dvd hcgt
  have hpLeC : p ≤ c := Nat.le_of_dvd (by omega) hpDvd
  refine ⟨by omega, hKp.trans_le hpLeC, ?_, hmu⟩
  rw [hlpf]
  exact hpU

/-- The complete atom carrier over the globally owned negative-orientation
cofactors in `(K,U]`. -/
def squareRootLowPrimeOwnedDeletionAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeOwnedDeletionCofactors R K U).biUnion
    (squareRootLowPrimeBadAtomFiber R)

/-- Distinct deletion-cofactor fibres of response atoms are disjoint. -/
theorem squareRootLowPrimeDeletionAtomFiber_pairwiseDisjoint
    (R K U : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeOwnedDeletionCofactors R K U))
      (squareRootLowPrimeBadAtomFiber R) := by
  intro c _hc d _hd hcd
  change Disjoint (squareRootLowPrimeBadAtomFiber R c)
    (squareRootLowPrimeBadAtomFiber R d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
  have hzdData := mem_squareRootLowPrimeBadAtomFiber.mp hzd
  exact hcd (hzcData.1.symm.trans hzdData.1)

/-- **Complete deletion-response atomization.**  The raw global deletion mass
on the deep interval is exactly the cardinality of its literal atom carrier. -/
theorem squareRootLowPrimeGlobalDeletionMass_eq_ownedDeletionAtoms_card
    {R K j U : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGlobalDeletionMass R K j K U =
      (squareRootLowPrimeOwnedDeletionAtoms R K U).card := by
  rw [squareRootLowPrimeGlobalDeletionMass_eq_ownedCofactorSum]
  symm
  calc
    (squareRootLowPrimeOwnedDeletionAtoms R K U).card =
        ∑ z ∈ squareRootLowPrimeOwnedDeletionAtoms R K U, 1 := by simp
    _ = ∑ c ∈ squareRootLowPrimeOwnedDeletionCofactors R K U,
          ∑ z ∈ squareRootLowPrimeBadAtomFiber R c, 1 := by
      unfold squareRootLowPrimeOwnedDeletionAtoms
      exact Finset.sum_biUnion
        (squareRootLowPrimeDeletionAtomFiber_pairwiseDisjoint R K U)
    _ = ∑ c ∈ squareRootLowPrimeOwnedDeletionCofactors R K U,
          (squareRootLowPrimeDeepPartnerSet R c).card := by
      apply Finset.sum_congr rfl
      intro c _hc
      simp [squareRootLowPrimeBadAtomFiber]
    _ = ∑ c ∈ squareRootLowPrimeOwnedDeletionCofactors R K U,
          squareRootLowPrimeCombinedFreshResponse R K j c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcData := squareRootLowPrimeOwnedDeletionCofactor_data hc
      exact card_squareRootLowPrimeDeepPartnerSet_eq_combinedFreshResponse
        (by omega) hcData.1 hcData.2.1

/-- Below the root, every partner of an owned deletion cofactor is larger than
all prime factors of that cofactor. -/
theorem canonicalLargestPrimeFactor_lt_partner_of_ownedDeletionAtom
    {R K U c q : ℕ} (hUR : U < R)
    (hc : c ∈ squareRootLowPrimeOwnedDeletionCofactors R K U)
    (hq : q ∈ squareRootLowPrimeDeepPartnerSet R c) :
    canonicalLargestPrimeFactor c < q := by
  rcases Finset.mem_union.mp hq with hborn | hpost
  · exact (Finset.mem_filter.mp hborn).2.2.1
  · have hcData := squareRootLowPrimeOwnedDeletionCofactor_data hc
    have hRq : R < q :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpost).1).1
    exact lt_of_le_of_lt hcData.2.2.1 (hUR.trans hRq)

/-- Bad and deletion atoms cannot overlap because their cofactor Möbius signs
are opposite. -/
theorem squareRootLowPrimeOwnedBadAtoms_disjoint_ownedDeletionAtoms
    (R K U : ℕ) :
    Disjoint (squareRootLowPrimeOwnedBadAtoms R K U)
      (squareRootLowPrimeOwnedDeletionAtoms R K U) := by
  rw [Finset.disjoint_left]
  intro z hzBad hzDeletion
  unfold squareRootLowPrimeOwnedBadAtoms at hzBad
  unfold squareRootLowPrimeOwnedDeletionAtoms at hzDeletion
  rcases Finset.mem_biUnion.mp hzBad with ⟨c, hc, hzc⟩
  rcases Finset.mem_biUnion.mp hzDeletion with ⟨d, hd, hzd⟩
  have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
  have hzdData := mem_squareRootLowPrimeBadAtomFiber.mp hzd
  have hcd : c = d := hzcData.1.symm.trans hzdData.1
  have hmuBad := (squareRootLowPrimeOwnedBadCofactor_data hc).2.2.2
  have hmuDeletion :=
    (squareRootLowPrimeOwnedDeletionCofactor_data hd).2.2.2
  rw [hcd] at hmuBad
  omega

/-- The complete signed response-atom carrier: positive and negative cofactor
orientations are reunited before any estimate. -/
def squareRootLowPrimeOwnedResponseAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  squareRootLowPrimeOwnedBadAtoms R K U ∪
    squareRootLowPrimeOwnedDeletionAtoms R K U

/-- Arithmetic and partner data forced by membership in the complete response
atom carrier. -/
theorem squareRootLowPrimeOwnedResponseAtom_data
    {R K U : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeOwnedResponseAtoms R K U) :
    0 < z.1 ∧ K < z.1 ∧
      canonicalLargestPrimeFactor z.1 ≤ U ∧
      z.2 ∈ squareRootLowPrimeDeepPartnerSet R z.1 := by
  unfold squareRootLowPrimeOwnedResponseAtoms at hz
  rcases Finset.mem_union.mp hz with hzBad | hzDeletion
  · unfold squareRootLowPrimeOwnedBadAtoms at hzBad
    rcases Finset.mem_biUnion.mp hzBad with ⟨c, hc, hzc⟩
    have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
    have hcData := squareRootLowPrimeOwnedBadCofactor_data hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hzcData.1]
      exact hcData.1
    · rw [hzcData.1]
      exact hcData.2.1
    · rw [hzcData.1]
      exact hcData.2.2.1
    · rw [hzcData.1]
      exact hzcData.2
  · unfold squareRootLowPrimeOwnedDeletionAtoms at hzDeletion
    rcases Finset.mem_biUnion.mp hzDeletion with ⟨c, hc, hzc⟩
    have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
    have hcData := squareRootLowPrimeOwnedDeletionCofactor_data hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hzcData.1]
      exact hcData.1
    · rw [hzcData.1]
      exact hcData.2.1
    · rw [hzcData.1]
      exact hcData.2.2.1
    · rw [hzcData.1]
      exact hzcData.2

/-- Every partner in the complete response carrier is the fresh largest prime
of its child. -/
theorem canonicalLargestPrimeFactor_lt_partner_of_ownedResponseAtom
    {R K U : ℕ} {z : ℕ × ℕ} (hUR : U < R)
    (hz : z ∈ squareRootLowPrimeOwnedResponseAtoms R K U) :
    canonicalLargestPrimeFactor z.1 < z.2 := by
  have hzData := squareRootLowPrimeOwnedResponseAtom_data hz
  rcases Finset.mem_union.mp hzData.2.2.2 with hborn | hpost
  · exact (Finset.mem_filter.mp hborn).2.2.1
  · have hRq : R < z.2 :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpost).1).1
    exact lt_of_le_of_lt hzData.2.2.1 (hUR.trans hRq)

/-- The arithmetic product map is injective on the complete signed atom carrier.
The child recovers its partner and cofactor canonically. -/
theorem squareRootLowPrimeBadAtomChild_injOn_ownedResponseAtoms
    {R K U : ℕ} (hUR : U < R) :
    Set.InjOn squareRootLowPrimeBadAtomChild
      (squareRootLowPrimeOwnedResponseAtoms R K U) := by
  intro z hz w hw hchild
  have hzData := squareRootLowPrimeOwnedResponseAtom_data hz
  have hwData := squareRootLowPrimeOwnedResponseAtom_data hw
  have hzPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hzData.2.2.2
  have hwPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hwData.2.2.2
  have hzRough :=
    canonicalLargestPrimeFactor_lt_partner_of_ownedResponseAtom hUR hz
  have hwRough :=
    canonicalLargestPrimeFactor_lt_partner_of_ownedResponseAtom hUR hw
  have hzLargest :
      canonicalLargestPrimeFactor (z.1 * z.2) = z.2 :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hzData.1 hzPrime hzRough
  have hwLargest :
      canonicalLargestPrimeFactor (w.1 * w.2) = w.2 :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hwData.1 hwPrime hwRough
  have hq : z.2 = w.2 := by
    rw [← hzLargest, ← hwLargest]
    exact congrArg canonicalLargestPrimeFactor hchild
  have hzCofactor : canonicalCofactor (z.1 * z.2) = z.1 :=
    canonicalCofactor_mul_prime_eq_of_rough hzData.1 hzPrime hzRough
  have hwCofactor : canonicalCofactor (w.1 * w.2) = w.1 :=
    canonicalCofactor_mul_prime_eq_of_rough hwData.1 hwPrime hwRough
  have hc : z.1 = w.1 := by
    rw [← hzCofactor, ← hwCofactor]
    exact congrArg canonicalCofactor hchild
  exact Prod.ext hc hq

/-- The literal arithmetic children generated by the complete signed response
carrier. -/
def squareRootLowPrimeOwnedResponseChildren
    (R K U : ℕ) : Finset ℕ :=
  (squareRootLowPrimeOwnedResponseAtoms R K U).image
    squareRootLowPrimeBadAtomChild

/-- Passing from response atoms to arithmetic children loses no cardinality. -/
theorem card_squareRootLowPrimeOwnedResponseChildren
    {R K U : ℕ} (hUR : U < R) :
    (squareRootLowPrimeOwnedResponseChildren R K U).card =
      (squareRootLowPrimeOwnedResponseAtoms R K U).card := by
  unfold squareRootLowPrimeOwnedResponseChildren
  exact Finset.card_image_iff.mpr
    (squareRootLowPrimeBadAtomChild_injOn_ownedResponseAtoms hUR)

/-- Every complete response child is positive and below the square endpoint. -/
theorem squareRootLowPrimeOwnedResponseChildren_subset_Icc
    {R K U : ℕ} :
    squareRootLowPrimeOwnedResponseChildren R K U ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
  have hzData := squareRootLowPrimeOwnedResponseAtom_data hz
  have hqPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hzData.2.2.2
  have hprod :=
    mul_le_squareRootEndpoint_of_mem_deepPartnerSet hzData.2.2.2
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hzData.1) hqPrime.ne_zero),
      hprod⟩

private theorem moebius_mul_prime_eq_neg_of_largestPrimeFactor_lt
    {c q : ℕ} (hc : 0 < c) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < q) :
    μ (c * q) = - μ c := by
  by_cases hcOne : c = 1
  · subst c
    simp [ArithmeticFunction.moebius_apply_prime hq]
  · have hcgt : 1 < c := by omega
    have hnot : ¬ q ∣ c := by
      intro hqdvd
      have hmem : q ∈ c.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hqdvd, by omega⟩
      have hqle : q ≤ canonicalLargestPrimeFactor c := by
        unfold canonicalLargestPrimeFactor
        rw [dif_pos hcgt]
        exact Finset.le_max' c.primeFactors q hmem
      omega
    have hcop : Nat.Coprime c q :=
      ((hq.coprime_iff_not_dvd).2 hnot).symm
    calc
      μ (c * q) = μ c * μ q :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      _ = μ c * (-1) := by
        rw [ArithmeticFunction.moebius_apply_prime hq]
      _ = - μ c := by ring

/-- Adjoining the fresh partner reverses the Möbius sign on every complete
response atom. -/
theorem squareRootLowPrimeOwnedResponseAtomChild_moebiusWeight
    {R K U : ℕ} {z : ℕ × ℕ} (hUR : U < R)
    (hz : z ∈ squareRootLowPrimeOwnedResponseAtoms R K U) :
    canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) =
      -canonicalMoebiusWeight z.1 := by
  have hzData := squareRootLowPrimeOwnedResponseAtom_data hz
  have hqPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hzData.2.2.2
  have hrough :=
    canonicalLargestPrimeFactor_lt_partner_of_ownedResponseAtom hUR hz
  have hmu := moebius_mul_prime_eq_neg_of_largestPrimeFactor_lt
    hzData.1 hqPrime hrough
  have hcast := congrArg (fun a : ℤ => (a : ℂ)) hmu
  simpa [squareRootLowPrimeBadAtomChild, canonicalMoebiusWeight] using hcast

/-- A bad atom produces a negative-Möbius child. -/
theorem squareRootLowPrimeOwnedBadAtomChild_moebiusWeight_eq_neg_one
    {R K U : ℕ} {z : ℕ × ℕ} (hUR : U < R)
    (hz : z ∈ squareRootLowPrimeOwnedBadAtoms R K U) :
    canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) = -1 := by
  have hflip := squareRootLowPrimeOwnedResponseAtomChild_moebiusWeight
    hUR (Finset.mem_union.mpr (Or.inl hz))
  unfold squareRootLowPrimeOwnedBadAtoms at hz
  rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
  have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
  have hcData := squareRootLowPrimeOwnedBadCofactor_data hc
  have hcofactor : canonicalMoebiusWeight z.1 = 1 := by
    unfold canonicalMoebiusWeight
    rw [hzcData.1, hcData.2.2.2]
    norm_num
  calc
    canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) =
        -canonicalMoebiusWeight z.1 := hflip
    _ = -1 := by rw [hcofactor]

/-- A deletion atom produces a positive-Möbius child. -/
theorem squareRootLowPrimeOwnedDeletionAtomChild_moebiusWeight_eq_one
    {R K U : ℕ} {z : ℕ × ℕ} (hUR : U < R)
    (hz : z ∈ squareRootLowPrimeOwnedDeletionAtoms R K U) :
    canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) = 1 := by
  have hflip := squareRootLowPrimeOwnedResponseAtomChild_moebiusWeight
    hUR (Finset.mem_union.mpr (Or.inr hz))
  unfold squareRootLowPrimeOwnedDeletionAtoms at hz
  rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
  have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
  have hcData := squareRootLowPrimeOwnedDeletionCofactor_data hc
  have hcofactor : canonicalMoebiusWeight z.1 = -1 := by
    unfold canonicalMoebiusWeight
    rw [hzcData.1, hcData.2.2.2]
    norm_num
  calc
    canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) =
        -canonicalMoebiusWeight z.1 := hflip
    _ = 1 := by
      rw [hcofactor]
      norm_num

/-- Signed Möbius mass of the bad child atoms. -/
theorem squareRootLowPrimeOwnedBadAtomChild_weight_sum_eq_neg_card
    {R K U : ℕ} (hUR : U < R) :
    (∑ z ∈ squareRootLowPrimeOwnedBadAtoms R K U,
      canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)) =
      -((squareRootLowPrimeOwnedBadAtoms R K U).card : ℂ) := by
  calc
    (∑ z ∈ squareRootLowPrimeOwnedBadAtoms R K U,
      canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)) =
        ∑ _z ∈ squareRootLowPrimeOwnedBadAtoms R K U, (-1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact squareRootLowPrimeOwnedBadAtomChild_moebiusWeight_eq_neg_one
        hUR hz
    _ = -((squareRootLowPrimeOwnedBadAtoms R K U).card : ℂ) := by simp

/-- Signed Möbius mass of the deletion child atoms. -/
theorem squareRootLowPrimeOwnedDeletionAtomChild_weight_sum_eq_card
    {R K U : ℕ} (hUR : U < R) :
    (∑ z ∈ squareRootLowPrimeOwnedDeletionAtoms R K U,
      canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)) =
      ((squareRootLowPrimeOwnedDeletionAtoms R K U).card : ℂ) := by
  calc
    (∑ z ∈ squareRootLowPrimeOwnedDeletionAtoms R K U,
      canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)) =
        ∑ _z ∈ squareRootLowPrimeOwnedDeletionAtoms R K U, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact squareRootLowPrimeOwnedDeletionAtomChild_moebiusWeight_eq_one
        hUR hz
    _ = ((squareRootLowPrimeOwnedDeletionAtoms R K U).card : ℂ) := by simp

/-- **Exact signed atom identity.**  The complete fresh-prime response over the
deep interval is the negative Möbius mass of one signed response-atom carrier. -/
theorem squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseAtomChildMass
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrement R K j p) =
      -∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
        canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) := by
  have hdisj :=
    squareRootLowPrimeOwnedBadAtoms_disjoint_ownedDeletionAtoms R K U
  rw [squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_badMass hR,
    squareRootLowPrimeGlobalDeletionMass_eq_ownedDeletionAtoms_card hR,
    squareRootLowPrimeGlobalBadMass_eq_ownedBadAtoms_card hR]
  unfold squareRootLowPrimeOwnedResponseAtoms
  rw [Finset.sum_union hdisj,
    squareRootLowPrimeOwnedBadAtomChild_weight_sum_eq_neg_card hUR,
    squareRootLowPrimeOwnedDeletionAtomChild_weight_sum_eq_card hUR]
  ring

/-- Möbius mass is preserved when the injective response-atom carrier is
reindexed by its arithmetic children. -/
theorem squareRootLowPrimeOwnedResponseChildren_moebiusMass_eq_atoms
    {R K U : ℕ} (hUR : U < R) :
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
      canonicalMoebiusWeight n) =
      ∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
        canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) := by
  unfold squareRootLowPrimeOwnedResponseChildren
  apply Finset.sum_image
  intro z hz w hw hchild
  exact squareRootLowPrimeBadAtomChild_injOn_ownedResponseAtoms
    hUR hz hw hchild

/-- **Complete signed-child reduction.**  The exact weighted bad/deletion excess
is one restricted Möbius sum over unique arithmetic children below `R^2-1`.
No absolute value or analytic estimate has been taken. -/
theorem squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseChildrenMass
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrement R K j p) =
      -∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
        canonicalMoebiusWeight n := by
  rw [squareRootLowPrimeOwnedResponseChildren_moebiusMass_eq_atoms hUR]
  exact squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseAtomChildMass
    hR hUR

end RHLean.Proof
