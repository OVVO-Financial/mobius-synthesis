import Mathlib
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren

/-!
# Per-prime signed response children in the quadratic energy identity

`SquareRootLowPrimeSignedResponseChildren` identifies the total fresh response
on the full deep interval `(K,U]` with the negative Möbius mass of one injective
child carrier.  For the quadratic dissipation identity, however, the response
cutoff `K` must be kept distinct from the lower endpoint `L` of a selected
prime interval.

This file makes that separation.  Whenever `K <= L < U < R`, it proves

`sum_{L < p <= U} Delta_p = -sum_{n in ResponseChildren(R,L,U)} mu(n)`.

Taking `L = p-1` gives the local identity

`Delta_p = -sum_{n in ResponseChildren(R,p-1,p)} mu(n)`

for every prime `K < p < R`.  Substitution into the already-proved quadratic
energy step then writes

`T(p-1)^2 - T(p)^2 = 2*T(p-1)*C_p - C_p^2`,

where `C_p` is that exact signed child mass.

This is an exact carrier-level reformulation of the energy gate.  It does not
prove that the right-hand side is positive on average, establish an `O(R)`
signed excess estimate, or supply the required global energy decrement.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The complete bad response on any selected interval `(L,U]` is the
cardinality of its owned atom carrier, provided the response cutoff `K` is no
larger than `L`. -/
theorem squareRootLowPrimeGlobalBadMass_eq_ownedBadAtoms_card_of_le
    {R K j L U : ℕ} (hR : 2 ≤ R) (hKL : K ≤ L) :
    squareRootLowPrimeGlobalBadMass R K j L U =
      (squareRootLowPrimeOwnedBadAtoms R L U).card := by
  rw [squareRootLowPrimeGlobalBadMass_eq_ownedCofactorSum]
  symm
  calc
    (squareRootLowPrimeOwnedBadAtoms R L U).card =
        ∑ z ∈ squareRootLowPrimeOwnedBadAtoms R L U, 1 := by simp
    _ = ∑ c ∈ squareRootLowPrimeOwnedBadCofactors R L U,
          ∑ z ∈ squareRootLowPrimeBadAtomFiber R c, 1 := by
      unfold squareRootLowPrimeOwnedBadAtoms
      exact Finset.sum_biUnion
        (squareRootLowPrimeBadAtomFiber_pairwiseDisjoint R L U)
    _ = ∑ c ∈ squareRootLowPrimeOwnedBadCofactors R L U,
          (squareRootLowPrimeDeepPartnerSet R c).card := by
      apply Finset.sum_congr rfl
      intro c _hc
      simp [squareRootLowPrimeBadAtomFiber]
    _ = ∑ c ∈ squareRootLowPrimeOwnedBadCofactors R L U,
          squareRootLowPrimeCombinedFreshResponse R K j c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcData := squareRootLowPrimeOwnedBadCofactor_data hc
      exact card_squareRootLowPrimeDeepPartnerSet_eq_combinedFreshResponse
        (by omega) hcData.1 (lt_of_le_of_lt hKL hcData.2.1)

/-- The complete deletion response on any selected interval `(L,U]` is the
cardinality of its owned atom carrier under the same cutoff separation. -/
theorem squareRootLowPrimeGlobalDeletionMass_eq_ownedDeletionAtoms_card_of_le
    {R K j L U : ℕ} (hR : 2 ≤ R) (hKL : K ≤ L) :
    squareRootLowPrimeGlobalDeletionMass R K j L U =
      (squareRootLowPrimeOwnedDeletionAtoms R L U).card := by
  rw [squareRootLowPrimeGlobalDeletionMass_eq_ownedCofactorSum]
  symm
  calc
    (squareRootLowPrimeOwnedDeletionAtoms R L U).card =
        ∑ z ∈ squareRootLowPrimeOwnedDeletionAtoms R L U, 1 := by simp
    _ = ∑ c ∈ squareRootLowPrimeOwnedDeletionCofactors R L U,
          ∑ z ∈ squareRootLowPrimeBadAtomFiber R c, 1 := by
      unfold squareRootLowPrimeOwnedDeletionAtoms
      exact Finset.sum_biUnion
        (squareRootLowPrimeDeletionAtomFiber_pairwiseDisjoint R L U)
    _ = ∑ c ∈ squareRootLowPrimeOwnedDeletionCofactors R L U,
          (squareRootLowPrimeDeepPartnerSet R c).card := by
      apply Finset.sum_congr rfl
      intro c _hc
      simp [squareRootLowPrimeBadAtomFiber]
    _ = ∑ c ∈ squareRootLowPrimeOwnedDeletionCofactors R L U,
          squareRootLowPrimeCombinedFreshResponse R K j c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcData := squareRootLowPrimeOwnedDeletionCofactor_data hc
      exact card_squareRootLowPrimeDeepPartnerSet_eq_combinedFreshResponse
        (by omega) hcData.1 (lt_of_le_of_lt hKL hcData.2.1)

/-- Exact signed atom identity on a subinterval above the response cutoff. -/
theorem squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseAtomChildMass_of_le
    {R K j L U : ℕ} (hR : 2 ≤ R) (hKL : K ≤ L) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
      squareRootLowPrimeFreshIncrement R K j p) =
      -∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R L U,
        canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z) := by
  have hdisj :=
    squareRootLowPrimeOwnedBadAtoms_disjoint_ownedDeletionAtoms R L U
  rw [squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_badMass hR,
    squareRootLowPrimeGlobalDeletionMass_eq_ownedDeletionAtoms_card_of_le hR hKL,
    squareRootLowPrimeGlobalBadMass_eq_ownedBadAtoms_card_of_le hR hKL]
  unfold squareRootLowPrimeOwnedResponseAtoms
  rw [Finset.sum_union hdisj,
    squareRootLowPrimeOwnedBadAtomChild_weight_sum_eq_neg_card hUR,
    squareRootLowPrimeOwnedDeletionAtomChild_weight_sum_eq_card hUR]
  ring

/-- **Subinterval signed-child reduction.**  Above the response cutoff, the
exact interval response is one restricted Möbius sum over unique children. -/
theorem squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseChildrenMass_of_le
    {R K j L U : ℕ} (hR : 2 ≤ R) (hKL : K ≤ L) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
      squareRootLowPrimeFreshIncrement R K j p) =
      -∑ n ∈ squareRootLowPrimeOwnedResponseChildren R L U,
        canonicalMoebiusWeight n := by
  rw [squareRootLowPrimeOwnedResponseChildren_moebiusMass_eq_atoms hUR]
  exact
    squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseAtomChildMass_of_le
      hR hKL hUR

/-- A one-point prime interval `(p-1,p]` contains exactly `p`. -/
@[simp] theorem squareRootLowPrimeFreshPrimeSet_pred_eq_singleton
    {p : ℕ} (hp : p.Prime) :
    squareRootLowPrimeFreshPrimeSet (p - 1) p = {p} := by
  have hp2 : 2 ≤ p := hp.two_le
  ext q
  simp only [squareRootLowPrimeFreshPrimeSet, Finset.mem_filter,
    Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, _hqPrime⟩
    omega
  · intro hqp
    subst q
    exact ⟨⟨by omega, le_rfl⟩, hp⟩

/-- **Local signed-child identity.**  Every individual deep fresh-prime
increment is the negative Möbius mass of its own uniquely owned response
children. -/
theorem squareRootLowPrimeFreshIncrement_eq_neg_ownedResponseChildrenMass
    {R K j p : ℕ} (hR : 2 ≤ R) (hKp : K < p)
    (hp : p.Prime) (hpR : p < R) :
    squareRootLowPrimeFreshIncrement R K j p =
      -∑ n ∈ squareRootLowPrimeOwnedResponseChildren R (p - 1) p,
        canonicalMoebiusWeight n := by
  have hKL : K ≤ p - 1 := by omega
  have hsum :=
    squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseChildrenMass_of_le
      (R := R) (K := K) (j := j) (L := p - 1) (U := p)
      hR hKL hpR
  rw [squareRootLowPrimeFreshPrimeSet_pred_eq_singleton hp] at hsum
  simpa using hsum

/-- **Quadratic energy step on the exact signed child carrier.**  This is the
existing energy identity with the local response replaced by its canonical
child mass; no inequality is asserted. -/
theorem squareRootLowPrimeRunningEnergy_step_eq_signedResponseChildren
    {R K j p : ℕ} (hR : 2 ≤ R) (hKp : K < p)
    (hp : p.Prime) (hpR : p < R) :
    squareRootLowPrimeRunningImbalance R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalance R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          (-∑ n ∈ squareRootLowPrimeOwnedResponseChildren R (p - 1) p,
            canonicalMoebiusWeight n) -
        (-∑ n ∈ squareRootLowPrimeOwnedResponseChildren R (p - 1) p,
          canonicalMoebiusWeight n) ^ 2 := by
  calc
    squareRootLowPrimeRunningImbalance R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalance R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          squareRootLowPrimeFreshIncrement R K j p -
        squareRootLowPrimeFreshIncrement R K j p ^ 2 :=
      squareRootLowPrimeRunningEnergy_step R K j p hp
    _ = 2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          (-∑ n ∈ squareRootLowPrimeOwnedResponseChildren R (p - 1) p,
            canonicalMoebiusWeight n) -
        (-∑ n ∈ squareRootLowPrimeOwnedResponseChildren R (p - 1) p,
          canonicalMoebiusWeight n) ^ 2 := by
      rw [squareRootLowPrimeFreshIncrement_eq_neg_ownedResponseChildrenMass
        hR hKp hp hpR]

end RHLean.Proof
