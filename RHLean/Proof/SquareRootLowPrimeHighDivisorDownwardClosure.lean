import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalChildCharacterization
import RHLean.Proof.SquareRootLowPrimeResponseForest

/-!
# Arbitrary-divisor downward closure of the post-root channel

Canonical-parent descent is sufficient for ancestry, but the sequential
matching can displace a state through any earlier prime coordinate.  The high
channel therefore needs the stronger statement proved here: deleting any
squarefree prime factor from an owned post-root cofactor preserves the literal
post-root atom whenever the smaller cofactor still has an owner in `(K,U]`.

The reason is completely elementary.  Division lowers the cofactor, so the
hyperbolic condition `c*q <= R^2-1` remains true.  Nonzero Möbius orientation
makes the cofactor squarefree, hence every divisor remains squarefree.  The
only possible failure is that the smaller divisor's largest prime has crossed
the lower owner cutoff `K`.

Combined with the displacement-diamond theorem, this eliminates interior high
upper-instability: a missing lower corner is necessarily cutoff-supported.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Post-root partner support is downward closed in the cofactor under any
positive divisor relation. -/
theorem squareRootPostRootPrimePartnerSet_of_dvd
    {R c d q : ℕ} (hc : 0 < c) (_hd : 0 < d) (hdc : d ∣ c)
    (hq : q ∈ squareRootPostRootPrimePartnerSet R c) :
    q ∈ squareRootPostRootPrimePartnerSet R d := by
  unfold squareRootPostRootPrimePartnerSet at hq ⊢
  rcases Finset.mem_filter.mp hq with ⟨hqRange, hqPrime, hcq⟩
  have hdcLe : d ≤ c := Nat.le_of_dvd hc hdc
  exact Finset.mem_filter.mpr
    ⟨hqRange, hqPrime,
      (Nat.mul_le_mul_right q hdcLe).trans hcq⟩

/-- A positive divisor of an owned squarefree response cofactor remains owned
provided its own largest prime is still in the selected fresh-prime interval. -/
theorem squareRootLowPrimeResponseDivisor_mem_ownedResponseCofactors
    {R K U c d : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U)
    (hd : 0 < d) (hdc : d ∣ c) (hcUpper : c ≤ squareRootEndpoint R)
    (hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U) :
    d ∈ squareRootLowPrimeOwnedResponseCofactors R K U := by
  have hcSign :=
    squareRootLowPrimeOwnedResponseCofactor_moebius_eq_one_or_neg_one hc
  have hcMuNe : μ c ≠ 0 := by
    rcases hcSign with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hcSq : Squarefree c :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hcMuNe
  have hdSq : Squarefree d := hcSq.squarefree_of_dvd hdc
  have hdMuNe : μ d ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hdSq
  have hdBound := ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [abs_le] at hdBound
  have hdSign : μ d = 1 ∨ μ d = -1 := by omega
  have hcPos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos h
    subst c
    simp at hcMuNe
  have hdUpper : d ≤ squareRootEndpoint R :=
    (Nat.le_of_dvd hcPos hdc).trans hcUpper
  have hdFresh :
      d ∈ squareRootLowPrimeBornFreshCofactors R
        (canonicalLargestPrimeFactor d) := by
    unfold squareRootLowPrimeBornFreshCofactors
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd), hdUpper⟩,
        rfl⟩
  rcases hdSign with hpos | hneg
  · apply mem_squareRootLowPrimeOwnedResponseCofactors.mpr
    left
    unfold squareRootLowPrimeOwnedBadCofactors
    exact Finset.mem_biUnion.mpr
      ⟨canonicalLargestPrimeFactor d, hdOwner,
        Finset.mem_filter.mpr ⟨hdFresh, hpos⟩⟩
  · apply mem_squareRootLowPrimeOwnedResponseCofactors.mpr
    right
    unfold squareRootLowPrimeOwnedDeletionCofactors
    exact Finset.mem_biUnion.mpr
      ⟨canonicalLargestPrimeFactor d, hdOwner,
        Finset.mem_filter.mpr ⟨hdFresh, hneg⟩⟩

/-- Rebuild an owned response atom from the complete signed cofactor carrier. -/
theorem squareRootLowPrimeOwnedResponseAtom_of_ownedCofactor
    {R K U c q : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U)
    (hq : q ∈ squareRootLowPrimeDeepPartnerSet R c) :
    (c, q) ∈ squareRootLowPrimeOwnedResponseAtoms R K U := by
  apply mem_squareRootLowPrimeOwnedResponseAtoms_iff.mpr
  constructor
  · simpa [squareRootLowPrimeOwnedResponseCofactors,
      squareRootLowPrimeOwnedSignedCofactors] using hc
  · exact hq

/-- **Arbitrary-divisor post-root closure.** -/
theorem squareRootLowPrimePostRootDivisorAtom_mem
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U)
    (hd : 0 < d) (hdc : d ∣ c)
    (hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U) :
    (d, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U := by
  rcases mem_squareRootLowPrimePostRootResponseAtoms.mp hz with
    ⟨hzResponse, hzPost⟩
  have hcOwned :=
    squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors
      hzResponse
  have hcSign :=
    squareRootLowPrimeOwnedResponseCofactor_moebius_eq_one_or_neg_one hcOwned
  have hcMuNe : μ c ≠ 0 := by
    rcases hcSign with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hcPos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos h
    subst c
    simp at hcMuNe
  have hqData := Finset.mem_filter.mp hzPost
  have hcUpper : c ≤ squareRootEndpoint R := by
    have hcLeProd : c ≤ c * q := by
      simpa using Nat.mul_le_mul_left c hqData.2.1.pos
    exact hcLeProd.trans hqData.2.2
  have hdOwned :=
    squareRootLowPrimeResponseDivisor_mem_ownedResponseCofactors
      hcOwned hd hdc hcUpper hdOwner
  have hdPost :=
    squareRootPostRootPrimePartnerSet_of_dvd hcPos hd hdc hzPost
  apply mem_squareRootLowPrimePostRootResponseAtoms.mpr
  exact ⟨squareRootLowPrimeOwnedResponseAtom_of_ownedCofactor
      hdOwned (Finset.mem_union.mpr (Or.inr hdPost)),
    hdPost⟩

/-- Consequently a missing divisor-parent post-root atom can occur only after
that divisor's owner has crossed the lower cutoff. -/
theorem squareRootLowPrimePostRoot_missingDivisor_supported_at_owner_cutoff
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U)
    (hd : 0 < d) (hdc : d ∣ c)
    (hmissing : (d, q) ∉
      squareRootLowPrimePostRootResponseAtoms R K U) :
    canonicalLargestPrimeFactor d ∉ squareRootLowPrimeFreshPrimeSet K U := by
  intro hdOwner
  exact hmissing
    (squareRootLowPrimePostRootDivisorAtom_mem hz hd hdc hdOwner)

/-- Prime-factor form used by an upper displacement square. -/
theorem squareRootLowPrimePostRoot_primeFactorParent_mem
    {R K U c d r q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U)
    (_hr : r.Prime) (hd : 0 < d) (hprod : d * r = c)
    (hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U) :
    (d, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U := by
  have hdc : d ∣ c := ⟨r, hprod.symm⟩
  exact squareRootLowPrimePostRootDivisorAtom_mem hz hd hdc hdOwner

end RHLean.Proof
