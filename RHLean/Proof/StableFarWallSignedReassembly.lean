import RHLean.Proof.StableFarWallExactQ2Split
import RHLean.Proof.LowWheelFrozenSquareResidualParentCarrier

/-!
# Signed arithmetic reassembly of the far-wall census

The far prime must remain attached when the low cofactor is stripped.  The
map `(q,d,p) -> (q,d*p)` is injective on the actual far carrier: `p` and `d`
are recovered as the largest prime and canonical cofactor of `d*p`.
Consequently its weight is the true `mu(d*p) = -mu(d)`.

The owner tag is retained throughout.  Different owners can represent the same
integer; forgetting that tag is permitted only with its exact multiplicity.
All results in this module are finite signed identities, before any norm.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Arithmetic data on the actual stripped far-wall triples. -/
theorem lowWheelFarPrimeLowCofactorTriple_data
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    t.1.Prime ∧ t.1 < R ∧ 1 ≤ t.2.1 ∧ t.2.2.Prime ∧
      R + 8 ≤ t.2.2 ∧ Squarefree t.2.1 ∧
      canonicalLargestPrimeFactor t.2.1 < t.1 ∧
      t.1 * t.2.1 * t.2.2 ≤ squareRootEndpoint R := by
  rcases Finset.mem_image.mp ht with ⟨⟨c,p⟩, hcp, rfl⟩
  have h := lowWheelFarPrimeNonUnitPair_data hcp
  have hcgt : 1 < c := (Finset.mem_filter.mp hcp).2
  have hpRange := (mem_lowWheelFarPrimePairSet.mp
    (mem_lowWheelFarPrimeSquarefreePairSet.mp (Finset.mem_filter.mp hcp).1).1).2.1
  exact ⟨h.1, h.2.1, canonicalCofactor_pos hcgt, h.2.2.2.1,
    (Finset.mem_Icc.mp hpRange).1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1⟩

/-- Converse census from independent arithmetic data.  In particular the old
cofactor root restriction follows from the product cutoff and the far prime. -/
theorem lowWheelFarPrimeLowCofactorTriple_mem_of_data
    {R q d p : ℕ} (hq : q.Prime) (hqR : q < R) (hd1 : 1 ≤ d)
    (hp : p.Prime) (hpR : R + 8 ≤ p) (hdsq : Squarefree d)
    (hdq : canonicalLargestPrimeFactor d < q)
    (hcut : q * d * p ≤ squareRootEndpoint R) :
    (q,(d,p)) ∈ lowWheelFarPrimeLowCofactorTriples R := by
  have hnot := squareRootLowPrimePrime_fresh_of_lpf_lt hd1 hq hdq
  have hcop : Nat.Coprime q d := (hq.coprime_iff_not_dvd).2 hnot
  have hcsq : Squarefree (q * d) := (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hdsq⟩
  have hcgt : 1 < q * d := by nlinarith [hq.two_le]
  have hRpos : 0 < R := hq.pos.trans hqR
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  have hcR : q * d < R := by
    by_contra hnot
    have hRc : R ≤ q * d := Nat.le_of_not_gt hnot
    have hRp : R ≤ p := by omega
    exact (Nat.not_lt_of_ge ((Nat.mul_le_mul hRc hRp).trans hcut)) hXlt
  have hpX : p ≤ squareRootEndpoint R := by
    have hle : p ≤ (q * d) * p := by
      simpa using Nat.mul_le_mul_right p (show 1 ≤ q * d by omega)
    exact hle.trans hcut
  have hpair : (q * d,p) ∈ lowWheelFarPrimeNonUnitPairSet R := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_lowWheelFarPrimeSquarefreePairSet.mpr ⟨?_, hcsq⟩, hcgt⟩
    exact mem_lowWheelFarPrimePairSet.mpr
      ⟨Finset.mem_Ico.mpr ⟨by omega, hcR⟩,
        Finset.mem_Icc.mpr ⟨hpR, hpX⟩, hp, hcut⟩
  have hqEq : canonicalLargestPrimeFactor (q * d) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hd1 hq hdq
  have hdEq : canonicalCofactor (q * d) = d := by
    simpa [Nat.mul_comm] using canonicalCofactor_mul_prime_eq_of_rough hd1 hq hdq
  exact Finset.mem_image.mpr ⟨(q * d,p), hpair, by
    simp [lowWheelFarPrimeLowCofactorTag, hqEq, hdEq]⟩

/-- The carrier is exactly its arithmetic census, rather than merely a map
into a larger candidate set. -/
theorem mem_lowWheelFarPrimeLowCofactorTriples_iff_data {R q d p : ℕ} :
    (q,(d,p)) ∈ lowWheelFarPrimeLowCofactorTriples R ↔
      q.Prime ∧ q < R ∧ 1 ≤ d ∧ p.Prime ∧ R + 8 ≤ p ∧
        Squarefree d ∧ canonicalLargestPrimeFactor d < q ∧
          q * d * p ≤ squareRootEndpoint R := by
  constructor
  · exact lowWheelFarPrimeLowCofactorTriple_data
  · rintro ⟨hq, hqR, hd1, hp, hpR, hsq, hdq, hcut⟩
    exact lowWheelFarPrimeLowCofactorTriple_mem_of_data hq hqR hd1 hp hpR hsq hdq hcut

/-- The far prime is included in the arithmetic daughter product. -/
def lowWheelFarPrimeProductKey (t : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (t.1, t.2.1 * t.2.2)

/-- The product determines the far prime and the stripped low cofactor. -/
theorem lowWheelFarPrimeProduct_coordinates
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    canonicalLargestPrimeFactor (lowWheelFarPrimeProductKey t).2 = t.2.2 ∧
      canonicalCofactor (lowWheelFarPrimeProductKey t).2 = t.2.1 := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨_hq, hqR, hd1, hp, hpR, _hsq, hdq, _hcut⟩
  have hdp : canonicalLargestPrimeFactor t.2.1 < t.2.2 := by omega
  exact ⟨canonicalLargestPrimeFactor_mul_prime_eq_of_rough hd1 hp hdp,
    canonicalCofactor_mul_prime_eq_of_rough hd1 hp hdp⟩

/-- Fixed owner and product recover the complete physical triple. -/
theorem lowWheelFarPrimeProductKey_injOn (R : ℕ) :
    Set.InjOn lowWheelFarPrimeProductKey
      (lowWheelFarPrimeLowCofactorTriples R : Set (ℕ × (ℕ × ℕ))) := by
  intro a ha b hb hab
  have hq := congrArg Prod.fst hab
  have hm := congrArg Prod.snd hab
  have haData := lowWheelFarPrimeProduct_coordinates ha
  have hbData := lowWheelFarPrimeProduct_coordinates hb
  have hp : a.2.2 = b.2.2 := by
    rw [← haData.1, ← hbData.1, hm]
  have hd : a.2.1 = b.2.1 := by
    rw [← haData.2, ← hbData.2, hm]
  exact Prod.ext hq (Prod.ext hd hp)

/-- Reattaching the far prime gives the actual Möbius sign. -/
theorem lowWheelFarPrimeProduct_weight
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    canonicalMoebiusWeight (lowWheelFarPrimeProductKey t).2 =
      -canonicalMoebiusWeight t.2.1 := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨_hq, hqR, hd1, hp, hpR, _hsq, hdq, _hcut⟩
  have hdp : canonicalLargestPrimeFactor t.2.1 < t.2.2 := by omega
  exact canonicalMoebiusWeight_mul_freshPrime hp
    (squareRootLowPrimePrime_fresh_of_lpf_lt hd1 hp hdp)

/-- Every product is squarefree, post-root, and has its genuine far owner. -/
theorem lowWheelFarPrimeProduct_geometry
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    Squarefree (lowWheelFarPrimeProductKey t).2 ∧
      R + 8 ≤ (lowWheelFarPrimeProductKey t).2 ∧
      t.1 * (lowWheelFarPrimeProductKey t).2 ≤ squareRootEndpoint R ∧
      R + 8 ≤ canonicalLargestPrimeFactor (lowWheelFarPrimeProductKey t).2 := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨_hq, hqR, hd1, hp, hpR, hsq, hdq, hcut⟩
  have hdp : canonicalLargestPrimeFactor t.2.1 < t.2.2 := by omega
  have hnot := squareRootLowPrimePrime_fresh_of_lpf_lt hd1 hp hdp
  have hcop : Nat.Coprime t.2.1 t.2.2 :=
    ((hp.coprime_iff_not_dvd).2 hnot).symm
  refine ⟨(Nat.squarefree_mul hcop).2 ⟨hsq, hp.squarefree⟩, ?_, ?_, ?_⟩
  · exact hpR.trans (by simpa using Nat.mul_le_mul_right t.2.2 hd1)
  · simpa [lowWheelFarPrimeProductKey, Nat.mul_assoc] using hcut
  · rw [(lowWheelFarPrimeProduct_coordinates ht).1]
    exact hpR

/-- True product carriers of the descended and crossing populations. -/
def lowWheelFarPrimeDescendedProductCarrier (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFarPrimeQ2DescendedTriples R).image lowWheelFarPrimeProductKey

def lowWheelFarPrimeCrossingProductCarrier (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFarPrimeQ2CrossingTriples R).image lowWheelFarPrimeProductKey

/-- Generic signed pushforward; no source occurrence is lost or duplicated. -/
theorem lowWheelFarPrimeProduct_mass
    {R : ℕ} (S : Finset (ℕ × (ℕ × ℕ)))
    (hS : S ⊆ lowWheelFarPrimeLowCofactorTriples R) :
    (∑ t ∈ S, canonicalMoebiusWeight t.2.1) =
      -∑ x ∈ S.image lowWheelFarPrimeProductKey,
        canonicalMoebiusWeight x.2 := by
  rw [Finset.sum_image]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [lowWheelFarPrimeProduct_weight (hS ht), neg_neg]
  · intro a ha b hb hab
    exact lowWheelFarPrimeProductKey_injOn R (hS ha) (hS hb) hab

/-- The descended packet has the true product weight, with the far sign kept. -/
theorem lowWheelFarPrimeQ2DescendedMass_eq_neg_productMass (R : ℕ) :
    lowWheelFarPrimeQ2DescendedMass R =
      -∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
        canonicalMoebiusWeight x.2 := by
  exact lowWheelFarPrimeProduct_mass _ (Finset.filter_subset _ _)

/-- The strict crossing packet is also an honest signed product carrier. -/
theorem lowWheelFarPrimeQ2CrossingMass_eq_neg_productMass (R : ℕ) :
    lowWheelFarPrimeQ2CrossingMass R =
      -∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        canonicalMoebiusWeight x.2 := by
  exact lowWheelFarPrimeProduct_mass _ (Finset.filter_subset _ _)

/-- The two true product carriers lie on opposite sides of the exact q² wall. -/
theorem lowWheelFarPrimeDescendedProduct_disjoint_crossing (R : ℕ) :
    Disjoint (lowWheelFarPrimeDescendedProductCarrier R)
      (lowWheelFarPrimeCrossingProductCarrier R) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rcases Finset.mem_image.mp hx with ⟨a, ha, hax⟩
  rcases Finset.mem_image.mp hy with ⟨b, hb, hbx⟩
  have hab := lowWheelFarPrimeProductKey_injOn R
    (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 (hax.trans hbx.symm)
  subst b
  exact (Nat.not_lt_of_ge (Finset.mem_filter.mp ha).2) (Finset.mem_filter.mp hb).2

end RHLean.Proof
