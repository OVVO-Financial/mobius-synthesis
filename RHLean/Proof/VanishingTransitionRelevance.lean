import RHLean.Proof.VanishingTransitionRelevanceBase

/-!
# Canonical first-jump prime slices

The first-jump residual of every oriented state is already a disjoint signed
sum over its canonical first failing prime.  This module lifts that exact
partition to the global state carrier without taking norms.  It is the
correct object on which to attempt the next deterministic finite-difference
contraction.

The quantitative section isolates the still-missing norm-after-signs estimate
for one prime slice and proves that it implies the global bound by an exact
finite product packing.  The local estimate itself is not proved here.  The
final section records the complementary structural fact that the remaining
high-owner carrier is an ordered prime triangle, not an independent family.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

/-- A fixed finite prime universe containing every predecessor prime that can
occur in an oriented state at root `R`. -/
def firstJumpPrimeUniverse (R : ℕ) : Finset ℕ :=
  primesUpTo (squareRootEndpoint R)

/-- Signed contribution of one canonical first-jump prime to one oriented
state.  The state sign is kept outside the predecessor slice. -/
noncomputable def signedFirstJumpPrimeStateSlice
    (R p : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if _h : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
      Nat.sqrt R < lowWheelCanonicalDowncrossPivot x then
    if _hp : p ∈ primesUpTo (lowWheelCanonicalDowncrossPivot x - 1) then
      canonicalMoebiusWeight x.1 *
        ((predecessorFirstJumpFrozenWindowSliceMass
          3 (Nat.sqrt R)
          (primesUpTo (lowWheelCanonicalDowncrossPivot x - 1))
          (R / x.2)
          (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2)
          p : ℤ) : ℂ)
    else 0
  else 0

/-- Global signed mass owned by one canonical first-jump prime. -/
def signedFirstJumpPrimeSliceAggregate (R p : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    signedFirstJumpPrimeStateSlice R p x

/-- The local predecessor prime set of every actual oriented state is contained
in the common finite prime universe. -/
theorem predecessorPrimeSet_subset_firstJumpPrimeUniverse
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    primesUpTo (lowWheelCanonicalDowncrossPivot x - 1) ⊆
      firstJumpPrimeUniverse R := by
  classical
  rcases x with ⟨c, k⟩
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  have hne := hxData.2
  have hkPivot : k = lowWheelCanonicalDowncrossPivot (c, k) :=
    lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
  have hkMem := (Finset.mem_product.mp hxData.1).2
  have hkLe : k ≤ squareRootEndpoint R := (Finset.mem_Icc.mp hkMem).2
  intro p hp
  rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpLe⟩
  apply mem_primesUpTo.mpr
  refine ⟨hpPrime, ?_⟩
  omega

/-- For one actual state, the complete first-jump fibre is exactly the signed
sum of its canonical prime slices over the common universe. -/
theorem lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_primeSlices
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x =
      ∑ p ∈ firstJumpPrimeUniverse R,
        signedFirstJumpPrimeStateSlice R p x := by
  classical
  rcases x with ⟨c, k⟩
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  have hne := hxData.2
  by_cases hroot : Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k)
  · have hstate :
        (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty ∧
          Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k) :=
      ⟨hne, hroot⟩
    let S := primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1)
    let A := R / k
    let B := lowWheelCanonicalDowncrossOwnershipUpper R c k
    have hmass :=
      predecessorFirstJumpFrozenWindowMass_eq_sum_slices
        3 (Nat.sqrt R) S A B
    have hcast := congrArg (fun z : ℤ => (z : ℂ)) hmass
    push_cast at hcast
    unfold lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre
    rw [if_pos hstate]
    change canonicalMoebiusWeight c *
        ((predecessorFirstJumpFrozenWindowMass
          3 (Nat.sqrt R) S A B : ℤ) : ℂ) = _
    rw [hcast, Finset.mul_sum]
    have hsubset : S ⊆ firstJumpPrimeUniverse R := by
      simpa [S] using
        (predecessorPrimeSet_subset_firstJumpPrimeUniverse (R := R)
          (x := (c, k)) hx)
    calc
      (∑ p ∈ S,
          canonicalMoebiusWeight c *
            ((predecessorFirstJumpFrozenWindowSliceMass
              3 (Nat.sqrt R) S A B p : ℤ) : ℂ)) =
        ∑ p ∈ S, signedFirstJumpPrimeStateSlice R p (c, k) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [signedFirstJumpPrimeStateSlice, hstate, hp, S, A, B]
      _ = ∑ p ∈ firstJumpPrimeUniverse R,
          signedFirstJumpPrimeStateSlice R p (c, k) := by
          apply Finset.sum_subset hsubset
          intro p hpU hpNot
          simp [signedFirstJumpPrimeStateSlice, hstate, hpNot, S]
  · have hstate :
        ¬((lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty ∧
          Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k)) := by
      simp [hne, hroot]
    simp [lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre,
      signedFirstJumpPrimeStateSlice, hstate]

/-- **Exact global prime-slice Fubini.**  The signed live first-jump aggregate is
literally the sum of its canonical first-jump-prime aggregates.  No norm,
probability model, or PNT estimate occurs in this identity. -/
theorem signedLiveFirstJumpAggregate_eq_sum_primeSlices
    (R : ℕ) :
    signedLiveFirstJumpAggregate R =
      ∑ p ∈ firstJumpPrimeUniverse R,
        signedFirstJumpPrimeSliceAggregate R p := by
  classical
  unfold signedLiveFirstJumpAggregate signedFirstJumpPrimeSliceAggregate
  calc
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        ∑ p ∈ firstJumpPrimeUniverse R,
          signedFirstJumpPrimeStateSlice R p x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_primeSlices hx
    _ = ∑ p ∈ firstJumpPrimeUniverse R,
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
          signedFirstJumpPrimeStateSlice R p x := by
        rw [Finset.sum_comm]

/-- A canonical first-jump slice below the predecessor threshold is empty. -/
theorem predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_le_threshold
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ}
    (hp : p ≤ Y) :
    predecessorFirstJumpFrozenWindowSliceMass d Y S A B p = 0 := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
  apply Finset.sum_eq_zero
  intro t ht
  have hfirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp ht).2
  have hYp : Y < p := hfirst.2.1
  omega

/-- A canonical first-jump slice above the physical window endpoint is empty
when the prime universe is an actual prime prefix. -/
theorem predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt
    {d Y K A B p : ℕ}
    (hBp : B < p) :
    predecessorFirstJumpFrozenWindowSliceMass
        d Y (primesUpTo K) A B p = 0 := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
  apply Finset.sum_eq_zero
  intro t ht
  have hslice := mem_predecessorFirstJumpFrozenWindowSlice.mp ht
  have hfirst := hslice.2
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hslice.1).1
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htPow, _hlo, _hup⟩
  have hprodPos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset htPow
  have hpdvd : p ∣ primeFaceProduct t := by
    change p ∣ t.prod id
    exact Finset.dvd_prod_of_mem id hfirst.1
  have hple : p ≤ primeFaceProduct t := Nat.le_of_dvd hprodPos hpdvd
  have hprodLe : primeFaceProduct t ≤ B :=
    (mem_frozenPrimeUniverseWindowFaces.mp hwindow).2.2
  omega

/-- Consequently a state slice is zero at primes at or below the root wall. -/
theorem signedFirstJumpPrimeStateSlice_eq_zero_of_le_root
    {R p : ℕ} {x : LowWheelCofactorQuotientState}
    (hp : p ≤ Nat.sqrt R) :
    signedFirstJumpPrimeStateSlice R p x = 0 := by
  classical
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_le_threshold hp]
    simp
  · rfl
  · rfl

/-- A state slice is also zero above the physical root endpoint `R`; the
ownership window itself is already contained in `[1,R]`. -/
theorem signedFirstJumpPrimeStateSlice_eq_zero_of_root_lt
    {R p : ℕ} {x : LowWheelCofactorQuotientState}
    (hRp : R < p) :
    signedFirstJumpPrimeStateSlice R p x = 0 := by
  classical
  rcases x with ⟨c, k⟩
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · have hupper : lowWheelCanonicalDowncrossOwnershipUpper R c k ≤ R := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_left _ _).trans (Nat.div_le_self _ _)
    have hBp : lowWheelCanonicalDowncrossOwnershipUpper R c k < p :=
      hupper.trans_lt hRp
    rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt hBp]
    simp
  · rfl
  · rfl

/-- The global prime slice vanishes below the root wall. -/
theorem signedFirstJumpPrimeSliceAggregate_eq_zero_of_le_root
    {R p : ℕ} (hp : p ≤ Nat.sqrt R) :
    signedFirstJumpPrimeSliceAggregate R p = 0 := by
  unfold signedFirstJumpPrimeSliceAggregate
  apply Finset.sum_eq_zero
  intro x _hx
  exact signedFirstJumpPrimeStateSlice_eq_zero_of_le_root hp

/-- The global prime slice vanishes above `R`. -/
theorem signedFirstJumpPrimeSliceAggregate_eq_zero_of_root_lt
    {R p : ℕ} (hp : R < p) :
    signedFirstJumpPrimeSliceAggregate R p = 0 := by
  unfold signedFirstJumpPrimeSliceAggregate
  apply Finset.sum_eq_zero
  intro x _hx
  exact signedFirstJumpPrimeStateSlice_eq_zero_of_root_lt hp

/-- The actual first-jump prime carrier is the post-root prime interval. -/
def signedFirstJumpPostRootPrimeSet (R : ℕ) : Finset ℕ :=
  frozenPrimeUniverseHighPrimeSet (Nat.sqrt R) R

/-- Only primes strictly between the square-root wall and `R` survive in the
global signed first-jump decomposition. -/
theorem signedLiveFirstJumpAggregate_eq_sum_postRootPrimeSlices
    (R : ℕ) (hR : 3 ≤ R) :
    signedLiveFirstJumpAggregate R =
      ∑ p ∈ signedFirstJumpPostRootPrimeSet R,
        signedFirstJumpPrimeSliceAggregate R p := by
  classical
  rw [signedLiveFirstJumpAggregate_eq_sum_primeSlices]
  have hRend : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsquare : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hsubset : signedFirstJumpPostRootPrimeSet R ⊆ firstJumpPrimeUniverse R := by
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    unfold firstJumpPrimeUniverse
    exact mem_primesUpTo.mpr ⟨hpData.1, hpData.2.2.trans hRend⟩
  symm
  apply Finset.sum_subset hsubset
  intro p hpU hpNot
  have hpPrime : p.Prime := (mem_primesUpTo.mp hpU).1
  by_cases hpLow : p ≤ Nat.sqrt R
  · exact signedFirstJumpPrimeSliceAggregate_eq_zero_of_le_root hpLow
  · have hpHigh : Nat.sqrt R < p := Nat.lt_of_not_ge hpLow
    have hpNotData : ¬(p.Prime ∧ Nat.sqrt R < p ∧ p ≤ R) := by
      simpa [signedFirstJumpPostRootPrimeSet,
        mem_frozenPrimeUniverseHighPrimeSet] using hpNot
    have hRp : R < p := by
      by_contra hnot
      have hpR : p ≤ R := Nat.le_of_not_gt hnot
      exact hpNotData ⟨hpPrime, hpHigh, hpR⟩
    exact signedFirstJumpPrimeSliceAggregate_eq_zero_of_root_lt hRp

/-- The desired signed live-boundary estimate, with the norm taken only after
all state and Möbius signs have been summed. -/
def PNTFiniteDifferenceLiveExposureBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖signedLiveFirstJumpAggregate R‖ ≤
        C * (R : ℝ) * (Real.log (R : ℝ) + 1)

/-! ## Finite product-packing reduction

For one post-root first-jump prime `p`, the exact finite seat scale is the
natural-number quotient `(R / p : ℕ)`, not the stronger real quotient
`(R : ℝ) / (p : ℝ)`.  The local arithmetic input below is imposed only after
every state and Boolean sign in the `p`-slice has been summed.

The products `c * p`, with `1 <= c <= R / p`, remember `p` uniquely: because
`sqrt R < p`, every such `c` is strictly smaller than `p`, so `p` is the
canonical largest prime factor.  Consequently the seat-product sets for
distinct post-root primes are disjoint and their total cardinality is at most
`R`.  This is the finite product packing which leaves one logarithmic factor
from the prime-local estimate; it uses neither PNT nor prime gaps.  These sets
are only certificates for packing the numerical factors `(R / p : ℕ)`; they
are not identified with the actual prime-slice state carriers.
-/

/-- The genuinely missing prime-local finite-difference estimate.  Its seat
factor is the exact cardinality `R / p`; the norm is outside the complete
signed `p`-slice. -/
def FirstJumpPrimeSliceFiniteDifferenceBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R p : ℕ, 3 ≤ R → p ∈ signedFirstJumpPostRootPrimeSet R →
      ‖signedFirstJumpPrimeSliceAggregate R p‖ ≤
        C * (((R / p : ℕ) : ℝ)) * (Real.log (R : ℝ) + 1)

/-- Auxiliary products packing the numerical `R / p` seat factor of one
post-root prime. -/
def signedFirstJumpPrimeSeatProductSet (R p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R / p)).image fun c => c * p

/-- Multiplication by a prime preserves the number of finite seats. -/
theorem signedFirstJumpPrimeSeatProductSet_card
    {R p : ℕ} (hp : p.Prime) :
    (signedFirstJumpPrimeSeatProductSet R p).card = R / p := by
  unfold signedFirstJumpPrimeSeatProductSet
  rw [Finset.card_image_of_injective _
    (fun a b hab => Nat.eq_of_mul_eq_mul_right hp.pos hab)]
  rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- Every seat product is a positive integer at most `R`. -/
theorem signedFirstJumpPrimeSeatProductSet_subset_Icc
    {R p : ℕ} (hp : p.Prime) :
    signedFirstJumpPrimeSeatProductSet R p ⊆ Finset.Icc 1 R := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨c, hc, rfl⟩
  rcases Finset.mem_Icc.mp hc with ⟨hc1, hcTop⟩
  have hprodPos : 0 < c * p := Nat.mul_pos hc1 hp.pos
  have hprodTop : c * p ≤ R :=
    (Nat.le_div_iff_mul_le hp.pos).1 hcTop
  exact Finset.mem_Icc.mpr ⟨hprodPos, hprodTop⟩

/-- Above the square-root wall every legal seat cofactor is smaller than its
prime label. -/
theorem signedFirstJumpPrimeSeat_lt_prime
    {R p c : ℕ} (hp : p.Prime) (hroot : Nat.sqrt R < p)
    (hc : c ∈ Finset.Icc 1 (R / p)) :
    c < p := by
  have hcTop := (Finset.mem_Icc.mp hc).2
  have hcp : c * p ≤ R := (Nat.le_div_iff_mul_le hp.pos).1 hcTop
  have hnext : R < (Nat.sqrt R + 1) ^ 2 := Nat.lt_succ_sqrt' R
  have hsp : Nat.sqrt R + 1 ≤ p := by omega
  have hpp : (Nat.sqrt R + 1) ^ 2 ≤ p * p := by
    rw [pow_two]
    exact Nat.mul_le_mul hsp hsp
  have hRpp : R < p * p := hnext.trans_le hpp
  by_contra hnot
  have hpcLower : p * p ≤ c * p :=
    Nat.mul_le_mul_right p (Nat.le_of_not_gt hnot)
  omega

/-- Distinct post-root primes have disjoint seat-product images. -/
theorem signedFirstJumpPrimeSeatProductSet_pairwiseDisjoint
    (R : ℕ) :
    Set.PairwiseDisjoint (↑(signedFirstJumpPostRootPrimeSet R))
      (signedFirstJumpPrimeSeatProductSet R) := by
  intro p hpMem q hqMem hpq
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hpMem
  have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hqMem
  change Disjoint
    (signedFirstJumpPrimeSeatProductSet R p)
    (signedFirstJumpPrimeSeatProductSet R q)
  rw [Finset.disjoint_left]
  intro n hnp hnq
  rcases Finset.mem_image.mp hnp with ⟨c, hc, hcp⟩
  rcases Finset.mem_image.mp hnq with ⟨d, hd, hdq⟩
  have hcpos : 0 < c := (Finset.mem_Icc.mp hc).1
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hcLtP := signedFirstJumpPrimeSeat_lt_prime hpData.1 hpData.2.1 hc
  have hdLtQ := signedFirstJumpPrimeSeat_lt_prime hqData.1 hqData.2.1 hd
  have hpTop : canonicalLargestPrimeFactor (c * p) = p :=
    canonicalLargestPrimeFactor_mul_prime_eq hcpos hcLtP hpData.1
  have hqTop : canonicalLargestPrimeFactor (d * q) = q :=
    canonicalLargestPrimeFactor_mul_prime_eq hdpos hdLtQ hqData.1
  have hprod : c * p = d * q := hcp.trans hdq.symm
  have hpqEq : p = q := by
    calc
      p = canonicalLargestPrimeFactor (c * p) := hpTop.symm
      _ = canonicalLargestPrimeFactor (d * q) := by rw [hprod]
      _ = q := hqTop
  exact hpq hpqEq

/-- The union of all post-root seat products lies in `[1,R]`. -/
theorem signedFirstJumpPrimeSeatProductUnion_subset_Icc
    (R : ℕ) :
    (signedFirstJumpPostRootPrimeSet R).biUnion
        (signedFirstJumpPrimeSeatProductSet R) ⊆ Finset.Icc 1 R := by
  intro n hn
  rcases Finset.mem_biUnion.mp hn with ⟨p, hpSet, hnp⟩
  have hpPrime := (mem_frozenPrimeUniverseHighPrimeSet.mp hpSet).1
  exact signedFirstJumpPrimeSeatProductSet_subset_Icc hpPrime hnp

/-- **Exact root packing.**  The total number of quotient seats over all
post-root prime labels is at most `R`. -/
theorem sum_signedFirstJumpPostRootPrimeSeatCounts_le_root
    (R : ℕ) :
    (∑ p ∈ signedFirstJumpPostRootPrimeSet R, R / p) ≤ R := by
  let S := signedFirstJumpPostRootPrimeSet R
  let F := signedFirstJumpPrimeSeatProductSet R
  have hpair : Set.PairwiseDisjoint (↑S) F := by
    simpa [S, F] using signedFirstJumpPrimeSeatProductSet_pairwiseDisjoint R
  have hunion : (S.biUnion F).card = ∑ p ∈ S, (F p).card := by
    have h := Finset.sum_biUnion hpair (f := fun _ : ℕ => (1 : ℕ))
    simpa using h
  have hsubset : S.biUnion F ⊆ Finset.Icc 1 R := by
    simpa [S, F] using signedFirstJumpPrimeSeatProductUnion_subset_Icc R
  calc
    (∑ p ∈ signedFirstJumpPostRootPrimeSet R, R / p) =
        ∑ p ∈ S, (F p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpAsHigh :
          p ∈ frozenPrimeUniverseHighPrimeSet (Nat.sqrt R) R := by
        simpa [S, signedFirstJumpPostRootPrimeSet] using hp
      have hpPrime := (mem_frozenPrimeUniverseHighPrimeSet.mp hpAsHigh).1
      exact (signedFirstJumpPrimeSeatProductSet_card hpPrime).symm
    _ = (S.biUnion F).card := hunion.symm
    _ ≤ (Finset.Icc 1 R).card := Finset.card_le_card hsubset
    _ = R := by
      rw [Nat.card_Icc]
      omega

/-- **Advertised finite product-packing reduction.**  The prime-local signed
finite-difference estimate implies the global signed `R log R` target.  The
only triangle inequality is over the already-completed prime slices. -/
theorem pntFiniteDifferenceLiveExposureBound_of_firstJumpPrimeSliceBound
    (hlocal : FirstJumpPrimeSliceFiniteDifferenceBound) :
    PNTFiniteDifferenceLiveExposureBound := by
  rcases hlocal with ⟨C, hC, hlocal⟩
  refine ⟨C, hC, ?_⟩
  intro R hR
  rw [signedLiveFirstJumpAggregate_eq_sum_postRootPrimeSlices R hR]
  have hpackNat := sum_signedFirstJumpPostRootPrimeSeatCounts_le_root R
  have hpack :
      (∑ p ∈ signedFirstJumpPostRootPrimeSet R,
        ((R / p : ℕ) : ℝ)) ≤ (R : ℝ) := by
    exact_mod_cast hpackNat
  have hlog : 0 ≤ Real.log (R : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ R by omega)
  have hfactor : 0 ≤ C * (Real.log (R : ℝ) + 1) := by positivity
  calc
    ‖∑ p ∈ signedFirstJumpPostRootPrimeSet R,
        signedFirstJumpPrimeSliceAggregate R p‖ ≤
        ∑ p ∈ signedFirstJumpPostRootPrimeSet R,
          ‖signedFirstJumpPrimeSliceAggregate R p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ signedFirstJumpPostRootPrimeSet R,
          C * (((R / p : ℕ) : ℝ)) * (Real.log (R : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hlocal R p hR hp
    _ = C * (Real.log (R : ℝ) + 1) *
          (∑ p ∈ signedFirstJumpPostRootPrimeSet R,
            ((R / p : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ C * (Real.log (R : ℝ) + 1) * (R : ℝ) :=
      mul_le_mul_of_nonneg_left hpack hfactor
    _ = C * (R : ℝ) * (Real.log (R : ℝ) + 1) := by ring

/-! ## High-owner state classification

Once the oriented owner `k` is above `sqrt R`, all prime factors of the rough
cofactor `c` are strictly larger than `k`.  But `c < R`.  Two such prime
factors would already force `c > R`.  Hence the cofactor is either `1` or one
single prime above the owner.  This is the exact deterministic replacement for
viewing the high states as unrelated samples.
-/

/-- **High-owner oriented states form an ordered prime triangle.**  For an
actual oriented state above the square-root wall, the owner is prime and the
rough cofactor is either `1` or a single later prime. -/
theorem highOwner_orientedState_shape
    {R c k : ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R)
    (hkroot : Nat.sqrt R < k) :
    k.Prime ∧ (c = 1 ∨ (c.Prime ∧ k < c)) := by
  classical
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  rcases hxData.2 with ⟨t, ht⟩
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨_htPow, hpart⟩
  have hkPivot : k = lowWheelCanonicalDowncrossPivot (c, k) :=
    lowWheelCanonicalDowncrossOriented_quotient_eq_pivot hpart
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hpart).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  have hkPrime : k.Prime := by
    simpa only [← hkPivot] using hgeom.1
  have hroughPivot := lowWheelCanonicalDowncrossOriented_cofactor_roughAbove hpart
  have hrough : RoughAbove k c := by
    simpa only [← hkPivot] using hroughPivot
  have hphys :=
    mem_lowWheelCanonicalPhysicalStateSet.mp
      (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
  have hcRange := Finset.mem_Ico.mp hphys.1
  rcases hcRange with ⟨hc1, hcR⟩
  refine ⟨hkPrime, ?_⟩
  by_cases hcOne : c = 1
  · exact Or.inl hcOne
  · right
    by_cases hcPrime : c.Prime
    · refine ⟨hcPrime, ?_⟩
      have hc0 : c ≠ 0 := by omega
      have hcPF : c ∈ c.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hcPrime, dvd_rfl, hc0⟩
      exact hrough c hcPF
    · exfalso
      have hcpos : 0 < c := by omega
      have hc0 : c ≠ 0 := Nat.ne_of_gt hcpos
      let q := Nat.minFac c
      have hqPrime : q.Prime := by
        dsimp [q]
        exact Nat.minFac_prime hcOne
      have hqDvd : q ∣ c := by
        simpa [q] using Nat.minFac_dvd c
      have hqPF : q ∈ c.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, hc0⟩
      have hkq : k < q := hrough q hqPF
      have hqSqLe : q ^ 2 ≤ c := by
        simpa [q] using Nat.minFac_sq_le_self hcpos hcPrime
      have hsQ : Nat.sqrt R + 1 ≤ q := by omega
      have hRlt : R < (Nat.sqrt R + 1) ^ 2 := Nat.lt_succ_sqrt' R
      have hpow : (Nat.sqrt R + 1) ^ 2 ≤ q ^ 2 :=
        Nat.pow_le_pow_left hsQ 2
      have hRc : R < c := hRlt.trans_le (hpow.trans hqSqLe)
      omega

end RHLean.Proof
