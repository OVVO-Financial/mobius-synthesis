import Mathlib
import RHLean.Arithmetic.PrimeFaceMoebius
import RHLean.Proof.PrimeCombVisualizationFrames

/-!
# Frozen primorial universe identity

The visualization exercise freezes a finite prime universe at

* an old nonempty prime set `S`, whose complete squarefree cube already fits
  below the cutoff `X`, and
* one fresh prime `p`.

There are no additional prime coordinates.  Thus the fitted signed mass is the
alternating mass of those faces of `insert p S` whose prime product is at most
`X`.

Splitting the powerset into the old face and the `p`-face gives the exact
identity

`F_(insert p S)(X) = F_S(X) - F_S(floor(X/p))`.

When every old face fits, `F_S(X)=0` by complete Boolean-cube cancellation, so

`F_(insert p S)(X) = -F_S(floor(X/p))`.

Equivalently this is the old signed Möbius mass of exactly those parents `d`
whose partners `p*d` miss the cutoff.  This file deliberately keeps that
finite-universe quantity distinct from the unrestricted ordinary Mertens
function.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Signed Möbius mass in a frozen finite prime universe, truncated by the
ordinary size cutoff `X`. -/
def frozenPrimeUniverseMass (S : Finset ℕ) (X : ℕ) : ℤ :=
  truncatedCubeAlternatingSum S (primeProductAdmissible S X)

/-- Old-parent mass whose fresh-`p` partners lie beyond `X`. -/
def frozenPrimeUniverseMissingParentMass
    (S : Finset ℕ) (p X : ℕ) : ℤ := by
  classical
  exact ∑ t ∈ S.powerset,
    if X < p * primeFaceProduct t then booleanCubeSign t else 0

/-- On the powerset of `S`, the subset condition in `primeProductAdmissible`
is automatic, so the frozen mass is just the product-cutoff alternating sum. -/
theorem frozenPrimeUniverseMass_eq_cutoffSum
    (S : Finset ℕ) (X : ℕ) :
    frozenPrimeUniverseMass S X =
      ∑ t ∈ S.powerset,
        if primeFaceProduct t ≤ X then booleanCubeSign t else 0 := by
  classical
  unfold frozenPrimeUniverseMass truncatedCubeAlternatingSum
  apply Finset.sum_congr rfl
  intro t ht
  have htS : t ⊆ S := Finset.mem_powerset.mp ht
  simp [primeProductAdmissible, htS]

/-- The same finite quantity written with actual Möbius values of the represented
squarefree products. -/
theorem frozenPrimeUniverseMass_eq_moebius
    (S : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    frozenPrimeUniverseMass S X =
      ∑ t ∈ S.powerset,
        if primeFaceProduct t ≤ X then μ (primeFaceProduct t) else 0 := by
  rw [frozenPrimeUniverseMass_eq_cutoffSum]
  apply Finset.sum_congr rfl
  intro t ht
  have htS : t ⊆ S := Finset.mem_powerset.mp ht
  have hmu : μ (primeFaceProduct t) = booleanCubeSign t :=
    moebius_primeFaceProduct_eq_booleanCubeSign t (by
      intro q hq
      exact hprime q (htS hq))
  by_cases hcut : primeFaceProduct t ≤ X
  · simp [hcut, hmu]
  · simp [hcut]

/-- Missing-parent mass in actual Möbius notation. -/
theorem frozenPrimeUniverseMissingParentMass_eq_moebius
    (S : Finset ℕ) (p X : ℕ)
    (hprime : ∀ q ∈ S, q.Prime) :
    frozenPrimeUniverseMissingParentMass S p X =
      ∑ t ∈ S.powerset,
        if X < p * primeFaceProduct t then μ (primeFaceProduct t) else 0 := by
  classical
  unfold frozenPrimeUniverseMissingParentMass
  apply Finset.sum_congr rfl
  intro t ht
  have htS : t ⊆ S := Finset.mem_powerset.mp ht
  have hmu : μ (primeFaceProduct t) = booleanCubeSign t :=
    moebius_primeFaceProduct_eq_booleanCubeSign t (by
      intro q hq
      exact hprime q (htS hq))
  by_cases hmiss : X < p * primeFaceProduct t
  · simp [hmiss, hmu]
  · simp [hmiss]

/-- **Fresh-prime frozen-universe recurrence.**  No other prime coordinates are
introduced.  Splitting the finite powerset into faces omitting and containing
`p` gives exactly

`F_(S union {p})(X) = F_S(X) - F_S(floor(X/p))`. -/
theorem frozenPrimeUniverseMass_insert
    {S : Finset ℕ} {p X : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) :
    frozenPrimeUniverseMass (insert p S) X =
      frozenPrimeUniverseMass S X - frozenPrimeUniverseMass S (X / p) := by
  classical
  rw [frozenPrimeUniverseMass_eq_cutoffSum,
    frozenPrimeUniverseMass_eq_cutoffSum,
    frozenPrimeUniverseMass_eq_cutoffSum]
  rw [Finset.sum_powerset_insert hp]
  have hchild :
      (∑ t ∈ S.powerset,
        if primeFaceProduct (insert p t) ≤ X then
          booleanCubeSign (insert p t) else 0) =
        -∑ t ∈ S.powerset,
          if primeFaceProduct t ≤ X / p then booleanCubeSign t else 0 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hpt : p ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem ht hp
    have hprod :
        primeFaceProduct (insert p t) = p * primeFaceProduct t := by
      simp [primeFaceProduct, hpt]
    have hsign :
        booleanCubeSign (insert p t) = -booleanCubeSign t := by
      unfold booleanCubeSign
      rw [Finset.card_insert_of_notMem hpt, pow_succ]
      ring
    have hcut :
        primeFaceProduct (insert p t) ≤ X ↔
          primeFaceProduct t ≤ X / p := by
      rw [hprod]
      constructor
      · intro hle
        apply (Nat.le_div_iff_mul_le hpPrime.pos).2
        simpa [Nat.mul_comm] using hle
      · intro hle
        have hmul := (Nat.le_div_iff_mul_le hpPrime.pos).1 hle
        simpa [Nat.mul_comm] using hmul
    by_cases hle : primeFaceProduct t ≤ X / p
    · have hchildFit := hcut.mpr hle
      simp [hle, hchildFit, hsign]
    · have hchildMiss : ¬ primeFaceProduct (insert p t) ≤ X := by
        intro h
        exact hle (hcut.mp h)
      simp [hle, hchildMiss]
  rw [hchild]
  ring

/-- If the complete old cube fits below `X`, then its truncated mass is the
complete Boolean-cube mass and is exactly zero. -/
theorem frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
    {S : Finset ℕ} {X : ℕ}
    (hS : S.Nonempty)
    (hprime : ∀ p ∈ S, p.Prime)
    (hfit : primeFaceProduct S ≤ X) :
    frozenPrimeUniverseMass S X = 0 := by
  rw [frozenPrimeUniverseMass_eq_cutoffSum]
  calc
    (∑ t ∈ S.powerset,
        if primeFaceProduct t ≤ X then booleanCubeSign t else 0) =
      ∑ t ∈ S.powerset, booleanCubeSign t := by
        apply Finset.sum_congr rfl
        intro t ht
        have htS : t ⊆ S := Finset.mem_powerset.mp ht
        have hprodLe : primeFaceProduct t ≤ primeFaceProduct S := by
          unfold primeFaceProduct
          exact Finset.prod_le_prod_of_subset_of_one_le' htS (by
            intro q hqS _hqt
            exact (hprime q hqS).one_le)
        simp [hprodLe.trans hfit]
    _ = booleanCubeAlternatingSum S := by
      rfl
    _ = 0 := booleanCubeAlternatingSum_eq_zero hS

/-- **Frozen last-primorial identity.**  Once every old primorial face fits,
the finite universe with one fresh prime has no old contribution left:

`F_(S union {p})(X) = -F_S(floor(X/p))`. -/
theorem frozenPrimeUniverseMass_insert_eq_neg_old_cutoff
    {S : Finset ℕ} {p X : ℕ}
    (hS : S.Nonempty)
    (hprime : ∀ q ∈ S, q.Prime)
    (hp : p ∉ S) (hpPrime : p.Prime)
    (hfit : primeFaceProduct S ≤ X) :
    frozenPrimeUniverseMass (insert p S) X =
      -frozenPrimeUniverseMass S (X / p) := by
  rw [frozenPrimeUniverseMass_insert hp hpPrime,
    frozenPrimeUniverseMass_eq_zero_of_complete_old_cube hS hprime hfit]
  ring

/-- The negative old cutoff is exactly the signed mass of old parents whose
`p`-partners miss.  This is the complement formulation of the same identity. -/
theorem neg_frozenPrimeUniverseMass_div_eq_missingParentMass
    {S : Finset ℕ} {p X : ℕ}
    (hS : S.Nonempty) (hpPrime : p.Prime) :
    -frozenPrimeUniverseMass S (X / p) =
      frozenPrimeUniverseMissingParentMass S p X := by
  classical
  have hpartition :
      booleanCubeAlternatingSum S =
        frozenPrimeUniverseMass S (X / p) +
          frozenPrimeUniverseMissingParentMass S p X := by
    rw [frozenPrimeUniverseMass_eq_cutoffSum]
    unfold frozenPrimeUniverseMissingParentMass booleanCubeAlternatingSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    by_cases hfit : primeFaceProduct t ≤ X / p
    · have hmul : primeFaceProduct t * p ≤ X :=
        (Nat.le_div_iff_mul_le hpPrime.pos).1 hfit
      have hmul' : p * primeFaceProduct t ≤ X := by
        simpa [Nat.mul_comm] using hmul
      have hnotmiss : ¬ X < p * primeFaceProduct t :=
        Nat.not_lt.mpr hmul'
      simp [hfit, hnotmiss]
    · have hlt : X / p < primeFaceProduct t := Nat.lt_of_not_ge hfit
      have hmiss : X < p * primeFaceProduct t := by
        have h := (Nat.div_lt_iff_lt_mul hpPrime.pos).1 hlt
        simpa [Nat.mul_comm] using h
      simp [hfit, hmiss]
  have hzero := booleanCubeAlternatingSum_eq_zero hS
  rw [hzero] at hpartition
  omega

/-- The two forms requested by the finite exercise are literally the same
quantity. -/
theorem frozenPrimeUniverseMass_insert_eq_missingParentMass
    {S : Finset ℕ} {p X : ℕ}
    (hS : S.Nonempty)
    (hprime : ∀ q ∈ S, q.Prime)
    (hp : p ∉ S) (hpPrime : p.Prime)
    (hfit : primeFaceProduct S ≤ X) :
    frozenPrimeUniverseMass (insert p S) X =
      frozenPrimeUniverseMissingParentMass S p X := by
  rw [frozenPrimeUniverseMass_insert_eq_neg_old_cutoff
    hS hprime hp hpPrime hfit]
  exact neg_frozenPrimeUniverseMass_div_eq_missingParentMass hS hpPrime

/-! ## The `210, 11, 1234` check -/

/-- Old universe from the largest primorial fitting below `1234`. -/
def frozenOldUniverse210 : Finset ℕ := {2, 3, 5, 7}

@[simp] theorem frozenOldUniverse210_product :
    primeFaceProduct frozenOldUniverse210 = 210 := by
  norm_num [frozenOldUniverse210, primeFaceProduct]

private theorem frozenOldUniverse210_allPrime :
    ∀ q ∈ frozenOldUniverse210, q.Prime := by
  intro q hq
  simp [frozenOldUniverse210] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> norm_num

/-- `floor(1234/11)=112`, and among old squarefree products only the full
`210` face lies above that cutoff.  Hence the old truncated mass is `-1`. -/
theorem frozenOldUniverse210_mass_112 :
    frozenPrimeUniverseMass frozenOldUniverse210 112 = -1 := by
  rw [frozenPrimeUniverseMass_eq_cutoffSum]
  native_decide

/-- Exact finite-universe value for the exercise:

`F_{2,3,5,7,11}(1234)=1`. -/
theorem frozenPrimeUniverse_1234_eq_one :
    frozenPrimeUniverseMass (insert 11 frozenOldUniverse210) 1234 = 1 := by
  have hS : frozenOldUniverse210.Nonempty := by
    simp [frozenOldUniverse210]
  have hpFresh : 11 ∉ frozenOldUniverse210 := by
    norm_num [frozenOldUniverse210]
  have hpPrime : Nat.Prime 11 := by norm_num
  have hfit : primeFaceProduct frozenOldUniverse210 ≤ 1234 := by
    simp
  rw [frozenPrimeUniverseMass_insert_eq_neg_old_cutoff
    hS frozenOldUniverse210_allPrime hpFresh hpPrime hfit]
  norm_num [frozenOldUniverse210_mass_112]

/-- In missing-partner form the only residual parent is the old full face
`210`, whose Möbius sign is `+1`. -/
theorem frozenPrimeUniverse_1234_missingParentMass_eq_one :
    frozenPrimeUniverseMissingParentMass frozenOldUniverse210 11 1234 = 1 := by
  rw [← frozenPrimeUniverseMass_insert_eq_missingParentMass
    (S := frozenOldUniverse210) (p := 11) (X := 1234)]
  · exact frozenPrimeUniverse_1234_eq_one
  · simp [frozenOldUniverse210]
  · exact frozenOldUniverse210_allPrime
  · norm_num [frozenOldUniverse210]
  · norm_num
  · simp

/-! ## The post-square-root weighted pile -/

/-- Prime count in the active post-root interval `sqrt(W) < p <= W/2`. -/
def primeCombMiddlePrimeCount (W : ℕ) : ℕ :=
  ((Finset.Ioc (Nat.sqrt W) (W / 2)).filter Nat.Prime).card

/-- Prime count in the inert interval `W/2 < p <= W`. -/
def primeCombInertPrimeCount (W : ℕ) : ℕ :=
  ((Finset.Ioc (W / 2) W).filter Nat.Prime).card

/-- Unit-weight prime mass in the active post-root interval. -/
def primeCombMiddlePrimeCountMass (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) (W / 2),
    if p.Prime then 1 else 0

/-- Unit-weight prime mass in the inert interval. -/
def primeCombInertPrimeCountMass (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (W / 2) W,
    if p.Prime then 1 else 0

/-- Unit-weight prime mass over the entire post-root interval. -/
def primeCombPostSqrtPrimeCountMass (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
    if p.Prime then 1 else 0

/-- Mertens-weighted active post-root pile. -/
def primeCombMiddleMertensMass (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) (W / 2),
    if p.Prime then RHLean.Analysis.mertensSummatory (W / p) else 0

/-- The centered weighted middle pile.  This is the exact analytic residue:
geometry alone supplies no bound for it. -/
def primeCombMiddleCenteredMertensMass (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) (W / 2),
    if p.Prime then RHLean.Analysis.mertensSummatory (W / p) - 1 else 0

/-- Mertens-weighted inert pile. -/
def primeCombInertMertensMass (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (W / 2) W,
    if p.Prime then RHLean.Analysis.mertensSummatory (W / p) else 0

/-- Every inert prime has reciprocal quotient exactly one. -/
theorem primeComb_inert_div_eq_one
    {W p : ℕ} (hp : p.Prime)
    (hpHalf : W / 2 < p) (hpW : p ≤ W) :
    W / p = 1 := by
  have hWlt0 : W < p * 2 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).1 hpHalf
  have hWlt : W < 2 * p := by
    simpa [Nat.mul_comm] using hWlt0
  have hlt : W / p < 2 :=
    (Nat.div_lt_iff_lt_mul hp.pos).2 hWlt
  have hle : 1 ≤ W / p := by
    apply (Nat.le_div_iff_mul_le hp.pos).2
    simpa using hpW
  omega

private theorem primeComb_mertensSummatory_one :
    RHLean.Analysis.mertensSummatory 1 = 1 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]

/-- The inert Mertens-weighted pile is literally the unit prime-count pile.
This is geometry, not a cancellation estimate. -/
theorem primeCombInertMertensMass_eq_primeCountMass (W : ℕ) :
    primeCombInertMertensMass W = primeCombInertPrimeCountMass W := by
  unfold primeCombInertMertensMass primeCombInertPrimeCountMass
  apply Finset.sum_congr rfl
  intro p hpRange
  rcases Finset.mem_Ioc.mp hpRange with ⟨hpHalf, hpW⟩
  by_cases hprime : p.Prime
  · have hdiv := primeComb_inert_div_eq_one hprime hpHalf hpW
    simp [hprime, hdiv]
  · simp [hprime]

/-- The active middle weighted mass is its unit baseline plus the centered
Mertens residue.  No norm is taken. -/
theorem primeCombMiddleMertensMass_eq_count_add_centered (W : ℕ) :
    primeCombMiddleMertensMass W =
      primeCombMiddlePrimeCountMass W +
        primeCombMiddleCenteredMertensMass W := by
  unfold primeCombMiddleMertensMass primeCombMiddlePrimeCountMass
    primeCombMiddleCenteredMertensMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hpRange
  by_cases hprime : p.Prime
  · simp [hprime]
  · simp [hprime]

/-- The entire post-root prime count splits into the active middle and inert
intervals.  This theorem asserts only the exact partition, not equality of the
two counts. -/
theorem primeCombPostSqrtPrimeCountMass_eq_middle_add_inert
    (W : ℕ) (hseam : Nat.sqrt W ≤ W / 2) :
    primeCombPostSqrtPrimeCountMass W =
      primeCombMiddlePrimeCountMass W + primeCombInertPrimeCountMass W := by
  unfold primeCombPostSqrtPrimeCountMass primeCombMiddlePrimeCountMass
    primeCombInertPrimeCountMass
  have hsplit := Finset.sum_Ioc_consecutive
    (f := fun p : ℕ => if p.Prime then (1 : ℂ) else 0)
    hseam (Nat.div_le_self W 2)
  exact hsplit.symm

/-- The Mertens-weighted post-root tail splits over the same two intervals. -/
theorem primeSieveMertensPrimeTail_sqrt_eq_middle_add_inert
    (W : ℕ) (hseam : Nat.sqrt W ≤ W / 2) :
    primeSieveMertensPrimeTail (Nat.sqrt W) W =
      primeCombMiddleMertensMass W + primeCombInertMertensMass W := by
  unfold primeSieveMertensPrimeTail primeCombMiddleMertensMass
    primeCombInertMertensMass
  have hsplit := Finset.sum_Ioc_consecutive
    (f := fun p : ℕ =>
      if p.Prime then RHLean.Analysis.mertensSummatory (W / p) else 0)
    hseam (Nat.div_le_self W 2)
  exact hsplit.symm

/-- **Exact pile identity from the animation.**  The post-root Mertens tail is
not determined by the number of primes on the two sides of `W/2`.  It is the
unit post-root prime pile plus the centered weighted middle throw

`sum_{sqrt W < p <= W/2} (M(floor(W/p)) - 1)`.

The second term is deliberately left signed and unestimated. -/
theorem primeSieveMertensPrimeTail_sqrt_eq_count_add_centered
    (W : ℕ) (hseam : Nat.sqrt W ≤ W / 2) :
    primeSieveMertensPrimeTail (Nat.sqrt W) W =
      primeCombPostSqrtPrimeCountMass W +
        primeCombMiddleCenteredMertensMass W := by
  rw [primeSieveMertensPrimeTail_sqrt_eq_middle_add_inert W hseam,
    primeCombMiddleMertensMass_eq_count_add_centered,
    primeCombInertMertensMass_eq_primeCountMass,
    primeCombPostSqrtPrimeCountMass_eq_middle_add_inert W hseam]
  ring

/-- Proper-multiple signed channel before a large-prime flip. -/
def primeCombTailChannelMass (W p : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 2 (W / p), canonicalMoebiusWeight c

/-- The proper-multiple channel is exactly `M(floor(W/p))-1`. -/
theorem primeCombTailChannelMass_eq_mertens_sub_one
    {W p : ℕ} (hp : 0 < p) (hpW : p ≤ W) :
    primeCombTailChannelMass W p =
      RHLean.Analysis.mertensSummatory (W / p) - 1 := by
  have hK1 : 1 ≤ W / p := by
    apply (Nat.le_div_iff_mul_le hp).2
    simpa using hpW
  have hset :
      Finset.Icc 1 (W / p) = insert 1 (Finset.Icc 2 (W / p)) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hM := cofactorMobiusPrefixMass_eq_mertensSummatory (W / p)
  unfold cofactorMobiusPrefixMass at hM
  rw [hset, Finset.sum_insert (by simp)] at hM
  simp [canonicalMoebiusWeight] at hM
  unfold primeCombTailChannelMass canonicalMoebiusWeight
  linear_combination hM

/-- Signed change of the displayed total when a post-root prime flips its
proper-multiple channel. -/
def primeCombTailSignedDelta (W p : ℕ) : ℂ :=
  -2 * primeCombTailChannelMass W p

/-- The frame formula printed by the visualization:
`Delta B_p = 2 * (1 - M(floor(W/p)))`. -/
theorem primeCombTailSignedDelta_eq
    {W p : ℕ} (hp : 0 < p) (hpW : p ≤ W) :
    primeCombTailSignedDelta W p =
      2 * (1 - RHLean.Analysis.mertensSummatory (W / p)) := by
  rw [primeCombTailSignedDelta, primeCombTailChannelMass_eq_mertens_sub_one hp hpW]
  ring

/-! ## Literal per-prime masks and score accounting -/

/-- The site is still alive immediately before the current prime acts. -/
def PrimeCombFrameAlive (S : Finset ℕ) (n : ℕ) : Prop :=
  primeCombFrameSite S n ≠ 0

/-- The current prime reaches this site as a proper multiple. -/
def PrimeCombFrameProperMultiple (p n : ℕ) : Prop :=
  p < n ∧ p ∣ n

/-- Literal `killed` mask from the animation. -/
def PrimeCombFrameKilled (S : Finset ℕ) (p n : ℕ) : Prop :=
  PrimeCombFrameAlive S n ∧
    PrimeCombFrameProperMultiple p n ∧
      p ^ 2 ∣ n

/-- Literal `first_hit` mask: the site is alive, is a proper multiple of `p`,
has not been hit by an earlier proper-multiple rake, and is not killed now. -/
def PrimeCombFrameFirstHit (S : Finset ℕ) (p n : ℕ) : Prop :=
  PrimeCombFrameAlive S n ∧
    PrimeCombFrameProperMultiple p n ∧
      ¬ PrimeCombFrameProperTouched S n ∧
        ¬ p ^ 2 ∣ n

/-- Literal `flipped` mask: the site is alive, has already been hit, is reached
again by `p`, and is not killed by `p^2`. -/
def PrimeCombFrameFlipped (S : Finset ℕ) (p n : ℕ) : Prop :=
  PrimeCombFrameAlive S n ∧
    PrimeCombFrameProperMultiple p n ∧
      PrimeCombFrameProperTouched S n ∧
        ¬ p ^ 2 ∣ n

instance instDecidablePrimeCombFrameKilled (S : Finset ℕ) (p n : ℕ) :
    Decidable (PrimeCombFrameKilled S p n) :=
  Classical.propDecidable _

instance instDecidablePrimeCombFrameFirstHit (S : Finset ℕ) (p n : ℕ) :
    Decidable (PrimeCombFrameFirstHit S p n) :=
  Classical.propDecidable _

instance instDecidablePrimeCombFrameFlipped (S : Finset ℕ) (p n : ℕ) :
    Decidable (PrimeCombFrameFlipped S p n) :=
  Classical.propDecidable _

/-- Every alive proper multiple belongs to exactly one operational channel:
kill, first touch, or later-touch flip. -/
theorem primeCombFrameAliveProper_partition
    (S : Finset ℕ) {p n : ℕ}
    (halive : PrimeCombFrameAlive S n)
    (hproper : PrimeCombFrameProperMultiple p n) :
    PrimeCombFrameKilled S p n ∨
      PrimeCombFrameFirstHit S p n ∨
        PrimeCombFrameFlipped S p n := by
  classical
  by_cases hsq : p ^ 2 ∣ n
  · exact Or.inl ⟨halive, hproper, hsq⟩
  · by_cases htouched : PrimeCombFrameProperTouched S n
    · exact Or.inr (Or.inr ⟨halive, hproper, htouched, hsq⟩)
    · exact Or.inr (Or.inl ⟨halive, hproper, htouched, hsq⟩)

/-- Kill and flip masks are disjoint. -/
theorem primeCombFrameKilled_not_flipped
    (S : Finset ℕ) (p n : ℕ) :
    ¬ (PrimeCombFrameKilled S p n ∧ PrimeCombFrameFlipped S p n) := by
  intro h
  unfold PrimeCombFrameKilled PrimeCombFrameFlipped at h
  exact h.2.2.2.2 h.1.2.2

/-- The animation updates `hit` on every proper multiple, including a first
hit and a square kill. -/
theorem primeCombFrameProperTouched_insert_of_proper
    (S : Finset ℕ) {p n : ℕ}
    (hproper : PrimeCombFrameProperMultiple p n) :
    PrimeCombFrameProperTouched (insert p S) n := by
  unfold PrimeCombFrameProperTouched PrimeCombFrameProperMultiple at *
  exact ⟨p, Finset.mem_insert_self p S, hproper.1, hproper.2⟩

/-- Literal one-prime state transition used by the visualization. -/
def primeCombAnimationStepSite (S : Finset ℕ) (p n : ℕ) : ℤ := by
  classical
  exact
    if PrimeCombFrameKilled S p n then 0
    else if PrimeCombFrameFlipped S p n then -primeCombFrameSite S n
    else primeCombFrameSite S n

/-- First touch leaves the prime-candidate sign unchanged. -/
theorem primeCombAnimationStepSite_eq_of_firstHit
    (S : Finset ℕ) {p n : ℕ}
    (h : PrimeCombFrameFirstHit S p n) :
    primeCombAnimationStepSite S p n = primeCombFrameSite S n := by
  classical
  unfold PrimeCombFrameFirstHit at h
  rcases h with ⟨halive, hproper, hnotTouched, hnotSq⟩
  simp [primeCombAnimationStepSite, PrimeCombFrameKilled,
    PrimeCombFrameFlipped, halive, hproper, hnotTouched, hnotSq]

/-- A kill writes zero. -/
theorem primeCombAnimationStepSite_eq_zero_of_killed
    (S : Finset ℕ) {p n : ℕ}
    (h : PrimeCombFrameKilled S p n) :
    primeCombAnimationStepSite S p n = 0 := by
  classical
  simp [primeCombAnimationStepSite, h]

/-- A later touch flips the old sign. -/
theorem primeCombAnimationStepSite_eq_neg_of_flipped
    (S : Finset ℕ) {p n : ℕ}
    (h : PrimeCombFrameFlipped S p n) :
    primeCombAnimationStepSite S p n = -primeCombFrameSite S n := by
  classical
  unfold PrimeCombFrameFlipped at h
  rcases h with ⟨halive, hproper, htouched, hnotSq⟩
  simp [primeCombAnimationStepSite, PrimeCombFrameKilled,
    PrimeCombFrameFlipped, halive, hproper, htouched, hnotSq]

/-- Per-site score change in exactly the form used by the Python assertion. -/
theorem primeCombAnimationStepSite_sub
    (S : Finset ℕ) (p n : ℕ) :
    primeCombAnimationStepSite S p n - primeCombFrameSite S n =
      -(if PrimeCombFrameKilled S p n then primeCombFrameSite S n else 0) -
        2 * (if PrimeCombFrameFlipped S p n then primeCombFrameSite S n else 0) := by
  classical
  by_cases hkilled : PrimeCombFrameKilled S p n
  · have hnotFlipped : ¬ PrimeCombFrameFlipped S p n := by
      intro hflipped
      exact primeCombFrameKilled_not_flipped S p n ⟨hkilled, hflipped⟩
    simp [primeCombAnimationStepSite, hkilled, hnotFlipped]
  · by_cases hflipped : PrimeCombFrameFlipped S p n
    · simp [primeCombAnimationStepSite, hkilled, hflipped]
      ring
    · simp [primeCombAnimationStepSite, hkilled, hflipped]

/-- Number of killed seats in the current frame. -/
def primeCombFrameKilledCount (S : Finset ℕ) (p W : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 W).filter fun n => PrimeCombFrameKilled S p n).card

/-- Number of first-hit seats in the current frame. -/
def primeCombFrameFirstHitCount (S : Finset ℕ) (p W : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 W).filter fun n => PrimeCombFrameFirstHit S p n).card

/-- Number of later-touch flipped seats in the current frame. -/
def primeCombFrameFlippedCount (S : Finset ℕ) (p W : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 W).filter fun n => PrimeCombFrameFlipped S p n).card

/-- Signed old-state mass on seats killed in this frame. -/
def primeCombFrameKillChannelMass (S : Finset ℕ) (p W : ℕ) : ℤ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 W,
    if PrimeCombFrameKilled S p n then primeCombFrameSite S n else 0

/-- Signed old-state mass on seats flipped in this frame. -/
def primeCombFrameFlipChannelMass (S : Finset ℕ) (p W : ℕ) : ℤ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 W,
    if PrimeCombFrameFlipped S p n then primeCombFrameSite S n else 0

/-- Prefix score after applying exactly one animation step. -/
def primeCombAnimationStepPrefixMass (S : Finset ℕ) (p W : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 W, primeCombAnimationStepSite S p n

/-- Displayed signed-score change in the current frame. -/
def primeCombAnimationStepDelta (S : Finset ℕ) (p W : ℕ) : ℤ :=
  primeCombAnimationStepPrefixMass S p W - primeCombFramePrefixMass S W

/-- **Exact frame score assertion.**  Summing the pointwise update gives the
Python identity

`delta_signed_sum = - kill_channel_mass_before - 2 * flip_channel_mass_before`.
-/
theorem primeCombAnimationStepDelta_eq_channels
    (S : Finset ℕ) (p W : ℕ) :
    primeCombAnimationStepDelta S p W =
      -primeCombFrameKillChannelMass S p W -
        2 * primeCombFrameFlipChannelMass S p W := by
  classical
  unfold primeCombAnimationStepDelta primeCombAnimationStepPrefixMass
    primeCombFramePrefixMass
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ n ∈ Finset.Icc 1 W,
        (primeCombAnimationStepSite S p n - primeCombFrameSite S n)) =
      ∑ n ∈ Finset.Icc 1 W,
        (-(if PrimeCombFrameKilled S p n then primeCombFrameSite S n else 0) -
          2 * (if PrimeCombFrameFlipped S p n then primeCombFrameSite S n else 0)) := by
            apply Finset.sum_congr rfl
            intro n _hn
            exact primeCombAnimationStepSite_sub S p n
    _ = -primeCombFrameKillChannelMass S p W -
          2 * primeCombFrameFlipChannelMass S p W := by
            unfold primeCombFrameKillChannelMass primeCombFrameFlipChannelMass
            rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]

end RHLean.Proof
