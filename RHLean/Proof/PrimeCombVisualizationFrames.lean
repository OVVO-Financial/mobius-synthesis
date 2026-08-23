import Mathlib
import RHLean.Proof.PrimeSievePostSqrtGap

/-!
# Frame-by-frame prime-candidate comb dynamics

This module formalizes the exact state machine displayed by the diagnostic
`prime_comb_viz 2.py`.

The visualization does not start from the all-plus field.  It starts from the
prime-candidate seed

```text
J_0(1) = +1,
J_0(n) = -1  for n >= 2.
```

A prime acts on proper multiples only.  A selected prime-square hit kills a
site.  On squarefree support, the first selected prime divisor leaves the
initial `-1` unchanged and every later selected prime divisor flips the sign.
The definitions below encode the displayed frame directly from the finite set
of primes that have already been processed.

The later sections identify the geometric thresholds shown by the animation:

* a prime `p` has exactly `floor(W/p)-1` possible proper-multiple seats;
* after `p > W/3`, at most the single child `2p` remains;
* after all primes through `sqrt W`, the small-prime writing phase is complete
  on every smooth site, and every unresolved composite `c*p` with
  `p > sqrt W` carries the already-written cofactor sign `mu(c)`;
* a prime above `sqrt W` cannot kill, and a prime above `W/2` has no proper
  multiple in the block and is completely inert.

No estimate or asymptotic input occurs in this file.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## The displayed frame -/

/-- Selected prime coordinates dividing a site. -/
def primeCombFrameDivisors (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  S.filter fun p => p ∣ n

/-- A square kill has already occurred in the displayed frame. -/
def PrimeCombFrameSquareHit (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p ∈ S, p ^ 2 ∣ n

/-- At least one selected prime coordinate divides the site. -/
def PrimeCombFrameTouched (S : Finset ℕ) (n : ℕ) : Prop :=
  (primeCombFrameDivisors S n).Nonempty

/-- At least one already-processed prime has hit the site as a proper multiple.
This is the mathematical counterpart of the visualization's `hit` Boolean. -/
def PrimeCombFrameProperTouched (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p ∈ S, p < n ∧ p ∣ n

/-- The exact displayed prime-candidate state after the prime coordinates in
`S` have been processed.

The exceptional site `1` remains `+1`.  Every other untouched site remains the
prime-candidate value `-1`.  A selected square hit is `0`.  Once at least one
selected prime divisor is present, the surviving sign is the parity of the
number of selected distinct prime divisors. -/
def primeCombFrameSite (S : Finset ℕ) (n : ℕ) : ℤ := by
  classical
  exact
    if n = 0 then 0
    else if n = 1 then 1
    else if PrimeCombFrameSquareHit S n then 0
    else
      let k := (primeCombFrameDivisors S n).card
      if k = 0 then -1 else (-1 : ℤ) ^ k

/-- Signed sum displayed in the lower-left plot. -/
def primeCombFramePrefixMass (S : Finset ℕ) (W : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 W, primeCombFrameSite S n

/-- Number of white sites in the displayed grid. -/
def primeCombFrameWhiteCount (S : Finset ℕ) (W : ℕ) : ℕ :=
  ((Finset.Icc 1 W).filter fun n => primeCombFrameSite S n = 0).card

/-- Number of displayed sites already agreeing with the true Möbius value. -/
def primeCombFrameAgreementCount (S : Finset ℕ) (W : ℕ) : ℕ :=
  ((Finset.Icc 1 W).filter fun n => primeCombFrameSite S n = μ n).card

@[simp] theorem primeCombFrameDivisors_empty (n : ℕ) :
    primeCombFrameDivisors ∅ n = ∅ := by
  simp [primeCombFrameDivisors]

@[simp] theorem primeCombFrameSite_zero (S : Finset ℕ) :
    primeCombFrameSite S 0 = 0 := by
  simp [primeCombFrameSite]

@[simp] theorem primeCombFrameSite_one (S : Finset ℕ) :
    primeCombFrameSite S 1 = 1 := by
  simp [primeCombFrameSite]

/-- Exact prime-candidate seed shown by frame zero. -/
theorem primeCombFrameSite_empty_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    primeCombFrameSite ∅ n = -1 := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  simp [primeCombFrameSite, PrimeCombFrameSquareHit, hn0, hn1]

/-- The visualization's seed is therefore `+1,-1,-1,...` on every finite
positive block. -/
theorem primeCombFrameSeed
    (n : ℕ) (hn : 1 ≤ n) :
    primeCombFrameSite ∅ n = if n = 1 then 1 else -1 := by
  by_cases hn1 : n = 1
  · subst n
    simp
  · have hn2 : 2 ≤ n := by omega
    simp [hn1, primeCombFrameSite_empty_of_two_le hn2]

@[simp] theorem primeCombFrameDivisors_insert
    (S : Finset ℕ) (p n : ℕ) :
    primeCombFrameDivisors (insert p S) n =
      if p ∣ n then insert p (primeCombFrameDivisors S n)
      else primeCombFrameDivisors S n := by
  classical
  ext q
  by_cases hpn : p ∣ n
  · simp only [hpn, if_true, primeCombFrameDivisors,
      Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hqp | hqS, hqdiv⟩
      · exact Or.inl hqp
      · exact Or.inr ⟨hqS, hqdiv⟩
    · rintro (hqp | ⟨hqS, hqdiv⟩)
      · subst q
        exact ⟨Or.inl rfl, hpn⟩
      · exact ⟨Or.inr hqS, hqdiv⟩
  · simp only [hpn, if_false, primeCombFrameDivisors,
      Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hqp | hqS, hqdiv⟩
      · subst q
        exact (hpn hqdiv).elim
      · exact ⟨hqS, hqdiv⟩
    · rintro ⟨hqS, hqdiv⟩
      exact ⟨Or.inr hqS, hqdiv⟩

@[simp] theorem primeCombFrameSquareHit_insert
    (S : Finset ℕ) (p n : ℕ) :
    PrimeCombFrameSquareHit (insert p S) n ↔
      p ^ 2 ∣ n ∨ PrimeCombFrameSquareHit S n := by
  simp [PrimeCombFrameSquareHit]

/-! ## Shrinking rake geometry -/

/-- Multiplier indices `k` for the proper multiples `k*p <= W`. -/
def primeCombProperMultiplierSet (p W : ℕ) : Finset ℕ :=
  Finset.Icc 2 (W / p)

/-- Actual proper-multiple seats that prime `p` can possibly rake in the block. -/
def primeCombProperMultipleSet (p W : ℕ) : Finset ℕ :=
  (primeCombProperMultiplierSet p W).image fun k => k * p

/-- The candidate bunch has exactly `floor(W/p)-1` multiplier indices. -/
theorem card_primeCombProperMultiplierSet (p W : ℕ) :
    (primeCombProperMultiplierSet p W).card = W / p - 1 := by
  unfold primeCombProperMultiplierSet
  rw [Nat.card_Icc]
  omega

/-- For positive `p`, multiplication by `p` is injective, so the number of
possible seats is also exactly `floor(W/p)-1`. -/
theorem card_primeCombProperMultipleSet
    (p W : ℕ) (hp : 0 < p) :
    (primeCombProperMultipleSet p W).card = W / p - 1 := by
  unfold primeCombProperMultipleSet
  rw [Finset.card_image_of_injective _
    (fun a b hab => Nat.eq_of_mul_eq_mul_right hp hab)]
  exact card_primeCombProperMultiplierSet p W

/-- Membership in the multiplier bunch is exactly the hyperbolic inequality
`2 <= k` and `k*p <= W`. -/
theorem mem_primeCombProperMultiplierSet_iff
    {p W k : ℕ} (hp : 0 < p) :
    k ∈ primeCombProperMultiplierSet p W ↔
      2 ≤ k ∧ k * p ≤ W := by
  unfold primeCombProperMultiplierSet
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨hk2, hkdiv⟩
    exact ⟨hk2, (Nat.le_div_iff_mul_le hp).1 hkdiv⟩
  · rintro ⟨hk2, hkmul⟩
    exact ⟨hk2, (Nat.le_div_iff_mul_le hp).2 hkmul⟩

/-- Once `p > W/3`, the only possible multiplier index is `2`. -/
theorem primeCombProperMultiplierSet_subset_two_of_third_lt
    {W p : ℕ} (hp : 0 < p) (hpThird : W / 3 < p) :
    primeCombProperMultiplierSet p W ⊆ {2} := by
  intro k hk
  have hkData := (mem_primeCombProperMultiplierSet_iff hp).1 hk
  have hWlt : W < p * 3 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).1 hpThird
  have hWlt' : W < 3 * p := by simpa [Nat.mul_comm] using hWlt
  have hdivlt : W / p < 3 :=
    (Nat.div_lt_iff_lt_mul hp).2 hWlt'
  have hkLe : k ≤ W / p :=
    (Nat.le_div_iff_mul_le hp).2 hkData.2
  have hkLt3 : k < 3 := hkLe.trans_lt hdivlt
  have hkLe2 : k ≤ 2 := by
    exact Nat.lt_succ_iff.mp (by simpa using hkLt3)
  have hkEq : k = 2 := Nat.le_antisymm hkLe2 hkData.1
  simp [hkEq]

/-- On the active part of that regime, the bunch is literally the singleton
`{2}`: the rake has become the pairing `p <-> 2p`. -/
theorem primeCombProperMultiplierSet_eq_two_of_third_lt_of_active
    {W p : ℕ} (hp : 0 < p)
    (hpThird : W / 3 < p) (hactive : 2 * p ≤ W) :
    primeCombProperMultiplierSet p W = {2} := by
  apply Finset.Subset.antisymm
  · exact primeCombProperMultiplierSet_subset_two_of_third_lt hp hpThird
  · intro k hk
    simp only [Finset.mem_singleton] at hk
    subst k
    exact (mem_primeCombProperMultiplierSet_iff hp).2 ⟨by omega, hactive⟩

/-- Above `W/2` there are no proper-multiple indices at all. -/
theorem primeCombProperMultiplierSet_eq_empty_of_half_lt
    {W p : ℕ} (hp : 0 < p) (hpHalf : W / 2 < p) :
    primeCombProperMultiplierSet p W = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [card_primeCombProperMultiplierSet]
  have hWlt : W < p * 2 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).1 hpHalf
  have hWlt' : W < 2 * p := by simpa [Nat.mul_comm] using hWlt
  have hdivlt : W / p < 2 :=
    (Nat.div_lt_iff_lt_mul hp).2 hWlt'
  omega

/-- Prime children available to a fixed parent/cofactor `c`. -/
def primeCombParentPrimeChildren (c W : ℕ) : Finset ℕ :=
  (primeCombProperMultiplierSet c W).filter Nat.Prime

/-- Parent-side degree is bounded by the same shrinking hyperbola. -/
theorem card_primeCombParentPrimeChildren_le
    (c W : ℕ) :
    (primeCombParentPrimeChildren c W).card ≤ W / c - 1 := by
  unfold primeCombParentPrimeChildren
  calc
    ((primeCombProperMultiplierSet c W).filter Nat.Prime).card ≤
        (primeCombProperMultiplierSet c W).card := Finset.card_filter_le _ _
    _ = W / c - 1 := card_primeCombProperMultiplierSet c W

/-- Once the parent itself lies beyond `W/3`, at most the prime child `2` can
still fit. -/
theorem card_primeCombParentPrimeChildren_le_one_of_third_lt
    {W c : ℕ} (hc : 0 < c) (hcThird : W / 3 < c) :
    (primeCombParentPrimeChildren c W).card ≤ 1 := by
  have hsub : primeCombParentPrimeChildren c W ⊆ ({2} : Finset ℕ) := by
    intro q hq
    have hqBase := (Finset.mem_filter.mp hq).1
    exact primeCombProperMultiplierSet_subset_two_of_third_lt hc hcThird hqBase
  exact (Finset.card_le_card hsub).trans (by simp)

/-! ## Exact relation with the repository's multiplicative comb -/

private theorem no_frameSquareHit_of_squarefree
    (S : Finset ℕ) {n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsq : Squarefree n) :
    ¬ PrimeCombFrameSquareHit S n := by
  intro hhit
  rcases hhit with ⟨p, hpS, hp2⟩
  have hpPrime := hprime p hpS
  have hnot : ¬ p ^ 2 ∣ n := by
    simpa [pow_two] using
      (Nat.squarefree_iff_prime_squarefree.mp hsq p hpPrime)
  exact hnot hp2

/-- Once a squarefree site has actually been touched, the prime-candidate frame
is exactly the all-plus multiplicative comb state.  The only difference between
the two presentations is the deliberately retained `-1` on untouched prime
candidates. -/
theorem primeCombFrameSite_eq_allPlus_of_squarefree_touched
    (S : Finset ℕ) {n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hnpos : 0 < n) (hn1 : n ≠ 1)
    (hsq : Squarefree n)
    (htouched : PrimeCombFrameTouched S n) :
    primeCombFrameSite S n = allPlusPrimeCombSite S n := by
  classical
  have hnoSquare := no_frameSquareHit_of_squarefree S hprime hsq
  have hcard : (primeCombFrameDivisors S n).card ≠ 0 := by
    exact Finset.card_ne_zero.mpr htouched
  have hseed :=
    seededPrimeComb_eq_neg_negOnePow_filter_card S n hprime hsq
  have hseed' :
      seededPrimeComb S n =
        -((-1 : ℤ) ^ (primeCombFrameDivisors S n).card) := by
    simpa [primeCombFrameDivisors] using hseed
  unfold primeCombFrameSite
  rw [if_neg (Nat.ne_of_gt hnpos), if_neg hn1, if_neg hnoSquare]
  dsimp
  rw [if_neg hcard]
  unfold allPlusPrimeCombSite
  rw [if_neg (Nat.ne_of_gt hnpos), hseed']
  ring

/-! ## The square-root seam -/

/-- A prime above the square-root frontier cannot create a square kill anywhere
inside the block. -/
theorem largePrime_cannot_squareKill
    {W p n : ℕ}
    (hpRoot : Nat.sqrt W < p)
    (hnpos : 0 < n) (hnW : n ≤ W) :
    ¬ p ^ 2 ∣ n := by
  intro hsq
  have hp2le : p ^ 2 ≤ n := Nat.le_of_dvd hnpos hsq
  have hpLe : p ≤ Nat.sqrt W :=
    Nat.le_sqrt.mpr (by
      simpa [pow_two] using hp2le.trans hnW)
  omega

/-- Conversely, every prime-square kill visible in the block is caused by an
active prime `p <= floor(W/2)`. -/
theorem squareKill_prime_le_activeBound
    {W p n : ℕ}
    (hp : p.Prime) (hnpos : 0 < n) (hnW : n ≤ W)
    (hsq : p ^ 2 ∣ n) :
    p ≤ W / 2 := by
  have hp2le : p ^ 2 ≤ n := Nat.le_of_dvd hnpos hsq
  have hp2 : 2 ≤ p := hp.two_le
  have h2p : 2 * p ≤ p ^ 2 := by
    nlinarith
  omega

/-- A prime above `W/2` has no proper multiple in `1,...,W`.  This is the exact
inert-prime geometry used by the animation. -/
theorem primeAboveHalf_no_properMultiple
    {W p n : ℕ}
    (hpHalf : W / 2 < p) (hnW : n ≤ W) :
    ¬ (2 * p ≤ n ∧ p ∣ n) := by
  intro h
  have hWlt : W < 2 * p := by omega
  omega

/-- If `p > sqrt W` and `c*p <= W`, then the cofactor lies on the small side of
the hyperbola. -/
theorem cofactor_le_sqrt_of_largePrime_mul_le
    {W c p : ℕ}
    (hpRoot : Nat.sqrt W < p)
    (hcpW : c * p ≤ W) :
    c ≤ Nat.sqrt W := by
  by_contra hnot
  have hcRoot : Nat.sqrt W < c := Nat.lt_of_not_ge hnot
  have hcSucc : Nat.sqrt W + 1 ≤ c := by omega
  have hpSucc : Nat.sqrt W + 1 ≤ p := by omega
  have hmul :
      (Nat.sqrt W + 1) * (Nat.sqrt W + 1) ≤ c * p :=
    Nat.mul_le_mul hcSucc hpSucc
  have hlt : W < (Nat.sqrt W + 1) ^ 2 := Nat.lt_succ_sqrt' W
  have : W < c * p := by
    calc
      W < (Nat.sqrt W + 1) ^ 2 := hlt
      _ = (Nat.sqrt W + 1) * (Nat.sqrt W + 1) := by ring
      _ ≤ c * p := hmul
  omega

/-- The canonical square-root coordinate set really covers the square-root
frontier, with no strict `sqrt W < y` slack. -/
theorem primesUpTo_sqrt_exactCoverage (W : ℕ) :
    PrimeWheelSqrtCoverage (primesUpTo (Nat.sqrt W)) W := by
  exact primesUpTo_sqrtCoverage (le_rfl)

/-- Every squarefree `sqrt W`-smooth site is already exactly Möbius in the
prime-candidate frame. -/
theorem primeCombSqrtFrame_eq_moebius_of_smooth
    {W n : ℕ}
    (hnpos : 0 < n) (hnW : n ≤ W)
    (hsq : Squarefree n)
    (hsmooth :
      IsPrimeWheelSmooth (primesUpTo (Nat.sqrt W)) n) :
    primeCombFrameSite (primesUpTo (Nat.sqrt W)) n = μ n := by
  classical
  by_cases hn1 : n = 1
  · subst n
    simp
  have hprime : ∀ p ∈ primesUpTo (Nat.sqrt W), Nat.Prime p := by
    intro p hp
    exact prime_of_mem_primesUpTo hp
  have htouched : PrimeCombFrameTouched (primesUpTo (Nat.sqrt W)) n := by
    have hn : 1 < n := by omega
    have hqmem := canonicalLargestPrimeFactor_mem_primeFactors hn
    have hqS := hsmooth.2 _ hqmem
    unfold PrimeCombFrameTouched primeCombFrameDivisors
    exact ⟨canonicalLargestPrimeFactor n, Finset.mem_filter.mpr
      ⟨hqS, Nat.dvd_of_mem_primeFactors hqmem⟩⟩
  rw [primeCombFrameSite_eq_allPlus_of_squarefree_touched
    (primesUpTo (Nat.sqrt W)) hprime hnpos hn1 hsq htouched]
  exact allPlusPrimeCombSite_eq_moebius_of_smooth
    (primesUpTo (Nat.sqrt W)) hprime hnpos hsmooth

/-- Every nonsquarefree site has already been killed after the square-root
prime phase. -/
theorem primeCombSqrtFrame_eq_zero_of_not_squarefree
    {W n : ℕ}
    (hnpos : 0 < n) (hnW : n ≤ W)
    (hnsq : ¬ Squarefree n) :
    primeCombFrameSite (primesUpTo (Nat.sqrt W)) n = 0 := by
  classical
  have hn1 : n ≠ 1 := by
    intro hn
    subst n
    exact hnsq (by simp)
  rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push_neg at hnsq
  rcases hnsq with ⟨p, hpPrime, hpSq⟩
  have hpSqLeN : p * p ≤ n := Nat.le_of_dvd hnpos hpSq
  have hpLe : p ≤ Nat.sqrt W :=
    Nat.le_sqrt.mpr (hpSqLeN.trans hnW)
  have hpS : p ∈ primesUpTo (Nat.sqrt W) :=
    mem_primesUpTo.mpr ⟨hpPrime, hpLe⟩
  have hhit : PrimeCombFrameSquareHit (primesUpTo (Nat.sqrt W)) n := by
    refine ⟨p, hpS, ?_⟩
    simpa [pow_two] using hpSq
  simp [primeCombFrameSite, Nat.ne_of_gt hnpos, hn1, hhit]

/-- In particular every site `n <= sqrt W` is already exact after the small
primes have been processed. -/
theorem primeCombSqrtFrame_eq_moebius_of_le_sqrt
    {W n : ℕ}
    (hnpos : 0 < n) (hnRoot : n ≤ Nat.sqrt W) :
    primeCombFrameSite (primesUpTo (Nat.sqrt W)) n = μ n := by
  by_cases hsq : Squarefree n
  · have hprime : ∀ p ∈ primesUpTo (Nat.sqrt W), Nat.Prime p := by
      intro p hp
      exact prime_of_mem_primesUpTo hp
    have hsmooth : IsPrimeWheelSmooth (primesUpTo (Nat.sqrt W)) n := by
      refine ⟨hsq, ?_⟩
      intro p hp
      have hpdata := Nat.mem_primeFactors.mp hp
      have hpLeN : p ≤ n := Nat.le_of_dvd hnpos hpdata.2.1
      exact mem_primesUpTo.mpr ⟨hpdata.1, hpLeN.trans hnRoot⟩
    exact primeCombSqrtFrame_eq_moebius_of_smooth
      hnpos (hnRoot.trans (Nat.sqrt_le_self W)) hsq hsmooth
  · have hzero := primeCombSqrtFrame_eq_zero_of_not_squarefree
      hnpos (hnRoot.trans (Nat.sqrt_le_self W)) hsq
    have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    simpa [hmu] using hzero

/-! ## Tail seats: the small-prime writing is already complete -/

private theorem moebius_mul_prime_eq_neg_of_lt
    {c p : ℕ}
    (hp : p.Prime) (hcpos : 0 < c) (hcp : c < p) :
    μ (c * p) = -μ c := by
  have hpnot : ¬ p ∣ c := by
    intro hpc
    have hpLe : p ≤ c := Nat.le_of_dvd hcpos hpc
    omega
  have hcop : Nat.Coprime c p :=
    (hp.coprime_iff_not_dvd.mpr hpnot).symm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- A proper large-prime tail seat `c*p` has already been touched by the
small-prime phase: one of the prime factors of `c` lies at or below `sqrt W`. -/
theorem primeCombSqrtFrame_tailSeat_touched
    {W c p : ℕ}
    (hpRoot : Nat.sqrt W < p)
    (hc : 2 ≤ c) (hcpW : c * p ≤ W) :
    PrimeCombFrameTouched (primesUpTo (Nat.sqrt W)) (c * p) := by
  have hcRoot : c ≤ Nat.sqrt W :=
    cofactor_le_sqrt_of_largePrime_mul_le hpRoot hcpW
  have hcgt : 1 < c := by omega
  have hqPrime := canonicalLargestPrimeFactor_prime hcgt
  have hqmem := canonicalLargestPrimeFactor_mem_primeFactors hcgt
  have hqdiv : canonicalLargestPrimeFactor c ∣ c :=
    Nat.dvd_of_mem_primeFactors hqmem
  have hqLeC : canonicalLargestPrimeFactor c ≤ c :=
    Nat.le_of_dvd (by omega) hqdiv
  have hqS : canonicalLargestPrimeFactor c ∈ primesUpTo (Nat.sqrt W) :=
    mem_primesUpTo.mpr ⟨hqPrime, hqLeC.trans hcRoot⟩
  unfold PrimeCombFrameTouched primeCombFrameDivisors
  refine ⟨canonicalLargestPrimeFactor c, Finset.mem_filter.mpr ⟨hqS, ?_⟩⟩
  exact dvd_mul_of_dvd_left hqdiv p

/-- Such a tail seat is not small-prime smooth because its large prime factor
`p` is still missing from the processed coordinate set. -/
theorem primeCombSqrtFrame_tailSeat_not_smooth
    {W c p : ℕ}
    (hp : p.Prime) (hpRoot : Nat.sqrt W < p)
    (hcpos : 0 < c) :
    ¬ IsPrimeWheelSmooth (primesUpTo (Nat.sqrt W)) (c * p) := by
  intro hsmooth
  have hn0 : c * p ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt hcpos) hp.ne_zero
  have hpdiv : p ∣ c * p := by
    exact ⟨c, by simp [Nat.mul_comm]⟩
  have hpmem : p ∈ (c * p).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdiv, hn0⟩
  have hpS := hsmooth.2 p hpmem
  have hpLe := (mem_primesUpTo.mp hpS).2
  omega

/-- **Tail-seat frame theorem.**  After the square-root phase, every proper
unresolved squarefree seat `n=c*p` with `p>sqrt W` is literally sitting at the
already-finished cofactor value `mu(c)`, waiting for the large prime `p` to
flip it. -/
theorem primeCombSqrtFrame_tailSeat_eq_cofactorMoebius
    {W c p : ℕ}
    (hp : p.Prime) (hpRoot : Nat.sqrt W < p)
    (hc : 2 ≤ c) (hcpW : c * p ≤ W)
    (hsq : Squarefree (c * p)) :
    primeCombFrameSite (primesUpTo (Nat.sqrt W)) (c * p) = μ c := by
  have hcRoot : c ≤ Nat.sqrt W :=
    cofactor_le_sqrt_of_largePrime_mul_le hpRoot hcpW
  have hcp : c < p := hcRoot.trans_lt hpRoot
  have hnpos : 0 < c * p := Nat.mul_pos (by omega) hp.pos
  have hn1 : c * p ≠ 1 := by
    have hcp2 : 2 ≤ c * p := by
      calc
        2 = 2 * 1 := by simp
        _ ≤ c * p := Nat.mul_le_mul hc hp.one_le
    omega
  have hprime : ∀ q ∈ primesUpTo (Nat.sqrt W), Nat.Prime q := by
    intro q hq
    exact prime_of_mem_primesUpTo hq
  have htouched := primeCombSqrtFrame_tailSeat_touched hpRoot hc hcpW
  have hframe := primeCombFrameSite_eq_allPlus_of_squarefree_touched
    (primesUpTo (Nat.sqrt W)) hprime hnpos hn1 hsq htouched
  have hcover := primesUpTo_sqrt_exactCoverage W
  have hnonsmooth :=
    primeCombSqrtFrame_tailSeat_not_smooth hp hpRoot (by omega : 0 < c)
  have hall := allPlusPrimeCombSite_eq_neg_moebius_of_not_smooth
    (primesUpTo (Nat.sqrt W)) hprime hcover hsq hcpW hnonsmooth
  have hmu := moebius_mul_prime_eq_neg_of_lt hp (by omega) hcp
  rw [hframe, hall, hmu]
  ring

/-- An unresolved large prime itself is the exceptional cofactor-one face.  It
never receives a proper-prime hit and simply remains the displayed prime
candidate `-1`, already equal to its final Möbius value. -/
theorem primeCombSqrtFrame_largePrimeSeat_eq_neg_one
    {W p : ℕ}
    (hp : p.Prime) (hpRoot : Nat.sqrt W < p) :
    primeCombFrameSite (primesUpTo (Nat.sqrt W)) p = -1 := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : p ≠ 1 := hp.ne_one
  have hdiv : primeCombFrameDivisors (primesUpTo (Nat.sqrt W)) p = ∅ := by
    ext q
    simp only [primeCombFrameDivisors, Finset.mem_filter, Finset.notMem_empty,
      iff_false]
    intro h
    rcases h with ⟨hqS, hqdiv⟩
    have hqPrime := prime_of_mem_primesUpTo hqS
    rcases (Nat.dvd_prime hp).mp hqdiv with hq1 | hqp
    · exact hqPrime.ne_one hq1
    · have hqLe := (mem_primesUpTo.mp hqS).2
      subst q
      omega
  have hnoSquare : ¬ PrimeCombFrameSquareHit
      (primesUpTo (Nat.sqrt W)) p := by
    intro hsq
    rcases hsq with ⟨q, hqS, hq2⟩
    have hqdiv : q ∣ p := by
      rcases hq2 with ⟨k, hk⟩
      refine ⟨q * k, ?_⟩
      simpa [pow_two, Nat.mul_assoc] using hk
    have hmem : q ∈ primeCombFrameDivisors (primesUpTo (Nat.sqrt W)) p :=
      Finset.mem_filter.mpr ⟨hqS, hqdiv⟩
    rw [hdiv] at hmem
    exact (Finset.notMem_empty q) hmem
  simp [primeCombFrameSite, hp0, hp1, hnoSquare, hdiv]

/-! ## Active and inert large-prime frames -/

/-- The post-square-root phase cannot produce any new white square-kill sites. -/
theorem primeComb_largePrimeStep_no_squareHit
    {W p n : ℕ}
    (hpRoot : Nat.sqrt W < p)
    (hnpos : 0 < n) (hnW : n ≤ W) :
    ¬ p ^ 2 ∣ n :=
  largePrime_cannot_squareKill hpRoot hnpos hnW

/-- The far tail `p>W/2` has no proper-multiple rake at all. -/
theorem primeComb_farPrimeStep_inert_geometry
    {W p n : ℕ}
    (hpHalf : W / 2 < p) (hnW : n ≤ W) :
    ¬ (2 * p ≤ n ∧ p ∣ n) :=
  primeAboveHalf_no_properMultiple hpHalf hnW

end RHLean.Proof
