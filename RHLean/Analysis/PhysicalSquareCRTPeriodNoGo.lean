import Mathlib
import RHLean.Analysis.PhysicalSquareCRTTransfer
import RHLean.Analysis.OutsidePrimeCompleteDeletionFirstMoment
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Analysis.ElevenWeightOneFirstMoment

/-!
# The complete-CRT core is empty once the period exceeds the square block

`PhysicalSquareCRTTransfer` partitions the physical zero-free transition
population of one square block into cells lying on complete aligned CRT periods
and the incomplete square-clock boundary:

`physicalT R = crtT P R + boundaryT P R`.

That partition is exact for every `P` and `R`.  This module records the
geometric constraint that decides whether it carries any content.

The square-block transition window `threeSlotSquareBlockTransitionCells R`
consists of `k` with `R^2 <= 4*k+1` and `4*k+7 < (R+1)^2`, so the injection
`k ↦ 4*k+1` lands it inside `Icc (R^2) ((R+1)^2)` and its cardinality is at most
`2*R+2`.  An aligned CRT period has cardinality exactly
`finitePrimeCRTPeriod P = max 1 (prod_{p in P} p^2)`.  A complete period can
therefore sit inside the window only if

`prod_{p in P} p^2 <= 2*R + 2`.

When that fails the complete-period core is *empty*, `crtT P R = 0`, and
`boundaryT P R = physicalT R`: the partition degenerates to
`physicalT = 0 + physicalT` and the CRT interior carries nothing.

The constraint bites immediately, because `FinitePrimeTMixing` only gives strict
Walsh contraction for `p >= 11`.  Taking the selected primes from `11` upward:

```text
P = {11}              period          121   needs R >=            60
P = {11,13}           period       20 449   needs R >=        10 224
P = {11,13,17}        period    5 909 761   needs R >=     2 954 880
P = {11,13,17,19}     period 2 133 423 721   needs R >= 1 066 711 860
```

The period is a product of squares, so it grows doubly exponentially in the
number of selected primes while the window grows linearly in `R`.  The number of
usable primes is therefore `O(log R)`, and the total available Walsh contraction
`prod_{p in P} (1 - 2*s*(p-1)/(p^2-6))` over such a set is a bounded factor, not
a power saving.

This module also records the corrected six-offset `q^2` transport needed after
an earlier layer.  A fixed least-owner physical channel transports the selected-prime field
by affine pullback to the source cell; it is not literally the rough Go Mobius
daughter.  The complete `{11}` / `q=3` population kernel-certifies that
obstruction, while simultaneously certifying that the exact `19/23` weight-one
factor survives.
-/

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- An aligned CRT period has exactly the period's cardinality. -/
theorem card_finitePrimeCRTOrbit (P : Finset ℕ) (k : ℕ) :
    (finitePrimeCRTOrbit P k).card = finitePrimeCRTPeriod P := by
  have hEq : finitePrimeCRTOrbit P k =
      Finset.Ico ((k / finitePrimeCRTPeriod P) * finitePrimeCRTPeriod P)
        ((k / finitePrimeCRTPeriod P + 1) * finitePrimeCRTPeriod P) := rfl
  rw [hEq, Nat.card_Ico]
  have hmul :
      (k / finitePrimeCRTPeriod P + 1) * finitePrimeCRTPeriod P =
        (k / finitePrimeCRTPeriod P) * finitePrimeCRTPeriod P +
          finitePrimeCRTPeriod P := by
    ring
  omega

/-- The square-block transition window holds at most `2*R+2` cells.  The active
sites `4*k+1` of distinct cells are distinct and all lie in `Icc (R^2) ((R+1)^2)`. -/
theorem card_threeSlotSquareBlockTransitionCells_le (R : ℕ) :
    (threeSlotSquareBlockTransitionCells R).card ≤ 2 * R + 2 := by
  classical
  have hmaps : ∀ k ∈ threeSlotSquareBlockTransitionCells R,
      4 * k + 1 ∈ Finset.Icc (R ^ 2) ((R + 1) ^ 2) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨_hrange, hlo, hhi⟩
    exact Finset.mem_Icc.mpr ⟨hlo, by omega⟩
  have hinj : Set.InjOn (fun k => 4 * k + 1)
      (threeSlotSquareBlockTransitionCells R : Set ℕ) := by
    intro a _ha b _hb hab
    have hab' : 4 * a + 1 = 4 * b + 1 := hab
    omega
  have hcard :=
    Finset.card_le_card_of_injOn (fun k => 4 * k + 1) hmaps hinj
  have hIcc : (Finset.Icc (R ^ 2) ((R + 1) ^ 2)).card = 2 * R + 2 := by
    rw [Nat.card_Icc]
    have hexp : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    omega
  omega

/-- **Vacuity threshold.**  If the CRT period exceeds the square-block window,
no complete aligned period fits and the core is empty. -/
theorem physicalSquareCompleteCRTCells_eq_empty_of_period_gt
    (P : Finset ℕ) (R : ℕ) (h : 2 * R + 2 < finitePrimeCRTPeriod P) :
    physicalSquareCompleteCRTCells P R = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hsub := finitePrimeCRTOrbit_subset_squareBlock_of_mem_complete hk
  have hle := Finset.card_le_card hsub
  rw [card_finitePrimeCRTOrbit] at hle
  have hbound := card_threeSlotSquareBlockTransitionCells_le R
  omega

/-- Contrapositive: a nonempty complete-period core forces the CRT period below
the square-block window. -/
theorem finitePrimeCRTPeriod_le_of_complete_nonempty
    {P : Finset ℕ} {R : ℕ}
    (hne : (physicalSquareCompleteCRTCells P R).Nonempty) :
    finitePrimeCRTPeriod P ≤ 2 * R + 2 := by
  by_contra hcon
  have hempty :=
    physicalSquareCompleteCRTCells_eq_empty_of_period_gt P R (by omega)
  rw [hempty] at hne
  exact absurd hne (by simp)

/-- Above the threshold the CRT interior carries no mass at all. -/
theorem crtT_eq_zero_of_period_gt
    (P : Finset ℕ) (R : ℕ) (h : 2 * R + 2 < finitePrimeCRTPeriod P) :
    crtT P R = 0 := by
  unfold crtT
  rw [physicalSquareCompleteCRTCells_eq_empty_of_period_gt P R h]
  simp

/-- Above the threshold the exact partition degenerates: the whole physical mass
is the square-clock boundary. -/
theorem boundaryT_eq_physicalT_of_period_gt
    (P : Finset ℕ) (R : ℕ) (h : 2 * R + 2 < finitePrimeCRTPeriod P) :
    boundaryT P R = physicalT R := by
  have hpart := physicalTransport_is_crtTransport_add_boundary P R
  rw [crtT_eq_zero_of_period_gt P R h] at hpart
  omega

/-! ## Exact six-offset q-square transport -/

/-- Integer form of the selected degree-one observable. -/
def selectedDegreeOneProjectionInt (P : Finset ℕ) (k : ℕ) : ℤ :=
  selectedPrimeSign P (tActiveForm (0 : Fin 3) k) -
    selectedPrimeSign P (tActiveForm (1 : Fin 3) k) +
      selectedPrimeSign P (tActiveForm (2 : Fin 3) k)

@[simp] theorem selectedDegreeOneProjection_eq_intCast
    (P : Finset ℕ) (k : ℕ) :
    selectedDegreeOneProjection P k =
      ((selectedDegreeOneProjectionInt P k : ℤ) : ℝ) := by
  rfl

/-- Daughter integer produced by a q-square contact at physical offset `a`. -/
def qSquareOffsetDaughter (q a k : ℕ) : ℕ :=
  (4 * k + a) / (q * q)

/-- Source cell reconstructed from a tagged q-square daughter. -/
def qSquareOffsetSourceCell (q a d : ℕ) : ℕ :=
  (q * q * d - a) / 4

/-- On the contact locus the quotient is exact. -/
theorem qSquareOffsetDaughter_exact
    {q a k : ℕ} (hdiv : q * q ∣ 4 * k + a) :
    q * q * qSquareOffsetDaughter q a k = 4 * k + a := by
  unfold qSquareOffsetDaughter
  exact Nat.mul_div_cancel' hdiv

/-- The tagged affine substitution reconstructs the original physical cell. -/
theorem qSquareOffsetSourceCell_daughter
    {q a k : ℕ} (hdiv : q * q ∣ 4 * k + a) :
    qSquareOffsetSourceCell q a (qSquareOffsetDaughter q a k) = k := by
  have hexact := qSquareOffsetDaughter_exact hdiv
  unfold qSquareOffsetSourceCell
  have hsub :
      q * q * qSquareOffsetDaughter q a k - a = 4 * k := by
    omega
  rw [hsub]
  omega

/-- Membership in the six-offset union is equivalent to an actual q-square hit. -/
theorem mem_physicalSquareHitCells_iff
    {K q k : ℕ} (hq : q.Prime) :
    k ∈ physicalSquareHitCells K q ↔
      k < K ∧ physicalSquarePrimeAtEdge k q := by
  constructor
  · intro hk
    unfold physicalSquareHitCells at hk
    rcases Finset.mem_biUnion.mp hk with ⟨a, ha, hka⟩
    rcases Finset.mem_filter.mp hka with ⟨hkK, hdiv⟩
    refine ⟨Finset.mem_range.mp hkK, hq, a, ha, ?_⟩
    simpa [pow_two] using hdiv
  · rintro ⟨hkK, hhit⟩
    exact mem_physicalSquareHitCells_of_squarePrimeAtEdge hkK hhit

/-- If `q` is the least square-prime owner, no smaller prime can hit any of the
six physical offsets.  This is the exact earlier-square exclusion needed by the
complementary field. -/
theorem outsidePrimeLeastDeletionChannel_no_earlier_square
    {P O : Finset ℕ} {q k p : ℕ}
    (hk : k ∈ outsidePrimeLeastDeletionChannelCells P O q)
    (hpq : p < q) :
    ¬ physicalSquarePrimeAtEdge k p := by
  intro hpHit
  rcases Finset.mem_filter.mp hk with ⟨hkDel, howner⟩
  have hne := outsidePrimeDeletion_leastSquare_ne_none hkDel
  cases hleast : physicalLeastOddSquarePrime k with
  | none => exact (hne hleast).elim
  | some r =>
      have hrq : r = q := by
        simpa [hleast] using howner
      have hle : r ≤ p := physicalLeastOddSquarePrime_le hleast hpHit
      omega

/-- Every q-owned deleted cell supplies an actual tagged contact among the six
physical offsets. -/
theorem outsidePrimeLeastDeletionChannel_exists_offset
    {P O : Finset ℕ} {q k : ℕ}
    (hk : k ∈ outsidePrimeLeastDeletionChannelCells P O q) :
    ∃ a ∈ physicalTransitionActiveOffsets,
      q * q ∣ 4 * k + a := by
  rcases Finset.mem_filter.mp hk with ⟨hkDel, howner⟩
  have hne := outsidePrimeDeletion_leastSquare_ne_none hkDel
  cases hleast : physicalLeastOddSquarePrime k with
  | none => exact (hne hleast).elim
  | some r =>
      have hrq : r = q := by
        simpa [hleast] using howner
      subst r
      rcases physicalLeastOddSquarePrime_some_spec hleast with
        ⟨_hq, a, ha, hdiv⟩
      exact ⟨a, ha, by simpa [pow_two] using hdiv⟩

/-- The exact transported selected field attached to a tagged daughter.  The
source-cell pullback is the feature that a literal Go identification omits. -/
def selectedDegreeOneOffsetDaughterField
    (P : Finset ℕ) (q a d : ℕ) : ℤ :=
  selectedDegreeOneProjectionInt P (qSquareOffsetSourceCell q a d)

/-- On every contact, transporting the selected field to the daughter and then
pulling it back recovers the original physical weight exactly. -/
theorem selectedDegreeOneOffsetDaughterField_contact
    (P : Finset ℕ) {q a k : ℕ}
    (hdiv : q * q ∣ 4 * k + a) :
    selectedDegreeOneOffsetDaughterField P q a
        (qSquareOffsetDaughter q a k) =
      selectedDegreeOneProjectionInt P k := by
  rw [selectedDegreeOneOffsetDaughterField,
    qSquareOffsetSourceCell_daughter hdiv]

/-! ## Arbitrary tagged complementary fields retain the 11 contraction -/

/-- The prime-11 first-moment law survives arbitrary variation of the
complementary field across both physical contact tags and the six transition
coordinates.  This is the linear assembly needed for the actual six-offset
population: the complementary field need not be a rough Go daughter, and no
independence or constancy is assumed. -/
theorem eleven_coprimeTensor_taggedFirstMoment
    {α : Type*} [Fintype α]
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime 121 M)
    (c : α → Fin 6 → ℚ)
    (g : α → Fin 6 → ZMod M → ℚ) :
    (∑ a : α, ∑ i : Fin 6,
      c a i *
        (∑ z : ZMod (121 * M),
          elevenZeroFreeCoordinateMultiplierZMod i
              ((ZMod.chineseRemainder hcop) z).1 *
            g a i ((ZMod.chineseRemainder hcop) z).2)) =
      onePrimeWalshFactor 11 1 *
        (∑ a : α, ∑ i : Fin 6,
          c a i *
            (∑ z : ZMod (121 * M),
              elevenZeroFreeIndicatorZMod
                  ((ZMod.chineseRemainder hcop) z).1 *
                g a i ((ZMod.chineseRemainder hcop) z).2)) := by
  classical
  calc
    (∑ a : α, ∑ i : Fin 6,
      c a i *
        (∑ z : ZMod (121 * M),
          elevenZeroFreeCoordinateMultiplierZMod i
              ((ZMod.chineseRemainder hcop) z).1 *
            g a i ((ZMod.chineseRemainder hcop) z).2)) =
      ∑ a : α, ∑ i : Fin 6,
        c a i *
          (onePrimeWalshFactor 11 1 *
            (∑ z : ZMod (121 * M),
              elevenZeroFreeIndicatorZMod
                  ((ZMod.chineseRemainder hcop) z).1 *
                g a i ((ZMod.chineseRemainder hcop) z).2)) := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro i
      rw [eleven_coprimeTensor_firstMoment M hcop i (g a i)]
    _ = onePrimeWalshFactor 11 1 *
        (∑ a : α, ∑ i : Fin 6,
          c a i *
            (∑ z : ZMod (121 * M),
              elevenZeroFreeIndicatorZMod
                  ((ZMod.chineseRemainder hcop) z).1 *
                g a i ((ZMod.chineseRemainder hcop) z).2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- Squaring the tagged identity gives the common `(19/23)^2` energy factor for
an arbitrary finite assembly of contact fields. -/
theorem eleven_coprimeTensor_taggedFirstMoment_sq
    {α : Type*} [Fintype α]
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime 121 M)
    (c : α → Fin 6 → ℚ)
    (g : α → Fin 6 → ZMod M → ℚ) :
    (∑ a : α, ∑ i : Fin 6,
      c a i *
        (∑ z : ZMod (121 * M),
          elevenZeroFreeCoordinateMultiplierZMod i
              ((ZMod.chineseRemainder hcop) z).1 *
            g a i ((ZMod.chineseRemainder hcop) z).2)) ^ 2 =
      (onePrimeWalshFactor 11 1) ^ 2 *
        (∑ a : α, ∑ i : Fin 6,
          c a i *
            (∑ z : ZMod (121 * M),
              elevenZeroFreeIndicatorZMod
                  ((ZMod.chineseRemainder hcop) z).1 *
                g a i ((ZMod.chineseRemainder hcop) z).2)) ^ 2 := by
  rw [eleven_coprimeTensor_taggedFirstMoment M hcop c g]
  ring

/-! ## The q=3 complete-orbit obstruction to a literal Go daughter -/

/-- Computable six-offset `{11}`-selected q=3 contact population on one complete
period `4 * 3^2 * 11^2 = 4356`. -/
def elevenThreeCompleteSelectedDeletionCells : Finset ℕ :=
  (physicalSquareHitCells 4356 3).filter (tSquareZeroFreeAt 11)

/-- Its signed selected-prime degree-one mass, kept over `ℤ` so the complete
finite certificate is kernel-executable. -/
def elevenThreeCompleteSelectedDeletionMass : ℤ :=
  ∑ k ∈ elevenThreeCompleteSelectedDeletionCells,
    selectedDegreeOneProjectionInt ({11} : Finset ℕ) k

/-- The complete population has 2760 cells. -/
theorem elevenThreeCompleteSelectedDeletionCells_card :
    elevenThreeCompleteSelectedDeletionCells.card = 2760 := by
  native_decide

/-- **Finite counterexample to literal fixed-owner Go identification.** -/
theorem elevenThreeCompleteSelectedDeletionMass_eq_2280 :
    elevenThreeCompleteSelectedDeletionMass = 2280 := by
  native_decide

/-- The same complete population still carries the exact prime-11 weight-one
factor: `2280 / 2760 = 19 / 23`.  This separates the surviving spectral law from
the failed rough-daughter identification. -/
theorem elevenThreeCompleteSelectedDeletionMass_has_eleven_factor :
    (23 : ℤ) * elevenThreeCompleteSelectedDeletionMass =
      19 * (elevenThreeCompleteSelectedDeletionCells.card : ℤ) := by
  rw [elevenThreeCompleteSelectedDeletionMass_eq_2280,
    elevenThreeCompleteSelectedDeletionCells_card]
  norm_num

/-- The corresponding square-energy identity is exactly `(19/23)^2`. -/
theorem elevenThreeCompleteSelectedDeletionMass_has_eleven_energy_factor :
    (23 : ℤ) ^ 2 * elevenThreeCompleteSelectedDeletionMass ^ 2 =
      (19 : ℤ) ^ 2 *
        (elevenThreeCompleteSelectedDeletionCells.card : ℤ) ^ 2 := by
  rw [elevenThreeCompleteSelectedDeletionMass_eq_2280,
    elevenThreeCompleteSelectedDeletionCells_card]
  norm_num

/-- For q=3, a 3-square hit is automatically the least odd square-prime owner. -/
theorem physicalLeastOddSquarePrime_eq_some_three_iff (k : ℕ) :
    physicalLeastOddSquarePrime k = some 3 ↔
      physicalSquarePrimeAtEdge k 3 := by
  constructor
  · exact physicalLeastOddSquarePrime_some_spec
  · intro hthree
    have hne : physicalLeastOddSquarePrime k ≠ none := by
      intro hnone
      have hno := (physicalLeastOddSquarePrime_eq_none_iff k).mp hnone
      exact hno ⟨3, hthree⟩
    cases hleast : physicalLeastOddSquarePrime k with
    | none => exact (hne hleast).elim
    | some p =>
        have hpHit := physicalLeastOddSquarePrime_some_spec hleast
        have hpLe : p ≤ 3 := physicalLeastOddSquarePrime_le hleast hthree
        have hpPrime : p.Prime := hpHit.1
        have hpOdd : p % 2 = 1 := physicalSquarePrimeAtEdge_odd hpHit
        have hthreeLe : 3 ≤ p := by
          have hpTwo : 2 ≤ p := hpPrime.two_le
          omega
        have hp : p = 3 := by omega
        subst p
        rfl

/-- Exact q=3 selected deletion carrier at every prefix, including all of the
least-owner and actual-deletion conditions. -/
theorem outsidePrimeLeastDeletionChannelCells_eleven_three (K : ℕ) :
    outsidePrimeLeastDeletionChannelCells
        ({11} : Finset ℕ) (Finset.range K) 3 =
      (physicalSquareHitCells K 3).filter (tSquareZeroFreeAt 11) := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkDel, howner⟩
    rcases (mem_outsidePrimeDeletionCells_iff.mp hkDel) with
      ⟨hkRange, hselected, _hnotActual⟩
    have hne := outsidePrimeDeletion_leastSquare_ne_none hkDel
    cases hleast : physicalLeastOddSquarePrime k with
    | none => exact (hne hleast).elim
    | some p =>
        have hp3 : p = 3 := by
          simpa [hleast] using howner
        subst p
        have hhit : physicalSquarePrimeAtEdge k 3 :=
          physicalLeastOddSquarePrime_some_spec hleast
        apply Finset.mem_filter.mpr
        constructor
        · exact (mem_physicalSquareHitCells_iff (K := K)
            (q := 3) (k := k) (by norm_num)).2
              ⟨Finset.mem_range.mp hkRange, hhit⟩
        · simpa [outsidePrimeSelectedZeroFreeAt] using hselected
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkSquare, h11zero⟩
    rcases (mem_physicalSquareHitCells_iff (K := K)
        (q := 3) (k := k) (by norm_num)).1 hkSquare with
      ⟨hklt, hthree⟩
    have hleast : physicalLeastOddSquarePrime k = some 3 :=
      (physicalLeastOddSquarePrime_eq_some_three_iff k).2 hthree
    have hselected :
        outsidePrimeSelectedZeroFreeAt ({11} : Finset ℕ) k := by
      simpa [outsidePrimeSelectedZeroFreeAt] using h11zero
    have hnotActual : ¬ outsidePrimeActualZeroFreeAt k := by
      intro hactual
      have hedge :
          threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
            threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates := by
        exact ⟨
          (isThreeSlotNonzeroState_iff_mem_physicalThreeSlotNonzeroStates _).mp
            hactual.1,
          (isThreeSlotNonzeroState_iff_mem_physicalThreeSlotNonzeroStates _).mp
            hactual.2⟩
      have hnone : physicalLeastOddSquarePrime k = none :=
        (physicalLeastOddSquarePrime_eq_none_iff_nonzeroEdge k).2 hedge
      rw [hleast] at hnone
      simp at hnone
    apply Finset.mem_filter.mpr
    constructor
    · exact mem_outsidePrimeDeletionCells_iff.mpr
        ⟨Finset.mem_range.mpr hklt, hselected, hnotActual⟩
    · simp [hleast]

/-- The complete-period certificate is an instance of the exact prefix carrier. -/
theorem outsidePrimeLeastDeletionChannelCells_eleven_three_4356 :
    outsidePrimeLeastDeletionChannelCells
        ({11} : Finset ℕ) (Finset.range 4356) 3 =
      elevenThreeCompleteSelectedDeletionCells := by
  exact outsidePrimeLeastDeletionChannelCells_eleven_three 4356

/-- The ordinary q=3 rough daughter at cutoff 2 is `mu(1)+mu(2)=0`. -/
theorem roughCofactorMobiusPrefixMass_three_two_eq_zero :
    RHLean.Proof.roughCofactorMobiusPrefixMass 3 2 = 0 := by
  rw [RHLean.Proof.roughCofactorMobiusPrefixMass_eq_cofactorMobiusPrefixMass
    (by norm_num : 2 < 3)]
  unfold RHLean.Proof.cofactorMobiusPrefixMass
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
    native_decide
  rw [hIcc]
  simp [RHLean.Proof.canonicalMoebiusWeight,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- Consequently the actual q=3 selected-sign source cannot be identified with
that plain rough daughter, even on a complete least-owner super-period. -/
theorem elevenThree_selectedMass_ne_plainRoughDaughter :
    ((elevenThreeCompleteSelectedDeletionMass : ℤ) : ℂ) ≠
      RHLean.Proof.roughCofactorMobiusPrefixMass 3 2 := by
  rw [elevenThreeCompleteSelectedDeletionMass_eq_2280,
    roughCofactorMobiusPrefixMass_three_two_eq_zero]
  norm_num

end RHLean.Analysis
