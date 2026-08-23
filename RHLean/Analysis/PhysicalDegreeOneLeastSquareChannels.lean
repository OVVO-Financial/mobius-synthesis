import Mathlib
import RHLean.Analysis.PhysicalDegreeOneTransitionEstimate

/-!
# Physical degree-one least-square channels

This is a proof-side decomposition of the structured physical transition defect.
Each adjacent three-slot edge has six active sites

`4k+1, 4k+2, 4k+3, 4k+5, 4k+6, 4k+7`.

If one of those sites has a square prime divisor, `physicalLeastOddSquarePrime`
records the least such prime.  It is an `Option` because an all-squarefree edge
has no square channel.  The active geometry excludes the prime `2`, so every
returned prime is automatically odd.

The defect is partitioned exactly into disjoint least-square channels.  The
first channel, `p = 3`, is identified with the six residue classes
`k mod 9 = 1,...,6` and its exact nine-edge recurrence is pushed back to a
short Mertens increment.  No estimate or cancellation hypothesis is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The six active sites on the physical edge from cell `k` to cell `k+1`. -/
def physicalTransitionActiveOffsets : Finset ℕ :=
  {1, 2, 3, 5, 6, 7}

/-- A prime whose square divides at least one of the six active sites of edge `k`. -/
def physicalSquarePrimeAtEdge (k p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∃ a ∈ physicalTransitionActiveOffsets, p * p ∣ 4 * k + a

/-- The least square-prime channel of edge `k`, or `none` when all six active
sites are squarefree. -/
noncomputable def physicalLeastOddSquarePrime (k : ℕ) : Option ℕ := by
  classical
  exact if h : ∃ p, physicalSquarePrimeAtEdge k p then
    some (Nat.find h)
  else
    none

/-- The degree-one observable on the destination cell of edge `k`. -/
def physicalDefectEdgeValue (k : ℕ) : ℤ :=
  threeSlotDegreeOneValue (threeSlotState (k + 1))

/-- The signed least-square channel `D_{p^2}(K)`. -/
def physicalLeastSquareChannel (K p : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K with physicalLeastOddSquarePrime k = some p,
    physicalDefectEdgeValue k

/-- The finite set of least square primes that actually occur among the first
`K` physical edges. -/
def physicalLeastSquarePrimes (K : ℕ) : Finset ℕ :=
  ((Finset.range K).filter fun k => physicalLeastOddSquarePrime k ≠ none).image
    (fun k => (physicalLeastOddSquarePrime k).getD 0)

/-- The `3^2` least-square channel. -/
def physicalD9 (K : ℕ) : ℤ :=
  physicalLeastSquareChannel K 3

/-- The six edge residues carrying a forced `3^2` hit. -/
def physicalNineChannelResidues : Finset ℕ :=
  {1, 2, 3, 4, 5, 6}

private theorem physicalActiveOffset_not_four_dvd
    (k a : ℕ) (ha : a ∈ physicalTransitionActiveOffsets) :
    ¬ 4 ∣ 4 * k + a := by
  intro h
  rw [Nat.dvd_iff_mod_eq_zero] at h
  simp [physicalTransitionActiveOffsets] at ha
  omega

/-- Every prime-square hit in the six active sites is odd. -/
theorem physicalSquarePrimeAtEdge_odd
    {k p : ℕ} (h : physicalSquarePrimeAtEdge k p) : p % 2 = 1 := by
  rcases h with ⟨hp, a, ha, hsq⟩
  have hpne : p ≠ 2 := by
    intro htwo
    subst p
    norm_num at hsq
    exact physicalActiveOffset_not_four_dvd k a ha hsq
  exact hp.mod_two_eq_one_iff_ne_two.mpr hpne

private theorem physicalSquarePrimeAtEdge_three_le
    {k p : ℕ} (h : physicalSquarePrimeAtEdge k p) : 3 ≤ p := by
  have hp2 := h.1.two_le
  have hodd := physicalSquarePrimeAtEdge_odd h
  omega

/-- A returned least channel is an actual square-prime hit. -/
theorem physicalLeastOddSquarePrime_some_spec
    {k p : ℕ} (h : physicalLeastOddSquarePrime k = some p) :
    physicalSquarePrimeAtEdge k p := by
  classical
  by_cases hex : ∃ q, physicalSquarePrimeAtEdge k q
  · have hfind : Nat.find hex = p := by
      simpa [physicalLeastOddSquarePrime, hex] using h
    rw [← hfind]
    exact Nat.find_spec hex
  · simp [physicalLeastOddSquarePrime, hex] at h

/-- A returned least channel is no larger than any other square-prime hit. -/
theorem physicalLeastOddSquarePrime_le
    {k p q : ℕ}
    (hp : physicalLeastOddSquarePrime k = some p)
    (hq : physicalSquarePrimeAtEdge k q) : p ≤ q := by
  classical
  have hex : ∃ r, physicalSquarePrimeAtEdge k r := ⟨q, hq⟩
  have hfind : Nat.find hex = p := by
    simpa [physicalLeastOddSquarePrime, hex] using hp
  rw [← hfind]
  exact Nat.find_min' hex hq

theorem physicalLeastOddSquarePrime_eq_none_iff (k : ℕ) :
    physicalLeastOddSquarePrime k = none ↔
      ¬ ∃ p, physicalSquarePrimeAtEdge k p := by
  classical
  by_cases hex : ∃ p, physicalSquarePrimeAtEdge k p <;>
    simp [physicalLeastOddSquarePrime, hex]

private theorem no_physicalSquarePrimeAtEdge_iff_squarefree
    (k : ℕ) :
    (¬ ∃ p, physicalSquarePrimeAtEdge k p) ↔
      ∀ a ∈ physicalTransitionActiveOffsets, Squarefree (4 * k + a) := by
  constructor
  · intro h a ha
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hsq
    exact h ⟨p, hp, a, ha, hsq⟩
  · intro h hex
    rcases hex with ⟨p, hp, a, ha, hsq⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp (h a ha) p hp) hsq

private theorem tritSign_ne_zero_iff_val_ne_one (t : Fin 3) :
    tritSign t ≠ 0 ↔ t.1 ≠ 1 := by
  unfold tritSign
  omega

private theorem encodeThreeTrits_mem_physicalNonzero_iff
    (a b c : Fin 3) :
    encodeThreeTrits a b c ∈ physicalThreeSlotNonzeroStates ↔
      tritSign a ≠ 0 ∧ tritSign b ≠ 0 ∧ tritSign c ≠ 0 := by
  simp only [tritSign_ne_zero_iff_val_ne_one]
  simp only [physicalThreeSlotNonzeroStates, Finset.mem_insert,
    Finset.mem_singleton, Fin.ext_iff, encodeThreeTrits]
  omega

private theorem threeSlotState_mem_physicalNonzero_iff
    (k : ℕ) :
    threeSlotState k ∈ physicalThreeSlotNonzeroStates ↔
      μ (4 * k + 1) ≠ 0 ∧ μ (4 * k + 2) ≠ 0 ∧ μ (4 * k + 3) ≠ 0 := by
  unfold threeSlotState
  rw [encodeThreeTrits_mem_physicalNonzero_iff]
  simp

private theorem physicalNonzeroEdge_iff_activeSquarefree
    (k : ℕ) :
    (threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
        threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates) ↔
      ∀ a ∈ physicalTransitionActiveOffsets, Squarefree (4 * k + a) := by
  rw [threeSlotState_mem_physicalNonzero_iff,
    threeSlotState_mem_physicalNonzero_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, ⟨h5, h6, h7⟩⟩
    have hs1 : Squarefree (4 * k + 1) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h1
    have hs2 : Squarefree (4 * k + 2) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h2
    have hs3 : Squarefree (4 * k + 3) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h3
    have hs5 : Squarefree (4 * k + 5) := by
      rw [← show 4 * (k + 1) + 1 = 4 * k + 5 by omega]
      exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h5
    have hs6 : Squarefree (4 * k + 6) := by
      rw [← show 4 * (k + 1) + 2 = 4 * k + 6 by omega]
      exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h6
    have hs7 : Squarefree (4 * k + 7) := by
      rw [← show 4 * (k + 1) + 3 = 4 * k + 7 by omega]
      exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h7
    intro a ha
    simp [physicalTransitionActiveOffsets] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs1
    · exact hs2
    · exact hs3
    · exact hs5
    · exact hs6
    · exact hs7
  · intro h
    have hs1 := h 1 (by simp [physicalTransitionActiveOffsets])
    have hs2 := h 2 (by simp [physicalTransitionActiveOffsets])
    have hs3 := h 3 (by simp [physicalTransitionActiveOffsets])
    have hs5 := h 5 (by simp [physicalTransitionActiveOffsets])
    have hs6 := h 6 (by simp [physicalTransitionActiveOffsets])
    have hs7 := h 7 (by simp [physicalTransitionActiveOffsets])
    have h1 : μ (4 * k + 1) ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs1
    have h2 : μ (4 * k + 2) ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs2
    have h3 : μ (4 * k + 3) ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs3
    have h5 : μ (4 * (k + 1) + 1) ≠ 0 := by
      rw [show 4 * (k + 1) + 1 = 4 * k + 5 by omega]
      exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs5
    have h6 : μ (4 * (k + 1) + 2) ≠ 0 := by
      rw [show 4 * (k + 1) + 2 = 4 * k + 6 by omega]
      exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs6
    have h7 : μ (4 * (k + 1) + 3) ≠ 0 := by
      rw [show 4 * (k + 1) + 3 = 4 * k + 7 by omega]
      exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs7
    exact ⟨⟨h1, h2, h3⟩, ⟨h5, h6, h7⟩⟩

/-- `none` is exactly the all-squarefree physical edge, i.e. both endpoints
lie in the eight-state sign sector. -/
theorem physicalLeastOddSquarePrime_eq_none_iff_nonzeroEdge
    (k : ℕ) :
    physicalLeastOddSquarePrime k = none ↔
      threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
        threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates := by
  rw [physicalLeastOddSquarePrime_eq_none_iff]
  exact (no_physicalSquarePrimeAtEdge_iff_squarefree k).trans
    (physicalNonzeroEdge_iff_activeSquarefree k).symm

private theorem threeSlotTransitionMomentOn_eq_nonzeroDestinationSum
    (F : Finset ℕ) (s : Fin 27) (χ : Fin 27 → ℤ) :
    threeSlotTransitionMomentOn F s χ =
      ∑ k ∈ F with
        threeSlotState k = s ∧
          threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates,
        χ (threeSlotState (k + 1)) := by
  classical
  let E : Finset ℕ := F.filter fun k =>
    threeSlotState k = s ∧
      threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates
  have hmaps : ∀ k ∈ E,
      threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2.2
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    (s := E)
    (t := physicalThreeSlotNonzeroStates)
    (g := fun k => threeSlotState (k + 1))
    hmaps χ
  have hcount : ∀ t ∈ physicalThreeSlotNonzeroStates,
      (∑ k ∈ E with threeSlotState (k + 1) = t, χ t) =
        (threeSlotTransitionCountOn F s t : ℤ) * χ t := by
    intro t ht
    have hcard :
        ((E.filter fun k => threeSlotState (k + 1) = t).card) =
          threeSlotTransitionCountOn F s t := by
      unfold threeSlotTransitionCountOn
      apply congrArg Finset.card
      ext k
      simp only [E, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hkF, hsrc, hdestA⟩, hdest⟩
        exact ⟨hkF, hsrc, hdest⟩
      · rintro ⟨hkF, hsrc, hdest⟩
        refine ⟨⟨hkF, hsrc, ?_⟩, hdest⟩
        rw [hdest]
        exact ht
    simp [hcard]
  calc
    threeSlotTransitionMomentOn F s χ =
        ∑ t ∈ physicalThreeSlotNonzeroStates,
          (threeSlotTransitionCountOn F s t : ℤ) * χ t := by
            simp [threeSlotTransitionMomentOn,
              physicalThreeSlotNonzeroStates]
            ring
    _ = ∑ t ∈ physicalThreeSlotNonzeroStates,
          ∑ k ∈ E with threeSlotState (k + 1) = t, χ t := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [hcount t ht]
    _ = ∑ k ∈ E, χ (threeSlotState (k + 1)) := hfiber
    _ = ∑ k ∈ F with
        threeSlotState k = s ∧
          threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates,
        χ (threeSlotState (k + 1)) := by rfl

/-- The conditioned transition mass is literally the destination degree-one sum
on edges whose two endpoints are both in the nonzero sign sector. -/
theorem physicalDegreeOneT_eq_nonzeroEdgeSum (K : ℕ) :
    physicalDegreeOneT K =
      ∑ k ∈ Finset.range K with
        threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
          threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates,
        physicalDefectEdgeValue k := by
  classical
  let E : Finset ℕ := (Finset.range K).filter fun k =>
    threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
      threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates
  have hmaps : ∀ k ∈ E, threeSlotState k ∈ physicalThreeSlotNonzeroStates := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2.1
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := E)
    (t := physicalThreeSlotNonzeroStates)
    (g := threeSlotState)
    hmaps physicalDefectEdgeValue
  have hrow : ∀ s ∈ physicalThreeSlotNonzeroStates,
      (∑ k ∈ E with threeSlotState k = s, physicalDefectEdgeValue k) =
        threeSlotTransitionMomentOn
          (Finset.range K) s threeSlotDegreeOneValue := by
    intro s hs
    rw [threeSlotTransitionMomentOn_eq_nonzeroDestinationSum]
    apply Finset.sum_congr
    · ext k
      simp only [E, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨hk, hsrcA, hdestA⟩, hsrc⟩
        exact ⟨hk, hsrc, hdestA⟩
      · rintro ⟨hk, hsrc, hdestA⟩
        refine ⟨⟨hk, ?_, hdestA⟩, hsrc⟩
        rw [hsrc]
        exact hs
    · intro k hk
      rfl
  calc
    physicalDegreeOneT K =
        ∑ s ∈ physicalThreeSlotNonzeroStates,
          threeSlotTransitionMomentOn
            (Finset.range K) s threeSlotDegreeOneValue := by
              simp [physicalDegreeOneT, threeSlotTransitionDegreeOneMass,
                physicalThreeSlotNonzeroStates]
              ring
    _ = ∑ s ∈ physicalThreeSlotNonzeroStates,
          ∑ k ∈ E with threeSlotState k = s, physicalDefectEdgeValue k := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [hrow s hs]
    _ = ∑ k ∈ E, physicalDefectEdgeValue k := hfiber
    _ = ∑ k ∈ Finset.range K with
        threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
          threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates,
        physicalDefectEdgeValue k := by rfl

/-- The conditioned transition mass is the sum over precisely the edges with no
least square-prime channel. -/
theorem physicalDegreeOneT_eq_leastSquareNoneSum (K : ℕ) :
    physicalDegreeOneT K =
      ∑ k ∈ Finset.range K with physicalLeastOddSquarePrime k = none,
        physicalDefectEdgeValue k := by
  rw [physicalDegreeOneT_eq_nonzeroEdgeSum]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [physicalLeastOddSquarePrime_eq_none_iff_nonzeroEdge]
  · intro k hk
    rfl

/-- The defect is literally the signed destination sum on the square-supported
edges.  No absolute-value splitting has occurred. -/
theorem physicalTransitionD_eq_leastSquareSupportedSum (K : ℕ) :
    physicalTransitionD K =
      ∑ k ∈ Finset.range K with physicalLeastOddSquarePrime k ≠ none,
        physicalDefectEdgeValue k := by
  change
    (∑ k ∈ Finset.range K, physicalDefectEdgeValue k) -
        physicalDegreeOneT K = _
  rw [physicalDegreeOneT_eq_leastSquareNoneSum]
  have hpart := Finset.sum_filter_add_sum_filter_not
    (Finset.range K)
    (fun k => physicalLeastOddSquarePrime k = none)
    physicalDefectEdgeValue
  rw [← hpart]
  ring

/-- Every index appearing in the finite channel set is an odd prime. -/
theorem physicalLeastSquarePrime_mem_spec
    {K p : ℕ} (hp : p ∈ physicalLeastSquarePrimes K) :
    Nat.Prime p ∧ p % 2 = 1 := by
  classical
  rw [physicalLeastSquarePrimes, Finset.mem_image] at hp
  rcases hp with ⟨k, hk, rfl⟩
  have hne : physicalLeastOddSquarePrime k ≠ none :=
    (Finset.mem_filter.mp hk).2
  cases hleast : physicalLeastOddSquarePrime k with
  | none => exact (hne hleast).elim
  | some q =>
      have hspec := physicalLeastOddSquarePrime_some_spec hleast
      simpa [hleast] using
        (show Nat.Prime q ∧ q % 2 = 1 from
          ⟨hspec.1, physicalSquarePrimeAtEdge_odd hspec⟩)

/-- **Exact disjoint channel decomposition.**  The finite index set consists
only of odd primes and each defect-supported edge enters exactly one least
square-prime channel. -/
theorem physicalTransitionD_eq_sum_leastSquareChannels (K : ℕ) :
    physicalTransitionD K =
      ∑ p ∈ physicalLeastSquarePrimes K, physicalLeastSquareChannel K p := by
  classical
  let E : Finset ℕ :=
    (Finset.range K).filter fun k => physicalLeastOddSquarePrime k ≠ none
  let q : ℕ → ℕ := fun k => (physicalLeastOddSquarePrime k).getD 0
  have hmaps : ∀ k ∈ E, q k ∈ physicalLeastSquarePrimes K := by
    intro k hk
    rw [physicalLeastSquarePrimes, Finset.mem_image]
    exact ⟨k, hk, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := E)
    (t := physicalLeastSquarePrimes K)
    (g := q)
    hmaps physicalDefectEdgeValue
  have hchannel : ∀ p ∈ physicalLeastSquarePrimes K,
      (∑ k ∈ E with q k = p, physicalDefectEdgeValue k) =
        physicalLeastSquareChannel K p := by
    intro p hp
    unfold physicalLeastSquareChannel
    apply Finset.sum_congr
    · ext k
      simp only [E, q, Finset.mem_filter, Finset.mem_range]
      cases hleast : physicalLeastOddSquarePrime k <;> simp
    · intro k hk
      rfl
  rw [physicalTransitionD_eq_leastSquareSupportedSum]
  change (∑ k ∈ E, physicalDefectEdgeValue k) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro p hp
  exact hchannel p hp

/-- A `3^2` hit occurs exactly on the six forced residues modulo `9`. -/
theorem physicalSquarePrimeAtEdge_three_iff (k : ℕ) :
    physicalSquarePrimeAtEdge k 3 ↔
      k % 9 ∈ physicalNineChannelResidues := by
  constructor
  · rintro ⟨_, a, ha, hdiv⟩
    norm_num at hdiv
    simp [physicalTransitionActiveOffsets] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [Nat.dvd_iff_mod_eq_zero] at hdiv
      simp [Nat.add_mod, Nat.mul_mod] at hdiv
      simp [physicalNineChannelResidues]
      omega
  · intro hk
    simp [physicalNineChannelResidues] at hk
    rcases hk with h1 | h2 | h3 | h4 | h5 | h6
    · refine ⟨by norm_num, 5, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h1]
    · refine ⟨by norm_num, 1, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h2]
    · refine ⟨by norm_num, 6, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h3]
    · refine ⟨by norm_num, 2, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h4]
    · refine ⟨by norm_num, 7, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h5]
    · refine ⟨by norm_num, 3, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h6]

/-- Because every square-prime channel is at least `3`, a `3^2` hit is
automatically the least channel. -/
theorem physicalLeastOddSquarePrime_eq_three_iff (k : ℕ) :
    physicalLeastOddSquarePrime k = some 3 ↔
      physicalSquarePrimeAtEdge k 3 := by
  constructor
  · exact physicalLeastOddSquarePrime_some_spec
  · intro h3
    classical
    have hex : ∃ p, physicalSquarePrimeAtEdge k p := ⟨3, h3⟩
    have hle : Nat.find hex ≤ 3 := Nat.find_min' hex h3
    have hge : 3 ≤ Nat.find hex :=
      physicalSquarePrimeAtEdge_three_le (Nat.find_spec hex)
    have heq : Nat.find hex = 3 := le_antisymm hle hge
    simp [physicalLeastOddSquarePrime, hex, heq]

theorem physicalLeastOddSquarePrime_eq_three_iff_mod (k : ℕ) :
    physicalLeastOddSquarePrime k = some 3 ↔
      k % 9 ∈ physicalNineChannelResidues := by
  rw [physicalLeastOddSquarePrime_eq_three_iff,
    physicalSquarePrimeAtEdge_three_iff]

/-- Exact residue-class form of the `3^2` channel. -/
theorem physicalD9_eq_residueSum (K : ℕ) :
    physicalD9 K =
      ∑ k ∈ Finset.range K with k % 9 ∈ physicalNineChannelResidues,
        physicalDefectEdgeValue k := by
  unfold physicalD9 physicalLeastSquareChannel
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [physicalLeastOddSquarePrime_eq_three_iff_mod]
  · intro k hk
    rfl

/-- The destination degree-one cell observable is the ordinary four-slot cell
sum, since the fourth site is killed by `2^2`. -/
theorem physicalDefectEdgeValue_eq_fourSlotCellSum (k : ℕ) :
    physicalDefectEdgeValue k = fourSlotCellSum (k + 1) := by
  simp [physicalDefectEdgeValue, threeSlotDegreeOneValue_threeSlotState,
    fourSlotCellSum, moebius_four_mul_add_four]

/-- **Exact `3^2` recurrence.**  One complete nine-edge period of the least
`3^2` channel is exactly the Mertens increment over the corresponding six
four-cells. -/
theorem physicalD9_nine_step_recurrence (L : ℕ) :
    physicalD9 (9 * (L + 1)) - physicalD9 (9 * L) =
      moebiusPositivePrefix (36 * L + 32) -
        moebiusPositivePrefix (36 * L + 8) := by
  let f : ℕ → ℤ := fun k =>
    if k % 9 ∈ physicalNineChannelResidues then
      fourSlotCellSum (k + 1)
    else 0
  have hD9 : ∀ N : ℕ, physicalD9 N = ∑ k ∈ Finset.range N, f k := by
    intro N
    rw [physicalD9_eq_residueSum]
    simp [f, physicalDefectEdgeValue_eq_fourSlotCellSum, Finset.sum_filter]
  rw [hD9, hD9]
  have hblock :
      (∑ k ∈ Finset.range (9 * (L + 1)), f k) =
        (∑ k ∈ Finset.range (9 * L), f k) +
          f (9 * L) + f (9 * L + 1) + f (9 * L + 2) +
          f (9 * L + 3) + f (9 * L + 4) + f (9 * L + 5) +
          f (9 * L + 6) + f (9 * L + 7) + f (9 * L + 8) := by
    rw [show 9 * (L + 1) = 9 * L + 9 by omega]
    rw [show 9 * L + 9 = (9 * L + 8) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 8 = (9 * L + 7) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 7 = (9 * L + 6) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 6 = (9 * L + 5) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 5 = (9 * L + 4) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 4 = (9 * L + 3) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 3 = (9 * L + 2) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 2 = (9 * L + 1) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 1 = (9 * L) + 1 by omega,
      Finset.sum_range_succ]
  have hf0 : f (9 * L) = 0 := by
    simp [f, physicalNineChannelResidues]
  have hf1 : f (9 * L + 1) = fourSlotCellSum (9 * L + 2) := by
    simp [f, physicalNineChannelResidues, Nat.add_mod]
  have hf2 : f (9 * L + 2) = fourSlotCellSum (9 * L + 3) := by
    simp [f, physicalNineChannelResidues, Nat.add_mod]
  have hf3 : f (9 * L + 3) = fourSlotCellSum (9 * L + 4) := by
    simp [f, physicalNineChannelResidues, Nat.add_mod]
  have hf4 : f (9 * L + 4) = fourSlotCellSum (9 * L + 5) := by
    simp [f, physicalNineChannelResidues, Nat.add_mod]
  have hf5 : f (9 * L + 5) = fourSlotCellSum (9 * L + 6) := by
    simp [f, physicalNineChannelResidues, Nat.add_mod]
  have hf6 : f (9 * L + 6) = fourSlotCellSum (9 * L + 7) := by
    simp [f, physicalNineChannelResidues, Nat.add_mod]
  have hf7 : f (9 * L + 7) = 0 := by
    simp [f, physicalNineChannelResidues, Nat.add_mod]
  have hf8 : f (9 * L + 8) = 0 := by
    simp [f, physicalNineChannelResidues, Nat.add_mod]
  have hprefix :
      (∑ k ∈ Finset.range (9 * L + 8), fourSlotCellSum k) =
        (∑ k ∈ Finset.range (9 * L + 2), fourSlotCellSum k) +
          fourSlotCellSum (9 * L + 2) +
          fourSlotCellSum (9 * L + 3) +
          fourSlotCellSum (9 * L + 4) +
          fourSlotCellSum (9 * L + 5) +
          fourSlotCellSum (9 * L + 6) +
          fourSlotCellSum (9 * L + 7) := by
    rw [show 9 * L + 8 = (9 * L + 7) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 7 = (9 * L + 6) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 6 = (9 * L + 5) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 5 = (9 * L + 4) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 4 = (9 * L + 3) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 3 = (9 * L + 2) + 1 by omega,
      Finset.sum_range_succ]
  calc
    (∑ k ∈ Finset.range (9 * (L + 1)), f k) -
          ∑ k ∈ Finset.range (9 * L), f k =
        f (9 * L) + f (9 * L + 1) + f (9 * L + 2) +
          f (9 * L + 3) + f (9 * L + 4) + f (9 * L + 5) +
          f (9 * L + 6) + f (9 * L + 7) + f (9 * L + 8) := by
            rw [hblock]
            abel
    _ = fourSlotCellSum (9 * L + 2) +
          fourSlotCellSum (9 * L + 3) +
          fourSlotCellSum (9 * L + 4) +
          fourSlotCellSum (9 * L + 5) +
          fourSlotCellSum (9 * L + 6) +
          fourSlotCellSum (9 * L + 7) := by
            rw [hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]
            abel
    _ = moebiusPositivePrefix (36 * L + 32) -
          moebiusPositivePrefix (36 * L + 8) := by
            rw [show 36 * L + 32 = 4 * (9 * L + 8) by ring,
              show 36 * L + 8 = 4 * (9 * L + 2) by ring]
            rw [moebiusPositivePrefix_four_mul_eq_fourSlotCellSum,
              moebiusPositivePrefix_four_mul_eq_fourSlotCellSum]
            rw [hprefix]
            abel

end RHLean.Analysis
