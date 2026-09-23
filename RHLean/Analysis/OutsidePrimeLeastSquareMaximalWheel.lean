import Mathlib
import RHLean.Analysis.OutsidePrimeLeastSquareBlocker

/-!
# Finite maximal-wheel blocker for generic least-square owners

The least-owner super-orbit for `q` contains the selected prime set, every prime
strictly below `q`, and `q` itself.  This makes the growing wheel useful as a
geometric blocker: once the product of the reserved small squares, the selected
squares and `q^2` exceeds one square block, `q` cannot occur in the complete
least-owner interior.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- The small prime-square coordinates reserved outside the generic selected
wheel. -/
def outsidePrimeReservedBlockerPrimes : Finset ℕ := {2, 3, 5, 7}

@[simp] theorem outsidePrimeReservedBlockerPrimes_prod_sq :
    (∏ p ∈ outsidePrimeReservedBlockerPrimes, p ^ 2) = 210 ^ 2 := by
  native_decide

/-- A selected generic wheel contains only primes at least `11`. -/
def IsSelectedGenericBlockerWheel (P : Finset ℕ) : Prop :=
  ∀ p ∈ P, p.Prime ∧ 11 ≤ p

/-- Reserved primes are all decided before any generic owner. -/
theorem outsidePrimeReservedBlockerPrimes_subset_earlier
    {q : ℕ} (hq : 11 ≤ q) :
    outsidePrimeReservedBlockerPrimes ⊆ outsidePrimeEarlierPrimes q := by
  intro p hp
  have hpCases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    simpa [outsidePrimeReservedBlockerPrimes] using hp
  rcases hpCases with rfl | rfl | rfl | rfl
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by norm_num⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by norm_num⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by norm_num⟩

/-- A finite seed whose square-product is the reserved `210^2` factor, the
selected generic wheel, and the current outside owner. -/
def outsidePrimeBlockerSeed (P : Finset ℕ) (q : ℕ) : Finset ℕ :=
  insert q (outsidePrimeReservedBlockerPrimes ∪ P)

/-- The blocker seed is contained in the actual least-owner super-prime set. -/
theorem outsidePrimeBlockerSeed_subset_super
    {P : Finset ℕ} {q : ℕ} (hq : 11 ≤ q) :
    outsidePrimeBlockerSeed P q ⊆ outsidePrimeLeastSuperPrimeSet P q := by
  intro p hp
  rw [outsidePrimeBlockerSeed, Finset.mem_insert] at hp
  unfold outsidePrimeLeastSuperPrimeSet outsidePrimeLeastStagePrimes
  rcases hp with hpq | hp
  · subst p
    exact Finset.mem_insert_self _ _
  · rw [Finset.mem_union] at hp
    apply Finset.mem_insert_of_mem
    rcases hp with hpSmall | hpP
    · apply Finset.mem_union_right
      exact outsidePrimeReservedBlockerPrimes_subset_earlier hq hpSmall
    · exact Finset.mem_union_left _ hpP

/-- Every coordinate in a least-owner super-prime set is prime, provided the
selected wheel and the owner are prime. -/
theorem outsidePrimeLeastSuperPrimeSet_prime
    {P : Finset ℕ} {q r : ℕ}
    (hP : IsSelectedGenericBlockerWheel P) (hq : q.Prime)
    (hr : r ∈ outsidePrimeLeastSuperPrimeSet P q) : r.Prime := by
  unfold outsidePrimeLeastSuperPrimeSet outsidePrimeLeastStagePrimes at hr
  rcases Finset.mem_insert.mp hr with hrq | hr
  · simpa [hrq] using hq
  · rcases Finset.mem_union.mp hr with hrP | hrEarlier
    · exact (hP r hrP).1
    · exact (Finset.mem_filter.mp hrEarlier).2

/-- The blocker seed has exactly the expected square product. -/
theorem outsidePrimeBlockerSeed_prod_sq
    {P : Finset ℕ} {q : ℕ}
    (hP : IsSelectedGenericBlockerWheel P)
    (hq11 : 11 ≤ q) (hqP : q ∉ P) :
    (∏ p ∈ outsidePrimeBlockerSeed P q, p ^ 2) =
      210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2 := by
  have hdis : Disjoint outsidePrimeReservedBlockerPrimes P := by
    apply Finset.disjoint_left.mpr
    intro p hpSmall hpP
    have hp11 := (hP p hpP).2
    simp [outsidePrimeReservedBlockerPrimes] at hpSmall
    omega
  have hqSmall : q ∉ outsidePrimeReservedBlockerPrimes := by
    simp [outsidePrimeReservedBlockerPrimes]
    omega
  have hqUnion : q ∉ outsidePrimeReservedBlockerPrimes ∪ P := by
    simp [hqSmall, hqP]
  unfold outsidePrimeBlockerSeed
  rw [Finset.prod_insert hqUnion, Finset.prod_union hdis]
  rw [outsidePrimeReservedBlockerPrimes_prod_sq]
  ring

/-- **Exact period lower bound.**  The genuine least-owner super-orbit period
contains the reserved small-prime squares, every selected generic square, and
`q^2`. -/
theorem outsidePrimeLeastSuperPeriod_ge_blocker
    {P : Finset ℕ} {q : ℕ}
    (hP : IsSelectedGenericBlockerWheel P)
    (hq : q.Prime) (hq11 : 11 ≤ q) (hqP : q ∉ P) :
    210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2 ≤
      finitePrimeCRTPeriod (outsidePrimeLeastSuperPrimeSet P q) := by
  have hsub := outsidePrimeBlockerSeed_subset_super (P := P) hq11
  have hprod :
      (∏ p ∈ outsidePrimeBlockerSeed P q, p ^ 2) ≤
        ∏ p ∈ outsidePrimeLeastSuperPrimeSet P q, p ^ 2 := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub (by
      intro p hpSuper _hpSeed
      have hpPrime := outsidePrimeLeastSuperPrimeSet_prime hP hq hpSuper
      nlinarith [hpPrime.two_le])
  rw [outsidePrimeBlockerSeed_prod_sq hP hq11 hqP] at hprod
  unfold finitePrimeCRTPeriod
  exact hprod.trans (le_max_right _ _)

/-- **Generic complete-owner blocker.**  Any generic owner outside the selected
wheel whose reserved/selected/owner square product exceeds the square block is
forced out of the complete interior. -/
theorem outsidePrimeLeastComplete_no_generic_owner_of_blocker
    {P : Finset ℕ} {R q k : ℕ}
    (hP : IsSelectedGenericBlockerWheel P)
    (hq : q.Prime) (hq11 : 11 ≤ q) (hqP : q ∉ P)
    (hlarge : 2 * R + 2 <
      210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2)
    (hk : k ∈ squareBlockOutsidePrimeLeastCompleteCells P R) :
    physicalLeastOddSquarePrime k ≠ some q := by
  apply outsidePrimeLeastComplete_no_owner_of_period_gt
  exact hlarge.trans_le
    (outsidePrimeLeastSuperPeriod_ge_blocker hP hq hq11 hqP)
  exact hk

/-- For an odd prime, a physical six-offset `q^2` hit is exactly failure of the
selected `q^2` zero-free predicate.  The two compressed middle coordinates use
that `q^2` is coprime to `2`. -/
theorem physicalSquarePrimeAtEdge_iff_not_tSquareZeroFreeAt
    {k q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    physicalSquarePrimeAtEdge k q ↔ ¬ tSquareZeroFreeAt q k := by
  have hcop4 : Nat.Coprime (q ^ 2) 4 := by
    simpa using
      (Nat.coprime_pow_primes (p := q) (q := 2) 2 2
        hq Nat.prime_two hq2)
  have hcop2 : Nat.Coprime (q ^ 2) 2 :=
    hcop4.coprime_dvd_right (by norm_num : 2 ∣ 4)
  constructor
  · rintro ⟨_hq, a, ha, hdiv⟩ hzero
    simp [physicalTransitionActiveOffsets] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hzero (0 : Fin 6)) (by simpa [tTransitionForm, pow_two] using hdiv)
    · have hdiv' : q ^ 2 ∣ 2 * (2 * k + 1) := by
        convert hdiv using 1 <;> ring
      have hsmall : q ^ 2 ∣ 2 * k + 1 :=
        hcop2.dvd_of_dvd_mul_left hdiv'
      exact (hzero (1 : Fin 6)) (by simpa [tTransitionForm] using hsmall)
    · exact (hzero (2 : Fin 6)) (by simpa [tTransitionForm, pow_two] using hdiv)
    · exact (hzero (3 : Fin 6)) (by simpa [tTransitionForm, pow_two] using hdiv)
    · have hdiv' : q ^ 2 ∣ 2 * (2 * k + 3) := by
        convert hdiv using 1 <;> ring
      have hsmall : q ^ 2 ∣ 2 * k + 3 :=
        hcop2.dvd_of_dvd_mul_left hdiv'
      exact (hzero (4 : Fin 6)) (by simpa [tTransitionForm] using hsmall)
    · exact (hzero (5 : Fin 6)) (by simpa [tTransitionForm, pow_two] using hdiv)
  · intro hnot
    unfold tSquareZeroFreeAt at hnot
    push_neg at hnot
    rcases hnot with ⟨i, hi⟩
    fin_cases i
    · exact ⟨hq, 1, by simp [physicalTransitionActiveOffsets], by simpa [tTransitionForm, pow_two] using hi⟩
    · refine ⟨hq, 2, by simp [physicalTransitionActiveOffsets], ?_⟩
      have hmul : q ^ 2 ∣ 2 * (2 * k + 1) := dvd_mul_of_dvd_right hi 2
      convert hmul using 1 <;> ring
    · exact ⟨hq, 3, by simp [physicalTransitionActiveOffsets], by simpa [tTransitionForm, pow_two] using hi⟩
    · exact ⟨hq, 5, by simp [physicalTransitionActiveOffsets], by simpa [tTransitionForm, pow_two] using hi⟩
    · refine ⟨hq, 6, by simp [physicalTransitionActiveOffsets], ?_⟩
      have hmul : q ^ 2 ∣ 2 * (2 * k + 3) := dvd_mul_of_dvd_right hi 2
      convert hmul using 1 <;> ring
    · exact ⟨hq, 7, by simp [physicalTransitionActiveOffsets], by simpa [tTransitionForm, pow_two] using hi⟩

/-- A prime already selected into the zero-free CRT wheel cannot simultaneously
be the least outside-square owner of a deletion cell. -/
theorem outsidePrimeLeastDeletionChannel_no_selected_owner
    {P O : Finset ℕ} {q k : ℕ}
    (hP : IsSelectedGenericBlockerWheel P)
    (hqP : q ∈ P)
    (hk : k ∈ outsidePrimeLeastDeletionChannelCells P O q) : False := by
  have hq := (hP q hqP).1
  have hq2 : q ≠ 2 := by
    have hq11 := (hP q hqP).2
    omega
  have hkDel := (Finset.mem_filter.mp hk).1
  have hselected := (mem_outsidePrimeDeletionCells_iff.mp hkDel).2.1 q hqP
  have hownerGet := (Finset.mem_filter.mp hk).2
  have hne := outsidePrimeDeletion_leastSquare_ne_none hkDel
  cases hleast : physicalLeastOddSquarePrime k with
  | none => exact (hne hleast).elim
  | some r =>
      have hrq : r = q := by simpa [hleast] using hownerGet
      subst r
      have hhit := physicalLeastOddSquarePrime_some_spec hleast
      exact (physicalSquarePrimeAtEdge_iff_not_tSquareZeroFreeAt hq hq2).mp hhit hselected

/-- A finite certificate for the geometric blocker.  It deliberately separates
existence/construction of a wheel from the theorem that consumes one: selected
owners are excluded by zero-freeness, while every unselected generic prime is
forced to have an overlong super-period. -/
structure OutsidePrimeGenericBlockerCertificate (R : ℕ) (P : Finset ℕ) : Prop where
  generic : IsSelectedGenericBlockerWheel P
  unselected_large : ∀ q : ℕ, q.Prime → 11 ≤ q → q ∉ P →
    2 * R + 2 < 210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2

/-- **No generic complete owner.**  Under a blocker certificate, every complete
least-owner deletion cell has owner strictly below `11`; generic owners are
absent before any norm is taken. -/
theorem outsidePrimeLeastComplete_owner_lt_eleven_of_certificate
    {P : Finset ℕ} {R q k : ℕ}
    (hcert : OutsidePrimeGenericBlockerCertificate R P)
    (hk : k ∈ squareBlockOutsidePrimeLeastCompleteCells P R)
    (howner : physicalLeastOddSquarePrime k = some q) :
    q < 11 := by
  by_contra hnot
  have hq11 : 11 ≤ q := by omega
  have hqPrime := (physicalLeastOddSquarePrime_some_spec howner).1
  by_cases hqP : q ∈ P
  · have hkDel : k ∈ outsidePrimeLeastDeletionChannelCells P
        (threeSlotSquareBlockTransitionCells R) q := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact (Finset.mem_filter.mp hk).1
      · simp [howner]
    exact outsidePrimeLeastDeletionChannel_no_selected_owner
      hcert.generic hqP hkDel
  · have hlarge := hcert.unselected_large q hqPrime hq11 hqP
    exact (outsidePrimeLeastComplete_no_generic_owner_of_blocker
      hcert.generic hqPrime hq11 hqP hlarge hk) howner

end RHLean.Analysis
