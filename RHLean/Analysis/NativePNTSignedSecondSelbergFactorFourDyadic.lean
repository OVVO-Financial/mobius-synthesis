import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourFubini

/-!
# Exact prime-two fold of the factor-four signed K2 shell

The physical-product Fubini shell is partitioned by parity. Every nonzero
Möbius term with even divisor has the form `d = 2*m` with `m` odd. It pairs
bijectively with the odd-divisor, even-quotient term `(m, 2*k)` at the same
physical product. Terms with `4 | d` vanish because Möbius is zero.

No absolute value is taken in this file.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Physical pairs representing the factor-four annulus. -/
def nativePNTSignedK2FactorFourPairSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun dk =>
    N / 4 < dk.1 * dk.2 ∧ dk.1 * dk.2 ≤ N

/-- The same factor-four shell written directly on physical pairs. -/
def nativePNTSignedK2FactorFourPairMass (N : ℕ) : ℝ :=
  ∑ dk ∈ nativePNTSignedK2FactorFourPairSet N,
    nativePNTSignedK2RecipFubiniAtom dk.1 dk.2

@[simp] theorem mem_nativePNTSignedK2FactorFourPairSet
    {N d k : ℕ} :
    (d, k) ∈ nativePNTSignedK2FactorFourPairSet N ↔
      d ∈ Finset.Icc 1 N ∧ k ∈ Finset.Icc 1 N ∧
        N / 4 < d * k ∧ d * k ≤ N := by
  simp [nativePNTSignedK2FactorFourPairSet, and_assoc, and_left_comm, and_comm]

private theorem nativePNTSignedK2FactorFour_inner_set
    (N d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    Finset.Ioc ((N / 4) / d) (N / d) =
      (Finset.Icc 1 N).filter fun k =>
        N / 4 < d * k ∧ d * k ≤ N := by
  ext k
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdI.1
  simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hlow, hup⟩
    have hkpos : 0 < k :=
      Nat.lt_of_le_of_lt (Nat.zero_le ((N / 4) / d)) hlow
    have hlow' : N / 4 < d * k := by
      have h := (Nat.div_lt_iff_lt_mul hdpos).1 hlow
      simpa [Nat.mul_comm] using h
    have hup' : d * k ≤ N := by
      have h := (Nat.le_div_iff_mul_le hdpos).1 hup
      simpa [Nat.mul_comm] using h
    have hkN : k ≤ N := by
      calc
        k = 1 * k := by simp
        _ ≤ d * k := Nat.mul_le_mul_right k hdI.1
        _ ≤ N := hup'
    exact ⟨⟨Nat.succ_le_iff.mpr hkpos, hkN⟩, hlow', hup'⟩
  · rintro ⟨⟨_hk1, _hkN⟩, hlow, hup⟩
    constructor
    · apply (Nat.div_lt_iff_lt_mul hdpos).2
      simpa [Nat.mul_comm] using hlow
    · apply (Nat.le_div_iff_mul_le hdpos).2
      simpa [Nat.mul_comm] using hup

/-- The nested quotient Fubini shell and the physical-pair shell are identical. -/
theorem nativePNTSignedK2RecipDoubleShell_eq_pairMass
    (N : ℕ) :
    nativePNTSignedK2RecipDoubleShell N =
      nativePNTSignedK2FactorFourPairMass N := by
  classical
  unfold nativePNTSignedK2RecipDoubleShell
    nativePNTSignedK2FactorFourPairMass nativePNTSignedK2FactorFourPairSet
  rw [Finset.sum_filter]
  have hprod := Finset.sum_product
    (s := Finset.Icc 1 N) (t := Finset.Icc 1 N)
    (f := fun dk : ℕ × ℕ =>
      if N / 4 < dk.1 * dk.2 ∧ dk.1 * dk.2 ≤ N then
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2 else 0)
  calc
    (∑ d ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Ioc ((N / 4) / d) (N / d),
          nativePNTSignedK2RecipFubiniAtom d k) =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          if N / 4 < d * k ∧ d * k ≤ N then
            nativePNTSignedK2RecipFubiniAtom d k else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hset := nativePNTSignedK2FactorFour_inner_set N d hd
      calc
        (∑ k ∈ Finset.Ioc ((N / 4) / d) (N / d),
            nativePNTSignedK2RecipFubiniAtom d k) =
          ∑ k ∈ (Finset.Icc 1 N).filter (fun k =>
              N / 4 < d * k ∧ d * k ≤ N),
            nativePNTSignedK2RecipFubiniAtom d k := by rw [← hset]
        _ = ∑ k ∈ Finset.Icc 1 N,
            if N / 4 < d * k ∧ d * k ≤ N then
              nativePNTSignedK2RecipFubiniAtom d k else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ a ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        if N / 4 < a.1 * a.2 ∧ a.1 * a.2 ≤ N then
          nativePNTSignedK2RecipFubiniAtom a.1 a.2 else 0 := by
      simpa using hprod.symm

/-- Odd-divisor part of the physical pair set. -/
def nativePNTSignedK2FactorFourOddPairSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourPairSet N).filter fun dk => Odd dk.1

/-- Odd-divisor, odd-quotient core left after one prime-two fold. -/
def nativePNTSignedK2FactorFourOddOddSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourOddPairSet N).filter fun dk => Odd dk.2

/-- Odd-divisor, even-quotient half of the prime-two matched family. -/
def nativePNTSignedK2FactorFourOddEvenSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourOddPairSet N).filter fun dk => Even dk.2

/-- Even-divisor half of the prime-two matched family. -/
def nativePNTSignedK2FactorFourEvenSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourPairSet N).filter fun dk => Even dk.1

/-- Parent pairs for the map `(m,k) -> (2*m,k)`. -/
def nativePNTSignedK2FactorFourPrimeTwoParentAllSet
    (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun mk =>
    N / 4 < (2 * mk.1) * mk.2 ∧ (2 * mk.1) * mk.2 ≤ N

/-- Nonzero prime-two parents. -/
def nativePNTSignedK2FactorFourPrimeTwoParentSet
    (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourPrimeTwoParentAllSet N).filter fun mk => Odd mk.1

@[simp] theorem mem_nativePNTSignedK2FactorFourPrimeTwoParentAllSet
    {N m k : ℕ} :
    (m, k) ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N ↔
      m ∈ Finset.Icc 1 N ∧ k ∈ Finset.Icc 1 N ∧
        N / 4 < (2 * m) * k ∧ (2 * m) * k ≤ N := by
  simp [nativePNTSignedK2FactorFourPrimeTwoParentAllSet,
    and_assoc, and_left_comm, and_comm]

@[simp] theorem mem_nativePNTSignedK2FactorFourPrimeTwoParentSet
    {N m k : ℕ} :
    (m, k) ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N ↔
      m ∈ Finset.Icc 1 N ∧ k ∈ Finset.Icc 1 N ∧
        N / 4 < (2 * m) * k ∧ (2 * m) * k ≤ N ∧ Odd m := by
  simp [nativePNTSignedK2FactorFourPrimeTwoParentSet,
    nativePNTSignedK2FactorFourPrimeTwoParentAllSet,
    and_assoc, and_left_comm, and_comm]

/-- A doubled even parent contains the square `2^2`, hence its Möbius atom is zero. -/
theorem nativePNTSignedK2RecipFubiniAtom_two_mul_eq_zero_of_even
    (m k : ℕ) (hm : Even m) :
    nativePNTSignedK2RecipFubiniAtom (2 * m) k = 0 := by
  have hnot : ¬ Squarefree (2 * m) := by
    intro hsq
    rcases hm with ⟨r, hr⟩
    have hfour : 2 * 2 ∣ 2 * m := by
      refine ⟨r, ?_⟩
      omega
    exact Nat.prime_two.not_isUnit (hsq 2 hfour)
  have hmuZ : (μ : ArithmeticFunction ℝ) (2 * m) = 0 := by
    change (((μ (2 * m) : ℤ) : ℝ)) = 0
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]
    norm_num
  simp [nativePNTSignedK2RecipFubiniAtom, hmuZ]

private theorem factorFour_sum_eq_odd1_add_even1
    (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (∑ z ∈ s, f z) =
      (∑ z ∈ s.filter (fun z => Odd z.1), f z) +
        ∑ z ∈ s.filter (fun z => Even z.1), f z := by
  calc
    (∑ z ∈ s, f z) =
      ∑ z ∈ s, ((if Odd z.1 then f z else 0) +
        (if Even z.1 then f z else 0)) := by
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hodd : Odd z.1
        · have hneven : ¬ Even z.1 := Nat.not_even_iff_odd.mpr hodd
          simp [hodd, hneven]
        · have heven : Even z.1 := Nat.not_odd_iff_even.mp hodd
          simp [hodd, heven]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]

private theorem factorFour_sum_eq_odd2_add_even2
    (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (∑ z ∈ s, f z) =
      (∑ z ∈ s.filter (fun z => Odd z.2), f z) +
        ∑ z ∈ s.filter (fun z => Even z.2), f z := by
  calc
    (∑ z ∈ s, f z) =
      ∑ z ∈ s, ((if Odd z.2 then f z else 0) +
        (if Even z.2 then f z else 0)) := by
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hodd : Odd z.2
        · have hneven : ¬ Even z.2 := Nat.not_even_iff_odd.mpr hodd
          simp [hodd, hneven]
        · have heven : Even z.2 := Nat.not_odd_iff_even.mp hodd
          simp [hodd, heven]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]

private theorem factorFour_odd_sum_eq_oddOdd_add_oddEven
    (N : ℕ) :
    (∑ dk ∈ nativePNTSignedK2FactorFourOddPairSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) =
      (∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
      ∑ dk ∈ nativePNTSignedK2FactorFourOddEvenSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2 := by
  simpa [nativePNTSignedK2FactorFourOddOddSet,
    nativePNTSignedK2FactorFourOddEvenSet] using
    factorFour_sum_eq_odd2_add_even2
      (nativePNTSignedK2FactorFourOddPairSet N)
      (fun dk => nativePNTSignedK2RecipFubiniAtom dk.1 dk.2)

private theorem factorFour_oddEven_sum_eq_parent_right
    (N : ℕ) :
    (∑ dk ∈ nativePNTSignedK2FactorFourOddEvenSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) =
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
        nativePNTSignedK2RecipFubiniAtom mk.1 (2 * mk.2) := by
  classical
  symm
  refine Finset.sum_bij
    (fun mk _hmk => (mk.1, 2 * mk.2)) ?_ ?_ ?_ ?_
  · intro mk hmk
    rcases mem_nativePNTSignedK2FactorFourPrimeTwoParentSet.mp hmk with
      ⟨hmI, hkI, hlow, hup, hmodd⟩
    have hm1 := (Finset.mem_Icc.mp hmI).1
    have hk1 := (Finset.mem_Icc.mp hkI).1
    have h2kN : 2 * mk.2 ≤ N := by
      calc
        2 * mk.2 = 1 * (2 * mk.2) := by simp
        _ ≤ mk.1 * (2 * mk.2) := Nat.mul_le_mul_right (2 * mk.2) hm1
        _ = (2 * mk.1) * mk.2 := by ring
        _ ≤ N := hup
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨mem_nativePNTSignedK2FactorFourPairSet.mpr
        ⟨hmI, Finset.mem_Icc.mpr ⟨by omega, h2kN⟩,
          by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlow,
          by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hup⟩,
        hmodd⟩
    · exact even_two_mul mk.2
  · intro a _ha b _hb hab
    injection hab with hfst hsnd
    apply Prod.ext
    · exact hfst
    · omega
  · intro dk hdk
    rcases Finset.mem_filter.mp hdk with ⟨hoddSet, hkeven⟩
    rcases Finset.mem_filter.mp hoddSet with ⟨hpair, hdodd⟩
    rcases mem_nativePNTSignedK2FactorFourPairSet.mp hpair with
      ⟨hdI, hkI, hlow, hup⟩
    have hkI' := Finset.mem_Icc.mp hkI
    have hdouble : 2 * (dk.2 / 2) = dk.2 := Nat.two_mul_div_two_of_even hkeven
    have hhalf1 : 1 ≤ dk.2 / 2 := by
      have hkpos : 0 < dk.2 := lt_of_lt_of_le Nat.zero_lt_one hkI'.1
      rcases hkeven with ⟨r, hr⟩
      omega
    have hhalfN : dk.2 / 2 ≤ N := (Nat.div_le_self dk.2 2).trans hkI'.2
    refine ⟨(dk.1, dk.2 / 2), ?_, ?_⟩
    · apply mem_nativePNTSignedK2FactorFourPrimeTwoParentSet.mpr
      exact ⟨hdI, Finset.mem_Icc.mpr ⟨hhalf1, hhalfN⟩,
        by simpa [hdouble, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlow,
        by simpa [hdouble, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hup,
        hdodd⟩
    · apply Prod.ext <;> simp [hdouble]
  · intro mk _hmk
    rfl

private theorem factorFour_even_sum_eq_parentAll_left
    (N : ℕ) :
    (∑ dk ∈ nativePNTSignedK2FactorFourEvenSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) =
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N,
        nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2 := by
  classical
  symm
  refine Finset.sum_bij
    (fun mk _hmk => (2 * mk.1, mk.2)) ?_ ?_ ?_ ?_
  · intro mk hmk
    rcases mem_nativePNTSignedK2FactorFourPrimeTwoParentAllSet.mp hmk with
      ⟨hmI, hkI, hlow, hup⟩
    have hm1 := (Finset.mem_Icc.mp hmI).1
    have hk1 := (Finset.mem_Icc.mp hkI).1
    have h2mN : 2 * mk.1 ≤ N := by
      calc
        2 * mk.1 = (2 * mk.1) * 1 := by simp
        _ ≤ (2 * mk.1) * mk.2 :=
          Nat.mul_le_mul_left (2 * mk.1) hk1
        _ ≤ N := hup
    apply Finset.mem_filter.mpr
    exact ⟨mem_nativePNTSignedK2FactorFourPairSet.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, h2mN⟩, hkI, hlow, hup⟩,
      even_two_mul mk.1⟩
  · intro a _ha b _hb hab
    injection hab with hfst hsnd
    apply Prod.ext
    · omega
    · exact hsnd
  · intro dk hdk
    rcases Finset.mem_filter.mp hdk with ⟨hpair, hdeven⟩
    rcases mem_nativePNTSignedK2FactorFourPairSet.mp hpair with
      ⟨hdI, hkI, hlow, hup⟩
    have hdI' := Finset.mem_Icc.mp hdI
    have hdouble : 2 * (dk.1 / 2) = dk.1 := Nat.two_mul_div_two_of_even hdeven
    have hhalf1 : 1 ≤ dk.1 / 2 := by
      have hdpos : 0 < dk.1 := lt_of_lt_of_le Nat.zero_lt_one hdI'.1
      rcases hdeven with ⟨r, hr⟩
      omega
    have hhalfN : dk.1 / 2 ≤ N := (Nat.div_le_self dk.1 2).trans hdI'.2
    refine ⟨(dk.1 / 2, dk.2), ?_, ?_⟩
    · apply mem_nativePNTSignedK2FactorFourPrimeTwoParentAllSet.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hhalf1, hhalfN⟩, hkI,
        by simpa [hdouble] using hlow,
        by simpa [hdouble] using hup⟩
    · apply Prod.ext <;> simp [hdouble]
  · intro mk _hmk
    rfl

private theorem factorFour_parentAll_left_eq_parentOdd_left
    (N : ℕ) :
    (∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N,
        nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2) =
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
        nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2 := by
  classical
  calc
    (∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N,
        nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2) =
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N,
        if Odd mk.1 then nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2 else 0 := by
          apply Finset.sum_congr rfl
          intro mk _hmk
          by_cases hodd : Odd mk.1
          · simp [hodd]
          · have heven : Even mk.1 := Nat.not_odd_iff_even.mp hodd
            rw [nativePNTSignedK2RecipFubiniAtom_two_mul_eq_zero_of_even
              mk.1 mk.2 heven]
            simp [hodd]
    _ = _ := by
      unfold nativePNTSignedK2FactorFourPrimeTwoParentSet
      rw [Finset.sum_filter]

/-- Exact prime-two factor-four fold. -/
theorem nativePNTSignedK2FactorFourPairMass_eq_oddOdd_add_primeTwo
    (N : ℕ) :
    nativePNTSignedK2FactorFourPairMass N =
      (∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
        (-(μ : ArithmeticFunction ℝ) mk.1 *
          ((Real.log (2 : ℝ)) ^ 2 +
            2 * Real.log (2 : ℝ) * Real.log (mk.1 : ℝ)) /
          (((mk.1 * 2) * mk.2 : ℕ) : ℝ)) := by
  classical
  have hfirst := factorFour_sum_eq_odd1_add_even1
    (nativePNTSignedK2FactorFourPairSet N)
    (fun dk => nativePNTSignedK2RecipFubiniAtom dk.1 dk.2)
  have hodd := factorFour_odd_sum_eq_oddOdd_add_oddEven N
  have hsplit :
      nativePNTSignedK2FactorFourPairMass N =
        ((∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
        (∑ dk ∈ nativePNTSignedK2FactorFourOddEvenSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2)) +
        ∑ dk ∈ nativePNTSignedK2FactorFourEvenSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2 := by
    unfold nativePNTSignedK2FactorFourPairMass
    rw [hfirst]
    change
      (∑ dk ∈ nativePNTSignedK2FactorFourOddPairSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
        (∑ dk ∈ nativePNTSignedK2FactorFourEvenSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) = _
    rw [hodd]
  calc
    nativePNTSignedK2FactorFourPairMass N =
        ((∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
        (∑ dk ∈ nativePNTSignedK2FactorFourOddEvenSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2)) +
        ∑ dk ∈ nativePNTSignedK2FactorFourEvenSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2 := hsplit
    _ = ((∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
        (∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
          nativePNTSignedK2RecipFubiniAtom mk.1 (2 * mk.2))) +
        ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
          nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2 := by
      rw [factorFour_oddEven_sum_eq_parent_right,
        factorFour_even_sum_eq_parentAll_left,
        factorFour_parentAll_left_eq_parentOdd_left]
    _ = (∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
        ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
          (-(μ : ArithmeticFunction ℝ) mk.1 *
            ((Real.log (2 : ℝ)) ^ 2 +
              2 * Real.log (2 : ℝ) * Real.log (mk.1 : ℝ)) /
            (((mk.1 * 2) * mk.2 : ℕ) : ℝ)) := by
      rw [add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro mk hmk
      rcases mem_nativePNTSignedK2FactorFourPrimeTwoParentSet.mp hmk with
        ⟨_hmI, hkI, _hlow, _hup, hmodd⟩
      have hk1 := (Finset.mem_Icc.mp hkI).1
      have hpair := nativePNTSignedK2RecipFubiniAtom_two_sameProduct
        mk.1 mk.2 hmodd hk1
      simpa [Nat.mul_comm, add_comm] using hpair

/-- The original factor-four interval inherits the exact prime-two fold. -/
theorem nativePNTSignedK2RecipInterval_four_eq_oddOdd_add_primeTwo
    (N : ℕ) :
    nativePNTSignedK2RecipInterval N 4 =
      (∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
        (-(μ : ArithmeticFunction ℝ) mk.1 *
          ((Real.log (2 : ℝ)) ^ 2 +
            2 * Real.log (2 : ℝ) * Real.log (mk.1 : ℝ)) /
          (((mk.1 * 2) * mk.2 : ℕ) : ℝ)) := by
  rw [nativePNTSignedK2RecipInterval_four_eq_doubleShell,
    nativePNTSignedK2RecipDoubleShell_eq_pairMass,
    nativePNTSignedK2FactorFourPairMass_eq_oddOdd_add_primeTwo]

end RHLean.Analysis
