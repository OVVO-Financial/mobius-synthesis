import Mathlib
import RHLean.Analysis.OutsidePrimeLeastSquareMaximalWheel

/-!
# Construction of the maximal finite blocker wheel

The previous blocker module isolates the exact certificate needed to force every
complete outside least-square owner below 11.  Here the certificate is actually
constructed from a finite maximal feasible wheel.

We maximize cardinality among subsets of the generic prime pool through the
square-block length whose reserved square product still fits in the block.  If an
unselected generic prime could be adjoined while preserving feasibility, the
cardinality would increase, contradicting maximality.  Primes above the finite
pool violate the blocker inequality automatically.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Generic primes that could conceivably be needed by the blocker at stage R. -/
def outsidePrimeGenericWheelPool (R : ℕ) : Finset ℕ :=
  (primesUpTo (2 * R + 2)).filter fun p => 11 ≤ p

/-- Feasible selected generic wheels at stage R. -/
def outsidePrimeFeasibleGenericWheels (R : ℕ) : Finset (Finset ℕ) :=
  (outsidePrimeGenericWheelPool R).powerset.filter fun P =>
    210 ^ 2 * (∏ p ∈ P, p ^ 2) ≤ 2 * R + 2

/-- The empty wheel is feasible as soon as the reserved exceptional period fits. -/
theorem outsidePrimeFeasibleGenericWheels_nonempty
    {R : ℕ} (hbase : 210 ^ 2 ≤ 2 * R + 2) :
    (outsidePrimeFeasibleGenericWheels R).Nonempty := by
  refine ⟨∅, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨by simp, ?_⟩
  simpa using hbase

/-- Every member of a feasible wheel is a generic prime. -/
theorem outsidePrimeFeasibleGenericWheel_generic
    {R : ℕ} {P : Finset ℕ}
    (hP : P ∈ outsidePrimeFeasibleGenericWheels R) :
    IsSelectedGenericBlockerWheel P := by
  intro p hp
  have hsub : P ⊆ outsidePrimeGenericWheelPool R :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  have hpPool := hsub hp
  have hpData : p ∈ primesUpTo (2 * R + 2) ∧ 11 ≤ p := by
    simpa [outsidePrimeGenericWheelPool] using hpPool
  exact ⟨(mem_primesUpTo.mp hpData.1).1, hpData.2⟩

/-- Every feasible wheel obeys the reserved-period bound. -/
theorem outsidePrimeFeasibleGenericWheel_period
    {R : ℕ} {P : Finset ℕ}
    (hP : P ∈ outsidePrimeFeasibleGenericWheels R) :
    210 ^ 2 * (∏ p ∈ P, p ^ 2) ≤ 2 * R + 2 :=
  (Finset.mem_filter.mp hP).2

/-- **Existence of a genuine maximal blocker certificate.**  Once the fixed
`210^2` exceptional reserve fits, there is a finite selected generic wheel that
both fits the square block and forces every unselected generic owner to have an
overlong least-owner super-period. -/
theorem exists_outsidePrimeGenericBlockerCertificate
    {R : ℕ} (hbase : 210 ^ 2 ≤ 2 * R + 2) :
    ∃ P : Finset ℕ,
      OutsidePrimeGenericBlockerCertificate R P ∧
      210 ^ 2 * (∏ p ∈ P, p ^ 2) ≤ 2 * R + 2 := by
  classical
  let C := outsidePrimeFeasibleGenericWheels R
  have hC : C.Nonempty := outsidePrimeFeasibleGenericWheels_nonempty hbase
  let cards : Finset ℕ := C.image Finset.card
  have hcards : cards.Nonempty := hC.image Finset.card
  let m : ℕ := cards.max' hcards
  have hm : m ∈ cards := Finset.max'_mem cards hcards
  rcases Finset.mem_image.mp hm with ⟨P, hPC, hcardP⟩
  refine ⟨P, ?_, outsidePrimeFeasibleGenericWheel_period hPC⟩
  refine ⟨outsidePrimeFeasibleGenericWheel_generic hPC, ?_⟩
  intro q hq hq11 hqP
  by_cases hqBound : q ≤ 2 * R + 2
  · have hqPool : q ∈ outsidePrimeGenericWheelPool R := by
      unfold outsidePrimeGenericWheelPool
      apply Finset.mem_filter.mpr
      exact ⟨mem_primesUpTo.mpr ⟨hq, hqBound⟩, hq11⟩
    by_contra hnot
    have hfeas :
        210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2 ≤ 2 * R + 2 :=
      Nat.le_of_not_gt hnot
    have hsubP : P ⊆ outsidePrimeGenericWheelPool R :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hPC).1
    have hInsertSub : insert q P ⊆ outsidePrimeGenericWheelPool R := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hqPool
      · exact hsubP hr
    have hprodInsert :
        (∏ p ∈ insert q P, p ^ 2) =
          (∏ p ∈ P, p ^ 2) * q ^ 2 := by
      rw [Finset.prod_insert hqP]
      ring
    have hInsertC : insert q P ∈ C := by
      unfold C outsidePrimeFeasibleGenericWheels
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr hInsertSub, ?_⟩
      rw [hprodInsert]
      simpa [Nat.mul_assoc] using hfeas
    have hInsertCardMem : (insert q P).card ∈ cards := by
      exact Finset.mem_image.mpr ⟨insert q P, hInsertC, rfl⟩
    have hle : (insert q P).card ≤ m := Finset.le_max' cards _ hInsertCardMem
    have hmEq : m = P.card := hcardP.symm
    rw [Finset.card_insert_of_notMem hqP, hmEq] at hle
    omega
  · have hqLarge : 2 * R + 2 < q := Nat.lt_of_not_ge hqBound
    have hPgen := outsidePrimeFeasibleGenericWheel_generic hPC
    have hprodPos : 0 < ∏ p ∈ P, p ^ 2 := by
      apply Finset.prod_pos
      intro p hp
      have hpPrime := (hPgen p hp).1
      exact pow_pos hpPrime.pos 2
    have hqPos : 0 < q := hq.pos
    have hqLeSq : q ≤ q ^ 2 := by nlinarith
    have hmult : q ^ 2 ≤ 210 ^ 2 * (∏ p ∈ P, p ^ 2) * q ^ 2 := by
      have hone : 1 ≤ 210 ^ 2 * (∏ p ∈ P, p ^ 2) := by
        nlinarith
      nlinarith
    exact hqLarge.trans_le (hqLeSq.trans hmult)

/-- Consequently the maximal-wheel blocker is not a conditional bookkeeping
step: for every sufficiently large square stage it yields an actual certificate
consumed by `outsidePrimeLeastComplete_owner_lt_eleven_of_certificate`. -/
theorem exists_blockerWheel_complete_owner_lt_eleven
    {R : ℕ} (hbase : 210 ^ 2 ≤ 2 * R + 2) :
    ∃ P : Finset ℕ,
      210 ^ 2 * (∏ p ∈ P, p ^ 2) ≤ 2 * R + 2 ∧
      ∀ q k : ℕ,
        k ∈ squareBlockOutsidePrimeLeastCompleteCells P R →
        physicalLeastOddSquarePrime k = some q → q < 11 := by
  obtain ⟨P, hcert, hfit⟩ := exists_outsidePrimeGenericBlockerCertificate hbase
  refine ⟨P, hfit, ?_⟩
  intro q k hk howner
  exact outsidePrimeLeastComplete_owner_lt_eleven_of_certificate hcert hk howner

end RHLean.Analysis
