import Mathlib
import RHLean.Analysis.PhysicalSquareCRTTransfer

/-!
# Outside-prime deletion mask on complete CRT orbits

A complete finite-prime CRT orbit carries an exact selected-prime zero-free law,
but the actual Mobius `T` population is obtained only after square factors from
primes outside the selected set delete additional cells.

This module isolates that deletion operation exactly.  It keeps the selected
signed degree-one observable intact throughout: no absolute value or triangle
inequality is applied to the deletion term.

The final `OutsidePrimeDeletionUnbiased` declaration is only a proposition-valued
analytic target.  No theorem in this file asserts it.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Generic finite-prime sets to which the finite-prime `T` law applies. -/
def IsGenericFinitePrimeSet (P : Finset ℕ) : Prop :=
  ∀ p ∈ P, p.Prime ∧ 11 ≤ p

/-- An exact aligned complete CRT orbit for a generic selected-prime set. -/
def IsCompleteCRTOrbit (P O : Finset ℕ) : Prop :=
  IsGenericFinitePrimeSet P ∧ ∃ k : ℕ, O = finitePrimeCRTOrbit P k

/-- All six physical Mobius coordinates are nonzero. -/
def outsidePrimeActualZeroFreeAt (k : ℕ) : Prop :=
  IsThreeSlotNonzeroState (threeSlotState k) ∧
    IsThreeSlotNonzeroState (threeSlotState (k + 1))

instance outsidePrimeActualZeroFreeAt_decidable (k : ℕ) :
    Decidable (outsidePrimeActualZeroFreeAt k) := by
  unfold outsidePrimeActualZeroFreeAt
  infer_instance

/-- Every selected prime-square coordinate avoids all six transition forms. -/
def outsidePrimeSelectedZeroFreeAt (P : Finset ℕ) (k : ℕ) : Prop :=
  ∀ p ∈ P, tSquareZeroFreeAt p k

instance outsidePrimeSelectedZeroFreeAt_decidable (P : Finset ℕ) (k : ℕ) :
    Decidable (outsidePrimeSelectedZeroFreeAt P k) := by
  unfold outsidePrimeSelectedZeroFreeAt
  infer_instance

/-- Sign contributed by the selected prime coordinates to one arithmetic form. -/
def selectedPrimeSign (P : Finset ℕ) (n : ℕ) : ℤ :=
  ∏ p ∈ P, if p ∣ n then (-1 : ℤ) else 1

/-- Degree-one selected-prime observable on the source `T` state.

The middle coordinate is the odd compressed form `2*k+1`; therefore the physical
prime-2 sign is already represented by the `a-b+c` convention. -/
def selectedDegreeOneProjection (P : Finset ℕ) (k : ℕ) : ℝ :=
  ((selectedPrimeSign P (tActiveForm (0 : Fin 3) k) -
      selectedPrimeSign P (tActiveForm (1 : Fin 3) k) +
        selectedPrimeSign P (tActiveForm (2 : Fin 3) k) : ℤ) : ℝ)

/-- `O ∩ Z_all`: cells retained by the actual all-prime Mobius zero-free mask. -/
def outsidePrimeActualRetainedCells (O : Finset ℕ) : Finset ℕ :=
  O.filter outsidePrimeActualZeroFreeAt

/-- `O ∩ Z_P`: cells retained by the selected-prime square-zero mask. -/
def outsidePrimeSelectedRetainedCells
    (P O : Finset ℕ) : Finset ℕ :=
  O.filter (outsidePrimeSelectedZeroFreeAt P)

/-- `O ∩ (Z_P \ Z_all)`: selected-prime cells deleted by outside-prime squares. -/
def outsidePrimeDeletionCells (P O : Finset ℕ) : Finset ℕ :=
  outsidePrimeSelectedRetainedCells P O \
    outsidePrimeActualRetainedCells O

/-- A prime-square divisor forces the Mobius value to vanish. -/
private theorem moebius_eq_zero_of_prime_sq_dvd
    {p n : ℕ} (hp : p.Prime) (hdiv : p ^ 2 ∣ n) :
    μ n = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  have hunit := hsq p (by simpa [pow_two] using hdiv)
  rw [Nat.isUnit_iff] at hunit
  have hpTwo : 2 ≤ p := hp.two_le
  omega

/-- Multiplying an odd-compressed middle form by the fixed factor `2` preserves
any selected prime-square divisor. -/
private theorem prime_sq_dvd_two_mul
    {p n : ℕ} (hdiv : p ^ 2 ∣ n) :
    p ^ 2 ∣ 2 * n := by
  rcases hdiv with ⟨c, hc⟩
  refine ⟨2 * c, ?_⟩
  calc
    2 * n = 2 * (p ^ 2 * c) := by rw [hc]
    _ = p ^ 2 * (2 * c) := by ring

/-- Actual all-prime zero-freeness implies selected-prime zero-freeness for any
prime set.  The two compressed middle coordinates are handled by the fixed
prime-2 factor explicitly. -/
theorem outsidePrimeActualZeroFreeAt_implies_selected
    {P : Finset ℕ} {k : ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (hk : outsidePrimeActualZeroFreeAt k) :
    outsidePrimeSelectedZeroFreeAt P k := by
  intro p hpMem i
  have hpPrime : p.Prime := hP p hpMem
  intro hdiv
  rcases hk with ⟨hsrc, hdst⟩
  change
    chiA (threeSlotState k) ≠ 0 ∧
      chiB (threeSlotState k) ≠ 0 ∧
        chiC (threeSlotState k) ≠ 0 at hsrc
  change
    chiA (threeSlotState (k + 1)) ≠ 0 ∧
      chiB (threeSlotState (k + 1)) ≠ 0 ∧
        chiC (threeSlotState (k + 1)) ≠ 0 at hdst
  fin_cases i
  · apply hsrc.1
    rw [chiA_threeSlotState]
    apply moebius_eq_zero_of_prime_sq_dvd hpPrime
    simpa [tTransitionForm] using hdiv
  · apply hsrc.2.1
    rw [chiB_threeSlotState]
    apply moebius_eq_zero_of_prime_sq_dvd hpPrime
    have hsmall : p ^ 2 ∣ 2 * k + 1 := by
      simpa [tTransitionForm] using hdiv
    have htwo : p ^ 2 ∣ 2 * (2 * k + 1) :=
      prime_sq_dvd_two_mul hsmall
    have heq : 2 * (2 * k + 1) = 4 * k + 2 := by ring
    rwa [heq] at htwo
  · apply hsrc.2.2
    rw [chiC_threeSlotState]
    apply moebius_eq_zero_of_prime_sq_dvd hpPrime
    simpa [tTransitionForm] using hdiv
  · apply hdst.1
    rw [chiA_threeSlotState]
    apply moebius_eq_zero_of_prime_sq_dvd hpPrime
    have hsmall : p ^ 2 ∣ 4 * k + 5 := by
      simpa [tTransitionForm] using hdiv
    have heq : 4 * (k + 1) + 1 = 4 * k + 5 := by omega
    rwa [heq]
  · apply hdst.2.1
    rw [chiB_threeSlotState]
    apply moebius_eq_zero_of_prime_sq_dvd hpPrime
    have hsmall : p ^ 2 ∣ 2 * k + 3 := by
      simpa [tTransitionForm] using hdiv
    have htwo : p ^ 2 ∣ 2 * (2 * k + 3) :=
      prime_sq_dvd_two_mul hsmall
    have heq : 4 * (k + 1) + 2 = 2 * (2 * k + 3) := by ring
    rwa [heq]
  · apply hdst.2.2
    rw [chiC_threeSlotState]
    apply moebius_eq_zero_of_prime_sq_dvd hpPrime
    have hsmall : p ^ 2 ∣ 4 * k + 7 := by
      simpa [tTransitionForm] using hdiv
    have heq : 4 * (k + 1) + 3 = 4 * k + 7 := by omega
    rwa [heq]

/-- The actual retained population is a subset of the selected retained
population on every generic complete CRT orbit. -/
theorem outsidePrimeActualRetainedCells_subset_selected
    {P O : Finset ℕ} (hO : IsCompleteCRTOrbit P O) :
    outsidePrimeActualRetainedCells O ⊆
      outsidePrimeSelectedRetainedCells P O := by
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkO, hkActual⟩
  apply Finset.mem_filter.mpr
  refine ⟨hkO, ?_⟩
  apply outsidePrimeActualZeroFreeAt_implies_selected
  · intro p hp
    exact (hO.1 p hp).1
  · exact hkActual

/-- Exact retained/deleted partition:

`O ∩ Z_P = (O ∩ Z_all) ⊔ (O ∩ (Z_P \ Z_all))`.
-/
theorem outsidePrimeSelectedRetainedCells_eq_actual_union_deletion
    {P O : Finset ℕ} (hO : IsCompleteCRTOrbit P O) :
    outsidePrimeSelectedRetainedCells P O =
      outsidePrimeActualRetainedCells O ∪ outsidePrimeDeletionCells P O := by
  have hsub := outsidePrimeActualRetainedCells_subset_selected hO
  ext k
  constructor
  · intro hk
    by_cases hka : k ∈ outsidePrimeActualRetainedCells O
    · exact Finset.mem_union_left _ hka
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hk, hka⟩)
  · intro hk
    rcases Finset.mem_union.mp hk with hka | hkd
    · exact hsub hka
    · exact (Finset.mem_sdiff.mp hkd).1

/-- The two pieces of the retained/deleted partition are disjoint. -/
theorem outsidePrimeActualRetainedCells_disjoint_deletion
    (P O : Finset ℕ) :
    Disjoint (outsidePrimeActualRetainedCells O)
      (outsidePrimeDeletionCells P O) := by
  apply Finset.disjoint_left.mpr
  intro k hka hkd
  exact (Finset.mem_sdiff.mp hkd).2 hka

/-- Membership in the deletion mask is exactly selected-prime zero-freeness
without actual all-prime zero-freeness. -/
theorem mem_outsidePrimeDeletionCells_iff
    {P O : Finset ℕ} {k : ℕ} :
    k ∈ outsidePrimeDeletionCells P O ↔
      k ∈ O ∧ outsidePrimeSelectedZeroFreeAt P k ∧
        ¬ outsidePrimeActualZeroFreeAt k := by
  unfold outsidePrimeDeletionCells
  constructor
  · intro hk
    rcases Finset.mem_sdiff.mp hk with ⟨hkSelectedMem, hkNotActualMem⟩
    rcases Finset.mem_filter.mp hkSelectedMem with ⟨hkO, hkSelected⟩
    refine ⟨hkO, hkSelected, ?_⟩
    intro hkActual
    apply hkNotActualMem
    exact Finset.mem_filter.mpr ⟨hkO, hkActual⟩
  · rintro ⟨hkO, hkSelected, hkNotActual⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨hkO, hkSelected⟩
    · intro hkActualMem
      exact hkNotActual (Finset.mem_filter.mp hkActualMem).2

/-- Selected CRT degree-one mass before outside-prime deletion. -/
def outsidePrimeSelectedT (P O : Finset ℕ) : ℝ :=
  ∑ k ∈ outsidePrimeSelectedRetainedCells P O,
    selectedDegreeOneProjection P k

/-- The same selected CRT observable after imposing the actual all-prime
zero-free mask.  This name refers to the actual retained population; it does not
identify the selected-prime signs with the full Mobius signs. -/
def outsidePrimeActualT (P O : Finset ℕ) : ℝ :=
  ∑ k ∈ outsidePrimeActualRetainedCells O,
    selectedDegreeOneProjection P k

/-- Signed selected CRT mass removed by outside-prime square deletions. -/
def outsidePrimeDeletionT (P O : Finset ℕ) : ℝ :=
  ∑ k ∈ outsidePrimeDeletionCells P O,
    selectedDegreeOneProjection P k

/-- Exact signed deletion identity.  No norm or triangle inequality is used. -/
theorem outsidePrimeActualT_eq_selectedT_sub_deletionT
    {P O : Finset ℕ} (hO : IsCompleteCRTOrbit P O) :
    outsidePrimeActualT P O =
      outsidePrimeSelectedT P O - outsidePrimeDeletionT P O := by
  have hsub := outsidePrimeActualRetainedCells_subset_selected hO
  unfold outsidePrimeActualT outsidePrimeSelectedT outsidePrimeDeletionT
    outsidePrimeDeletionCells
  rw [← Finset.sum_sdiff hsub]
  ring

/-- Open analytic target: deleting cells by all primes outside the selected CRT
set does not create super-RH-scale degree-one bias on a complete orbit.

The exact physical `T` population is the six-coordinate all-prime zero-free
filter above.  The schematic single condition `μ m ≠ 0` is therefore replaced
here by that exact existing physical condition rather than by a weaker
one-coordinate surrogate. -/
def OutsidePrimeDeletionUnbiased : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset ℕ, ∀ O : Finset ℕ,
        IsCompleteCRTOrbit P O →
          |∑ k ∈ outsidePrimeActualRetainedCells O,
              selectedDegreeOneProjection P k| ^ 2 ≤
            C * Real.rpow (O.card : ℝ) (1 + ε)

end RHLean.Analysis
