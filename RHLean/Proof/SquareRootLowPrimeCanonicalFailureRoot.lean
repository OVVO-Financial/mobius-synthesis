import Mathlib
import RHLean.Proof.SquareRootLowPrimeSecondToggleCharge

/-!
# Canonical least-failing roots

The sequential residual should not be charged once for every prime coordinate.
For a last still-admissible root state `n <= B`, collect all fresh primes whose
extension leaves the cutoff and select the least one:

`a(n) = min {p : K < p <= U, p prime, p ∤ n, B < p*n}`.

This single root state already records the complete chronology.

* If `P+(n) < a(n)`, no prime inserted after `a(n)` occurs in `n`; this is the
  first-failure/no-toggle orientation.
* If `a(n) < P+(n)`, one or more later prime pivots occur in `n`; this is the
  unstable orientation.

Equality is impossible because `a(n)` is fresh for `n`, whereas `P+(n)` divides
`n` when `n>1` (and equals `1` when `n=1`).  Thus the two nominal residual
classes are a disjoint partition of one root set.  Their *combined* cardinality
is at most `B`, with no multiplicity from the number of later primes and no need
to identify which local pivot first exposed the state.

This is the global assignment promised by the sequential architecture: later
pivots are encoded in the prime factorization of `n`, but the residual is
charged once, to `n` itself.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Membership in the fresh failure-prime set, with every condition exposed. -/
@[simp] theorem mem_squareRootLowPrimeFailurePrimeCandidates
    {K U B n p : ℕ} :
    p ∈ squareRootLowPrimeFailurePrimeCandidates K U B n ↔
      K < p ∧ p ≤ U ∧ p.Prime ∧ (¬ p ∣ n) ∧ B < p * n := by
  simp only [squareRootLowPrimeFailurePrimeCandidates,
    Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-- The canonical least failing prime is an actual candidate whenever the
candidate set is nonempty. -/
theorem squareRootLowPrimeCanonicalFailurePrime_mem
    {K U B n : ℕ}
    (h : (squareRootLowPrimeFailurePrimeCandidates K U B n).Nonempty) :
    squareRootLowPrimeCanonicalFailurePrime K U B n ∈
      squareRootLowPrimeFailurePrimeCandidates K U B n := by
  unfold squareRootLowPrimeCanonicalFailurePrime
  rw [dif_pos h]
  exact Finset.min'_mem _ h

/-- Complete arithmetic data of the canonical least failing prime. -/
theorem squareRootLowPrimeCanonicalFailurePrime_data
    {K U B n : ℕ}
    (h : (squareRootLowPrimeFailurePrimeCandidates K U B n).Nonempty) :
    K < squareRootLowPrimeCanonicalFailurePrime K U B n ∧
      squareRootLowPrimeCanonicalFailurePrime K U B n ≤ U ∧
      (squareRootLowPrimeCanonicalFailurePrime K U B n).Prime ∧
      (¬ squareRootLowPrimeCanonicalFailurePrime K U B n ∣ n) ∧
      B < squareRootLowPrimeCanonicalFailurePrime K U B n * n := by
  exact mem_squareRootLowPrimeFailurePrimeCandidates.mp
    (squareRootLowPrimeCanonicalFailurePrime_mem h)

/-- A root state carrying at least one fresh failure prime. -/
def SquareRootLowPrimeCanonicalFailureRootData
    (K U B n : ℕ) : Prop :=
  0 < n ∧ n ≤ B ∧
    (squareRootLowPrimeFailurePrimeCandidates K U B n).Nonempty

/-- The canonical failing prime cannot equal the root's canonical largest prime
factor. -/
theorem squareRootLowPrimeCanonicalFailurePrime_ne_lpf
    {K U B n : ℕ}
    (hroot : SquareRootLowPrimeCanonicalFailureRootData K U B n) :
    squareRootLowPrimeCanonicalFailurePrime K U B n ≠
      canonicalLargestPrimeFactor n := by
  rcases hroot with ⟨hnPos, _hnB, hfail⟩
  rcases squareRootLowPrimeCanonicalFailurePrime_data hfail with
    ⟨_hK, _hU, haPrime, haFresh, _haFail⟩
  intro heq
  by_cases hnOne : n = 1
  · subst n
    have haOne : squareRootLowPrimeCanonicalFailurePrime K U B 1 = 1 := by
      simpa [canonicalLargestPrimeFactor] using heq
    exact haPrime.ne_one haOne
  · have hnGt : 1 < n := by omega
    apply haFresh
    rw [heq]
    exact canonicalLargestPrimeFactor_dvd hnGt

/-- **Exhaustive chronological dichotomy.**  Every canonical failure root is
uniquely either no-toggle or unstable. -/
theorem squareRootLowPrimeCanonicalFailureRoot_orientation
    {K U B n : ℕ}
    (hroot : SquareRootLowPrimeCanonicalFailureRootData K U B n) :
    canonicalLargestPrimeFactor n <
        squareRootLowPrimeCanonicalFailurePrime K U B n ∨
      squareRootLowPrimeCanonicalFailurePrime K U B n <
        canonicalLargestPrimeFactor n := by
  have hne := squareRootLowPrimeCanonicalFailurePrime_ne_lpf hroot
  omega

/-- Canonical roots in the first-failure/no-toggle orientation. -/
def squareRootLowPrimeCanonicalNoToggleRoots
    (K U B : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter fun n =>
    canonicalLargestPrimeFactor n <
      squareRootLowPrimeCanonicalFailurePrime K U B n

/-- Canonical roots containing at least one later unstable pivot. -/
def squareRootLowPrimeCanonicalUnstableRoots
    (K U B : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter fun n =>
    squareRootLowPrimeCanonicalFailurePrime K U B n <
      canonicalLargestPrimeFactor n

/-- The two orientations are disjoint because their strict inequalities point
in opposite directions. -/
theorem squareRootLowPrimeCanonicalNoToggleRoots_disjoint_unstable
    (K U B : ℕ) (S : Finset ℕ) :
    Disjoint (squareRootLowPrimeCanonicalNoToggleRoots K U B S)
      (squareRootLowPrimeCanonicalUnstableRoots K U B S) := by
  rw [Finset.disjoint_left]
  intro n hn hu
  rcases Finset.mem_filter.mp hn with ⟨_hnS, hnlt⟩
  rcases Finset.mem_filter.mp hu with ⟨_huS, hult⟩
  omega

/-- Under the canonical failure-root hypothesis, no-toggle and unstable roots
exhaust the original root carrier. -/
theorem squareRootLowPrimeCanonicalRoots_eq_noToggle_union_unstable
    {K U B : ℕ} (S : Finset ℕ)
    (hdata : ∀ n ∈ S,
      SquareRootLowPrimeCanonicalFailureRootData K U B n) :
    S = squareRootLowPrimeCanonicalNoToggleRoots K U B S ∪
      squareRootLowPrimeCanonicalUnstableRoots K U B S := by
  ext n
  constructor
  · intro hn
    rcases squareRootLowPrimeCanonicalFailureRoot_orientation
      (hdata n hn) with hno | hunstable
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hn, hno⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hn, hunstable⟩
  · intro hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact (Finset.mem_filter.mp hn).1
    · exact (Finset.mem_filter.mp hn).1

/-- Every canonical failure-root carrier injects into the root interval by the
identity map. -/
theorem squareRootLowPrimeCanonicalFailureRoots_card_le_bound
    {K U B : ℕ} (S : Finset ℕ)
    (hdata : ∀ n ∈ S,
      SquareRootLowPrimeCanonicalFailureRootData K U B n) :
    S.card ≤ B := by
  have hsub : S ⊆ Finset.Icc 1 B := by
    intro n hn
    have h := hdata n hn
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt h.1), h.2.1⟩
  calc
    S.card ≤ (Finset.Icc 1 B).card := Finset.card_le_card hsub
    _ = B := by simp

/-- **Combined no-toggle plus instability cardinality bound.**  Later unstable
pivots do not create a second population: both orientations together have at
most one state per root integer. -/
theorem squareRootLowPrimeCanonicalNoToggle_card_add_unstable_card_le_bound
    {K U B : ℕ} (S : Finset ℕ)
    (hdata : ∀ n ∈ S,
      SquareRootLowPrimeCanonicalFailureRootData K U B n) :
    (squareRootLowPrimeCanonicalNoToggleRoots K U B S).card +
        (squareRootLowPrimeCanonicalUnstableRoots K U B S).card ≤ B := by
  have hdisj :=
    squareRootLowPrimeCanonicalNoToggleRoots_disjoint_unstable K U B S
  have hunion :=
    squareRootLowPrimeCanonicalRoots_eq_noToggle_union_unstable S hdata
  calc
    (squareRootLowPrimeCanonicalNoToggleRoots K U B S).card +
        (squareRootLowPrimeCanonicalUnstableRoots K U B S).card =
      (squareRootLowPrimeCanonicalNoToggleRoots K U B S ∪
        squareRootLowPrimeCanonicalUnstableRoots K U B S).card := by
          symm
          exact Finset.card_union_of_disjoint hdisj
    _ = S.card := by rw [← hunion]
    _ ≤ B := squareRootLowPrimeCanonicalFailureRoots_card_le_bound S hdata

end RHLean.Proof
