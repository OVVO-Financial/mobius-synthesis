import Mathlib
import RHLean.Proof.CollisionCellFrontierBound
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren

/-!
# Canonical fresh-prime matching of the complete signed response children

`SquareRootLowPrimeSignedResponseChildren` identifies the exact deep increment
with one restricted Möbius sum over arithmetic children.  The raw carrier can
still have quadratic cardinality.  The relevant object is therefore not its
support size but the frontier left after every available fresh-prime sign flip
has been used.

For a finite child set `S` and a fresh prime `ell`, this file pairs

`n <-> ell*n`

whenever both integers lie in `S` and `ell` does not divide `n`.  Möbius
multiplicativity gives

`mu(ell*n) = -mu(n)`,

so the paired population has exactly zero signed mass.  Removing one such
coordinate therefore preserves the complete Möbius sum.  Iterating through the
fresh primes gives a canonical finite frontier with exactly the same signed
mass as the original response-child carrier.

The final quantitative reduction is

`|sum_{n in response children} mu(n)| <= #(matched frontier)`.

Thus the needed estimate is a cardinality theorem for the complete sequential
frontier, not an absolute bound for all response atoms.  The order of matching
coordinates is explicit but the cancellation theorem holds for every prime
list.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Lower endpoints of the available `ell`-edges inside a finite carrier. -/
def squareRootLowPrimeResponsePairLower
    (S : Finset ℕ) (ell : ℕ) : Finset ℕ :=
  S.filter fun n => ¬ ell ∣ n ∧ ell * n ∈ S

/-- Upper endpoints of the available `ell`-edges. -/
def squareRootLowPrimeResponsePairUpper
    (S : Finset ℕ) (ell : ℕ) : Finset ℕ :=
  (squareRootLowPrimeResponsePairLower S ell).image fun n => ell * n

/-- Complete population removed by one fresh-prime matching step. -/
def squareRootLowPrimeResponsePaired
    (S : Finset ℕ) (ell : ℕ) : Finset ℕ :=
  squareRootLowPrimeResponsePairLower S ell ∪
    squareRootLowPrimeResponsePairUpper S ell

/-- Frontier remaining after one fresh-prime matching step. -/
def squareRootLowPrimeResponseFrontierStep
    (S : Finset ℕ) (ell : ℕ) : Finset ℕ :=
  S \ squareRootLowPrimeResponsePaired S ell

@[simp] theorem mem_squareRootLowPrimeResponsePairLower
    {S : Finset ℕ} {ell n : ℕ} :
    n ∈ squareRootLowPrimeResponsePairLower S ell ↔
      n ∈ S ∧ ¬ ell ∣ n ∧ ell * n ∈ S := by
  simp [squareRootLowPrimeResponsePairLower]

/-- Every lower endpoint lies in the original carrier. -/
theorem squareRootLowPrimeResponsePairLower_subset
    (S : Finset ℕ) (ell : ℕ) :
    squareRootLowPrimeResponsePairLower S ell ⊆ S := by
  intro n hn
  exact (mem_squareRootLowPrimeResponsePairLower.mp hn).1

/-- Every upper endpoint lies in the original carrier. -/
theorem squareRootLowPrimeResponsePairUpper_subset
    (S : Finset ℕ) (ell : ℕ) :
    squareRootLowPrimeResponsePairUpper S ell ⊆ S := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
  exact (mem_squareRootLowPrimeResponsePairLower.mp hn).2.2

/-- The whole paired population lies in the original carrier. -/
theorem squareRootLowPrimeResponsePaired_subset
    (S : Finset ℕ) (ell : ℕ) :
    squareRootLowPrimeResponsePaired S ell ⊆ S := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact squareRootLowPrimeResponsePairLower_subset S ell hn
  · exact squareRootLowPrimeResponsePairUpper_subset S ell hn

/-- Lower and upper endpoints of one prime coordinate are disjoint. -/
theorem squareRootLowPrimeResponsePairLower_disjoint_upper
    (S : Finset ℕ) (ell : ℕ) :
    Disjoint (squareRootLowPrimeResponsePairLower S ell)
      (squareRootLowPrimeResponsePairUpper S ell) := by
  rw [Finset.disjoint_left]
  intro m hmLower hmUpper
  have hnot : ¬ ell ∣ m :=
    (mem_squareRootLowPrimeResponsePairLower.mp hmLower).2.1
  rcases Finset.mem_image.mp hmUpper with ⟨n, _hn, hmn⟩
  apply hnot
  exact ⟨n, hmn.symm⟩

/-- Multiplication by a positive fresh prime is injective. -/
theorem squareRootLowPrimeResponsePair_mul_injective
    {S : Finset ℕ} {ell : ℕ} (hell : ell.Prime) :
    Set.InjOn (fun n : ℕ => ell * n)
      (squareRootLowPrimeResponsePairLower S ell) := by
  intro a _ha b _hb hab
  exact Nat.mul_left_cancel hell.pos hab

/-- Fresh-prime multiplication reverses the Möbius sign. -/
theorem moebius_prime_mul_eq_neg_of_not_dvd
    {ell n : ℕ} (hell : ell.Prime) (hnot : ¬ ell ∣ n) :
    μ (ell * n) = -μ n := by
  have hcop : Nat.Coprime ell n :=
    (hell.coprime_iff_not_dvd).2 hnot
  calc
    μ (ell * n) = μ ell * μ n :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    _ = (-1) * μ n := by
      rw [ArithmeticFunction.moebius_apply_prime hell]
    _ = -μ n := by ring

/-- The upper endpoints carry the negative of the lower-endpoint Möbius mass. -/
theorem squareRootLowPrimeResponsePairUpper_moebiusSum_eq_neg_lower
    (S : Finset ℕ) {ell : ℕ} (hell : ell.Prime) :
    (∑ m ∈ squareRootLowPrimeResponsePairUpper S ell, μ m) =
      -∑ n ∈ squareRootLowPrimeResponsePairLower S ell, μ n := by
  unfold squareRootLowPrimeResponsePairUpper
  calc
    (∑ m ∈ (squareRootLowPrimeResponsePairLower S ell).image
        (fun n => ell * n), μ m) =
      ∑ n ∈ squareRootLowPrimeResponsePairLower S ell,
        μ (ell * n) := by
          apply Finset.sum_image
          intro a ha b hb hab
          exact squareRootLowPrimeResponsePair_mul_injective
            (S := S) hell ha hb hab
    _ = ∑ n ∈ squareRootLowPrimeResponsePairLower S ell,
        -μ n := by
          apply Finset.sum_congr rfl
          intro n hn
          exact moebius_prime_mul_eq_neg_of_not_dvd hell
            (mem_squareRootLowPrimeResponsePairLower.mp hn).2.1
    _ = -∑ n ∈ squareRootLowPrimeResponsePairLower S ell, μ n := by
      rw [Finset.sum_neg_distrib]

/-- One complete prime-coordinate matching has zero signed Möbius mass. -/
theorem squareRootLowPrimeResponsePaired_moebiusSum_eq_zero
    (S : Finset ℕ) {ell : ℕ} (hell : ell.Prime) :
    (∑ n ∈ squareRootLowPrimeResponsePaired S ell, μ n) = 0 := by
  unfold squareRootLowPrimeResponsePaired
  rw [Finset.sum_union
      (squareRootLowPrimeResponsePairLower_disjoint_upper S ell),
    squareRootLowPrimeResponsePairUpper_moebiusSum_eq_neg_lower S hell]
  ring

/-- The complement of the one-step frontier is exactly the paired population. -/
theorem squareRootLowPrimeResponse_sdiff_frontierStep_eq_paired
    (S : Finset ℕ) (ell : ℕ) :
    S \ squareRootLowPrimeResponseFrontierStep S ell =
      squareRootLowPrimeResponsePaired S ell := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_sdiff.mp hn with ⟨hnS, hnNotFrontier⟩
    by_contra hnNotPaired
    apply hnNotFrontier
    exact Finset.mem_sdiff.mpr ⟨hnS, hnNotPaired⟩
  · intro hnPaired
    have hnS := squareRootLowPrimeResponsePaired_subset S ell hnPaired
    apply Finset.mem_sdiff.mpr
    refine ⟨hnS, ?_⟩
    intro hnFrontier
    exact (Finset.mem_sdiff.mp hnFrontier).2 hnPaired

/-- One fresh-prime matching step preserves the complete signed Möbius mass. -/
theorem squareRootLowPrimeResponse_moebiusSum_eq_frontierStep
    (S : Finset ℕ) {ell : ℕ} (hell : ell.Prime) :
    (∑ n ∈ S, μ n) =
      ∑ n ∈ squareRootLowPrimeResponseFrontierStep S ell, μ n := by
  apply sum_eq_frontier_sum_of_complement_zero
    S (squareRootLowPrimeResponseFrontierStep S ell) (fun n => μ n)
  · intro n hn
    exact (Finset.mem_sdiff.mp hn).1
  · rw [squareRootLowPrimeResponse_sdiff_frontierStep_eq_paired]
    exact squareRootLowPrimeResponsePaired_moebiusSum_eq_zero S hell

/-- Iterate the matching step through an explicit ordered prime list. -/
def squareRootLowPrimeResponseMatchingFrontier :
    List ℕ → Finset ℕ → Finset ℕ
  | [], S => S
  | ell :: ells, S =>
      squareRootLowPrimeResponseMatchingFrontier ells
        (squareRootLowPrimeResponseFrontierStep S ell)

/-- Iterating prime-coordinate matchings preserves the complete Möbius mass. -/
theorem squareRootLowPrimeResponse_moebiusSum_eq_matchingFrontier
    (ells : List ℕ) (S : Finset ℕ)
    (hprime : ∀ ell ∈ ells, ell.Prime) :
    (∑ n ∈ S, μ n) =
      ∑ n ∈ squareRootLowPrimeResponseMatchingFrontier ells S, μ n := by
  induction ells generalizing S with
  | nil => simp [squareRootLowPrimeResponseMatchingFrontier]
  | cons ell ells ih =>
      have hell : ell.Prime := hprime ell (by simp)
      have hrest : ∀ q ∈ ells, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      calc
        (∑ n ∈ S, μ n) =
            ∑ n ∈ squareRootLowPrimeResponseFrontierStep S ell, μ n :=
          squareRootLowPrimeResponse_moebiusSum_eq_frontierStep S hell
        _ = ∑ n ∈
              squareRootLowPrimeResponseMatchingFrontier ells
                (squareRootLowPrimeResponseFrontierStep S ell), μ n :=
          ih (squareRootLowPrimeResponseFrontierStep S ell) hrest
        _ = ∑ n ∈
              squareRootLowPrimeResponseMatchingFrontier (ell :: ells) S,
                μ n := by
          rfl

/-- Fresh primes in increasing arithmetic order. -/
def squareRootLowPrimeFreshPrimeList (K U : ℕ) : List ℕ :=
  (squareRootLowPrimeFreshPrimeSet K U).sort (· ≤ ·)

/-- Every coordinate in the ordered fresh-prime list is prime. -/
theorem prime_of_mem_squareRootLowPrimeFreshPrimeList
    {K U ell : ℕ} (hell : ell ∈ squareRootLowPrimeFreshPrimeList K U) :
    ell.Prime := by
  have hset : ell ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hell
  exact (Finset.mem_filter.mp hset).2

/-- The complete sequentially matched response frontier. -/
def squareRootLowPrimeOwnedResponseMatchingFrontier
    (R K U : ℕ) : Finset ℕ :=
  squareRootLowPrimeResponseMatchingFrontier
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeOwnedResponseChildren R K U)

/-- **Exact complete-frontier reduction.**  The response-child Möbius mass is
supported entirely on the frontier left after every fresh-prime coordinate has
been processed. -/
theorem squareRootLowPrimeOwnedResponseChildren_moebiusSum_eq_matchingFrontier
    (R K U : ℕ) :
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n) =
      ∑ n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U, μ n := by
  unfold squareRootLowPrimeOwnedResponseMatchingFrontier
  apply squareRootLowPrimeResponse_moebiusSum_eq_matchingFrontier
  intro ell hell
  exact prime_of_mem_squareRootLowPrimeFreshPrimeList hell

/-- Möbius mass on a finite carrier is bounded by the carrier cardinality. -/
theorem abs_moebiusSum_le_card (S : Finset ℕ) :
    |∑ n ∈ S, μ n| ≤ (S.card : ℤ) := by
  calc
    |∑ n ∈ S, μ n| ≤ ∑ n ∈ S, |μ n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ S, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact ArithmeticFunction.abs_moebius_le_one
    _ = (S.card : ℤ) := by simp

/-- **Quantitative matching gate.**  Bounding the complete matched frontier is
sufficient to bound the entire signed response-child mass. -/
theorem abs_squareRootLowPrimeOwnedResponseChildren_moebiusSum_le_frontierCard
    (R K U : ℕ) :
    |∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n| ≤
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℤ) := by
  rw [squareRootLowPrimeOwnedResponseChildren_moebiusSum_eq_matchingFrontier]
  exact abs_moebiusSum_le_card
    (squareRootLowPrimeOwnedResponseMatchingFrontier R K U)

end RHLean.Proof
