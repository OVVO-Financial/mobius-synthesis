import Mathlib
import RHLean.Arithmetic.SquareBlockParityPopulation
import RHLean.Proof.CanonicalSignedParent

/-!
# One-block invariant architecture

Square blocks `1` and `2` are the fixed seed. Their union is `{1, 2, 3}`:
block `1 = [1,2)` contains no primes and block `2 = [2,4)` contains `2,3`.
Every block from `3` onward is inherited from canonical full-factorization
parents in the frozen earlier carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Old frozen parent cutoff used for target square block `a`. -/
def oldParentCutoff (a : ℕ) : ℕ :=
  (a ^ 2 - 1) / 2

/-- Every prime factor is bounded by the canonical largest prime factor. -/
theorem primeFactor_le_canonicalLargestPrimeFactor
    {n p : ℕ} (hn : 1 < n) (hp : p ∈ n.primeFactors) :
    p ≤ canonicalLargestPrimeFactor n := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hn]
  exact Finset.le_max' n.primeFactors p hp

/-- Above `2`, the canonical largest prime factor is at least `3`. -/
theorem three_le_canonicalLargestPrimeFactor
    {n : ℕ} (hsq : Squarefree n) (hn : 2 < n) :
    3 ≤ canonicalLargestPrimeFactor n := by
  have hn1 : 1 < n := by omega
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hqTwo : 2 ≤ canonicalLargestPrimeFactor n := hqPrime.two_le
  by_contra hcontra
  have hqEq : canonicalLargestPrimeFactor n = 2 := by omega
  have hfaces : n.primeFactors = {2} := by
    ext p
    constructor
    · intro hp
      have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpTwo : 2 ≤ p := hpPrime.two_le
      have hpLe : p ≤ canonicalLargestPrimeFactor n :=
        primeFactor_le_canonicalLargestPrimeFactor hn1 hp
      have hpEq : p = 2 := by omega
      simp [hpEq]
    · intro hp
      have hpEq : p = 2 := by simpa using hp
      subst p
      simpa [hqEq] using canonicalLargestPrimeFactor_mem_primeFactors hn1
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  rw [hfaces] at hprod
  simp at hprod
  omega

/-- The first block after the fixed seed already uses only the frozen carrier. -/
theorem canonicalCofactor_le_oldParentCutoff_three
    {n : ℕ} (hn : n ∈ squareBlockInterval 3)
    (hsq : Squarefree n) (hn1 : 1 < n) :
    canonicalCofactor n ≤ oldParentCutoff 3 := by
  have hnBounds : 9 ≤ n ∧ n < 16 := by
    simpa [squareBlockInterval, Finset.mem_Ico] using hn
  have hn2 : 2 < n := by omega
  have hq3 : 3 ≤ canonicalLargestPrimeFactor n :=
    three_le_canonicalLargestPrimeFactor hsq hn2
  have hprod := canonicalCofactor_mul_largestPrimeFactor hn1
  have hthree : 3 * canonicalCofactor n ≤ n := by
    calc
      3 * canonicalCofactor n = canonicalCofactor n * 3 := by omega
      _ ≤ canonicalCofactor n * canonicalLargestPrimeFactor n :=
        Nat.mul_le_mul_left _ hq3
      _ = n := hprod
  change canonicalCofactor n ≤ 4
  by_contra hnot
  have hcEq : canonicalCofactor n = 5 := by omega
  have hqEq : canonicalLargestPrimeFactor n = 3 := by
    nlinarith [hprod]
  have hnEq : n = 15 := by
    nlinarith [hprod]
  have h5 : 5 ∈ n.primeFactors := by
    subst n
    norm_num
  have h5le : 5 ≤ canonicalLargestPrimeFactor n :=
    primeFactor_le_canonicalLargestPrimeFactor hn1 h5
  omega

/-- The second block after the fixed seed already uses only the frozen carrier. -/
theorem canonicalCofactor_le_oldParentCutoff_four
    {n : ℕ} (hn : n ∈ squareBlockInterval 4)
    (hsq : Squarefree n) (hn1 : 1 < n) :
    canonicalCofactor n ≤ oldParentCutoff 4 := by
  have hnBounds : 16 ≤ n ∧ n < 25 := by
    simpa [squareBlockInterval, Finset.mem_Ico] using hn
  have hn2 : 2 < n := by omega
  have hq3 : 3 ≤ canonicalLargestPrimeFactor n :=
    three_le_canonicalLargestPrimeFactor hsq hn2
  have hprod := canonicalCofactor_mul_largestPrimeFactor hn1
  have hthree : 3 * canonicalCofactor n ≤ n := by
    calc
      3 * canonicalCofactor n = canonicalCofactor n * 3 := by omega
      _ ≤ canonicalCofactor n * canonicalLargestPrimeFactor n :=
        Nat.mul_le_mul_left _ hq3
      _ = n := hprod
  change canonicalCofactor n ≤ 7
  by_contra hnot
  have hcEq : canonicalCofactor n = 8 := by omega
  have hcSq : Squarefree (canonicalCofactor n) :=
    squarefree_canonicalCofactor hsq hn1
  rw [hcEq] at hcSq
  norm_num [Squarefree] at hcSq
  have hbad := hcSq 2 (by norm_num)
  norm_num at hbad

/-- **Uniform prior-carrier theorem.** Blocks `1` and `2` are the fixed seed;
every square block `a ≥ 3` is inherited from the frozen old parent carrier. -/
theorem canonicalCofactor_le_oldParentCutoff
    {a n : ℕ} (ha : 3 ≤ a)
    (hn : n ∈ squareBlockInterval a)
    (hsq : Squarefree n) (hn1 : 1 < n) :
    canonicalCofactor n ≤ oldParentCutoff a := by
  rcases lt_trichotomy a 5 with haLt | haEq | haGt
  · have haCases : a = 3 ∨ a = 4 := by omega
    rcases haCases with rfl | rfl
    · exact canonicalCofactor_le_oldParentCutoff_three hn hsq hn1
    · exact canonicalCofactor_le_oldParentCutoff_four hn hsq hn1
  · subst a
    have hnBounds : 5 ^ 2 ≤ n ∧ n < (5 + 1) ^ 2 := by
      simpa [squareBlockInterval, Finset.mem_Ico] using hn
    have hn2 : 2 < n := by omega
    have hq3 : 3 ≤ canonicalLargestPrimeFactor n :=
      three_le_canonicalLargestPrimeFactor hsq hn2
    have hprod := canonicalCofactor_mul_largestPrimeFactor hn1
    have hthree : 3 * canonicalCofactor n ≤ n := by
      calc
        3 * canonicalCofactor n = canonicalCofactor n * 3 := by omega
        _ ≤ canonicalCofactor n * canonicalLargestPrimeFactor n :=
          Nat.mul_le_mul_left _ hq3
        _ = n := hprod
    change canonicalCofactor n ≤ (5 ^ 2 - 1) / 2
    omega
  · have ha5 : 5 ≤ a := by omega
    have hnBounds : a ^ 2 ≤ n ∧ n < (a + 1) ^ 2 := by
      simpa [squareBlockInterval, Finset.mem_Ico] using hn
    have hn2 : 2 < n := by
      have : 9 ≤ a ^ 2 := by nlinarith
      omega
    have hq3 : 3 ≤ canonicalLargestPrimeFactor n :=
      three_le_canonicalLargestPrimeFactor hsq hn2
    have hprod := canonicalCofactor_mul_largestPrimeFactor hn1
    have hthree : 3 * canonicalCofactor n ≤ n := by
      calc
        3 * canonicalCofactor n = canonicalCofactor n * 3 := by omega
        _ ≤ canonicalCofactor n * canonicalLargestPrimeFactor n :=
          Nat.mul_le_mul_left _ hq3
        _ = n := hprod
    have h5a : 5 * a ≤ a * a := Nat.mul_le_mul_right a ha5
    have hquad : 4 * a + 2 ≤ a ^ 2 := by
      rw [pow_two]
      omega
    have hscale : 2 * (a + 1) ^ 2 ≤ 3 * a ^ 2 := by
      nlinarith
    have htwoLt : 2 * canonicalCofactor n < a ^ 2 := by
      nlinarith
    have htwoLe : canonicalCofactor n * 2 ≤ a ^ 2 - 1 := by
      omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 htwoLe

/-- Full-factorization inheritance statement for one square block. -/
def PriorCarrierDeterminesBlock (a : ℕ) : Prop :=
  ∀ n : ℕ, n ∈ squareBlockInterval a → Squarefree n → 1 < n →
    canonicalCofactor n ≤ oldParentCutoff a ∧
    μ n = -μ (canonicalCofactor n) ∧
    (FullFactorizationState.canonical n).omega =
      (FullFactorizationState.canonical (canonicalCofactor n)).omega + 1

/-- Once the parent-cutoff estimate is available, all sign and parity parts of
one-block inheritance follow from the full-factorization bridge. -/
theorem priorCarrierDeterminesBlock_of_parent_bound
    {a : ℕ}
    (hbound : ∀ n : ℕ, n ∈ squareBlockInterval a → Squarefree n → 1 < n →
      canonicalCofactor n ≤ oldParentCutoff a) :
    PriorCarrierDeterminesBlock a := by
  intro n hn hsq hn1
  exact ⟨hbound n hn hsq hn1,
    canonicalSignedParent_moebius hsq hn1,
    canonicalSignedParent_omega_succ hsq hn1⟩

/-- Every square block after seed blocks `1` and `2` is completely determined by
the frozen prior carrier. -/
theorem priorCarrierDeterminesBlock
    {a : ℕ} (ha : 3 ≤ a) : PriorCarrierDeterminesBlock a :=
  priorCarrierDeterminesBlock_of_parent_bound
    (fun _ hn hsq hn1 => canonicalCofactor_le_oldParentCutoff ha hn hsq hn1)

/-- Exact cumulative discrepancy after the first `N` square blocks. -/
def completedBlockPrefixSum : ℕ → ℤ
  | 0 => 0
  | N + 1 => completedBlockPrefixSum N + squareBlockMoebius (N + 1)

@[simp] theorem completedBlockPrefixSum_zero : completedBlockPrefixSum 0 = 0 := rfl

@[simp] theorem completedBlockPrefixSum_succ (N : ℕ) :
    completedBlockPrefixSum (N + 1) =
      completedBlockPrefixSum N + squareBlockMoebius (N + 1) := rfl

structure OneBlockInvariant (N : ℕ) where
  nextBlockInherited : PriorCarrierDeterminesBlock (N + 1)
  signedFrontier : ℤ
  signedFrontier_eq_prefix : signedFrontier = completedBlockPrefixSum N
  energyBudget : ℕ
  energy_control : signedFrontier ^ 2 ≤ (energyBudget : ℤ)

structure OneBlockExtensionData (N : ℕ) (hN : OneBlockInvariant N) where
  followingBlockInherited : PriorCarrierDeterminesBlock (N + 2)
  nextSignedFrontier : ℤ
  frontier_update :
    nextSignedFrontier = hN.signedFrontier + squareBlockMoebius (N + 1)
  nextEnergyBudget : ℕ
  next_energy_control : nextSignedFrontier ^ 2 ≤ (nextEnergyBudget : ℤ)

def oneBlockInvariant_succ
    {N : ℕ} (hN : OneBlockInvariant N)
    (hstep : OneBlockExtensionData N hN) :
    OneBlockInvariant (N + 1) where
  nextBlockInherited := hstep.followingBlockInherited
  signedFrontier := hstep.nextSignedFrontier
  signedFrontier_eq_prefix := by
    calc
      hstep.nextSignedFrontier =
          hN.signedFrontier + squareBlockMoebius (N + 1) := hstep.frontier_update
      _ = completedBlockPrefixSum N + squareBlockMoebius (N + 1) := by
          rw [hN.signedFrontier_eq_prefix]
      _ = completedBlockPrefixSum (N + 1) := by
          rw [completedBlockPrefixSum_succ]
  energyBudget := hstep.nextEnergyBudget
  energy_control := hstep.next_energy_control

def OneBlockExtensionLaw : Prop :=
  ∀ N : ℕ, ∀ hN : OneBlockInvariant N,
    Nonempty (OneBlockExtensionData N hN)

theorem oneBlockInvariant_all
    (h0 : OneBlockInvariant 0)
    (hlaw : OneBlockExtensionLaw) :
    ∀ N : ℕ, Nonempty (OneBlockInvariant N) := by
  intro N
  induction N with
  | zero => exact ⟨h0⟩
  | succ N ih =>
      obtain ⟨hN⟩ := ih
      obtain ⟨hstep⟩ := hlaw N hN
      exact ⟨oneBlockInvariant_succ hN hstep⟩

def OneBlockInvariantClosureStatement : Prop :=
  Nonempty (OneBlockInvariant 0) ∧ OneBlockExtensionLaw

end RHLean.Proof
