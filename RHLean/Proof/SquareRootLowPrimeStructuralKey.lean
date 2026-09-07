import Mathlib
import RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv
import RHLean.Proof.SquareRootLowPrimeHorizontalTerminalCoverage

/-!
# Structural key for alternating processed-seat components

The final no-liberty classifier uses the union of the chronological and
descending Othello involutions.  Every genuine processed prime edge adjoins or
removes a prime strictly above the shallow packet depth `K`, while preserving
the absolute seat coordinate.

This file isolates the invariant carried by those alternating components.

* `SquareRootLowPrimeProcessedStateShallow/Deep` is the canonical split at
  `P+(c) <= K` versus `K < P+(c)`.
* `squareRootLowPrimeShallowBase K c = gcd(c,K!)` strips all fresh prime
  coordinates above `K` on the squarefree processed carrier.
* `squareRootLowPrimeProcessedSeatStructuralKey K x` is the pair consisting of
  that shallow base and the literal seat index.

The key is preserved by every fresh-prime extension and therefore by both full
Othello involutions.  No cardinality equivalence or numerical encoding is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Shallow processed cofactors: all of their visible prime support is at or
below the packet depth. -/
def SquareRootLowPrimeProcessedStateShallow
    (K : ℕ) (x : SquareRootLowPrimeProcessedState) : Prop :=
  canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) ≤ K

/-- Deep processed cofactors: at least one canonical prime coordinate lies
strictly above the packet depth. -/
def SquareRootLowPrimeProcessedStateDeep
    (K : ℕ) (x : SquareRootLowPrimeProcessedState) : Prop :=
  K < canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x)

instance (K : ℕ) (x : SquareRootLowPrimeProcessedState) :
    Decidable (SquareRootLowPrimeProcessedStateShallow K x) := by
  unfold SquareRootLowPrimeProcessedStateShallow
  infer_instance

instance (K : ℕ) (x : SquareRootLowPrimeProcessedState) :
    Decidable (SquareRootLowPrimeProcessedStateDeep K x) := by
  unfold SquareRootLowPrimeProcessedStateDeep
  infer_instance

/-- The shallow/deep split is exhaustive and disjoint. -/
theorem squareRootLowPrimeProcessedState_shallow_or_deep
    (K : ℕ) (x : SquareRootLowPrimeProcessedState) :
    SquareRootLowPrimeProcessedStateShallow K x ∨
      SquareRootLowPrimeProcessedStateDeep K x := by
  unfold SquareRootLowPrimeProcessedStateShallow
    SquareRootLowPrimeProcessedStateDeep
  omega

/-- Strip every prime coordinate above `K`. On the squarefree processed
carrier this is exactly the shallow prime factor of `c`; the gcd presentation
makes fresh-prime invariance elementary. -/
def squareRootLowPrimeShallowBase (K c : ℕ) : ℕ :=
  Nat.gcd c K.factorial

/-- On a squarefree cofactor whose prime support is already entirely shallow,
`shallowBase` recovers the cofactor itself.  This is the unique-factorization
endpoint of the alternating structural key. -/
theorem squareRootLowPrimeShallowBase_eq_self_of_squarefree_lpf_le
    {K c : ℕ} (hsq : Squarefree c)
    (hlpf : canonicalLargestPrimeFactor c ≤ K) :
    squareRootLowPrimeShallowBase K c = c := by
  unfold squareRootLowPrimeShallowBase
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd
    · exact Nat.dvd_refl c
    · apply (Nat.factorization_prime_le_iff_dvd
        hsq.ne_zero (Nat.factorial_ne_zero K)).mp
      intro p hp
      by_cases hpc : p ∣ c
      · have hcOne : c ≠ 1 := fun hc => by
          subst c
          exact hp.not_dvd_one hpc
        have hcGt : 1 < c := by
          have hcPos : 0 < c := Nat.pos_of_ne_zero hsq.ne_zero
          omega
        have hpMem : p ∈ c.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp, hpc, hsq.ne_zero⟩
        have hpLeLpf : p ≤ canonicalLargestPrimeFactor c := by
          unfold canonicalLargestPrimeFactor
          rw [dif_pos hcGt]
          exact Finset.le_max' c.primeFactors p hpMem
        have hpK : p ≤ K := hpLeLpf.trans hlpf
        rw [Nat.factorization_eq_one_of_squarefree hsq hp hpc]
        exact (hp.dvd_iff_one_le_factorization
          (Nat.factorial_ne_zero K)).mp
            (Nat.dvd_factorial hp.pos hpK)
      · rw [Nat.factorization_eq_zero_of_not_dvd hpc]
        exact Nat.zero_le _

/-- Raw seat coordinate. Prime-toggle edges alter only the cofactor and leave
this coordinate literally unchanged. -/
def squareRootLowPrimeProcessedSeatIndex :
    SquareRootLowPrimeProcessedState → ℕ
  | none => 0
  | some z => z.2

/-- Canonical component key: shallow arithmetic base together with the literal
seat coordinate. -/
def squareRootLowPrimeProcessedSeatStructuralKey
    (K : ℕ) (x : SquareRootLowPrimeProcessedState) : ℕ × ℕ :=
  (squareRootLowPrimeShallowBase K
      (squareRootLowPrimeProcessedStateCofactor x),
    squareRootLowPrimeProcessedSeatIndex x)

/-- A shallow non-head processed carrier state is literally reconstructed by
its structural key. -/
theorem squareRootLowPrimeProcessedSeatStructuralKey_eq_state_of_shallow
    {R K j U c s : ℕ}
    (hx : some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hshallow : canonicalLargestPrimeFactor c ≤ K) :
    squareRootLowPrimeProcessedSeatStructuralKey K (some (c, s)) = (c, s) := by
  have hatom : (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hx
  have hsigned := (mem_squareRootLowPrimeProcessedSeatAtoms.mp hatom).1
  have hmu : μ c ≠ 0 := (Finset.mem_filter.mp hsigned).2.2
  have hsq : Squarefree c :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
  have hbase :=
    squareRootLowPrimeShallowBase_eq_self_of_squarefree_lpf_le hsq hshallow
  simp [squareRootLowPrimeProcessedSeatStructuralKey,
    squareRootLowPrimeProcessedStateCofactor,
    squareRootLowPrimeProcessedSeatIndex, hbase]

/-- Adjoining one prime strictly above `K` does not change the shallow base. -/
theorem squareRootLowPrimeShallowBase_mul_fresh_prime
    {K c p : ℕ} (hp : p.Prime) (hKp : K < p) :
    squareRootLowPrimeShallowBase K (p * c) =
      squareRootLowPrimeShallowBase K c := by
  unfold squareRootLowPrimeShallowBase
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hdivMul : Nat.gcd (p * c) K.factorial ∣ p * c :=
        Nat.gcd_dvd_left _ _
      have hpCoprimeFact : p.Coprime K.factorial :=
        hp.coprime_factorial_of_lt hKp
      have hpCoprimeGcd : p.Coprime (Nat.gcd (p * c) K.factorial) :=
        hpCoprimeFact.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      exact hpCoprimeGcd.symm.dvd_of_dvd_mul_left hdivMul
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact (Nat.gcd_dvd_left c K.factorial).trans
        (Nat.dvd_mul_left c p)
    · exact Nat.gcd_dvd_right _ _

/-- Every fresh processed prime edge preserves the complete structural key. -/
theorem squareRootLowPrimeProcessedSeatStructuralKey_extend
    {K p : ℕ} (hp : p.Prime) (hKp : K < p)
    (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatStructuralKey K
        (squareRootLowPrimeProcessedSeatExtend p x) =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  rcases x with _ | z
  · rfl
  · simp only [squareRootLowPrimeProcessedSeatStructuralKey,
      squareRootLowPrimeProcessedStateCofactor,
      squareRootLowPrimeProcessedSeatExtend,
      squareRootLowPrimeProcessedSeatIndex]
    rw [squareRootLowPrimeShallowBase_mul_fresh_prime hp hKp]

/-- One completed prime-coordinate involution preserves the structural key in
both directions, including the upper-endpoint preimage branch. -/
theorem squareRootLowPrimeProcessedSeatStructuralKey_stepInvolution
    {K p : ℕ} (hp : p.Prime) (hKp : K < p)
    (S : Finset SquareRootLowPrimeProcessedState)
    (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatStructuralKey K
        (squareRootLowPrimeProcessedSeatStepInvolution S p x) =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p
  · have hstep :
        squareRootLowPrimeProcessedSeatStepInvolution S p x =
          squareRootLowPrimeProcessedSeatExtend p x := by
      dsimp only [squareRootLowPrimeProcessedSeatStepInvolution]
      rw [if_pos hxLower]
    rw [hstep]
    exact squareRootLowPrimeProcessedSeatStructuralKey_extend hp hKp x
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · let y := squareRootLowPrimeProcessedSeatPairPreimage S p x hupper
      have hy :
          y ∈ squareRootLowPrimeProcessedSeatPairLower S p ∧
            squareRootLowPrimeProcessedSeatExtend p y = x := by
        dsimp [y, squareRootLowPrimeProcessedSeatPairPreimage]
        exact Classical.choose_spec hupper
      have hstep :
          squareRootLowPrimeProcessedSeatStepInvolution S p x = y := by
        dsimp only [squareRootLowPrimeProcessedSeatStepInvolution]
        rw [if_neg hxLower, dif_pos hupper]
      rw [hstep, ← hy.2]
      exact (squareRootLowPrimeProcessedSeatStructuralKey_extend hp hKp y).symm
    · have hstep :
          squareRootLowPrimeProcessedSeatStepInvolution S p x = x := by
        dsimp only [squareRootLowPrimeProcessedSeatStepInvolution]
        rw [if_neg hxLower, dif_neg hupper]
      rw [hstep]

/-- A complete chronology made only of primes above `K` preserves the
structural key. -/
theorem squareRootLowPrimeProcessedSeatStructuralKey_matchingInvolution
    (K : ℕ) (ps : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime ∧ K < p)
    (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatStructuralKey K
        (squareRootLowPrimeProcessedSeatMatchingInvolution ps S x) =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  induction ps generalizing S x with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatMatchingInvolution]
  | cons p ps ih =>
      have hpData : p.Prime ∧ K < p := hprime p (by simp)
      have hrest : ∀ q ∈ ps, q.Prime ∧ K < q := by
        intro q hq
        exact hprime q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
      · rw [squareRootLowPrimeProcessedSeatMatchingInvolution]
        simp only [hxPaired, if_true]
        exact squareRootLowPrimeProcessedSeatStructuralKey_stepInvolution
          hpData.1 hpData.2 S x
      · rw [squareRootLowPrimeProcessedSeatMatchingInvolution]
        simp only [hxPaired, if_false]
        exact ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          hrest x

/-- Every chronological fresh-prime coordinate is prime and strictly above the
packet cutoff. -/
theorem squareRootLowPrimeFreshPrimeList_prime_and_above
    {K U p : ℕ} (hp : p ∈ squareRootLowPrimeFreshPrimeList K U) :
    p.Prime ∧ K < p := by
  have hset : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hp
  have hdata := Finset.mem_filter.mp hset
  exact ⟨hdata.2, (Finset.mem_Ioc.mp hdata.1).1⟩

/-- The same statement for the reversed prime order. -/
theorem squareRootLowPrimeFreshPrimeListDescending_prime_and_above
    {K U p : ℕ}
    (hp : p ∈ squareRootLowPrimeFreshPrimeListDescending K U) :
    p.Prime ∧ K < p := by
  have hpInc : p ∈ squareRootLowPrimeFreshPrimeList K U := by
    simpa [squareRootLowPrimeFreshPrimeListDescending] using hp
  exact squareRootLowPrimeFreshPrimeList_prime_and_above hpInc

/-- The increasing-order Othello mate on the common processed carrier. -/
noncomputable def squareRootLowPrimeProcessedSeatChronologicalMate
    (R K j U : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatMatchingInvolution
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- The structural key is invariant under the first Othello involution. -/
theorem squareRootLowPrimeProcessedSeatChronologicalMate_structuralKey
    (R K j U : ℕ) (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatStructuralKey K
        (squareRootLowPrimeProcessedSeatChronologicalMate R K j U x) =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  unfold squareRootLowPrimeProcessedSeatChronologicalMate
  apply squareRootLowPrimeProcessedSeatStructuralKey_matchingInvolution
  intro p hp
  exact squareRootLowPrimeFreshPrimeList_prime_and_above hp

/-- The structural key is invariant under the descending Othello involution. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_structuralKey
    (R K j U : ℕ) (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatStructuralKey K
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x) =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  unfold squareRootLowPrimeProcessedSeatNoLibertyMate
  apply squareRootLowPrimeProcessedSeatStructuralKey_matchingInvolution
  intro p hp
  exact squareRootLowPrimeFreshPrimeListDescending_prime_and_above hp

end RHLean.Proof
