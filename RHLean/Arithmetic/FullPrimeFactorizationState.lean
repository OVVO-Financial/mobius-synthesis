import Mathlib

/-!
# Full prime-factorization semantics for Möbius parity

This module is the semantic guardrail for every parent/cofactor construction in
this development.

A product display `n = c * q` is a transport edge between two distinct natural
numbers.  It is **not** a two-prime factorization unless both `c` and `q` are
prime.  Möbius parity is always computed from the complete prime factorization
of `n`, with multiplicity exposed.

For example, `102 = 6 * 17` is a valid transport edge, but the complete prime
factorization is `102 = 2 * 3 * 17`.  Hence its full factor depth is three, not
two.  The parent `6` and child `102` remain different Möbius arguments.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- Complete prime-factor depth, counting prime factors with multiplicity.

This is the arithmetic-function `Ω(n)`.  It must not be replaced by the number
of visible factors in a compressed product such as `n = c * q`. -/
def fullPrimeFactorDepth (n : ℕ) : ℕ :=
  ArithmeticFunction.cardFactors n

/-- Distinct prime-factor depth `ω(n)`.  On squarefree integers this agrees with
`fullPrimeFactorDepth`; outside the squarefree support it does not determine the
Möbius value by parity. -/
def distinctPrimeFactorDepth (n : ℕ) : ℕ :=
  ArithmeticFunction.cardDistinctFactors n

/-- The complete set of distinct primes occurring in the factorization of `n`.
Multiplicity is separately retained by `fullPrimeFactorDepth`. -/
def fullPrimeSupport (n : ℕ) : Finset ℕ :=
  n.primeFactors

/-- On the squarefree support, Möbius is exactly parity of the complete prime
factorization depth. -/
theorem moebius_eq_negOnePow_fullPrimeFactorDepth
    {n : ℕ} (hsq : Squarefree n) :
    μ n = (-1 : ℤ) ^ fullPrimeFactorDepth n := by
  simpa [fullPrimeFactorDepth] using
    ArithmeticFunction.moebius_apply_of_squarefree hsq

/-- Repeated prime factors force Möbius value zero. -/
theorem moebius_eq_zero_of_not_squarefree_fullState
    {n : ℕ} (hsq : ¬ Squarefree n) :
    μ n = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq

/-- For a squarefree integer, the product of the complete prime support is the
integer itself.  This is the formal statement that the factorization must be
fully expanded into primes before parity is read. -/
theorem prod_fullPrimeSupport_eq
    {n : ℕ} (hsq : Squarefree n) :
    ∏ p ∈ fullPrimeSupport n, p = n := by
  simpa [fullPrimeSupport] using Nat.prod_primeFactors_of_squarefree hsq

/-- On squarefree integers, complete factor depth and distinct-prime depth
coincide. -/
theorem fullPrimeFactorDepth_eq_distinctPrimeFactorDepth
    {n : ℕ} (hsq : Squarefree n) :
    fullPrimeFactorDepth n = distinctPrimeFactorDepth n := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  symm
  simpa [fullPrimeFactorDepth, distinctPrimeFactorDepth] using
    (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn0).2 hsq

/-- A compressed product record is only a transport statement.  The parent and
child are separate Möbius arguments, and this structure deliberately contains
no factor-depth field. -/
structure PrimeTransportEdge where
  parent : ℕ
  terminal : ℕ
  terminal_prime : terminal.Prime
  child : ℕ
  product_eq : parent * terminal = child

namespace PrimeTransportEdge

/-- A fresh transport edge flips the Möbius value.  This theorem is a recurrence
between two complete arithmetic states; it does not count `parent` as one prime
factor. -/
theorem moebius_child_eq_neg_parent
    (e : PrimeTransportEdge) (hfresh : ¬ e.terminal ∣ e.parent) :
    μ e.child = -μ e.parent := by
  have hcop : Nat.Coprime e.parent e.terminal :=
    (e.terminal_prime.coprime_iff_not_dvd).2 hfresh |>.symm
  calc
    μ e.child = μ (e.parent * e.terminal) := by rw [e.product_eq]
    _ = μ e.parent * μ e.terminal :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    _ = μ e.parent * (-1) := by
      rw [ArithmeticFunction.moebius_apply_prime e.terminal_prime]
    _ = -μ e.parent := by ring

/-- If the terminal prime already occurs in the complete parent factorization,
the child contains a repeated prime and has Möbius value zero. -/
theorem moebius_child_eq_zero_of_collision
    (e : PrimeTransportEdge) (hcollision : e.terminal ∣ e.parent) :
    μ e.child = 0 := by
  obtain ⟨k, hk⟩ := hcollision
  have hsq : e.terminal * e.terminal ∣ e.child := by
    refine ⟨k, ?_⟩
    calc
      e.child = e.parent * e.terminal := e.product_eq.symm
      _ = (e.terminal * k) * e.terminal := by rw [hk]
      _ = (e.terminal * e.terminal) * k := by ac_rfl
  have hnot : ¬ Squarefree e.child := by
    intro hs
    exact e.terminal_prime.not_isUnit (hs e.terminal hsq)
  exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot

end PrimeTransportEdge

/-- The finite square block `[m²,(m+1)²)`. -/
def fullFactorSquareBlock (m : ℕ) : Finset ℕ :=
  Finset.Ico (m ^ 2) ((m + 1) ^ 2)

/-- Nonzero Möbius support of a square block. -/
def fullFactorSquareBlockSupport (m : ℕ) : Finset ℕ :=
  (fullFactorSquareBlock m).filter fun n => μ n ≠ 0

/-- Full prime depths represented on the nonzero support of a square block. -/
def fullFactorSquareBlockDepthValues (m : ℕ) : Finset ℕ :=
  (fullFactorSquareBlockSupport m).image fullPrimeFactorDepth

/-- The squarefree population at complete prime depth `k`. -/
def fullFactorSquareBlockDepthFiber (m k : ℕ) : Finset ℕ :=
  (fullFactorSquareBlockSupport m).filter fun n => fullPrimeFactorDepth n = k

/-- Population count at complete prime depth `k`. -/
def fullFactorSquareBlockDepthCount (m k : ℕ) : ℕ :=
  (fullFactorSquareBlockDepthFiber m k).card

/-- Exact elementary depth-parity identity for a square block.

Every nonzero Möbius term is grouped by its complete prime-factor depth.  No
analytic estimate is used. -/
theorem squareBlockMoebius_eq_fullDepthParity (m : ℕ) :
    ∑ n ∈ fullFactorSquareBlock m, μ n =
      ∑ k ∈ fullFactorSquareBlockDepthValues m,
        (fullFactorSquareBlockDepthCount m k : ℤ) * (-1 : ℤ) ^ k := by
  classical
  have hmaps :
      ∀ n ∈ fullFactorSquareBlockSupport m,
        fullPrimeFactorDepth n ∈ fullFactorSquareBlockDepthValues m := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  calc
    (∑ n ∈ fullFactorSquareBlock m, μ n) =
        ∑ n ∈ fullFactorSquareBlockSupport m, μ n := by
      unfold fullFactorSquareBlockSupport
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hμ : μ n = 0
      · simp [hμ]
      · simp [hμ]
    _ = ∑ n ∈ fullFactorSquareBlockSupport m,
          (-1 : ℤ) ^ fullPrimeFactorDepth n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnData : n ∈ fullFactorSquareBlock m ∧ μ n ≠ 0 := by
        simpa [fullFactorSquareBlockSupport] using hn
      have hsq : Squarefree n :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hnData.2
      exact moebius_eq_negOnePow_fullPrimeFactorDepth hsq
    _ = ∑ k ∈ fullFactorSquareBlockDepthValues m,
          (fullFactorSquareBlockDepthCount m k : ℤ) * (-1 : ℤ) ^ k := by
      unfold fullFactorSquareBlockDepthCount fullFactorSquareBlockDepthFiber
      calc
        (∑ n ∈ fullFactorSquareBlockSupport m,
            (-1 : ℤ) ^ fullPrimeFactorDepth n) =
          ∑ k ∈ fullFactorSquareBlockDepthValues m,
            ∑ _n ∈ fullFactorSquareBlockSupport m with
                fullPrimeFactorDepth _n = k,
              (-1 : ℤ) ^ k := by
            simpa using
              (Finset.sum_fiberwise_of_maps_to'
                (s := fullFactorSquareBlockSupport m)
                (t := fullFactorSquareBlockDepthValues m)
                (g := fullPrimeFactorDepth)
                hmaps
                (fun k : ℕ => (-1 : ℤ) ^ k)).symm
        _ = ∑ k ∈ fullFactorSquareBlockDepthValues m,
              (((fullFactorSquareBlockSupport m).filter fun n =>
                  fullPrimeFactorDepth n = k).card : ℤ) * (-1 : ℤ) ^ k := by
            apply Finset.sum_congr rfl
            intro k hk
            simp

/-! ## Phase 1: explicit certified full-factorization state

`FullFactorizationState` makes the complete prime factorization a first-class
certified object.  Every Möbius/depth reader below takes the state, so a
compressed transport display `n = c * q` can never be read as a two-prime
factorization: the state always carries `n.factorization` with multiplicity.
-/

/-- The canonical complete-factorization state of a natural number.  It carries
`Nat.factorization` together with a proof that this finsupp is the true
factorization of `value`; the proof field makes the state unique per `value`. -/
structure FullFactorizationState where
  value : ℕ
  factorization : ℕ →₀ ℕ
  is_canonical : factorization = value.factorization

namespace FullFactorizationState

/-- Canonical constructor from a natural number. -/
def canonical (n : ℕ) : FullFactorizationState := ⟨n, n.factorization, rfl⟩

@[simp] theorem canonical_value (n : ℕ) : (canonical n).value = n := rfl

@[simp] theorem canonical_factorization (n : ℕ) :
    (canonical n).factorization = n.factorization := rfl

/-- Uniqueness / proof irrelevance: a state is determined by its value. -/
theorem eq_of_value_eq {s t : FullFactorizationState}
    (h : s.value = t.value) : s = t := by
  obtain ⟨sv, sf, hs⟩ := s
  obtain ⟨tv, tf, ht⟩ := t
  subst hs ht
  cases h
  rfl

@[simp] theorem canonical_value_self (s : FullFactorizationState) :
    canonical s.value = s :=
  eq_of_value_eq (by simp)

/-- Complete prime support of the state. -/
def support (s : FullFactorizationState) : Finset ℕ := s.factorization.support

/-- Prime-factor count with multiplicity, `Ω`, read from the complete
factorization (mathlib's `cardFactors`). -/
def bigOmega (s : FullFactorizationState) : ℕ :=
  fullPrimeFactorDepth s.value

/-- Distinct prime-factor count, `ω` (mathlib's `cardDistinctFactors`). -/
def omega (s : FullFactorizationState) : ℕ :=
  distinctPrimeFactorDepth s.value

/-- Squarefree state: no prime occurs with exponent `≥ 2`. -/
def IsSquarefreeState (s : FullFactorizationState) : Prop :=
  ∀ p, s.factorization p ≤ 1

/-- State-native Möbius sign: the alternating parity of the distinct-prime count
on the squarefree support, and zero otherwise. -/
noncomputable def moebiusSign (s : FullFactorizationState) : ℤ :=
  if Squarefree s.value then (-1 : ℤ) ^ s.omega else 0

/-- Support elements are prime. -/
theorem prime_of_mem_support (s : FullFactorizationState) {p : ℕ}
    (hp : p ∈ s.support) : p.Prime := by
  rw [support, s.is_canonical, Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

/-- The state support is exactly the complete prime set of the value. -/
theorem support_eq_primeFactors (s : FullFactorizationState) :
    s.support = s.value.primeFactors := by
  rw [support, s.is_canonical, Nat.support_factorization]

/-- The complete factorization reconstructs the value (nonzero value). -/
theorem prod_pow_factorization_eq (s : FullFactorizationState)
    (hn : s.value ≠ 0) :
    s.factorization.prod (fun p e => p ^ e) = s.value := by
  rw [s.is_canonical]
  exact Nat.factorization_prod_pow_eq_self hn

/-- `bigOmega` is exactly `cardFactors`. -/
theorem bigOmega_eq_cardFactors (s : FullFactorizationState) :
    s.bigOmega = ArithmeticFunction.cardFactors s.value := rfl

/-- `omega` is exactly `cardDistinctFactors`. -/
theorem omega_eq_cardDistinctFactors (s : FullFactorizationState) :
    s.omega = ArithmeticFunction.cardDistinctFactors s.value := rfl

/-- On a squarefree value, complete and distinct depth agree. -/
theorem bigOmega_eq_omega_of_squarefree (s : FullFactorizationState)
    (hsq : Squarefree s.value) : s.bigOmega = s.omega :=
  fullPrimeFactorDepth_eq_distinctPrimeFactorDepth hsq

/-- On a nonzero value, the state squarefree predicate matches squarefreeness. -/
theorem isSquarefreeState_iff (s : FullFactorizationState) (hn : s.value ≠ 0) :
    IsSquarefreeState s ↔ Squarefree s.value := by
  rw [IsSquarefreeState, s.is_canonical]
  exact (Nat.squarefree_iff_factorization_le_one hn).symm

/-- `μ` of the value equals the state-native Möbius sign. -/
theorem moebius_eq_moebiusSign (s : FullFactorizationState) :
    μ s.value = s.moebiusSign := by
  rw [moebiusSign]
  by_cases hsq : Squarefree s.value
  · rw [if_pos hsq, omega,
      ← fullPrimeFactorDepth_eq_distinctPrimeFactorDepth hsq]
    exact moebius_eq_negOnePow_fullPrimeFactorDepth hsq
  · rw [if_neg hsq]
    exact moebius_eq_zero_of_not_squarefree_fullState hsq

/-- Repeated prime exponents force Möbius value zero. -/
theorem moebius_eq_zero_of_not_isSquarefreeState (s : FullFactorizationState)
    (hn : s.value ≠ 0) (h : ¬ IsSquarefreeState s) : μ s.value = 0 := by
  apply moebius_eq_zero_of_not_squarefree_fullState
  rwa [isSquarefreeState_iff s hn] at h

end FullFactorizationState

/-- A certified transport edge: parent and child each carry a complete
factorization state, the terminal prime is appended, and the child factorization
is the explicit parent-plus-one-prime update.  There is deliberately no
factor-depth field: depth is always read from the states. -/
structure FullPrimeTransportEdge where
  parent : ℕ
  child : ℕ
  terminal : ℕ
  terminal_prime : terminal.Prime
  parentState : FullFactorizationState
  childState : FullFactorizationState
  parentState_value : parentState.value = parent
  childState_value : childState.value = child
  product_eq : parent * terminal = child
  factorization_update :
    childState.factorization
      = parentState.factorization + Finsupp.single terminal 1

namespace FullPrimeTransportEdge

/-- The canonical fresh transport edge `n ↦ n * q` for a prime `q` and `n ≠ 0`. -/
def ofCanonical (n q : ℕ) (hq : q.Prime) (hn : n ≠ 0) : FullPrimeTransportEdge where
  parent := n
  child := n * q
  terminal := q
  terminal_prime := hq
  parentState := FullFactorizationState.canonical n
  childState := FullFactorizationState.canonical (n * q)
  parentState_value := rfl
  childState_value := rfl
  product_eq := rfl
  factorization_update := by
    simp only [FullFactorizationState.canonical_factorization]
    rw [Nat.factorization_mul hn hq.ne_zero, hq.factorization]

theorem child_ne_zero (e : FullPrimeTransportEdge) : e.child ≠ 0 := by
  intro h0
  have hzero : e.childState.factorization = 0 := by
    rw [e.childState.is_canonical, e.childState_value, h0, Nat.factorization_zero]
  rw [e.factorization_update] at hzero
  have hcontra := congrArg (fun f => f e.terminal) hzero
  simp at hcontra

theorem parent_ne_zero (e : FullPrimeTransportEdge) : e.parent ≠ 0 := by
  intro h0
  exact e.child_ne_zero (by rw [← e.product_eq, h0, zero_mul])

/-- A fresh extension increases `bigOmega` by exactly one. -/
theorem bigOmega_child_eq_succ (e : FullPrimeTransportEdge) :
    e.childState.bigOmega = e.parentState.bigOmega + 1 := by
  rw [FullFactorizationState.bigOmega, FullFactorizationState.bigOmega,
    e.parentState_value, e.childState_value, fullPrimeFactorDepth,
    fullPrimeFactorDepth, ← e.product_eq,
    ArithmeticFunction.cardFactors_mul e.parent_ne_zero e.terminal_prime.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime e.terminal_prime]

/-- A fresh extension flips the Möbius sign. -/
theorem moebius_child_eq_neg_parent (e : FullPrimeTransportEdge)
    (hfresh : ¬ e.terminal ∣ e.parent) :
    μ e.child = -μ e.parent := by
  have hcop : Nat.Coprime e.parent e.terminal :=
    (e.terminal_prime.coprime_iff_not_dvd).2 hfresh |>.symm
  calc
    μ e.child = μ (e.parent * e.terminal) := by rw [e.product_eq]
    _ = μ e.parent * μ e.terminal :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    _ = μ e.parent * (-1) := by
      rw [ArithmeticFunction.moebius_apply_prime e.terminal_prime]
    _ = -μ e.parent := by ring

/-- A collision makes the terminal exponent at least two in the child state. -/
theorem two_le_child_factorization_terminal (e : FullPrimeTransportEdge)
    (hcollision : e.terminal ∣ e.parent) :
    2 ≤ e.childState.factorization e.terminal := by
  have hpar : 1 ≤ e.parentState.factorization e.terminal := by
    rw [e.parentState.is_canonical, e.parentState_value]
    exact (Nat.Prime.factorization_pos_of_dvd e.terminal_prime e.parent_ne_zero
      hcollision)
  have := congrArg (fun f => f e.terminal) e.factorization_update
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
  omega

/-- A collision therefore gives Möbius value zero. -/
theorem moebius_child_eq_zero_of_collision (e : FullPrimeTransportEdge)
    (hcollision : e.terminal ∣ e.parent) :
    μ e.child = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  have hchild : Squarefree e.childState.value := by rw [e.childState_value]; exact hsq
  have := (FullFactorizationState.isSquarefreeState_iff e.childState
    (by rw [e.childState_value]; exact e.child_ne_zero)).2 hchild
  have h2 := two_le_child_factorization_terminal e hcollision
  have := this e.terminal
  omega

end FullPrimeTransportEdge

end RHLean.Arithmetic
