import Mathlib
import RHLean.Proof.AlternatingSignMatchingParity
import RHLean.Proof.GlobalPrefixCarrierOthello

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Adaptive carrier-wide matching, and why a raw prefix carrier cannot carry one

`RHLean.Proof.GlobalPrefixCarrierOthello` plays one prime toggle across a whole
region.  That freezes the prime coordinate: the same `p` is used at every state,
so the matching is a family of two cycles chosen in advance.

The Othello notion the no-liberty architecture actually uses is different.  A
state may be matched along *any* prime edge

```text
n <-> n * p        or        n <-> n / p,
```

with the prime allowed to depend on the state, subject only to both endpoints
choosing each other.  This file isolates that notion.

* `AdaptivePrimeMate S m` says `m` preserves `S`, is involutive on `S`, and
  moves only along prime-toggle edges.  Sign reversal is then a *consequence*,
  not an extra hypothesis: a toggle that moves cannot be a square hit.
* `HasLiberty S n` says some prime edge at `n` moves and lands inside `S`, and
  `trueNoLibertyBoundary S` collects the states with no legal move left anywhere
  in the geometry.  This is the boundary notion the route wants, and it is
  strictly stronger than "my mate under one selected prime is outside".
* A no-liberty state is fixed by every adaptive mate, so the true boundary is
  always contained in the fixed set; the two coincide exactly when the mate is
  liberty exhausting.

The second half of the file shows the raw prefix carrier `(0, x]` is the wrong
geometry for this, in two independent ways.

* **No liberty-exhausting mate exists.**  Every squarefree site of `(0, x]` has
  a legal move — divide out its least prime factor, or at `1` multiply one in —
  so the true no-liberty boundary consists of square hits only and carries no
  Möbius mass at all.  A liberty-exhausting mate would therefore force
  `M(x) = 0`.
* **Every adaptive mate has a large fixed set.**  A prime `p` with `x < 2p` has
  exactly one legal move in `(0, x]`, namely `p -> 1`, because every other prime
  edge overshoots `x`.  All such primes compete for the single site `1`, and an
  involution can serve at most one of them, so the fixed set of *any* adaptive
  mate on `(0, x]` has at least `(number of primes in (x/2, x]) - 1` states.

Neither statement uses an estimate or an asymptotic input.  Together they say
the state-dependent freedom alone does not rescue a raw interval carrier: the
carrier itself has to retain the geometry that restricts which moves are legal.

**How to use this file.**  It is a *negative control*, not a template.  The raw
integer prime-toggle graph has the wrong capacity structure: thousands of
top-half primes share the single neighbour `1`.  The processed-seat carrier
replaces an arithmetic object by a population of response seats carrying the
relevant multiplicities, which is exactly the kind of enlargement that removes a
star bottleneck.  So the content here is

```text
raw carrier impossible  =>  processed multiplicity is mathematically load-bearing.
```

Do **not** port `AdaptivePrimeMate` to the processed-seat state.  That carrier
already has `squareRootLowPrimeProcessedSeatNoLibertyMate`, whose stable
population is already proved literally equal to the descending terminal
frontier, and `SquareRootLowPrimeNoLibertyFiniteEquiv` starts from that fact.
Re-deriving an abstraction of it would replace something concrete the repository
already knows.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Liberties and the true boundary -/

/-- A legal Othello move at `n` inside the carrier `S`: some prime toggle that
actually moves `n` and lands back inside `S`. -/
def HasLiberty (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ primeCarrierToggle p n ≠ n ∧ primeCarrierToggle p n ∈ S

/-- The true no-liberty boundary: states of the carrier with no legal
sign-reversing move remaining anywhere in the geometry. -/
def trueNoLibertyBoundary (S : Finset ℕ) : Finset ℕ :=
  S.filter fun n => ¬ HasLiberty S n

@[simp] theorem mem_trueNoLibertyBoundary {S : Finset ℕ} {n : ℕ} :
    n ∈ trueNoLibertyBoundary S ↔ n ∈ S ∧ ¬ HasLiberty S n :=
  Finset.mem_filter

/-! ## Adaptive mates -/

/-- A carrier-wide matching whose move at each state may use a different prime.

The prime is not part of the data: only the requirement that every move is
*some* legal prime edge, and that the two endpoints of a move choose each
other, which is exactly involutivity. -/
structure AdaptivePrimeMate (S : Finset ℕ) (m : ℕ → ℕ) : Prop where
  maps : ∀ n ∈ S, m n ∈ S
  involutive : ∀ n ∈ S, m (m n) = n
  isPrimeToggle : ∀ n ∈ S, m n ≠ n → ∃ p : ℕ, p.Prime ∧ m n = primeCarrierToggle p n

/-- **Sign reversal is automatic.**  A prime toggle that moves a state cannot be
a square hit, so it reverses the Möbius sign.  No separate hypothesis is
needed. -/
theorem AdaptivePrimeMate.moebius_neg
    {S : Finset ℕ} {m : ℕ → ℕ} (h : AdaptivePrimeMate S m)
    {n : ℕ} (hn : n ∈ S) (hne : m n ≠ n) :
    μ (m n) = -μ n := by
  obtain ⟨p, hp, hmp⟩ := h.isPrimeToggle n hn hne
  rw [hmp] at hne ⊢
  have hsq : ¬ p ^ 2 ∣ n := fun hd => hne (primeCarrierToggle_of_sq_dvd hd)
  exact moebius_primeCarrierToggle hp hsq

/-- **Adaptive global Othello theorem.**  The whole signed mass of the carrier
is the mass of the states the adaptive matching leaves fixed. -/
theorem sum_moebius_eq_fixed_of_adaptivePrimeMate
    {S : Finset ℕ} {m : ℕ → ℕ} (h : AdaptivePrimeMate S m) :
    (∑ n ∈ S, μ n) = ∑ n ∈ signMatchingFixedPart S m, μ n :=
  sum_eq_sum_signMatchingFixedPart S m (fun n => μ n) h.maps h.involutive
    fun _ hn hne => h.moebius_neg hn hne

/-- A state with no liberty is fixed by every adaptive mate. -/
theorem trueNoLibertyBoundary_subset_fixed
    {S : Finset ℕ} {m : ℕ → ℕ} (h : AdaptivePrimeMate S m) :
    trueNoLibertyBoundary S ⊆ signMatchingFixedPart S m := by
  intro n hn
  obtain ⟨hnS, hlib⟩ := mem_trueNoLibertyBoundary.mp hn
  refine mem_signMatchingFixedPart.mpr ⟨hnS, ?_⟩
  by_contra hne
  obtain ⟨p, hp, hmp⟩ := h.isPrimeToggle n hnS hne
  refine hlib ⟨p, hp, ?_, ?_⟩
  · rw [← hmp]; exact hne
  · rw [← hmp]; exact h.maps n hnS

/-- A matching exhausts liberties when it fixes only states that have none. -/
def LibertyExhausting (S : Finset ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ n ∈ S, m n = n → ¬ HasLiberty S n

/-- For a liberty-exhausting mate the fixed set is exactly the true boundary. -/
theorem fixed_eq_trueNoLibertyBoundary
    {S : Finset ℕ} {m : ℕ → ℕ} (h : AdaptivePrimeMate S m)
    (hex : LibertyExhausting S m) :
    signMatchingFixedPart S m = trueNoLibertyBoundary S := by
  apply Finset.Subset.antisymm
  · intro n hn
    obtain ⟨hnS, hfix⟩ := mem_signMatchingFixedPart.mp hn
    exact mem_trueNoLibertyBoundary.mpr ⟨hnS, hex n hnS hfix⟩
  · exact trueNoLibertyBoundary_subset_fixed h

/-- **The global prefix no-liberty theorem, as a conditional.**  A
liberty-exhausting adaptive matching would put the entire signed mass of the
carrier on its true no-liberty boundary. -/
theorem sum_moebius_eq_trueNoLibertyBoundary
    {S : Finset ℕ} {m : ℕ → ℕ} (h : AdaptivePrimeMate S m)
    (hex : LibertyExhausting S m) :
    (∑ n ∈ S, μ n) = ∑ n ∈ trueNoLibertyBoundary S, μ n := by
  rw [sum_moebius_eq_fixed_of_adaptivePrimeMate h, fixed_eq_trueNoLibertyBoundary h hex]

/-- The fixed-prime construction is the constant-selector special case: on the
part of a region whose `p`-mates stay inside, one frozen prime coordinate is an
adaptive mate. -/
theorem adaptivePrimeMate_primeCarrierToggle
    {p : ℕ} (hp : p.Prime) (S : Finset ℕ) :
    AdaptivePrimeMate (primeInteriorPart p S) (primeCarrierToggle p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨hnS, hmate⟩ := mem_primeInteriorPart.mp hn
    refine mem_primeInteriorPart.mpr ⟨hmate, ?_⟩
    rw [primeCarrierToggle_involutive hp n]
    exact hnS
  · exact fun n _ => primeCarrierToggle_involutive hp n
  · exact fun n _ _ => ⟨p, hp, rfl⟩

/-! ## The raw prefix carrier admits no liberty-exhausting mate -/

/-- Every squarefree site of a prefix carrier has a legal move: divide out its
least prime factor, or, at `1`, multiply a prime in. -/
theorem hasLiberty_Ioc_of_squarefree
    {x n : ℕ} (hx : 2 ≤ x) (hn : n ∈ Finset.Ioc 0 x) (hsf : Squarefree n) :
    HasLiberty (Finset.Ioc 0 x) n := by
  obtain ⟨hpos, hnx⟩ := Finset.mem_Ioc.mp hn
  by_cases hone : n = 1
  · subst hone
    have hnd : ¬ (2 : ℕ) ∣ 1 := by decide
    refine ⟨2, Nat.prime_two, ?_, ?_⟩
    · rw [primeCarrierToggle_of_not_dvd hnd]; decide
    · rw [primeCarrierToggle_of_not_dvd hnd]
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  · have hp : (Nat.minFac n).Prime := Nat.minFac_prime hone
    have hdvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have hsq : ¬ (Nat.minFac n) ^ 2 ∣ n := by
      intro hd
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf _ hp)
        (by simpa [pow_two] using hd)
    refine ⟨Nat.minFac n, hp, ?_, ?_⟩
    · rw [primeCarrierToggle_of_dvd hdvd hsq]
      exact Nat.ne_of_lt (Nat.div_lt_self hpos hp.one_lt)
    · rw [primeCarrierToggle_of_dvd hdvd hsq]
      refine Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hpos hdvd) hp.pos, ?_⟩
      exact le_trans (Nat.div_le_self n _) hnx

/-- **The true boundary of a raw prefix carrier carries no Möbius mass.**  Only
square hits can be liberty free there. -/
theorem sum_moebius_trueNoLibertyBoundary_Ioc_eq_zero
    {x : ℕ} (hx : 2 ≤ x) :
    (∑ n ∈ trueNoLibertyBoundary (Finset.Ioc 0 x), μ n) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro n hn
  obtain ⟨hnS, hlib⟩ := mem_trueNoLibertyBoundary.mp hn
  by_contra hmu
  exact hlib (hasLiberty_Ioc_of_squarefree hx hnS
    (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu))

/-- **First no-go.**  Whenever the prefix carries nonzero Möbius mass, no
adaptive matching on it can exhaust liberties. -/
theorem not_libertyExhausting_Ioc_of_sum_ne_zero
    {x : ℕ} (hx : 2 ≤ x) (hM : (∑ n ∈ Finset.Ioc 0 x, μ n) ≠ 0)
    {m : ℕ → ℕ} (h : AdaptivePrimeMate (Finset.Ioc 0 x) m) :
    ¬ LibertyExhausting (Finset.Ioc 0 x) m := by
  intro hex
  exact hM (by
    rw [sum_moebius_eq_trueNoLibertyBoundary h hex,
      sum_moebius_trueNoLibertyBoundary_Ioc_eq_zero hx])

/-! ## Every adaptive mate on a raw prefix carrier has a large fixed set -/

/-- Primes in the top half of a prefix carrier. -/
def topHalfPrimes (x : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 x).filter fun p => p.Prime ∧ x < 2 * p

@[simp] theorem mem_topHalfPrimes {x p : ℕ} :
    p ∈ topHalfPrimes x ↔ p ∈ Finset.Ioc 0 x ∧ p.Prime ∧ x < 2 * p :=
  Finset.mem_filter

private theorem not_sq_dvd_self_of_prime {q : ℕ} (hq : q.Prime) :
    ¬ q ^ 2 ∣ q := by
  intro hd
  have hle : q ^ 2 ≤ q := Nat.le_of_dvd hq.pos hd
  have hsq : q * q ≤ q := by rwa [pow_two] at hle
  have hgrow : q * 2 ≤ q * q := Nat.mul_le_mul (le_refl q) hq.two_le
  have hpos : 0 < q := hq.pos
  linarith

/-- **A top-half prime has exactly one legal move.**  Dividing by itself lands
on `1`; every other prime edge overshoots the cutoff. -/
theorem primeCarrierToggle_topHalfPrime_eq_one
    {x p q : ℕ} (hp : p ∈ topHalfPrimes x) (hq : q.Prime)
    (hmem : primeCarrierToggle q p ∈ Finset.Ioc 0 x) :
    primeCarrierToggle q p = 1 := by
  obtain ⟨_hpIoc, hpPrime, hhalf⟩ := mem_topHalfPrimes.mp hp
  by_cases hqp : q = p
  · rw [hqp,
      primeCarrierToggle_of_dvd dvd_rfl (not_sq_dvd_self_of_prime hpPrime)]
    exact Nat.div_self hpPrime.pos
  · exfalso
    have hnd : ¬ q ∣ p := by
      intro hd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq hpPrime).mp hd)
    rw [primeCarrierToggle_of_not_dvd hnd] at hmem
    have hgrow : p * 2 ≤ p * q := Nat.mul_le_mul (le_refl p) hq.two_le
    have hupper := (Finset.mem_Ioc.mp hmem).2
    linarith

/-- **Second no-go, quantitative.**  Every adaptive matching on the raw prefix
carrier leaves all but at most one top-half prime fixed, because they all have
the same unique legal move.  No choice of state-dependent primes avoids this. -/
theorem card_topHalfPrimes_le_fixedCard_succ
    {x : ℕ} {m : ℕ → ℕ} (h : AdaptivePrimeMate (Finset.Ioc 0 x) m) :
    (topHalfPrimes x).card ≤
      (signMatchingFixedPart (Finset.Ioc 0 x) m).card + 1 := by
  have hmapsOne : ∀ p ∈ (topHalfPrimes x).filter fun p => m p ≠ p, m p = 1 := by
    intro p hpA
    have hp : p ∈ topHalfPrimes x := (Finset.mem_filter.mp hpA).1
    have hne : m p ≠ p := (Finset.mem_filter.mp hpA).2
    have hpS : p ∈ Finset.Ioc 0 x := (mem_topHalfPrimes.mp hp).1
    obtain ⟨q, hq, hmq⟩ := h.isPrimeToggle p hpS hne
    have hmemS : primeCarrierToggle q p ∈ Finset.Ioc 0 x := by
      rw [← hmq]; exact h.maps p hpS
    rw [hmq]
    exact primeCarrierToggle_topHalfPrime_eq_one hp hq hmemS
  have hAcard : ((topHalfPrimes x).filter fun p => m p ≠ p).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have hpa : a ∈ Finset.Ioc 0 x :=
      (mem_topHalfPrimes.mp (Finset.mem_filter.mp ha).1).1
    have hpb : b ∈ Finset.Ioc 0 x :=
      (mem_topHalfPrimes.mp (Finset.mem_filter.mp hb).1).1
    have hmab : m a = m b := by rw [hmapsOne a ha, hmapsOne b hb]
    calc a = m (m a) := (h.involutive a hpa).symm
      _ = m (m b) := by rw [hmab]
      _ = b := h.involutive b hpb
  have hsub : topHalfPrimes x ⊆
      signMatchingFixedPart (Finset.Ioc 0 x) m ∪
        (topHalfPrimes x).filter fun p => m p ≠ p := by
    intro p hp
    have hpS : p ∈ Finset.Ioc 0 x := (mem_topHalfPrimes.mp hp).1
    by_cases hfix : m p = p
    · exact Finset.mem_union.mpr
        (Or.inl (mem_signMatchingFixedPart.mpr ⟨hpS, hfix⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp, hfix⟩))
  calc (topHalfPrimes x).card ≤
        (signMatchingFixedPart (Finset.Ioc 0 x) m ∪
          (topHalfPrimes x).filter fun p => m p ≠ p).card :=
        Finset.card_le_card hsub
    _ ≤ (signMatchingFixedPart (Finset.Ioc 0 x) m).card +
          ((topHalfPrimes x).filter fun p => m p ≠ p).card :=
        Finset.card_union_le _ _
    _ ≤ (signMatchingFixedPart (Finset.Ioc 0 x) m).card + 1 :=
        Nat.add_le_add_left hAcard _

end RHLean.Proof
