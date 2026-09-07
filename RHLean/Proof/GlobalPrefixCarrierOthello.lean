import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.MutableSupportBound

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Global Othello cancellation on a whole cumulative carrier

The sitewise Othello laws say what one move does: a first-power hit of a
selected prime reverses the sign of a site, and a square hit kills it.  Applied
term by term those laws describe the distribution of individual Möbius values,
which is not what a cumulative sum asks about.  `M(x)` asks whether an entire
ordered prefix retains a coherent imbalance, and a term-by-term estimate throws
that away the moment an absolute value is taken.

This file plays the same two laws on the whole region at once.

Fix a prime `p` and define the *carrier toggle*

```text
tau_p(n) = n * p        if p does not divide n
           n / p        if p divides n but p ^ 2 does not
           n            if p ^ 2 divides n.
```

This is an involution of `ℕ`.  Its moving states are exactly the sites free of
`p ^ 2`, where `mu (tau_p n) = - mu n`; its frozen states are exactly the sites
killed by a square hit, where `mu n = 0`.  So on any finite region closed under
`tau_p` the entire signed Möbius mass cancels in pairs.

For a region that is *not* closed the same argument still applies to the part
whose mate stays inside, and the conclusion is the global Othello statement

```text
sum over S of mu = sum over the escape part of S of mu,
```

where the escape part is the set of sites whose mate has left `S`.  Nothing is
estimated: this is an equality, and the whole interior of `S` contributes
exactly zero.

The scope is worth stating precisely, because it is narrower than the Othello
picture it is named after.  For one fixed `p` every orbit of `tau_p` is a two
cycle or a fixed point, so this is a global *pairing* of a cumulative region.
It is not a statement about long alternating components, and it contains no
birth-to-capture cancellation: there is no trajectory here, only a mate.  The
adaptive version, in which the prime is allowed to depend on the state, is
`RHLean.Proof.AdaptivePrimeMatching`.  The birth/death lifetime cancellation
over square time, where the length of a lifetime genuinely does drop out, is
`RHLean.Proof.LifetimeRunCancellation`.

Three consequences are recorded.

* A region closed under the toggle has signed mass exactly zero, so completing
  any region to a closed one makes its mass exactly minus the mass of the collar
  that was added.  A cumulative Mertens value is a boundary collar.
* On the cumulative prefix carrier `(L, x]` the escape part is exactly two
  explicit walls: the *anchor wall* of sites carrying one `p` whose quotient
  falls back past the fixed lower anchor, and the *cutoff wall* of `p`-free
  sites whose `p`-multiple overshoots the moving right endpoint.  So a whole
  prefix reduces to its two boundary walls.
* The construction iterates.  Peeling a list of distinguished primes one after
  another leaves the iterated boundary, and the signed mass of the original
  region is still exactly the signed mass of that iterated boundary.

No arithmetic estimate, asymptotic input or RH hypothesis appears here.  The
single-prime wall cardinalities proved at the end are honest but not yet a
saving; they are the quantity a later multiplicity theorem has to bound.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## The carrier toggle -/

/-- The distinguished-prime toggle on the whole integer carrier.

A site free of `p` gains one factor `p`, a site carrying exactly one `p` loses
it, and a site already carrying `p ^ 2` is frozen. -/
def primeCarrierToggle (p n : ℕ) : ℕ :=
  if p ^ 2 ∣ n then n else if p ∣ n then n / p else n * p

private theorem primeCarrier_mul_div_cancel_left {p m : ℕ} (hp : 0 < p) :
    p * m / p = m := by
  have h : p * (p * m / p) = p * m := Nat.mul_div_cancel' ⟨m, rfl⟩
  exact Nat.eq_of_mul_eq_mul_left hp h

private theorem primeCarrier_mul_div_cancel_right {p m : ℕ} (hp : 0 < p) :
    m * p / p = m := by
  rw [mul_comm]
  exact primeCarrier_mul_div_cancel_left hp

theorem primeCarrierToggle_of_sq_dvd {p n : ℕ} (h : p ^ 2 ∣ n) :
    primeCarrierToggle p n = n := by
  simp [primeCarrierToggle, h]

theorem primeCarrierToggle_of_dvd {p n : ℕ}
    (hdvd : p ∣ n) (hsq : ¬ p ^ 2 ∣ n) :
    primeCarrierToggle p n = n / p := by
  simp [primeCarrierToggle, hdvd, hsq]

theorem primeCarrierToggle_of_not_dvd {p n : ℕ} (hdvd : ¬ p ∣ n) :
    primeCarrierToggle p n = n * p := by
  have hsq : ¬ p ^ 2 ∣ n := by
    intro h
    exact hdvd ((dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans h)
  simp [primeCarrierToggle, hdvd, hsq]

/-- Dividing out the single `p` of a site free of `p ^ 2` leaves a site free
of `p`. -/
theorem not_dvd_div_of_not_sq_dvd {p n : ℕ}
    (hdvd : p ∣ n) (hsq : ¬ p ^ 2 ∣ n) :
    ¬ p ∣ n / p := by
  intro h
  obtain ⟨c, hc⟩ := h
  refine hsq ⟨c, ?_⟩
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hdvd
  calc n = p * (n / p) := hmul.symm
    _ = p * (p * c) := by rw [hc]
    _ = p ^ 2 * c := by ring

/-- Multiplying in a missing `p` never produces a `p ^ 2` hit. -/
theorem not_sq_dvd_mul_of_not_dvd {p n : ℕ} (hp : p.Prime) (hdvd : ¬ p ∣ n) :
    ¬ p ^ 2 ∣ n * p := by
  intro h
  obtain ⟨c, hc⟩ := h
  refine hdvd ⟨c, ?_⟩
  have hcancel : n * p = (p * c) * p := by
    rw [hc]; ring
  exact Nat.eq_of_mul_eq_mul_right hp.pos hcancel

/-- **The carrier toggle is an involution.** -/
theorem primeCarrierToggle_involutive {p : ℕ} (hp : p.Prime) (n : ℕ) :
    primeCarrierToggle p (primeCarrierToggle p n) = n := by
  by_cases hsq : p ^ 2 ∣ n
  · rw [primeCarrierToggle_of_sq_dvd hsq, primeCarrierToggle_of_sq_dvd hsq]
  · by_cases hdvd : p ∣ n
    · rw [primeCarrierToggle_of_dvd hdvd hsq,
        primeCarrierToggle_of_not_dvd (not_dvd_div_of_not_sq_dvd hdvd hsq),
        mul_comm]
      exact Nat.mul_div_cancel' hdvd
    · rw [primeCarrierToggle_of_not_dvd hdvd,
        primeCarrierToggle_of_dvd ⟨n, mul_comm n p⟩
          (not_sq_dvd_mul_of_not_dvd hp hdvd)]
      exact primeCarrier_mul_div_cancel_right hp.pos

/-- **Frozen states are exactly the square hits.**  Only the forward direction
needs the primality of `p`; it is the direction used to kill the stable part. -/
theorem sq_dvd_of_primeCarrierToggle_eq_self {p : ℕ} (hp : p.Prime) {n : ℕ}
    (h : primeCarrierToggle p n = n) : p ^ 2 ∣ n := by
  by_contra hsq
  by_cases hdvd : p ∣ n
  · rw [primeCarrierToggle_of_dvd hdvd hsq] at h
    have hn0 : n ≠ 0 := by
      intro h0
      exact hsq (by rw [h0]; exact dvd_zero _)
    have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    exact absurd h (Nat.ne_of_lt (Nat.div_lt_self hpos hp.one_lt))
  · rw [primeCarrierToggle_of_not_dvd hdvd] at h
    have hn0 : n ≠ 0 := by
      intro h0
      exact hdvd (by rw [h0]; exact dvd_zero _)
    have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    have h2 : n * 2 ≤ n * p := Nat.mul_le_mul (le_refl n) hp.two_le
    have h3 : n + n ≤ n * p := by
      have hrw : n * 2 = n + n := by ring
      rw [hrw] at h2
      exact h2
    have hlt : n < n * p := lt_of_lt_of_le (by omega) h3
    exact absurd h (Nat.ne_of_gt hlt)

/-- **The moving law.**  Away from a square hit the toggle reverses the Möbius
sign.  This is the Othello flip, stated once for the whole carrier. -/
theorem moebius_primeCarrierToggle {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hsq : ¬ p ^ 2 ∣ n) :
    μ (primeCarrierToggle p n) = -μ n := by
  by_cases hdvd : p ∣ n
  · obtain ⟨m, rfl⟩ := hdvd
    have hdvd' : p ∣ p * m := ⟨m, rfl⟩
    have hnotm : ¬ p ∣ m := by
      intro hm
      obtain ⟨c, rfl⟩ := hm
      exact hsq ⟨c, by ring⟩
    have htog : primeCarrierToggle p (p * m) = m := by
      rw [primeCarrierToggle_of_dvd hdvd' hsq]
      exact primeCarrier_mul_div_cancel_left hp.pos
    rw [htog]
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnotm
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    ring
  · rw [primeCarrierToggle_of_not_dvd hdvd]
    have hcop : Nat.Coprime n p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd).symm
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    ring

/-! ## The global Othello theorem on an arbitrary finite region -/

/-- Sites of a finite region whose distinguished-prime mate has left the
region.  This is the Othello boundary of the region. -/
def primeEscapePart (p : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter fun n => primeCarrierToggle p n ∉ S

/-- Sites of a finite region whose mate is still inside it. -/
def primeInteriorPart (p : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter fun n => primeCarrierToggle p n ∈ S

@[simp] theorem mem_primeEscapePart {p n : ℕ} {S : Finset ℕ} :
    n ∈ primeEscapePart p S ↔ n ∈ S ∧ primeCarrierToggle p n ∉ S :=
  Finset.mem_filter

@[simp] theorem mem_primeInteriorPart {p n : ℕ} {S : Finset ℕ} :
    n ∈ primeInteriorPart p S ↔ n ∈ S ∧ primeCarrierToggle p n ∈ S :=
  Finset.mem_filter

theorem primeEscapePart_subset (p : ℕ) (S : Finset ℕ) :
    primeEscapePart p S ⊆ S := Finset.filter_subset _ _

/-- **The interior of a region cancels exactly.**  Every moving state is paired
with a state of opposite Möbius sign, and every state the pairing freezes is a
square hit, which carries no Möbius mass at all.  No path length appears. -/
theorem sum_moebius_primeInteriorPart_eq_zero {p : ℕ} (hp : p.Prime)
    (S : Finset ℕ) :
    (∑ n ∈ primeInteriorPart p S, μ n) = 0 := by
  have hmem : ∀ x ∈ primeInteriorPart p S,
      primeCarrierToggle p x ∈ primeInteriorPart p S := by
    intro x hx
    obtain ⟨hxS, hmate⟩ := mem_primeInteriorPart.mp hx
    refine mem_primeInteriorPart.mpr ⟨hmate, ?_⟩
    rw [primeCarrierToggle_involutive hp x]
    exact hxS
  have hinv : ∀ x ∈ primeInteriorPart p S,
      primeCarrierToggle p (primeCarrierToggle p x) = x :=
    fun x _ => primeCarrierToggle_involutive hp x
  have hneg : ∀ x ∈ primeInteriorPart p S, primeCarrierToggle p x ≠ x →
      μ (primeCarrierToggle p x) = -μ x := by
    intro x _ hne
    have hsq : ¬ p ^ 2 ∣ x := fun h => hne (primeCarrierToggle_of_sq_dvd h)
    exact moebius_primeCarrierToggle hp hsq
  rw [sum_finiteOthelloRegion_eq_stable (primeInteriorPart p S)
    (primeCarrierToggle p) (fun n => μ n) hmem hinv hneg]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hfix : primeCarrierToggle p x = x := (Finset.mem_filter.mp hx).2
  have hsq : p ^ 2 ∣ x := sq_dvd_of_primeCarrierToggle_eq_self hp hfix
  refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
  intro hsf
  exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp)
    (by simpa [pow_two] using hsq)

/-- **Global Othello theorem.**  The entire signed Möbius mass of a finite
region sits on the boundary sites whose distinguished-prime mate has left the
region.  This is an exact identity, not an estimate. -/
theorem sum_moebius_eq_sum_primeEscapePart {p : ℕ} (hp : p.Prime)
    (S : Finset ℕ) :
    (∑ n ∈ S, μ n) = ∑ n ∈ primeEscapePart p S, μ n := by
  have hunion : primeInteriorPart p S ∪ primeEscapePart p S = S := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_union.mp hn with h | h
      · exact (mem_primeInteriorPart.mp h).1
      · exact (mem_primeEscapePart.mp h).1
    · intro hn
      by_cases hm : primeCarrierToggle p n ∈ S
      · exact Finset.mem_union.mpr (Or.inl (mem_primeInteriorPart.mpr ⟨hn, hm⟩))
      · exact Finset.mem_union.mpr (Or.inr (mem_primeEscapePart.mpr ⟨hn, hm⟩))
  have hdisj : Disjoint (primeInteriorPart p S) (primeEscapePart p S) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    exact (mem_primeEscapePart.mp hn').2 (mem_primeInteriorPart.mp hn).2
  calc (∑ n ∈ S, μ n)
      = ∑ n ∈ primeInteriorPart p S ∪ primeEscapePart p S, μ n := by
        rw [hunion]
    _ = (∑ n ∈ primeInteriorPart p S, μ n) +
          ∑ n ∈ primeEscapePart p S, μ n := Finset.sum_union hdisj
    _ = ∑ n ∈ primeEscapePart p S, μ n := by
        rw [sum_moebius_primeInteriorPart_eq_zero hp S, zero_add]

/-- **A region closed under the toggle carries no signed mass at all.**  This is
the pure Othello endgame: with no boundary there is nothing left to survive the
pairing. -/
theorem sum_moebius_eq_zero_of_toggleClosed {p : ℕ} (hp : p.Prime)
    {S : Finset ℕ} (hclosed : ∀ n ∈ S, primeCarrierToggle p n ∈ S) :
    (∑ n ∈ S, μ n) = 0 := by
  rw [sum_moebius_eq_sum_primeEscapePart hp S]
  refine Finset.sum_eq_zero ?_
  intro n hn
  obtain ⟨hnS, hout⟩ := mem_primeEscapePart.mp hn
  exact absurd (hclosed n hnS) hout

/-- **Completion form.**  Complete a region to a toggle-closed one; its mass is
then exactly minus the mass of the collar that was added.  Applied to a
cumulative prefix this says a Mertens value is a boundary collar, with no
reference to the interior at all. -/
theorem sum_moebius_eq_neg_sdiff_of_toggleClosed {p : ℕ} (hp : p.Prime)
    {S T : Finset ℕ} (hsub : T ⊆ S)
    (hclosed : ∀ n ∈ S, primeCarrierToggle p n ∈ S) :
    (∑ n ∈ T, μ n) = -∑ n ∈ S \ T, μ n := by
  have hsplit : (∑ n ∈ S \ T, μ n) + ∑ n ∈ T, μ n = ∑ n ∈ S, μ n :=
    Finset.sum_sdiff hsub
  rw [sum_moebius_eq_zero_of_toggleClosed hp hclosed] at hsplit
  exact eq_neg_of_add_eq_zero_right hsplit

/-! ## Iterating the peel -/

/-- Peel one distinguished prime after another.  What remains is the iterated
Othello boundary of the region. -/
def iteratedPrimeEscapePart : List ℕ → Finset ℕ → Finset ℕ
  | [], S => S
  | p :: ps, S => iteratedPrimeEscapePart ps (primeEscapePart p S)

@[simp] theorem iteratedPrimeEscapePart_nil (S : Finset ℕ) :
    iteratedPrimeEscapePart [] S = S := rfl

@[simp] theorem iteratedPrimeEscapePart_cons (p : ℕ) (ps : List ℕ)
    (S : Finset ℕ) :
    iteratedPrimeEscapePart (p :: ps) S =
      iteratedPrimeEscapePart ps (primeEscapePart p S) := rfl

theorem iteratedPrimeEscapePart_subset :
    ∀ (ps : List ℕ) (S : Finset ℕ), iteratedPrimeEscapePart ps S ⊆ S := by
  intro ps
  induction ps with
  | nil => intro S; exact Finset.Subset.refl S
  | cons p ps ih =>
      intro S
      exact (ih (primeEscapePart p S)).trans (primeEscapePart_subset p S)

/-- **Iterated global Othello theorem.**  The signed Möbius mass of a region is
still exactly the signed mass of what survives after peeling any finite list of
distinguished primes. -/
theorem sum_moebius_eq_sum_iteratedPrimeEscapePart :
    ∀ (ps : List ℕ), (∀ p ∈ ps, Nat.Prime p) → ∀ S : Finset ℕ,
      (∑ n ∈ S, μ n) = ∑ n ∈ iteratedPrimeEscapePart ps S, μ n := by
  intro ps
  induction ps with
  | nil => intro _ S; rfl
  | cons p ps ih =>
      intro hps S
      have hp : Nat.Prime p := hps p (by simp)
      have hps' : ∀ q ∈ ps, Nat.Prime q := by
        intro q hq
        exact hps q (by simp [hq])
      calc (∑ n ∈ S, μ n)
          = ∑ n ∈ primeEscapePart p S, μ n :=
            sum_moebius_eq_sum_primeEscapePart hp S
        _ = ∑ n ∈ iteratedPrimeEscapePart ps (primeEscapePart p S), μ n :=
            ih hps' (primeEscapePart p S)
        _ = ∑ n ∈ iteratedPrimeEscapePart (p :: ps) S, μ n := rfl

/-! ## Signed mass never exceeds boundary population

The population bound `abs_sum_moebius_le_card` is already available from
`RHLean.Proof.MutableSupportBound`; only its boundary specialization is new. -/

/-- **The multiplicity target.**  Whatever the interior of the region does, the
signed mass is bounded by the population of the iterated boundary alone. -/
theorem abs_sum_moebius_le_card_iteratedPrimeEscapePart
    (ps : List ℕ) (hps : ∀ p ∈ ps, Nat.Prime p) (S : Finset ℕ) :
    |∑ n ∈ S, μ n| ≤ ((iteratedPrimeEscapePart ps S).card : ℤ) := by
  rw [sum_moebius_eq_sum_iteratedPrimeEscapePart ps hps S]
  exact abs_sum_moebius_le_card _

end RHLean.Proof
