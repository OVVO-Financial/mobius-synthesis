import Mathlib
import RHLean.Analysis.DyadicTransportCompression

/-!
# Exact prime-dilate compression of canonical transport packets

This module generalizes the dyadic cancellation theorem from the pairing
`(c,q) <-> (2c,q)` to the prime-dilate pairing

`(c,q) <-> (p*c,q)`.

For distinct primes `p` and `q`, with `p ∤ c`, the two channels have opposite
Möbius weights, the same transition index `q - 1`, and nested square-root entry
indices. Their common transport suffix therefore cancels identically. The only
surviving packet is the boundary between the parent entry `sqrt(cq)` and the
child entry `sqrt(pcq)`.

For an arbitrary integer prefix `x`, writing

`B = floor(x / q)`,

the source-level parent/child boundary is exactly the reciprocal shell

`B / p < c <= B`.

The same prime-dilate pairing also compresses every complete cofactor prefix:
for any prime `p`, the full Möbius mass through `B` is exactly the mass of the
`p`-free cofactors in the boundary `B / p < c <= B`.

At a square endpoint `X = R^2 - 1`, this specializes to the square-root geometry
already used by the canonical transport architecture.

All statements below are exact finite identities. No cancellation estimate or
RH implication is asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The `p`-dilated child cofactor. -/
def primeDilateChildCofactor (p c : ℕ) : ℕ := p * c

/-- Endpoint of the residual boundary packet after prime-dilate cancellation. -/
def primeDilateBoundaryUpper (N p c q : ℕ) : ℕ :=
  min (Nat.sqrt (primeDilateChildCofactor p c * q)) (finiteTransportUpper N q)

/-- The parent channel is active but its `p`-dilated child has not yet entered. -/
def IsPrimeDilateBoundaryActive (N p c q t : ℕ) : Prop :=
  Nat.sqrt (c * q) ≤ t ∧ t < primeDilateBoundaryUpper N p c q

instance instDecidableIsPrimeDilateBoundaryActive (N p c q t : ℕ) :
    Decidable (IsPrimeDilateBoundaryActive N p c q t) := by
  unfold IsPrimeDilateBoundaryActive primeDilateBoundaryUpper finiteTransportUpper
  infer_instance

/-- Möbius-weighted contribution of the residual prime-dilate boundary packet. -/
def primeDilateBoundaryContribution (N p c q t : ℕ) : ℂ :=
  if IsPrimeDilateBoundaryActive N p c q t then
    canonicalMoebiusWeight (c * q)
  else
    0

/-- Prime dilation can only move the square-root entry weakly later. -/
theorem sqrt_mul_le_sqrt_primeDilateChild_mul
    (p c q : ℕ) (hp : p.Prime) :
    Nat.sqrt (c * q) ≤ Nat.sqrt (primeDilateChildCofactor p c * q) := by
  apply Nat.sqrt_le_sqrt
  unfold primeDilateChildCofactor
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp.ne_zero
  have hc : c ≤ p * c := by
    simpa using Nat.mul_le_mul_right c hp1
  exact Nat.mul_le_mul_right q hc

/-- Multiplication by a genuinely new prime flips the full Möbius source weight. -/
theorem canonicalMoebiusWeight_primeDilateChild
    {p c q : ℕ} (hp : p.Prime) (hnew : ¬ p ∣ c * q) :
    canonicalMoebiusWeight (primeDilateChildCofactor p c * q) =
      -canonicalMoebiusWeight (c * q) := by
  have hcop : Nat.Coprime p (c * q) := hp.coprime_iff_not_dvd.mpr hnew
  have hmu : μ (p * (c * q)) = -μ (c * q) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    rw [ArithmeticFunction.moebius_apply_prime hp]
    simp
  simpa [primeDilateChildCofactor, canonicalMoebiusWeight, Nat.mul_assoc] using
    congrArg (fun z : ℤ => (z : ℂ)) hmu

/-- If `p` and `q` are distinct primes and `p ∤ c`, then `p` is a genuinely new
prime factor of the source `c*q`. -/
theorem canonicalMoebiusWeight_primeDilateChild_of_distinct_primes
    {p c q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpc : ¬ p ∣ c) :
    canonicalMoebiusWeight (primeDilateChildCofactor p c * q) =
      -canonicalMoebiusWeight (c * q) := by
  apply canonicalMoebiusWeight_primeDilateChild hp
  intro hdiv
  rcases hp.dvd_mul.mp hdiv with hdivc | hdivq
  · exact hpc hdivc
  · have heq : p = q :=
      ((Nat.dvd_prime hq).mp hdivq).resolve_left hp.ne_one
    exact hpq heq

/-- Activity of the prime-dilated child implies activity of the parent channel. -/
theorem finiteTransportActive_parent_of_primeDilateChild
    {N p c q t : ℕ} (hp : p.Prime)
    (h : IsFiniteTransportActive N (primeDilateChildCofactor p c) q t) :
    IsFiniteTransportActive N c q t := by
  exact ⟨(sqrt_mul_le_sqrt_primeDilateChild_mul p c q hp).trans h.1, h.2⟩

/-- The explicit residual interval is exactly the active part of the parent not
shared by the `p`-dilated child. -/
theorem primeDilateBoundaryActive_iff_parent_and_not_child
    (N p c q t : ℕ) :
    IsPrimeDilateBoundaryActive N p c q t ↔
      IsFiniteTransportActive N c q t ∧
        ¬IsFiniteTransportActive N (primeDilateChildCofactor p c) q t := by
  constructor
  · intro h
    have hlt := lt_min_iff.mp h.2
    refine ⟨⟨h.1, hlt.2⟩, ?_⟩
    intro hchild
    exact (not_lt_of_ge hchild.1) hlt.1
  · rintro ⟨hparent, hnotChild⟩
    have hltChild : t < Nat.sqrt (primeDilateChildCofactor p c * q) := by
      by_contra hnot
      apply hnotChild
      exact ⟨Nat.le_of_not_gt hnot, hparent.2⟩
    exact ⟨hparent.1, lt_min hltChild hparent.2⟩

/-- Exact pointwise cancellation of a parent channel with its distinct-prime
`p`-dilated child. The common suffix vanishes identically; only the entry
boundary remains. -/
theorem finiteTransportContribution_add_primeDilateChild
    (N p c q t : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpc : ¬ p ∣ c) :
    finiteTransportContribution N c q t +
        finiteTransportContribution N (primeDilateChildCofactor p c) q t =
      primeDilateBoundaryContribution N p c q t := by
  have hweight :=
    canonicalMoebiusWeight_primeDilateChild_of_distinct_primes hp hq hpq hpc
  by_cases hparent : IsFiniteTransportActive N c q t
  · by_cases hchild :
        IsFiniteTransportActive N (primeDilateChildCofactor p c) q t <;>
      simp [finiteTransportContribution, primeDilateBoundaryContribution,
        hparent, hchild, hweight,
        primeDilateBoundaryActive_iff_parent_and_not_child N p c q t]
  · have hchild :
        ¬IsFiniteTransportActive N (primeDilateChildCofactor p c) q t := by
      intro h
      exact hparent (finiteTransportActive_parent_of_primeDilateChild hp h)
    simp [finiteTransportContribution, primeDilateBoundaryContribution,
      hparent, hchild,
      primeDilateBoundaryActive_iff_parent_and_not_child N p c q t]

/-- Finite residual packet left after exact prime-dilate cancellation. -/
def primeDilateBoundaryPacket (N p c q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range (N + 1), primeDilateBoundaryContribution N p c q t

/-- Exact packet-level prime-dilate compression identity. -/
theorem finiteTransportPacket_add_primeDilateChild
    (N p c q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpc : ¬ p ∣ c) :
    finiteTransportPacket N c q +
        finiteTransportPacket N (primeDilateChildCofactor p c) q =
      primeDilateBoundaryPacket N p c q := by
  unfold finiteTransportPacket primeDilateBoundaryPacket
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact finiteTransportContribution_add_primeDilateChild
    N p c q t hp hq hpq hpc

/-! ## Exact `1/p` reciprocal boundary at an arbitrary prefix -/

/-- Reciprocal cofactor cutoff in the prime-first `q`-fiber at an arbitrary
integer prefix `x`. -/
def primeDilatePrefixCutoff (x q : ℕ) : ℕ :=
  x / q

/-- Source-level boundary saying `(c,q)` lies in the prefix through `x` while
its `p`-dilated child `(p*c,q)` lies beyond that prefix. -/
def IsPrimeDilatePrefixBoundary (p x q c : ℕ) : Prop :=
  c * q ≤ x ∧ x < primeDilateChildCofactor p c * q

/-- For every integer prefix `x`, the parent-inside/child-outside condition is
exactly the reciprocal `1/p` shell. If `B = floor(x/q)`, then

`c*q <= x < (p*c)*q  <->  B/p < c <= B`.
-/
theorem primeDilatePrefixBoundary_iff_reciprocalShell
    (p x q c : ℕ) (hp : p.Prime) (hq : 0 < q) :
    IsPrimeDilatePrefixBoundary p x q c ↔
      c ≤ primeDilatePrefixCutoff x q ∧
        primeDilatePrefixCutoff x q / p < c := by
  unfold IsPrimeDilatePrefixBoundary primeDilatePrefixCutoff
  constructor
  · rintro ⟨hparent, hchild⟩
    have hcB : c ≤ x / q :=
      (Nat.le_div_iff_mul_le hq).2 hparent
    have hBltpc : x / q < p * c := by
      apply (Nat.div_lt_iff_lt_mul hq).2
      simpa [primeDilateChildCofactor, Nat.mul_assoc] using hchild
    have hshell : (x / q) / p < c := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      simpa [Nat.mul_comm] using hBltpc
    exact ⟨hcB, hshell⟩
  · rintro ⟨hcB, hshell⟩
    have hparent : c * q ≤ x :=
      (Nat.le_div_iff_mul_le hq).1 hcB
    have hBltcp : x / q < c * p :=
      (Nat.div_lt_iff_lt_mul hp.pos).1 hshell
    have hBltpc : x / q < p * c := by
      simpa [Nat.mul_comm] using hBltcp
    have hchild : x < (p * c) * q :=
      (Nat.div_lt_iff_lt_mul hq).1 hBltpc
    exact ⟨hparent, by simpa [primeDilateChildCofactor] using hchild⟩

/-- The literal finite `1/p` shell in the `q`-fiber of an arbitrary prefix. -/
def primeDilatePrefixReciprocalShell (p x q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (primeDilatePrefixCutoff x q)).filter fun c =>
    ¬ p ∣ c ∧ primeDilatePrefixCutoff x q / p < c

@[simp] theorem mem_primeDilatePrefixReciprocalShell
    {p x q c : ℕ} :
    c ∈ primeDilatePrefixReciprocalShell p x q ↔
      1 ≤ c ∧ c ≤ primeDilatePrefixCutoff x q ∧
        ¬ p ∣ c ∧ primeDilatePrefixCutoff x q / p < c := by
  simp [primeDilatePrefixReciprocalShell, and_assoc]

/-- With the new-prime condition `p ∤ c`, membership in the arbitrary-prefix
reciprocal shell is exactly the source-level condition that the parent is
present while its `p`-dilated child has not yet entered. -/
theorem mem_primeDilatePrefixReciprocalShell_iff_prefixBoundary
    (p x q c : ℕ) (hp : p.Prime) (hq : 0 < q) :
    c ∈ primeDilatePrefixReciprocalShell p x q ↔
      1 ≤ c ∧ ¬ p ∣ c ∧ IsPrimeDilatePrefixBoundary p x q c := by
  rw [mem_primeDilatePrefixReciprocalShell,
    primeDilatePrefixBoundary_iff_reciprocalShell p x q c hp hq]
  aesop

/-! ## Exact compression of complete cofactor prefixes by an arbitrary prime -/

/-- Positive cofactors through `B` that are free of the prime `p`. -/
def primeFreeCofactorPrefix (p B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter fun c => ¬ p ∣ c

/-- Positive cofactors through `B` that are divisible by `p`. -/
def primeDivisibleCofactorPrefix (p B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter fun c => p ∣ c

/-- The `p`-free reciprocal boundary `B / p < c <= B`. -/
def primeCofactorBoundary (p B : ℕ) : Finset ℕ :=
  primeFreeCofactorPrefix p B \ primeFreeCofactorPrefix p (B / p)

@[simp] theorem mem_primeFreeCofactorPrefix {p B c : ℕ} :
    c ∈ primeFreeCofactorPrefix p B ↔
      1 ≤ c ∧ c ≤ B ∧ ¬ p ∣ c := by
  simp [primeFreeCofactorPrefix, and_assoc]

@[simp] theorem mem_primeDivisibleCofactorPrefix {p B c : ℕ} :
    c ∈ primeDivisibleCofactorPrefix p B ↔
      1 ≤ c ∧ c ≤ B ∧ p ∣ c := by
  simp [primeDivisibleCofactorPrefix, and_assoc]

@[simp] theorem mem_primeCofactorBoundary {p B c : ℕ} :
    c ∈ primeCofactorBoundary p B ↔
      1 ≤ c ∧ c ≤ B ∧ ¬ p ∣ c ∧ B / p < c := by
  constructor
  · intro h
    rcases Finset.mem_sdiff.mp h with ⟨hbig, hsmall⟩
    rcases mem_primeFreeCofactorPrefix.mp hbig with ⟨hc1, hcB, hfree⟩
    have hboundary : B / p < c := by
      by_contra hnot
      apply hsmall
      exact mem_primeFreeCofactorPrefix.mpr
        ⟨hc1, Nat.le_of_not_gt hnot, hfree⟩
    exact ⟨hc1, hcB, hfree, hboundary⟩
  · rintro ⟨hc1, hcB, hfree, hboundary⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_primeFreeCofactorPrefix.mpr ⟨hc1, hcB, hfree⟩, ?_⟩
    intro hsmall
    exact (not_lt_of_ge (mem_primeFreeCofactorPrefix.mp hsmall).2.1) hboundary

/-- Multiplication by `p` flips a `p`-free Möbius weight and kills a weight that
already contains `p`. -/
theorem canonicalMoebiusWeight_prime_mul
    (p c : ℕ) (hp : p.Prime) :
    canonicalMoebiusWeight (p * c) =
      if p ∣ c then 0 else -canonicalMoebiusWeight c := by
  by_cases hpc : p ∣ c
  · rw [if_pos hpc]
    have hzero : μ (p * c) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hsq
      have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp
      apply hnot
      rcases hpc with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    simp [canonicalMoebiusWeight, hzero]
  · rw [if_neg hpc]
    simpa [primeDilateChildCofactor] using
      (canonicalMoebiusWeight_primeDilateChild
        (p := p) (c := c) (q := 1) hp (by simpa using hpc))

/-- Multiplication by `p` bijects the positive prefix through `B / p` with the
`p`-divisible cofactors through `B`. -/
theorem sum_prime_mul_eq_sum_primeDivisibleCofactorPrefix
    (p B : ℕ) (hp : p.Prime) :
    (∑ d ∈ Finset.Icc 1 (B / p), canonicalMoebiusWeight (p * d)) =
      ∑ c ∈ primeDivisibleCofactorPrefix p B, canonicalMoebiusWeight c := by
  classical
  refine Finset.sum_bij (fun d _ => p * d) ?_ ?_ ?_ ?_
  · intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hdB⟩
    have hpdB : p * d ≤ B := by
      have hmul := (Nat.le_div_iff_mul_le hp.pos).1 hdB
      simpa [Nat.mul_comm] using hmul
    exact mem_primeDivisibleCofactorPrefix.mpr
      ⟨by nlinarith [hp.two_le], hpdB, dvd_mul_right p d⟩
  · intro d1 hd1 d2 hd2 h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  · intro c hc
    rcases mem_primeDivisibleCofactorPrefix.mp hc with ⟨hc1, hcB, hpc⟩
    have hprod : p * (c / p) = c := Nat.mul_div_cancel' hpc
    refine ⟨c / p, ?_, hprod⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have hquotPos : 0 < c / p := by
        by_contra hnot
        have hzero : c / p = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hzero, mul_zero] at hprod
        omega
      exact hquotPos
    · apply (Nat.le_div_iff_mul_le hp.pos).2
      have hmul : (c / p) * p = c := by
        simpa [Nat.mul_comm] using hprod
      rw [hmul]
      exact hcB
  · intro d hd
    rfl

/-- The `p`-divisible cofactor mass is the negative `p`-free mass at scale
`B / p`; terms divisible by `p^2` vanish automatically. -/
theorem sum_primeDivisibleCofactorPrefix_eq_neg_primeFree_div
    (p B : ℕ) (hp : p.Prime) :
    (∑ c ∈ primeDivisibleCofactorPrefix p B, canonicalMoebiusWeight c) =
      -∑ d ∈ primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight d := by
  rw [← sum_prime_mul_eq_sum_primeDivisibleCofactorPrefix p B hp]
  calc
    (∑ d ∈ Finset.Icc 1 (B / p), canonicalMoebiusWeight (p * d)) =
        ∑ d ∈ Finset.Icc 1 (B / p),
          if p ∣ d then 0 else -canonicalMoebiusWeight d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact canonicalMoebiusWeight_prime_mul p d hp
    _ = ∑ d ∈ Finset.Icc 1 (B / p),
        if ¬ p ∣ d then -canonicalMoebiusWeight d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hpd : p ∣ d <;> simp [hpd]
    _ = ∑ d ∈ primeFreeCofactorPrefix p (B / p),
        -canonicalMoebiusWeight d := by
      unfold primeFreeCofactorPrefix
      rw [Finset.sum_filter]
    _ = -∑ d ∈ primeFreeCofactorPrefix p (B / p),
        canonicalMoebiusWeight d := by
      simp

/-- Every positive prefix splits exactly into its `p`-free and `p`-divisible
cofactors. -/
theorem sum_Icc_eq_primeFree_add_primeDivisible (p B : ℕ) :
    (∑ c ∈ Finset.Icc 1 B, canonicalMoebiusWeight c) =
      (∑ c ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight c) +
        ∑ c ∈ primeDivisibleCofactorPrefix p B, canonicalMoebiusWeight c := by
  calc
    (∑ c ∈ Finset.Icc 1 B, canonicalMoebiusWeight c) =
        ∑ c ∈ Finset.Icc 1 B,
          ((if ¬ p ∣ c then canonicalMoebiusWeight c else 0) +
            (if p ∣ c then canonicalMoebiusWeight c else 0)) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hpc : p ∣ c <;> simp [hpc]
    _ =
        (∑ c ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight c) +
          ∑ c ∈ primeDivisibleCofactorPrefix p B, canonicalMoebiusWeight c := by
      rw [Finset.sum_add_distrib]
      unfold primeFreeCofactorPrefix primeDivisibleCofactorPrefix
      rw [Finset.sum_filter, Finset.sum_filter]

/-- The `p`-free prefix at scale `B / p` is contained in the full `p`-free
prefix. -/
theorem primeFreeCofactorPrefix_div_subset (p B : ℕ) :
    primeFreeCofactorPrefix p (B / p) ⊆ primeFreeCofactorPrefix p B := by
  intro c hc
  rcases mem_primeFreeCofactorPrefix.mp hc with ⟨hc1, hcB, hfree⟩
  exact mem_primeFreeCofactorPrefix.mpr
    ⟨hc1, hcB.trans (Nat.div_le_self B p), hfree⟩

/-- Möbius mass of the exact `p`-free reciprocal boundary. -/
def primeCofactorBoundaryMass (p B : ℕ) : ℂ :=
  ∑ c ∈ primeCofactorBoundary p B, canonicalMoebiusWeight c

/-- Exact arbitrary-prime compression of every complete lower-cofactor prefix:

`M(B) = sum_{B/p < c <= B, p ∤ c} mu(c)`.
-/
theorem cofactorMobiusPrefixMass_eq_primeCofactorBoundaryMass
    (p B : ℕ) (hp : p.Prime) :
    cofactorMobiusPrefixMass B = primeCofactorBoundaryMass p B := by
  unfold cofactorMobiusPrefixMass primeCofactorBoundaryMass
  rw [sum_Icc_eq_primeFree_add_primeDivisible,
    sum_primeDivisibleCofactorPrefix_eq_neg_primeFree_div p B hp]
  have hsubset := primeFreeCofactorPrefix_div_subset p B
  have hpartition :
      (∑ c ∈ primeFreeCofactorPrefix p B \
          primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight c) +
        ∑ c ∈ primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight c =
          ∑ c ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight c := by
    exact Finset.sum_sdiff hsubset
  unfold primeCofactorBoundary
  calc
    (∑ c ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight c) +
          -∑ c ∈ primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight c =
        (∑ c ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight c) -
          ∑ c ∈ primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight c := by
      ring
    _ = ∑ c ∈ primeFreeCofactorPrefix p B \
          primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight c := by
      exact (eq_sub_of_add_eq hpartition).symm

/-- The complete-prefix arithmetic boundary is exactly the earlier development's arbitrary-prefix
geometric reciprocal shell in every `q`-fiber. -/
theorem primeCofactorBoundary_eq_primeDilatePrefixReciprocalShell
    (p x q : ℕ) :
    primeCofactorBoundary p (primeDilatePrefixCutoff x q) =
      primeDilatePrefixReciprocalShell p x q := by
  ext c
  simp [primeDilatePrefixCutoff]

/-! ## Exact `1/p` reciprocal boundary at a square endpoint -/

/-- Reciprocal cofactor cutoff in the prime-first `q`-fiber at `X = R^2 - 1`. -/
def primeDilateReciprocalCutoff (R q : ℕ) : ℕ :=
  squareRootEndpoint R / q

/-- Geometric boundary condition saying the parent source is inside the square
prefix while its `p`-dilated child is outside. -/
def IsPrimeDilateSquareBoundary (p R q c : ℕ) : Prop :=
  c * q ≤ squareRootEndpoint R ∧
    squareRootEndpoint R < primeDilateChildCofactor p c * q

/-- The square-prefix parent/child boundary is exactly the `1/p` reciprocal
cofactor shell. If `B = floor((R^2-1)/q)`, then

`parent inside, p-child outside  <->  B/p < c <= B`.
-/
theorem primeDilateSquareBoundary_iff_reciprocalShell
    (p R q c : ℕ) (hp : p.Prime) (hq : 0 < q) :
    IsPrimeDilateSquareBoundary p R q c ↔
      c ≤ primeDilateReciprocalCutoff R q ∧
        primeDilateReciprocalCutoff R q / p < c := by
  unfold IsPrimeDilateSquareBoundary primeDilateReciprocalCutoff
  constructor
  · rintro ⟨hparent, hchild⟩
    have hcB : c ≤ squareRootEndpoint R / q :=
      (Nat.le_div_iff_mul_le hq).2 hparent
    have hBltpc : squareRootEndpoint R / q < p * c := by
      apply (Nat.div_lt_iff_lt_mul hq).2
      simpa [primeDilateChildCofactor, Nat.mul_assoc] using hchild
    have hshell : (squareRootEndpoint R / q) / p < c := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      simpa [Nat.mul_comm] using hBltpc
    exact ⟨hcB, hshell⟩
  · rintro ⟨hcB, hshell⟩
    have hparent : c * q ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hq).1 hcB
    have hBltcp : squareRootEndpoint R / q < c * p :=
      (Nat.div_lt_iff_lt_mul hp.pos).1 hshell
    have hBltpc : squareRootEndpoint R / q < p * c := by
      simpa [Nat.mul_comm] using hBltcp
    have hchild : squareRootEndpoint R < (p * c) * q :=
      (Nat.div_lt_iff_lt_mul hq).1 hBltpc
    exact ⟨hparent, by simpa [primeDilateChildCofactor] using hchild⟩

/-- The literal finite `1/p` shell in a prime-first `q`-fiber. -/
def primeDilateReciprocalShell (p R q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (primeDilateReciprocalCutoff R q)).filter fun c =>
    ¬ p ∣ c ∧ primeDilateReciprocalCutoff R q / p < c

@[simp] theorem mem_primeDilateReciprocalShell
    {p R q c : ℕ} :
    c ∈ primeDilateReciprocalShell p R q ↔
      1 ≤ c ∧ c ≤ primeDilateReciprocalCutoff R q ∧
        ¬ p ∣ c ∧ primeDilateReciprocalCutoff R q / p < c := by
  simp [primeDilateReciprocalShell, and_assoc]

/-- With the new-prime condition `p ∤ c`, membership in the finite reciprocal
shell is exactly the source-level condition that `(c,q)` is present but
`(p*c,q)` lies beyond the square boundary. -/
theorem mem_primeDilateReciprocalShell_iff_squareBoundary
    (p R q c : ℕ) (hp : p.Prime) (hq : 0 < q) :
    c ∈ primeDilateReciprocalShell p R q ↔
      1 ≤ c ∧ ¬ p ∣ c ∧ IsPrimeDilateSquareBoundary p R q c := by
  rw [mem_primeDilateReciprocalShell,
    primeDilateSquareBoundary_iff_reciprocalShell p R q c hp hq]
  aesop

/-- The square-endpoint boundary is literally the arbitrary-prefix boundary
specialized to `x = R^2 - 1`. -/
theorem primeDilateSquareBoundary_iff_prefixBoundary
    (p R q c : ℕ) :
    IsPrimeDilateSquareBoundary p R q c ↔
      IsPrimeDilatePrefixBoundary p (squareRootEndpoint R) q c := by
  rfl

/-- The square-endpoint reciprocal shell is the arbitrary-prefix shell at the
same endpoint. -/
theorem primeDilateReciprocalShell_eq_prefixShell
    (p R q : ℕ) :
    primeDilateReciprocalShell p R q =
      primeDilatePrefixReciprocalShell p (squareRootEndpoint R) q := by
  rfl

end RHLean.Proof
