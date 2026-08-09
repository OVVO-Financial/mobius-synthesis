import Mathlib
import RHLean.Arithmetic.MoebiusDoubling
import RHLean.Analysis.TwoABPrimeDilation

/-!
# Exact dyadic compression of canonical transport packets

This module isolates the exact cancellation supplied by Möbius doubling.  For an
odd lower cofactor `c` and an odd upper prime `q`, the channels `(c,q)` and
`(2c,q)` have opposite Möbius weights, the same transition index `q-1`, and
nested entry indices.  Their common transport suffix therefore cancels
identically, leaving only the boundary packet between the two entry scales.

The second half of the module applies the same involution to every lower-cofactor
fiber of the paper's transport term.  It proves that the complete original
transport sum is exactly a sum over odd cofactors in the dyadic boundary
`B/2 < c <= B`, where `B = floor((R^2-1)/q)`.

All statements in this file are finite identities.  No cancellation estimate or
RH implication is asserted.

This module is classified under `RHLean/Analysis/` because its content is
represented in the bridge paper; the namespace remains `RHLean.Proof` for API
compatibility with existing references.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The finite-horizon endpoint for a transport channel.  Stages are restricted
to `0,...,N`, while the intrinsic transition endpoint is `q-1`. -/
def finiteTransportUpper (N q : ℕ) : ℕ :=
  min (q - 1) (N + 1)

/-- A raw prime-cofactor transport channel is active at stage `t` exactly between
its square-root entry and its finite-horizon endpoint. -/
def IsFiniteTransportActive (N c q t : ℕ) : Prop :=
  Nat.sqrt (c * q) ≤ t ∧ t < finiteTransportUpper N q

instance instDecidableIsFiniteTransportActive (N c q t : ℕ) :
    Decidable (IsFiniteTransportActive N c q t) := by
  unfold IsFiniteTransportActive finiteTransportUpper
  infer_instance

/-- Raw Möbius-weighted transport contribution of one factor channel. -/
def finiteTransportContribution (N c q t : ℕ) : ℂ :=
  if IsFiniteTransportActive N c q t then
    canonicalMoebiusWeight (c * q)
  else
    0

/-- The doubled cofactor channel. -/
def dyadicChildCofactor (c : ℕ) : ℕ :=
  2 * c

/-- Endpoint of the exact residual boundary packet after parent-child
cancellation. -/
def dyadicBoundaryUpper (N c q : ℕ) : ℕ :=
  min (Nat.sqrt (dyadicChildCofactor c * q)) (finiteTransportUpper N q)

/-- The residual dyadic boundary packet. -/
def IsDyadicBoundaryActive (N c q t : ℕ) : Prop :=
  Nat.sqrt (c * q) ≤ t ∧ t < dyadicBoundaryUpper N c q

instance instDecidableIsDyadicBoundaryActive (N c q t : ℕ) :
    Decidable (IsDyadicBoundaryActive N c q t) := by
  unfold IsDyadicBoundaryActive dyadicBoundaryUpper finiteTransportUpper
  infer_instance

/-- Möbius-weighted contribution of the residual boundary packet. -/
def dyadicBoundaryContribution (N c q t : ℕ) : ℂ :=
  if IsDyadicBoundaryActive N c q t then
    canonicalMoebiusWeight (c * q)
  else
    0

/-- Doubling the cofactor can only move the square-root entry weakly later. -/
theorem sqrt_mul_le_sqrt_dyadicChild_mul (c q : ℕ) :
    Nat.sqrt (c * q) ≤ Nat.sqrt (dyadicChildCofactor c * q) := by
  apply Nat.sqrt_le_sqrt
  unfold dyadicChildCofactor
  exact Nat.mul_le_mul_right q (by omega)

/-- Möbius doubling flips the full source weight when the parent product is odd. -/
theorem canonicalMoebiusWeight_dyadicChild
    {c q : ℕ} (hc : Odd c) (hq : Odd q) :
    canonicalMoebiusWeight (dyadicChildCofactor c * q) =
      -canonicalMoebiusWeight (c * q) := by
  have hodd : Odd (c * q) := hc.mul hq
  have hmu := RHLean.Arithmetic.moebius_two_mul_of_odd (c * q) hodd
  simpa [dyadicChildCofactor, canonicalMoebiusWeight, Nat.mul_assoc] using
    congrArg (fun z : ℤ => (z : ℂ)) hmu

/-- Prime-specialized form of the dyadic Möbius sign flip. -/
theorem canonicalMoebiusWeight_dyadicChild_of_prime
    {c q : ℕ} (hc : Odd c) (hq : q.Prime) (hq2 : q ≠ 2) :
    canonicalMoebiusWeight (dyadicChildCofactor c * q) =
      -canonicalMoebiusWeight (c * q) :=
  canonicalMoebiusWeight_dyadicChild hc (hq.odd_of_ne_two hq2)

/-- Activity of the doubled child implies activity of the parent channel. -/
theorem finiteTransportActive_parent_of_child
    {N c q t : ℕ}
    (h : IsFiniteTransportActive N (dyadicChildCofactor c) q t) :
    IsFiniteTransportActive N c q t := by
  exact ⟨(sqrt_mul_le_sqrt_dyadicChild_mul c q).trans h.1, h.2⟩

/-- The explicit boundary interval is exactly the active part of the parent not
shared by the doubled child. -/
theorem dyadicBoundaryActive_iff_parent_and_not_child
    (N c q t : ℕ) :
    IsDyadicBoundaryActive N c q t ↔
      IsFiniteTransportActive N c q t ∧
        ¬IsFiniteTransportActive N (dyadicChildCofactor c) q t := by
  constructor
  · intro h
    have hlt := (lt_min_iff.mp h.2)
    refine ⟨⟨h.1, hlt.2⟩, ?_⟩
    intro hchild
    exact (not_lt_of_ge hchild.1) hlt.1
  · rintro ⟨hparent, hnotChild⟩
    have hltChild : t < Nat.sqrt (dyadicChildCofactor c * q) := by
      by_contra hnot
      apply hnotChild
      exact ⟨Nat.le_of_not_gt hnot, hparent.2⟩
    exact ⟨hparent.1, lt_min hltChild hparent.2⟩

/-- Exact pointwise cancellation of an odd parent with its doubled child. -/
theorem finiteTransportContribution_add_dyadicChild
    (N c q t : ℕ) (hc : Odd c) (hq : Odd q) :
    finiteTransportContribution N c q t +
        finiteTransportContribution N (dyadicChildCofactor c) q t =
      dyadicBoundaryContribution N c q t := by
  have hweight := canonicalMoebiusWeight_dyadicChild hc hq
  by_cases hp : IsFiniteTransportActive N c q t
  · by_cases hchild : IsFiniteTransportActive N (dyadicChildCofactor c) q t <;>
      simp [finiteTransportContribution, dyadicBoundaryContribution, hp, hchild,
        hweight, dyadicBoundaryActive_iff_parent_and_not_child]
  · have hchild : ¬IsFiniteTransportActive N (dyadicChildCofactor c) q t := by
      intro h
      exact hp (finiteTransportActive_parent_of_child h)
    simp [finiteTransportContribution, dyadicBoundaryContribution, hp, hchild,
      dyadicBoundaryActive_iff_parent_and_not_child]

/-- Finite raw transport packet of one channel. -/
def finiteTransportPacket (N c q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range (N + 1), finiteTransportContribution N c q t

/-- Finite residual dyadic boundary packet. -/
def dyadicBoundaryPacket (N c q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range (N + 1), dyadicBoundaryContribution N c q t

/-- Exact packet-level dyadic compression identity. -/
theorem finiteTransportPacket_add_dyadicChild
    (N c q : ℕ) (hc : Odd c) (hq : Odd q) :
    finiteTransportPacket N c q +
        finiteTransportPacket N (dyadicChildCofactor c) q =
      dyadicBoundaryPacket N c q := by
  unfold finiteTransportPacket dyadicBoundaryPacket
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact finiteTransportContribution_add_dyadicChild N c q t hc hq

/-- Uncompressed finite transport amplitude of a family indexed by odd parent
cofactors. -/
def dyadicUncompressedTransportFamily
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ) (N t : ℕ) : ℂ :=
  ∑ i ∈ U,
    (finiteTransportContribution N (c i) (q i) t +
      finiteTransportContribution N (dyadicChildCofactor (c i)) (q i) t)

/-- Compressed dyadic boundary amplitude of the same family. -/
def dyadicCompressedTransportFamily
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ) (N t : ℕ) : ℂ :=
  ∑ i ∈ U, dyadicBoundaryContribution N (c i) (q i) t

/-- Exact finite-family compression. -/
theorem dyadicUncompressedTransportFamily_eq_compressed
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ) (N t : ℕ)
    (hc : ∀ i ∈ U, Odd (c i))
    (hq : ∀ i ∈ U, Odd (q i)) :
    dyadicUncompressedTransportFamily U c q N t =
      dyadicCompressedTransportFamily U c q N t := by
  unfold dyadicUncompressedTransportFamily dyadicCompressedTransportFamily
  apply Finset.sum_congr rfl
  intro i hi
  exact finiteTransportContribution_add_dyadicChild N (c i) (q i) t
    (hc i hi) (hq i hi)

/-- The doubled child has no active stage in the finite horizon exactly when its
entry lies beyond the horizon or at/after its intrinsic transition. -/
theorem no_finiteTransportActive_dyadicChild_iff
    (N c q : ℕ) :
    (¬∃ t, IsFiniteTransportActive N (dyadicChildCofactor c) q t) ↔
      N < Nat.sqrt (dyadicChildCofactor c * q) ∨
        q - 1 ≤ Nat.sqrt (dyadicChildCofactor c * q) := by
  constructor
  · intro hnone
    by_contra hnot
    push_neg at hnot
    have hentryHorizon : Nat.sqrt (dyadicChildCofactor c * q) ≤ N := hnot.1
    have hentryTransition :
        Nat.sqrt (dyadicChildCofactor c * q) < q - 1 := hnot.2
    apply hnone
    refine ⟨Nat.sqrt (dyadicChildCofactor c * q), ?_⟩
    constructor
    · exact le_rfl
    · unfold finiteTransportUpper
      exact lt_min hentryTransition (by omega)
  · rintro (hHorizon | hTransition)
    · rintro ⟨t, htLower, htUpper⟩
      have htHorizon : t < N + 1 := (lt_min_iff.mp htUpper).2
      omega
    · rintro ⟨t, htLower, htUpper⟩
      have htTransition : t < q - 1 := (lt_min_iff.mp htUpper).1
      omega

/-- Every unmatched doubled child is therefore an explicit finite-horizon or
born-smooth boundary, with no unclassified third case. -/
def IsDyadicFiniteHorizonBoundary (N c q : ℕ) : Prop :=
  N < Nat.sqrt (dyadicChildCofactor c * q)

/-- The doubled child has already lost its transport interval before entry. -/
def IsDyadicBornSmoothBoundary (c q : ℕ) : Prop :=
  q - 1 ≤ Nat.sqrt (dyadicChildCofactor c * q)

/-- Exact classification of absent child packets. -/
theorem no_finiteTransportActive_dyadicChild_iff_boundary
    (N c q : ℕ) :
    (¬∃ t, IsFiniteTransportActive N (dyadicChildCofactor c) q t) ↔
      IsDyadicFiniteHorizonBoundary N c q ∨
        IsDyadicBornSmoothBoundary c q := by
  exact no_finiteTransportActive_dyadicChild_iff N c q

/-! ## Exact compression of complete lower-cofactor fibers -/

/-- Positive odd cofactors through `B`. -/
def oddCofactorPrefix (B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter Odd

/-- Positive even cofactors through `B`. -/
def evenCofactorPrefix (B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter Even

/-- Odd cofactors in the dyadic boundary `B/2 < c <= B`. -/
def dyadicCofactorBoundary (B : ℕ) : Finset ℕ :=
  oddCofactorPrefix B \ oddCofactorPrefix (B / 2)

@[simp] theorem mem_oddCofactorPrefix {B c : ℕ} :
    c ∈ oddCofactorPrefix B ↔ 1 ≤ c ∧ c ≤ B ∧ Odd c := by
  simp [oddCofactorPrefix, and_assoc]

@[simp] theorem mem_evenCofactorPrefix {B c : ℕ} :
    c ∈ evenCofactorPrefix B ↔ 1 ≤ c ∧ c ≤ B ∧ Even c := by
  simp [evenCofactorPrefix, and_assoc]

/-- The set-difference definition is exactly the explicit dyadic boundary. -/
@[simp] theorem mem_dyadicCofactorBoundary {B c : ℕ} :
    c ∈ dyadicCofactorBoundary B ↔
      1 ≤ c ∧ c ≤ B ∧ Odd c ∧ B < 2 * c := by
  constructor
  · intro h
    rcases Finset.mem_sdiff.mp h with ⟨hbig, hsmall⟩
    rcases mem_oddCofactorPrefix.mp hbig with ⟨hc1, hcB, hcodd⟩
    have hhalf : B / 2 < c := by
      by_contra hnot
      apply hsmall
      exact mem_oddCofactorPrefix.mpr
        ⟨hc1, Nat.le_of_not_gt hnot, hcodd⟩
    exact ⟨hc1, hcB, hcodd, by omega⟩
  · rintro ⟨hc1, hcB, hcodd, hdouble⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_oddCofactorPrefix.mpr ⟨hc1, hcB, hcodd⟩, ?_⟩
    intro hsmall
    have hhalf := (mem_oddCofactorPrefix.mp hsmall).2.1
    omega

/-- Doubling any cofactor is either the negative odd-parent weight or zero when
the parent is even (because the doubled integer is then divisible by `4`). -/
theorem canonicalMoebiusWeight_two_mul (c : ℕ) :
    canonicalMoebiusWeight (2 * c) =
      if Odd c then -canonicalMoebiusWeight c else 0 := by
  by_cases hc : Odd c
  · rw [if_pos hc]
    simpa [dyadicChildCofactor] using
      (canonicalMoebiusWeight_dyadicChild
        (c := c) (q := 1) hc (by norm_num : Odd 1))
  · rw [if_neg hc]
    have heven : Even c := Nat.not_odd_iff_even.mp hc
    have hzero : μ (2 * c) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hsq
      have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
      apply hnot
      rcases heven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    simp [canonicalMoebiusWeight, hzero]

/-- Even cofactors through `B` are in bijection with positive integers through
`B/2`. -/
theorem sum_double_eq_sum_evenCofactorPrefix (B : ℕ) :
    (∑ d ∈ Finset.Icc 1 (B / 2), canonicalMoebiusWeight (2 * d)) =
      ∑ c ∈ evenCofactorPrefix B, canonicalMoebiusWeight c := by
  classical
  refine Finset.sum_bij (fun d _ => 2 * d) ?_ ?_ ?_ ?_
  · intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hdB⟩
    have h2dB : 2 * d ≤ B := by
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 hdB
      simpa [Nat.mul_comm] using hmul
    have hpos : 1 ≤ 2 * d := by omega
    have heven : Even (2 * d) := even_two_mul d
    exact mem_evenCofactorPrefix.mpr ⟨hpos, h2dB, heven⟩
  · intro d1 hd1 d2 hd2 h
    change 2 * d1 = 2 * d2 at h
    omega
  · intro c hc
    rcases mem_evenCofactorPrefix.mp hc with ⟨hc1, hcB, hceven⟩
    have hdouble : 2 * (c / 2) = c := Nat.two_mul_div_two_of_even hceven
    refine ⟨c / 2, ?_, hdouble⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have hcne : c ≠ 0 := by omega
      have hcgt : 1 < c := Nat.one_lt_of_ne_zero_of_even hcne hceven
      omega
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      have hmul : c / 2 * 2 = c := by
        simpa [Nat.mul_comm] using hdouble
      rw [hmul]
      exact hcB
  · intro d hd
    rfl

/-- The even-cofactor mass is the negative odd-cofactor mass at half scale. -/
theorem sum_evenCofactorPrefix_eq_neg_odd_half (B : ℕ) :
    (∑ c ∈ evenCofactorPrefix B, canonicalMoebiusWeight c) =
      -∑ d ∈ oddCofactorPrefix (B / 2), canonicalMoebiusWeight d := by
  rw [← sum_double_eq_sum_evenCofactorPrefix]
  calc
    (∑ d ∈ Finset.Icc 1 (B / 2), canonicalMoebiusWeight (2 * d)) =
        ∑ d ∈ Finset.Icc 1 (B / 2),
          if Odd d then -canonicalMoebiusWeight d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact canonicalMoebiusWeight_two_mul d
    _ = ∑ d ∈ oddCofactorPrefix (B / 2), -canonicalMoebiusWeight d := by
      unfold oddCofactorPrefix
      rw [Finset.sum_filter]
    _ = -∑ d ∈ oddCofactorPrefix (B / 2), canonicalMoebiusWeight d := by
      simp

/-- Every positive prefix splits exactly into its odd and even cofactors. -/
theorem sum_Icc_eq_odd_add_even (B : ℕ) :
    (∑ c ∈ Finset.Icc 1 B, canonicalMoebiusWeight c) =
      (∑ c ∈ oddCofactorPrefix B, canonicalMoebiusWeight c) +
        ∑ c ∈ evenCofactorPrefix B, canonicalMoebiusWeight c := by
  calc
    (∑ c ∈ Finset.Icc 1 B, canonicalMoebiusWeight c) =
        ∑ c ∈ Finset.Icc 1 B,
          ((if Odd c then canonicalMoebiusWeight c else 0) +
            (if Even c then canonicalMoebiusWeight c else 0)) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hodd : Odd c
      · have hnotEven : ¬Even c := Nat.not_even_iff_odd.mpr hodd
        simp [hodd, hnotEven]
      · have heven : Even c := Nat.not_odd_iff_even.mp hodd
        simp [hodd, heven]
    _ =
        (∑ c ∈ oddCofactorPrefix B, canonicalMoebiusWeight c) +
          ∑ c ∈ evenCofactorPrefix B, canonicalMoebiusWeight c := by
      rw [Finset.sum_add_distrib]
      unfold oddCofactorPrefix evenCofactorPrefix
      rw [Finset.sum_filter, Finset.sum_filter]

/-- The half-scale odd prefix is contained in the full odd prefix. -/
theorem oddCofactorPrefix_half_subset (B : ℕ) :
    oddCofactorPrefix (B / 2) ⊆ oddCofactorPrefix B := by
  intro c hc
  rcases mem_oddCofactorPrefix.mp hc with ⟨hc1, hcB, hcodd⟩
  exact mem_oddCofactorPrefix.mpr ⟨hc1, by omega, hcodd⟩

/-- Complex Möbius mass of the complete positive prefix through `B`. -/
def cofactorMobiusPrefixMass (B : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 B, canonicalMoebiusWeight c

/-- Möbius mass of the exact odd dyadic boundary. -/
def dyadicCofactorBoundaryMass (B : ℕ) : ℂ :=
  ∑ c ∈ dyadicCofactorBoundary B, canonicalMoebiusWeight c

/-- Exact dyadic compression of every complete lower-cofactor prefix. -/
theorem cofactorMobiusPrefixMass_eq_dyadicBoundaryMass (B : ℕ) :
    cofactorMobiusPrefixMass B = dyadicCofactorBoundaryMass B := by
  unfold cofactorMobiusPrefixMass dyadicCofactorBoundaryMass
  rw [sum_Icc_eq_odd_add_even, sum_evenCofactorPrefix_eq_neg_odd_half]
  have hsubset := oddCofactorPrefix_half_subset B
  have hpartition :
      (∑ c ∈ oddCofactorPrefix B \ oddCofactorPrefix (B / 2),
          canonicalMoebiusWeight c) +
        ∑ c ∈ oddCofactorPrefix (B / 2), canonicalMoebiusWeight c =
          ∑ c ∈ oddCofactorPrefix B, canonicalMoebiusWeight c := by
    exact Finset.sum_sdiff hsubset
  unfold dyadicCofactorBoundary
  calc
    (∑ c ∈ oddCofactorPrefix B, canonicalMoebiusWeight c) +
          -∑ c ∈ oddCofactorPrefix (B / 2), canonicalMoebiusWeight c =
        (∑ c ∈ oddCofactorPrefix B, canonicalMoebiusWeight c) -
          ∑ c ∈ oddCofactorPrefix (B / 2), canonicalMoebiusWeight c := by ring
    _ = ∑ c ∈ oddCofactorPrefix B \ oddCofactorPrefix (B / 2),
          canonicalMoebiusWeight c := by
      exact (eq_sub_of_add_eq hpartition).symm

/-! ## Exact compression of the complete transport term -/

/-- Dyadic boundary mass in the lower-cofactor fiber of an upper prime `q`. -/
def dyadicPrimeFiberBoundaryMass (R q : ℕ) : ℂ :=
  dyadicCofactorBoundaryMass (squareRootEndpoint R / q)

/-- The complete paper transport term after exact dyadic compression. -/
def squareRootDyadicTransportBoundaryMass (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
    if q.Prime then dyadicPrimeFiberBoundaryMass R q else 0

/-- For `q > R > 0`, the reciprocal cofactor cutoff lies strictly below `R`. -/
theorem squareRootEndpoint_div_lt
    {R q : ℕ} (hR : 0 < R) (hRq : R < q) (hq : 0 < q) :
    squareRootEndpoint R / q < R := by
  apply (Nat.div_lt_iff_lt_mul hq).2
  unfold squareRootEndpoint
  have hmul : R ^ 2 < R * q := by
    nlinarith
  exact lt_of_le_of_lt (Nat.sub_le _ _) hmul

/-- Each prime-first lower-cofactor fiber is exactly the positive Möbius prefix
through the reciprocal cutoff. -/
theorem primeDilatedLowCofactorMass_eq_cofactorMobiusPrefixMass
    (R q : ℕ) (hR : 0 < R) (hRq : R < q) (hq : 0 < q) :
    primeDilatedLowCofactorMass R q =
      cofactorMobiusPrefixMass (squareRootEndpoint R / q) := by
  unfold primeDilatedLowCofactorMass cofactorMobiusPrefixMass
  have hBlt := squareRootEndpoint_div_lt hR hRq hq
  have hset :
      (Finset.Ico 1 R).filter
          (fun c => c * q ≤ squareRootEndpoint R) =
        Finset.Icc 1 (squareRootEndpoint R / q) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hc1, hcR⟩, hmul⟩
      exact ⟨hc1, (Nat.le_div_iff_mul_le hq).2 hmul⟩
    · rintro ⟨hc1, hcB⟩
      exact ⟨⟨hc1, lt_of_le_of_lt hcB hBlt⟩,
        (Nat.le_div_iff_mul_le hq).1 hcB⟩
  calc
    (∑ c ∈ Finset.Ico 1 R,
        if c * q ≤ squareRootEndpoint R then canonicalMoebiusWeight c else 0) =
      ∑ c ∈ (Finset.Ico 1 R).filter
          (fun c => c * q ≤ squareRootEndpoint R), canonicalMoebiusWeight c := by
        rw [Finset.sum_filter]
    _ = ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
          canonicalMoebiusWeight c := by rw [hset]

/-- Exact odd-boundary form of every prime-first lower-cofactor fiber. -/
theorem primeDilatedLowCofactorMass_eq_dyadicPrimeFiberBoundaryMass
    (R q : ℕ) (hR : 0 < R) (hRq : R < q) (hq : 0 < q) :
    primeDilatedLowCofactorMass R q =
      dyadicPrimeFiberBoundaryMass R q := by
  rw [primeDilatedLowCofactorMass_eq_cofactorMobiusPrefixMass R q hR hRq hq]
  exact cofactorMobiusPrefixMass_eq_dyadicBoundaryMass _

/-- The original complete transport sum equals the exact dyadic odd-cofactor
boundary sum.  No transport source is discarded; the equality is finite Fubini
followed by Möbius doubling inside every prime fiber. -/
theorem squareRootTransportCofactorFirst_eq_dyadicBoundaryMass (R : ℕ) :
    squareRootTransportCofactorFirst R =
      squareRootDyadicTransportBoundaryMass R := by
  rw [squareRootTransportCofactorFirst_eq_primeFirst]
  by_cases hR0 : R = 0
  · subst R
    simp [squareRootTransportPrimeFirst, squareRootDyadicTransportBoundaryMass,
      squareRootEndpoint]
  · have hR : 0 < R := Nat.pos_of_ne_zero hR0
    unfold squareRootTransportPrimeFirst squareRootDyadicTransportBoundaryMass
    apply Finset.sum_congr rfl
    intro q hqmem
    by_cases hprime : q.Prime
    · have hRq : R < q := (Finset.mem_Ioc.mp hqmem).1
      have hqpos : 0 < q := hprime.pos
      simp only [hprime, if_true]
      exact primeDilatedLowCofactorMass_eq_dyadicPrimeFiberBoundaryMass
        R q hR hRq hqpos
    · simp [hprime]

end RHLean.Proof
