import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.PrimeCombVisualizationFrames

/-!
# Large-prime terminal flip layers

After the square-root phase, a surviving squarefree tail seat has the form
`c*q` with `q` the unique unprocessed large prime.  The lower cofactor `c` has
already acquired its final Möbius sign, and adjoining `q` flips that sign once.
This module isolates that terminal flip in reciprocal quotient layers.

For the canonical endpoint `X_R = R^2 - 1`, primes `q > R` are grouped by
`k = floor(X_R / q)`.  In one fixed layer, every prime has exactly the same
available cofactor set `2,...,k`.  The signed terminal-flip imbalance per prime
is therefore

`sum_{2 <= c <= k} -mu(c) = 1 - M(k)`.

Thus the high-prime coordinate contributes only the positive layer population;
all parity data is already lower-scale.  The first downward terminal flip
requires the positive Möbius cofactor `6`, so layers `k <= 5` are exactly
up-only.  Equivalently, `q > X/6` forces the reciprocal index below `6`.

Finally, summing the middle layers and swapping the order of summation gives the
exact dual weighted form

`- sum_{2 <= c < R} mu(c) * (pi(floor(X_R/c)) - pi(R))`.

The last section puts the untouched prime seat `c = 1` back into the same signed
object.  The complete post-root prime fibre is then `-M(k)`, not `1-M(k)`, and
the upper `k=1` block must remain paired with the first middle layers.  We define
its truncated packet and give the exact finite Abel form before any completion
of the reciprocal coordinate.

No estimate, asymptotic, PNT input, RH hypothesis, or norm bound is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- **Terminal sign law.**  If `q` lies above the square root of `X` and the
positive cofactor `c` still satisfies `c*q <= X`, then `c < q`, so adjoining the
fresh prime `q` negates the Möbius sign of the already-completed cofactor. -/
theorem moebius_mul_largePrime_eq_neg_cofactor
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hcpos : 0 < c) (hcqX : c * q ≤ X) :
    μ (c * q) = -μ c := by
  have hcRoot : c ≤ Nat.sqrt X :=
    cofactor_le_sqrt_of_largePrime_mul_le hqRoot hcqX
  have hcq : c < q := hcRoot.trans_lt hqRoot
  have hcop : Nat.Coprime c q :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hcpos) hcq hq).symm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- Complex-weight form of the same terminal sign law. -/
theorem canonicalMoebiusWeight_mul_largePrime_eq_neg_cofactor
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hcpos : 0 < c) (hcqX : c * q ≤ X) :
    canonicalMoebiusWeight (c * q) = -canonicalMoebiusWeight c := by
  have hcRoot : c ≤ Nat.sqrt X :=
    cofactor_le_sqrt_of_largePrime_mul_le hqRoot hcqX
  exact canonicalMoebiusWeight_mul_prime_eq_neg
    hcpos (hcRoot.trans_lt hqRoot) hq

/-- The squarefree-zero convention is preserved by the terminal sign law: if
the lower cofactor has already been killed, adjoining the large prime leaves
zero. -/
theorem moebius_mul_largePrime_eq_zero_of_cofactor_not_squarefree
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hcpos : 0 < c) (hcqX : c * q ≤ X)
    (hnsq : ¬ Squarefree c) :
    μ (c * q) = 0 := by
  rw [moebius_mul_largePrime_eq_neg_cofactor hq hqRoot hcpos hcqX,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
  simp

/-- Signed cofactor contribution of one terminal reciprocal layer.  The unit
cofactor `c=1` is excluded because it is an untouched prime seat rather than a
flip. -/
def largePrimeTerminalCofactorImbalance (k : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 2 k, -canonicalMoebiusWeight c

/-- **All parity in one layer is lower-scale.**  For every nonempty positive
prefix, the signed terminal-flip imbalance per large prime is exactly
`1 - M(k)`. -/
theorem largePrimeTerminalCofactorImbalance_eq_one_sub_mertens
    (k : ℕ) (hk : 1 ≤ k) :
    largePrimeTerminalCofactorImbalance k = 1 - mertensSummatory k := by
  have hset :
      Finset.Icc 1 k = ({1} : Finset ℕ) ∪ Finset.Icc 2 k := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 k) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rw [Finset.mem_singleton] at hc1
    subst c
    simp at hc2
  have hprefix :
      cofactorMobiusPrefixMass k =
        canonicalMoebiusWeight 1 +
          ∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c := by
    unfold cofactorMobiusPrefixMass
    rw [hset, Finset.sum_union hdisj]
    simp
  rw [cofactorMobiusPrefixMass_eq_mertensSummatory k] at hprefix
  have hmu1 : canonicalMoebiusWeight 1 = 1 := by
    simp [canonicalMoebiusWeight]
  rw [hmu1] at hprefix
  have hsum :
      (∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c) =
        mertensSummatory k - 1 := by
    calc
      (∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c) =
          (1 + ∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c) - 1 := by ring
      _ = mertensSummatory k - 1 := by rw [← hprefix]
  unfold largePrimeTerminalCofactorImbalance
  calc
    (∑ c ∈ Finset.Icc 2 k, -canonicalMoebiusWeight c) =
        -(∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c) := by simp
    _ = 1 - mertensSummatory k := by rw [hsum]; ring

/-- Prime population of the canonical reciprocal layer `k`. -/
def squareRootTerminalFlipLayerPrimeCount (R k : ℕ) : ℂ :=
  ((squareRootMiddleHarmonicLayerPrimes R k).card : ℂ)

/-- Signed terminal-flip imbalance of one reciprocal layer. -/
def squareRootTerminalFlipLayerImbalance (R k : ℕ) : ℂ :=
  squareRootTerminalFlipLayerPrimeCount R k *
    largePrimeTerminalCofactorImbalance k

/-- **Fixed-segment imbalance.**  The large-prime coordinate is only a positive
multiplicity profile: one reciprocal layer is exactly
`N_R(k) * (1 - M(k))`. -/
theorem squareRootTerminalFlipLayerImbalance_eq_count_mul_one_sub_mertens
    (R k : ℕ) (hk : 1 ≤ k) :
    squareRootTerminalFlipLayerImbalance R k =
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) k *
        (1 - mertensSummatory k) := by
  unfold squareRootTerminalFlipLayerImbalance
    squareRootTerminalFlipLayerPrimeCount
  rw [largePrimeTerminalCofactorImbalance_eq_one_sub_mertens k hk,
    squareRootMiddleHarmonicLayer_card_eq_reciprocalPrimeCount]

/-- Cofactors whose completed lower-scale sign is positive, hence whose fresh
large-prime terminal flip points downward. -/
def largePrimeTerminalDownCofactors (k : ℕ) : Finset ℕ :=
  (Finset.Icc 2 k).filter fun c => μ c = 1

/-- Cofactors whose completed lower-scale sign is negative, hence whose fresh
large-prime terminal flip points upward. -/
def largePrimeTerminalUpCofactors (k : ℕ) : Finset ℕ :=
  (Finset.Icc 2 k).filter fun c => μ c = -1

private theorem moebius_ne_one_of_two_le_of_le_five
    {c : ℕ} (hc2 : 2 ≤ c) (hc5 : c ≤ 5) :
    μ c ≠ 1 := by
  have hcases : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]
    norm_num
  · have hnsq : ¬ Squarefree 4 := by
      rw [Nat.squarefree_iff_prime_squarefree]
      push_neg
      exact ⟨2, Nat.prime_two, by norm_num⟩
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
    norm_num
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)]
    norm_num

/-- **Sharp one-way threshold in reciprocal coordinates.**  Before cofactor `6`
can enter, no positive Möbius cofactor exists, so every nonzero terminal flip
points upward. -/
theorem largePrimeTerminalDownCofactors_eq_empty_of_le_five
    {k : ℕ} (hk : k ≤ 5) :
    largePrimeTerminalDownCofactors k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  rcases Finset.mem_filter.mp hc with ⟨hcRange, hmu⟩
  rcases Finset.mem_Icc.mp hcRange with ⟨hc2, hck⟩
  exact (moebius_ne_one_of_two_le_of_le_five hc2 (hck.trans hk)) hmu

/-- The down-flip count therefore vanishes exactly throughout `k <= 5`. -/
theorem largePrimeTerminalDownCount_eq_zero_of_le_five
    {k : ℕ} (hk : k ≤ 5) :
    (largePrimeTerminalDownCofactors k).card = 0 := by
  rw [largePrimeTerminalDownCofactors_eq_empty_of_le_five hk]
  simp

/-- `q > X/6` is exactly strong enough to force the reciprocal quotient below
`6`; this is the geometric form of the `k <= 5` one-way threshold. -/
theorem reciprocalIndex_le_five_of_sixth_lt
    {X q : ℕ} (hqpos : 0 < q) (hqSixth : X / 6 < q) :
    X / q ≤ 5 := by
  have hXlt : X < q * 6 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)).1 hqSixth
  have hXlt' : X < 6 * q := by
    simpa [Nat.mul_comm] using hXlt
  have hdivlt : X / q < 6 :=
    (Nat.div_lt_iff_lt_mul hqpos).2 hXlt'
  omega

private theorem moebius_eq_neg_one_of_two_le_of_le_five_of_ne_zero
    {c : ℕ} (hc2 : 2 ≤ c) (hc5 : c ≤ 5) (hmu0 : μ c ≠ 0) :
    μ c = -1 := by
  have hcases : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]
  · have hnsq : ¬ Squarefree 4 := by
      rw [Nat.squarefree_iff_prime_squarefree]
      push_neg
      exact ⟨2, Nat.prime_two, by norm_num⟩
    have hzero : μ 4 = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    exact (hmu0 hzero).elim
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)]

/-- **Pointwise up-only form.**  In the genuine terminal sector, if
`q > X/6`, every surviving nonzero cofactor seat flips from `-1` to `+1`. -/
theorem largePrimeTerminalFlip_up_only_of_sixth_lt
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hqSixth : X / 6 < q) (hc2 : 2 ≤ c)
    (hcqX : c * q ≤ X) (hmu0 : μ c ≠ 0) :
    μ (c * q) = 1 := by
  have hcQuot : c ≤ X / q :=
    (Nat.le_div_iff_mul_le hq.pos).2 hcqX
  have hk5 : X / q ≤ 5 :=
    reciprocalIndex_le_five_of_sixth_lt hq.pos hqSixth
  have hc5 : c ≤ 5 := hcQuot.trans hk5
  have hmu : μ c = -1 :=
    moebius_eq_neg_one_of_two_le_of_le_five_of_ne_zero hc2 hc5 hmu0
  rw [moebius_mul_largePrime_eq_neg_cofactor hq hqRoot (by omega) hcqX, hmu]
  norm_num

/-- Total signed terminal-flip contribution of the canonical middle prime
corridor.  It is the middle prime population minus the ordinary middle Mertens
tail, because every large prime contributes `1 - M(floor(X_R/q))`. -/
def squareRootMiddleTerminalFlipMass (R : ℕ) : ℂ :=
  ((squareRootMiddleFibrePrimes R).card : ℂ) -
    squareRootMiddleMertensTail R

/-- Cofactor-first form of the same terminal-flip contribution. -/
def squareRootMiddleTerminalFlipDual (R : ℕ) : ℂ :=
  -∑ c ∈ Finset.Icc 2 (R - 1),
    canonicalMoebiusWeight c *
      ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
        (Nat.primeCounting R : ℂ))

/-- **Exact dual reindexing.**  The entire middle terminal-flip mass is the
weighted lower-scale Möbius sum

`- sum_{2 <= c < R} mu(c) * (pi(floor(X_R/c)) - pi(R))`.

The `c=2` term supplies exactly the raw middle-prime population, while the
`c>=3` terms are the already-formalized swapped middle Mertens tail. -/
theorem squareRootMiddleTerminalFlipMass_eq_dual
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleTerminalFlipMass R =
      squareRootMiddleTerminalFlipDual R := by
  have hset :
      Finset.Icc 2 (R - 1) =
        ({2} : Finset ℕ) ∪ Finset.Icc 3 (R - 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({2} : Finset ℕ) (Finset.Icc 3 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro c hc2 hc3
    rw [Finset.mem_singleton] at hc2
    subst c
    simp at hc3
  have hmu2 : canonicalMoebiusWeight 2 = -1 := by
    unfold canonicalMoebiusWeight
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  have hmidCount :=
    squareRootMiddleFibrePrimes_card_add_primeCounting_root R hR
  have hmidCountC :
      ((squareRootMiddleFibrePrimes R).card : ℂ) =
        (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) -
          (Nat.primeCounting R : ℂ) := by
    have hcast :
        ((squareRootMiddleFibrePrimes R).card : ℂ) +
            (Nat.primeCounting R : ℂ) =
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) := by
      exact_mod_cast hmidCount
    linear_combination hcast
  unfold squareRootMiddleTerminalFlipMass squareRootMiddleTerminalFlipDual
  rw [squareRootMiddleMertensTail_eq_swappedPrimeCounting R hR,
    hset, Finset.sum_union hdisj]
  simp only [Finset.sum_singleton]
  rw [hmu2, hmidCountC]
  ring

/-! ## Put the untouched prime seat back: truncated upper-middle packets -/

/-- Clipped post-root prime prefix at reciprocal depth `d`.

`P_R(d)` counts primes in `(R, max R floor(X_R/d)]`.  The clipping makes the
forward-difference identity valid even at the terminal quotient boundary. -/
def squareRootPostRootPrimePrefix (R d : ℕ) : ℂ :=
  primeSievePrefixPrimeCount (max R (squareRootEndpoint R / d)) -
    primeSievePrefixPrimeCount R

/-- The complete signed post-root packet through reciprocal layer `K`.

The prime seat `c=1` is included.  Hence one complete `d`-fibre contributes
`-M(d)`, and `d=1` is the same-sign upper block rather than a discarded edge. -/
def squareRootTruncatedUpperMiddlePacket (R K : ℕ) : ℂ :=
  -∑ d ∈ Finset.Icc 1 K,
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
      mertensSummatory d

/-- On every physical quotient-support layer, the reciprocal prime population
is the forward difference of the clipped post-root prefix. -/
theorem squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff
    {R d : ℕ} (hR : 1 ≤ R) (hd1 : 1 ≤ d) (hdR : d < R) :
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d =
      squareRootPostRootPrimePrefix R d -
        squareRootPostRootPrimePrefix R (d + 1) := by
  have htop : squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R hR
  have hdSupport :
      d ∈ primeSieveQuotientSupport R (squareRootEndpoint R) := by
    unfold primeSieveQuotientSupport
    rw [htop]
    exact Finset.mem_Icc.mpr ⟨hd1, by omega⟩
  have hRlt : R < squareRootEndpoint R / d :=
    lt_div_of_mem_primeSieveQuotientSupport hdSupport
  have hmono :
      squareRootEndpoint R / (d + 1) ≤ squareRootEndpoint R / d :=
    Nat.div_le_div_left (by omega) (by omega)
  have hle :
      primeSieveReciprocalLower R (squareRootEndpoint R) d ≤
        primeSieveReciprocalUpper (squareRootEndpoint R) d := by
    unfold primeSieveReciprocalLower primeSieveReciprocalUpper
    exact max_le hRlt.le hmono
  rw [primeSieveReciprocalPrimeCount_eq_sub R (squareRootEndpoint R) d hle]
  unfold squareRootPostRootPrimePrefix
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [max_eq_right hRlt.le]
  ring

/-- **Exact finite Abel packet.**  The truncated upper/middle object is a
Möbius-weighted post-root prime prefix plus one terminal `K` boundary.  This is
only a coordinate change; it asserts no estimate. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_abel
    (R K : ℕ) (hR : 1 ≤ R) (hK : K < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      -(∑ d ∈ Finset.Icc 1 K,
          (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d) +
        mertensSummatory K * squareRootPostRootPrimePrefix R (K + 1) := by
  have hrewrite :
      (∑ d ∈ Finset.Icc 1 K,
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d) =
        ∑ d ∈ Finset.Icc 1 K,
          mertensSummatory d *
            (squareRootPostRootPrimePrefix R d -
              squareRootPostRootPrimePrefix R (d + 1)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hdK⟩
    rw [squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff
      hR hd1 (hdK.trans_lt hK)]
    ring
  unfold squareRootTruncatedUpperMiddlePacket
  rw [hrewrite, sum_mertensSummatory_mul_forwardDifference]
  ring

/-- Unit-separated Abel form.  The upper boundary and the shallow middle
corrections remain inside one exact packet. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_upper_add_abelMiddle
    (R K : ℕ) (hR : 1 ≤ R) (hK1 : 1 ≤ K) (hKR : K < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      -squareRootPostRootPrimePrefix R 1 -
        (∑ d ∈ Finset.Icc 2 K,
          (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d) +
        mertensSummatory K * squareRootPostRootPrimePrefix R (K + 1) := by
  rw [squareRootTruncatedUpperMiddlePacket_eq_abel R K hR hKR]
  have hset :
      Finset.Icc 1 K = ({1} : Finset ℕ) ∪ Finset.Icc 2 K := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 K) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_singleton] at hd1
    subst d
    simp at hd2
  rw [hset, Finset.sum_union hdisj]
  simp
  ring

/-- The first reciprocal layer is exactly the same-sign top-prime block, with
its actual source sign.  This is the formal guardrail against asking the middle
to self-cancel. -/
theorem squareRootTruncatedUpperMiddlePacket_one_eq_neg_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTruncatedUpperMiddlePacket R 1 =
      -((squareRootTopFibrePrimes R).card : ℂ) := by
  unfold squareRootTruncatedUpperMiddlePacket
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  simp only [Finset.sum_singleton]
  rw [squareRootReciprocalPrimeCount_one_eq_topCard R hR]
  have hM1 : mertensSummatory 1 = 1 := by
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
    simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]
  rw [hM1]
  ring

/-! ## Reciprocal depth as a prime cutoff -/

/-- For a positive prime-coordinate candidate `q`, being above the reciprocal
cutoff `X/(K+1)` is exactly the same as having quotient depth at most `K`.
This is the elementary bridge between the `q`-picture and the truncated
`k`-packet. -/
theorem reciprocalIndex_le_iff_cutoff_lt
    {X q K : ℕ} (hq : 0 < q) :
    X / q ≤ K ↔ X / (K + 1) < q := by
  constructor
  · intro h
    have hlt : X / q < K + 1 := by omega
    have hmul : X < (K + 1) * q :=
      (Nat.div_lt_iff_lt_mul hq).1 hlt
    have hmul' : X < q * (K + 1) := by
      simpa [Nat.mul_comm] using hmul
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < K + 1)).2 hmul'
  · intro h
    have hmul : X < q * (K + 1) :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < K + 1)).1 h
    have hmul' : X < (K + 1) * q := by
      simpa [Nat.mul_comm] using hmul
    have hlt : X / q < K + 1 :=
      (Nat.div_lt_iff_lt_mul hq).2 hmul'
    omega

/-- Prime cutoff corresponding to a truncated reciprocal depth `K`. -/
def squareRootTruncatedPrimeCutoff (R K : ℕ) : ℕ :=
  squareRootEndpoint R / (K + 1)

/-- The reciprocal cutoff and quotient-depth conditions are literally
interchangeable at the square endpoint. -/
theorem squareRoot_reciprocalIndex_le_iff_truncatedPrimeCutoff_lt
    {R q K : ℕ} (hq : 0 < q) :
    squareRootEndpoint R / q ≤ K ↔
      squareRootTruncatedPrimeCutoff R K < q := by
  exact reciprocalIndex_le_iff_cutoff_lt hq

/-- If the truncated depth remains strictly inside the root corridor, its prime
cutoff is still strictly post-root.  Thus shallow `K` means a genuinely high
prime window, not a return to the root seam. -/
theorem squareRoot_root_lt_truncatedPrimeCutoff
    {R K : ℕ} (hR : 1 ≤ R) (hK : K + 1 < R) :
    R < squareRootTruncatedPrimeCutoff R K := by
  have htop : squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R hR
  have hmem :
      K + 1 ∈ primeSieveQuotientSupport R (squareRootEndpoint R) := by
    unfold primeSieveQuotientSupport
    rw [htop]
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  exact lt_div_of_mem_primeSieveQuotientSupport hmem

/-! ## The incomplete cap and its surviving finite-difference structure -/

/-- Prime multiplicity above the common lower boundary of a truncated packet.
The same boundary `P_R(K+1)` is subtracted from every cofactor coordinate. -/
def squareRootShallowCapWeight (R K d : ℕ) : ℂ :=
  squareRootPostRootPrimePrefix R d -
    squareRootPostRootPrimePrefix R (K + 1)

/-- The common lower prime boundary cancels when two cap weights are differenced. -/
theorem squareRootShallowCapWeight_sub
    (R K a b : ℕ) :
    squareRootShallowCapWeight R K a - squareRootShallowCapWeight R K b =
      squareRootPostRootPrimePrefix R a - squareRootPostRootPrimePrefix R b := by
  unfold squareRootShallowCapWeight
  ring

/-- **Direct incomplete-cap form.**  The Abel boundary exactly subtracts the
complete lower prime rectangle, leaving one common-boundary cap.  Upper and
middle therefore remain combined before any norm or completion. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_shallowCap
    (R K : ℕ) (hR : 1 ≤ R) (hKR : K < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      -∑ d ∈ Finset.Icc 1 K,
        (((μ d : ℤ) : ℂ)) * squareRootShallowCapWeight R K d := by
  rw [squareRootTruncatedUpperMiddlePacket_eq_abel R K hR hKR]
  have hmu :
      (∑ d ∈ Finset.Icc 1 K, (((μ d : ℤ) : ℂ))) = mertensSummatory K := by
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory K]
    rfl
  rw [← hmu]
  unfold squareRootShallowCapWeight
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

/-- **Fresh-prime finite difference inside the incomplete cap.**  Pairing a
cofactor `d` with its fresh-prime child `d*p` cancels the common truncated lower
boundary exactly.  What survives is only the nested prime-prefix difference
between `d` and `d*p`; the weight is therefore nonconstant on the completed
pair, unlike the dead completed-fibre routes. -/
theorem squareRootShallowCap_moebiusPrimePair
    {R K d p : ℕ} (hd : 0 < d) (hdp : d < p) (hp : p.Prime) :
    (-canonicalMoebiusWeight d * squareRootShallowCapWeight R K d) +
        (-canonicalMoebiusWeight (d * p) *
          squareRootShallowCapWeight R K (d * p)) =
      -canonicalMoebiusWeight d *
        (squareRootPostRootPrimePrefix R d -
          squareRootPostRootPrimePrefix R (d * p)) := by
  rw [canonicalMoebiusWeight_mul_prime_eq_neg hd hdp hp]
  unfold squareRootShallowCapWeight
  ring

/-! ## Exact coefficient packages behind the shallow-depth diagnostic -/

/-- The first reciprocal coefficient generated by summation by parts.  Written
as a Mertens-weighted finite difference, it is exactly the coefficient that
appears when a slowly varying reciprocal prime-density weight is expanded. -/
def squareRootPacketReciprocalCoefficient (K : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 K,
    mertensSummatory d *
      ((1 : ℂ) / (d : ℂ) - (1 : ℂ) / ((d + 1 : ℕ) : ℂ))

/-- Exact Möbius-boundary form of the first reciprocal coefficient:

`S_K = sum_{d<=K} mu(d)/d - M(K)/(K+1)`.
-/
theorem squareRootPacketReciprocalCoefficient_eq_moebiusBoundary
    (K : ℕ) :
    squareRootPacketReciprocalCoefficient K =
      (∑ d ∈ Finset.Icc 1 K,
        (((μ d : ℤ) : ℂ)) * ((1 : ℂ) / (d : ℂ))) -
      mertensSummatory K * ((1 : ℂ) / ((K + 1 : ℕ) : ℂ)) := by
  simpa [squareRootPacketReciprocalCoefficient] using
    (sum_mertensSummatory_mul_forwardDifference
      (fun d : ℕ => (1 : ℂ) / (d : ℂ)) K)

/-- Reciprocal logarithmic weight used by the next finite coefficient. -/
def squareRootPacketLogReciprocalValue (d : ℕ) : ℂ :=
  (((Real.log (d : ℝ)) / (d : ℝ) : ℝ) : ℂ)

/-- The next exact finite-difference coefficient, kept separate from any
asymptotic claim about its numerical value. -/
def squareRootPacketLogReciprocalCoefficient (K : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 K,
    mertensSummatory d *
      (squareRootPacketLogReciprocalValue d -
        squareRootPacketLogReciprocalValue (d + 1))

/-- Exact Möbius-boundary form of the logarithmic reciprocal coefficient. -/
theorem squareRootPacketLogReciprocalCoefficient_eq_moebiusBoundary
    (K : ℕ) :
    squareRootPacketLogReciprocalCoefficient K =
      (∑ d ∈ Finset.Icc 1 K,
        (((μ d : ℤ) : ℂ)) * squareRootPacketLogReciprocalValue d) -
      mertensSummatory K * squareRootPacketLogReciprocalValue (K + 1) := by
  simpa [squareRootPacketLogReciprocalCoefficient] using
    (sum_mertensSummatory_mul_forwardDifference
      squareRootPacketLogReciprocalValue K)

/-! ## Integer shadow, sign crossing, and partial-layer interpolation -/

/-- Integer-valued ordinary Mertens prefix, used only so sign crossings can be
stated in the ordered ring `ℤ`. -/
def squareRootMertensInt (K : ℕ) : ℤ :=
  ∑ d ∈ Finset.Icc 1 K, μ d

/-- The integer shadow is exactly the repository's complex Mertens sum after
casting. -/
theorem squareRootMertensInt_cast_complex (K : ℕ) :
    ((squareRootMertensInt K : ℤ) : ℂ) = mertensSummatory K := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory K]
  simp [squareRootMertensInt, cofactorMobiusPrefixMass, canonicalMoebiusWeight]

/-- Honest natural cardinality of one reciprocal prime layer. -/
def squareRootReciprocalPrimeLayerCard (R K : ℕ) : ℕ :=
  ((primeSieveReciprocalInterval R (squareRootEndpoint R) K).filter Nat.Prime).card

/-- The existing complex prime-count coordinate is just the cast of the honest
layer cardinality. -/
theorem squareRootReciprocalPrimeCount_eq_layerCard
    (R K : ℕ) :
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) K =
      (squareRootReciprocalPrimeLayerCard R K : ℂ) := by
  simpa [squareRootReciprocalPrimeLayerCard] using
    (primeSieveReciprocalPrimeCount_eq_card R (squareRootEndpoint R) K)

/-- Integer shadow of the complete truncated upper-middle packet. -/
def squareRootTruncatedUpperMiddlePacketInt (R K : ℕ) : ℤ :=
  -∑ d ∈ Finset.Icc 1 K,
    (squareRootReciprocalPrimeLayerCard R d : ℤ) * squareRootMertensInt d

/-- Casting the ordered integer packet recovers the existing complex packet
exactly. -/
theorem squareRootTruncatedUpperMiddlePacketInt_cast_complex
    (R K : ℕ) :
    ((squareRootTruncatedUpperMiddlePacketInt R K : ℤ) : ℂ) =
      squareRootTruncatedUpperMiddlePacket R K := by
  unfold squareRootTruncatedUpperMiddlePacketInt
    squareRootTruncatedUpperMiddlePacket
  push_cast
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro d _hd
  rw [squareRootMertensInt_cast_complex,
    ← squareRootReciprocalPrimeCount_eq_layerCard]

@[simp] theorem squareRootTruncatedUpperMiddlePacketInt_zero (R : ℕ) :
    squareRootTruncatedUpperMiddlePacketInt R 0 = 0 := by
  simp [squareRootTruncatedUpperMiddlePacketInt]

/-- One whole reciprocal layer changes the ordered packet by exactly
`-N_R(K+1) M(K+1)`. -/
theorem squareRootTruncatedUpperMiddlePacketInt_succ
    (R K : ℕ) :
    squareRootTruncatedUpperMiddlePacketInt R (K + 1) =
      squareRootTruncatedUpperMiddlePacketInt R K -
        (squareRootReciprocalPrimeLayerCard R (K + 1) : ℤ) *
          squareRootMertensInt (K + 1) := by
  unfold squareRootTruncatedUpperMiddlePacketInt
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
  ring

/-- Exact sign-crossing predicate for the ordered truncated packet. -/
def SquareRootPacketCrossesAt (R K : ℕ) : Prop :=
  1 ≤ K ∧
    squareRootTruncatedUpperMiddlePacketInt R (K - 1) < 0 ∧
      0 ≤ squareRootTruncatedUpperMiddlePacketInt R K

/-- A crossing layer must be nonempty and its lower Mertens value must be
negative.  Thus the upward jump is not an independent high-prime sign: it is a
positive multiplicity times the already-completed lower sign `-M(K)`. -/
theorem squareRootPacketCrossing_forces_layer_nonempty_and_mertens_neg
    {R K : ℕ} (hcross : SquareRootPacketCrossesAt R K) :
    0 < squareRootReciprocalPrimeLayerCard R K ∧
      squareRootMertensInt K < 0 := by
  rcases hcross with ⟨hK, hprev, hnow⟩
  have hstep := squareRootTruncatedUpperMiddlePacketInt_succ R (K - 1)
  rw [Nat.sub_add_cancel hK] at hstep
  have hprod :
      (squareRootReciprocalPrimeLayerCard R K : ℤ) * squareRootMertensInt K < 0 := by
    linarith
  have hM : squareRootMertensInt K < 0 := by
    by_contra hnot
    have hM0 : 0 ≤ squareRootMertensInt K := le_of_not_gt hnot
    have hN0 : 0 ≤ (squareRootReciprocalPrimeLayerCard R K : ℤ) := by positivity
    have hmul := mul_nonneg hN0 hM0
    linarith
  have hN : 0 < squareRootReciprocalPrimeLayerCard R K := by
    by_contra hnot
    have hz : squareRootReciprocalPrimeLayerCard R K = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hz] at hprod
    norm_num at hprod
  exact ⟨hN, hM⟩

/-- A sign crossing therefore occurs on an actual post-root prime quotient
fibre; it cannot be an empty numerical layer. -/
theorem squareRootPacketCrossing_has_postRootPrime
    {R K : ℕ} (hcross : SquareRootPacketCrossesAt R K) :
    ∃ q : ℕ, q.Prime ∧ R < q ∧ q ≤ squareRootEndpoint R ∧
      squareRootEndpoint R / q = K := by
  have hK1 : 1 ≤ K := hcross.1
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK1
  have hcard :=
    (squareRootPacketCrossing_forces_layer_nonempty_and_mertens_neg hcross).1
  have hcard' :
      0 < ((primeSieveReciprocalInterval R (squareRootEndpoint R) K).filter
        Nat.Prime).card := by
    simpa [squareRootReciprocalPrimeLayerCard] using hcard
  have hne :
      ((primeSieveReciprocalInterval R (squareRootEndpoint R) K).filter
        Nat.Prime).Nonempty := Finset.card_pos.mp hcard'
  rcases hne with ⟨q, hq⟩
  rcases Finset.mem_filter.mp hq with ⟨hqInterval, hqPrime⟩
  have hqFiber : q ∈ primeSieveQuotientFiber R (squareRootEndpoint R) K := by
    rw [primeSieveQuotientFiber_eq_reciprocalInterval
      R (squareRootEndpoint R) K hK]
    exact hqInterval
  rcases mem_primeSieveQuotientFiber.mp hqFiber with ⟨hRq, hqX, hqK⟩
  exact ⟨q, hqPrime, hRq, hqX, hqK⟩

/-- Packet value after admitting exactly `j` prime seats from the crossing
layer.  This count-level interpolation is independent of how those primes are
ordered inside the layer because every seat has the same increment `-M(K)`. -/
def squareRootCrossingLayerPartialPacketInt (R K j : ℕ) : ℤ :=
  squareRootTruncatedUpperMiddlePacketInt R (K - 1) -
    (j : ℤ) * squareRootMertensInt K

@[simp] theorem squareRootCrossingLayerPartialPacketInt_zero
    (R K : ℕ) :
    squareRootCrossingLayerPartialPacketInt R K 0 =
      squareRootTruncatedUpperMiddlePacketInt R (K - 1) := by
  simp [squareRootCrossingLayerPartialPacketInt]

/-- Each additional prime in a fixed reciprocal layer changes the partial
packet by exactly the same lower-scale amount `-M(K)`. -/
theorem squareRootCrossingLayerPartialPacketInt_succ
    (R K j : ℕ) :
    squareRootCrossingLayerPartialPacketInt R K (j + 1) =
      squareRootCrossingLayerPartialPacketInt R K j - squareRootMertensInt K := by
  unfold squareRootCrossingLayerPartialPacketInt
  push_cast
  ring

/-- Admitting every prime in the layer recovers the next whole-layer packet. -/
theorem squareRootCrossingLayerPartialPacketInt_full
    (R K : ℕ) (hK : 1 ≤ K) :
    squareRootCrossingLayerPartialPacketInt R K
        (squareRootReciprocalPrimeLayerCard R K) =
      squareRootTruncatedUpperMiddlePacketInt R K := by
  have hstep := squareRootTruncatedUpperMiddlePacketInt_succ R (K - 1)
  rw [Nat.sub_add_cancel hK] at hstep
  simpa [squareRootCrossingLayerPartialPacketInt] using hstep.symm

/-- Trivial but useful lower-scale bound: the magnitude of a negative Mertens
value is at most the number of available terms. -/
theorem neg_squareRootMertensInt_le_depth (K : ℕ) :
    -squareRootMertensInt K ≤ (K : ℤ) := by
  unfold squareRootMertensInt
  calc
    -(∑ d ∈ Finset.Icc 1 K, μ d) =
        ∑ d ∈ Finset.Icc 1 K, -μ d := by simp
    _ ≤ ∑ _d ∈ Finset.Icc 1 K, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro d _hd
      have h := ArithmeticFunction.abs_moebius_le_one (n := d)
      have hlo : (-1 : ℤ) ≤ μ d := (abs_le.mp h).1
      linarith
    _ = (K : ℤ) := by
      have hcard : (Finset.Icc 1 K).card = K := by
        rw [Nat.card_Icc]
        omega
      simp [hcard]

/-- **Discrete intermediate-value theorem for one crossing layer.**  If the
whole packet changes sign at `K`, then admitting a least sufficient number of
primes from that layer leaves a nonnegative residual strictly smaller than the
single-prime step `-M(K)`. -/
theorem squareRootPacketCrossing_exists_partial_residual
    {R K : ℕ} (hcross : SquareRootPacketCrossesAt R K) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R K ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R K j ∧
          squareRootCrossingLayerPartialPacketInt R K j <
            -squareRootMertensInt K := by
  classical
  have hK : 1 ≤ K := hcross.1
  have hprev := hcross.2.1
  have hnow := hcross.2.2
  let P : ℕ → Prop := fun j =>
    j ≤ squareRootReciprocalPrimeLayerCard R K ∧
      0 ≤ squareRootCrossingLayerPartialPacketInt R K j
  have hex : ∃ j, P j := by
    refine ⟨squareRootReciprocalPrimeLayerCard R K, le_rfl, ?_⟩
    rw [squareRootCrossingLayerPartialPacketInt_full R K hK]
    exact hnow
  let j := Nat.find hex
  have hj : P j := by
    exact Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra hnot
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero := hj.2
    rw [hj0, squareRootCrossingLayerPartialPacketInt_zero] at hzero
    linarith
  have hpredNeg : squareRootCrossingLayerPartialPacketInt R K (j - 1) < 0 := by
    by_contra hnot
    have hpredNonneg : 0 ≤ squareRootCrossingLayerPartialPacketInt R K (j - 1) :=
      le_of_not_gt hnot
    have hpredP : P (j - 1) :=
      ⟨(Nat.sub_le j 1).trans hj.1, hpredNonneg⟩
    have hfind := Nat.find_min' hex hpredP
    have hbad : j ≤ j - 1 := by
      simpa [j] using hfind
    omega
  have hsucc := squareRootCrossingLayerPartialPacketInt_succ R K (j - 1)
  rw [Nat.sub_add_cancel hjpos] at hsucc
  refine ⟨j, hj.1, hj.2, ?_⟩
  linarith

/-- Consequently the partial-layer residual is automatically smaller than the
reciprocal depth itself.  No prime-distribution estimate is used here. -/
theorem squareRootPacketCrossing_exists_partial_residual_lt_depth
    {R K : ℕ} (hcross : SquareRootPacketCrossesAt R K) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R K ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R K j ∧
          squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) := by
  rcases squareRootPacketCrossing_exists_partial_residual hcross with
    ⟨j, hj, hnonneg, hlt⟩
  exact ⟨j, hj, hnonneg,
    lt_of_lt_of_le hlt (neg_squareRootMertensInt_le_depth K)⟩

/-- If the crossing occurs anywhere before the root, the interpolated residual
is strictly sub-root.  Thus the open quantitative burden is the existence and
location of a crossing, not control of the overshoot once a crossing exists. -/
theorem squareRootPacketCrossing_exists_partial_residual_lt_root
    {R K : ℕ} (hcross : SquareRootPacketCrossesAt R K) (hKR : K < R) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R K ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R K j ∧
          squareRootCrossingLayerPartialPacketInt R K j < (R : ℤ) := by
  rcases squareRootPacketCrossing_exists_partial_residual_lt_depth hcross with
    ⟨j, hj, hnonneg, hlt⟩
  have hKRz : (K : ℤ) < (R : ℤ) := by exact_mod_cast hKR
  exact ⟨j, hj, hnonneg, hlt.trans hKRz⟩

/-! ## Explicit open crossing statements -/

/-- Weak structural target: every sufficiently large square prefix has some
post-root sign crossing before the reciprocal coordinate reaches the root. -/
def SquareRootPacketSubrootCrossingStatement : Prop :=
  ∀ R : ℕ, 3 ≤ R → ∃ K : ℕ, K < R ∧ SquareRootPacketCrossesAt R K

/-- Stronger diagnostic target suggested by the finite gate: the crossing depth
is logarithmic in the square-root parameter.  This is only a proposition, not a
theorem asserted here. -/
def SquareRootPacketLogCrossingStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ∃ K : ℕ,
        K < R ∧ SquareRootPacketCrossesAt R K ∧
          (K : ℝ) ≤ C * Real.log (R : ℝ)

end RHLean.Proof
