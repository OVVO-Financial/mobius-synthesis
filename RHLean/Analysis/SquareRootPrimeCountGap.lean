import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTransfer
import RHLean.Analysis.SquareRootTransportTopFibreNoGo

/-!
# Square-root middle versus inert prime-count gap

At the square endpoint `X_R = R^2 - 1`, the prime-first transport splits into

* middle primes `R < q <= X_R / 2`, whose reciprocal quotients lie in `[2,R)`;
* inert top primes `X_R / 2 < q <= X_R`, whose reciprocal quotient is exactly `1`.

The previous transport theorem shows that the top block is a same-sign block of
one unit per prime.  This file records the exact cardinality obstruction to a
one-for-one cancellation of that top block against the middle prime fibres.

Writing `pi(N) = Nat.primeCounting N`, the two fibre populations satisfy

`middle + pi(R) = pi(X_R / 2)`

and

`top + pi(X_R / 2) = pi(X_R)`.

Hence their signed count gap is exactly

`middle - top = 2*pi(X_R / 2) - pi(X_R) - pi(R)`.

This identity is unconditional.  The sign of the right-hand side is genuinely a
second-order prime-counting question: the repository's qualitative PNT
`pi(N) log N / N -> 1` does not determine it because the leading `X/log X`
terms cancel.  We therefore isolate the exact stronger input needed to force
non-offset rather than deriving it incorrectly from first-order PNT.
-/

noncomputable section

open Filter
open scoped Topology ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- Prime fibres strictly between the square-root cutoff and the inert top half. -/
def squareRootMiddleFibrePrimes (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R / 2)).filter Nat.Prime

/-- Prime cardinality of `(0,N]` is the ordinary prime-counting function. -/
private theorem primeCard_Ioc_zero_eq_primeCounting (N : ℕ) :
    ((Finset.Ioc 0 N).filter Nat.Prime).card = Nat.primeCounting N := by
  have hset :
      (Finset.Ioc 0 N).filter Nat.Prime = nativePrimeSet N := by
    unfold nativePrimeSet
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp0, hpN⟩, hpPrime⟩
      exact ⟨⟨by omega, hpN⟩, hpPrime⟩
    · rintro ⟨⟨hp1, hpN⟩, hpPrime⟩
      exact ⟨⟨by omega, hpN⟩, hpPrime⟩
  rw [hset, nativePrimeSet_card_eq_primeCounting]

/-- Exact prime count in an interval `(a,b]`, written additively to avoid any
truncation issue from natural-number subtraction. -/
theorem primeCard_Ioc_add_primeCounting_eq
    {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card + Nat.primeCounting a =
      Nat.primeCounting b := by
  let lower : Finset ℕ := (Finset.Ioc 0 a).filter Nat.Prime
  let upper : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime
  have hsplit :
      (Finset.Ioc 0 b).filter Nat.Prime = lower ∪ upper := by
    ext p
    simp only [lower, upper, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp0, hpb⟩, hpPrime⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨⟨hp0, hpa⟩, hpPrime⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hpa, hpb⟩, hpPrime⟩
    · rintro (h | h)
      · exact ⟨⟨h.1.1, h.1.2.trans hab⟩, h.2⟩
      · exact ⟨⟨by omega, h.1.2⟩, h.2⟩
  have hdisj : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro p hpLower hpUpper
    rcases Finset.mem_filter.mp hpLower with ⟨hpLowerIoc, _⟩
    rcases Finset.mem_filter.mp hpUpper with ⟨hpUpperIoc, _⟩
    rcases Finset.mem_Ioc.mp hpLowerIoc with ⟨_, hpa⟩
    rcases Finset.mem_Ioc.mp hpUpperIoc with ⟨hap, _⟩
    omega
  have hcard := congrArg Finset.card hsplit
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hlower : lower.card = Nat.primeCounting a := by
    dsimp [lower]
    exact primeCard_Ioc_zero_eq_primeCounting a
  have htotal : ((Finset.Ioc 0 b).filter Nat.Prime).card = Nat.primeCounting b :=
    primeCard_Ioc_zero_eq_primeCounting b
  dsimp [upper] at hcard ⊢
  rw [htotal, hlower] at hcard
  omega

/-- For `R >= 3`, the middle prime population plus the primes through `R`
is exactly `pi(X_R/2)`. -/
theorem squareRootMiddleFibrePrimes_card_add_primeCounting_root
    (R : ℕ) (hR : 3 ≤ R) :
    (squareRootMiddleFibrePrimes R).card + Nat.primeCounting R =
      Nat.primeCounting (squareRootEndpoint R / 2) := by
  have hpow : R ^ 2 = R * R := by ring
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 hmul
  unfold squareRootMiddleFibrePrimes
  exact primeCard_Ioc_add_primeCounting_eq hhalf

/-- The inert top-prime population plus the primes through the half endpoint is
exactly `pi(X_R)`. -/
theorem squareRootTopFibrePrimes_card_add_primeCounting_half
    (R : ℕ) :
    (squareRootTopFibrePrimes R).card +
        Nat.primeCounting (squareRootEndpoint R / 2) =
      Nat.primeCounting (squareRootEndpoint R) := by
  have hhalfX : squareRootEndpoint R / 2 ≤ squareRootEndpoint R :=
    Nat.div_le_self _ _
  unfold squareRootTopFibrePrimes
  exact primeCard_Ioc_add_primeCounting_eq hhalfX

/-- Integer-valued middle-minus-top prime-count gap.  The integer presentation
keeps the signed difference exact. -/
def squareRootMiddleTopPrimeCountGap (R : ℕ) : ℤ :=
  2 * (Nat.primeCounting (squareRootEndpoint R / 2) : ℤ) -
    (Nat.primeCounting (squareRootEndpoint R) : ℤ) -
    (Nat.primeCounting R : ℤ)

/-- The PNT-coordinate expression is exactly the geometric fibre-cardinality
difference. -/
theorem squareRootMiddleTopPrimeCountGap_eq_card_sub
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleTopPrimeCountGap R =
      ((squareRootMiddleFibrePrimes R).card : ℤ) -
        ((squareRootTopFibrePrimes R).card : ℤ) := by
  have hmid := squareRootMiddleFibrePrimes_card_add_primeCounting_root R hR
  have htop := squareRootTopFibrePrimes_card_add_primeCounting_half R
  have hmidZ :
      ((squareRootMiddleFibrePrimes R).card : ℤ) +
          (Nat.primeCounting R : ℤ) =
        (Nat.primeCounting (squareRootEndpoint R / 2) : ℤ) := by
    exact_mod_cast hmid
  have htopZ :
      ((squareRootTopFibrePrimes R).card : ℤ) +
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℤ) =
        (Nat.primeCounting (squareRootEndpoint R) : ℤ) := by
    exact_mod_cast htop
  unfold squareRootMiddleTopPrimeCountGap
  omega

/-- The two geometric prime layers fail to offset one-for-one exactly when the
second-order prime-counting gap is positive. -/
theorem squareRoot_top_card_lt_middle_iff_secondOrder_primeCounting_gap
    (R : ℕ) (hR : 3 ≤ R) :
    (squareRootTopFibrePrimes R).card <
        (squareRootMiddleFibrePrimes R).card ↔
      Nat.primeCounting (squareRootEndpoint R) + Nat.primeCounting R <
        2 * Nat.primeCounting (squareRootEndpoint R / 2) := by
  have hmid := squareRootMiddleFibrePrimes_card_add_primeCounting_root R hR
  have htop := squareRootTopFibrePrimes_card_add_primeCounting_half R
  omega

/-- The quantitative prime-counting input needed after first-order PNT.  It is
kept as a named proposition because `pi(N) log N / N -> 1` alone cannot decide
this second-order sign after the leading terms cancel. -/
def SquareRootSecondOrderPrimeCountGapStatement : Prop :=
  ∀ᶠ R : ℕ in atTop,
    Nat.primeCounting (squareRootEndpoint R) + Nat.primeCounting R <
      2 * Nat.primeCounting (squareRootEndpoint R / 2)

/-- Any proof of the second-order prime-counting gap immediately yields the
structural non-offset theorem for the square-root transport populations. -/
theorem squareRoot_middle_prime_population_eventually_exceeds_top
    (hgap : SquareRootSecondOrderPrimeCountGapStatement) :
    ∀ᶠ R : ℕ in atTop,
      (squareRootTopFibrePrimes R).card <
        (squareRootMiddleFibrePrimes R).card := by
  filter_upwards [hgap, eventually_ge_atTop 3] with R hpi hR
  exact
    (squareRoot_top_card_lt_middle_iff_secondOrder_primeCounting_gap R hR).2 hpi

/-! ## Exact harmonic peeling inside the middle section -/

private theorem mertensSummatory_two : mertensSummatory 2 = 0 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  unfold cofactorMobiusPrefixMass
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
  simp [canonicalMoebiusWeight,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- The middle tail retained after peeling all quotient layers below `j`.
For `j = 2` this is definitionally the original middle Mertens tail. -/
def squareRootMiddleHarmonicTail (R j : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc R (squareRootEndpoint R / j),
    if q.Prime then mertensSummatory (squareRootEndpoint R / q) else 0

/-- The exact prime layer removed when the harmonic cutoff moves from `j` to
`j+1`.  Defining the layer as a set difference keeps the lower constraint
`R < q` even in the last short layer near `j = R-1`. -/
def squareRootMiddleHarmonicLayerPrimes (R j : ℕ) : Finset ℕ :=
  ((Finset.Ioc R (squareRootEndpoint R / j)) \
      Finset.Ioc R (squareRootEndpoint R / (j + 1))).filter Nat.Prime

/-- **Exact zero top band of the middle section.**  Every prime in
`(X_R/3, X_R/2]` has reciprocal quotient exactly `2`, and `M(2)=0`.  This is
cancellation inside the cofactor prefix `mu(1)+mu(2)=0`; it does not identify
this statement with the separate source pairing `q <-> 2q`. -/
theorem squareRootMiddleHarmonicBand_two_eq_zero (R : ℕ) :
    (∑ q ∈ Finset.Ioc (squareRootEndpoint R / 3) (squareRootEndpoint R / 2),
      if q.Prime then mertensSummatory (squareRootEndpoint R / q) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hqPrime : q.Prime
  · rcases Finset.mem_Ioc.mp hq with ⟨hlow, hhigh⟩
    have hqpos : 0 < q := hqPrime.pos
    have htwo : 2 ≤ squareRootEndpoint R / q := by
      apply (Nat.le_div_iff_mul_le hqpos).2
      have hmul : q * 2 ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hhigh
      simpa [Nat.mul_comm] using hmul
    have hthree : squareRootEndpoint R / q < 3 := by
      apply (Nat.div_lt_iff_lt_mul hqpos).2
      have hmul : squareRootEndpoint R < q * 3 :=
        (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).1 hlow
      simpa [Nat.mul_comm] using hmul
    have hdiv : squareRootEndpoint R / q = 2 := by omega
    rw [if_pos hqPrime, hdiv, mertensSummatory_two]
  · simp [hqPrime]

/-- **One-layer harmonic peel.**  For `2 <= j < R`, the difference between the
`j` and `j+1` middle tails is exactly the prime layer on which
`floor(X_R/q)=j`, multiplied by the constant value `M(j)`.

In particular the specialization `j=2` gives `T_2=T_3` because `M(2)=0`.
No interval estimate is used. -/
theorem squareRootMiddleHarmonicTail_peel
    (R j : ℕ) (hj : 2 ≤ j) (_hjR : j < R) :
    squareRootMiddleHarmonicTail R j =
      mertensSummatory j * ((squareRootMiddleHarmonicLayerPrimes R j).card : ℂ) +
        squareRootMiddleHarmonicTail R (j + 1) := by
  classical
  let X := squareRootEndpoint R
  let big : Finset ℕ := Finset.Ioc R (X / j)
  let small : Finset ℕ := Finset.Ioc R (X / (j + 1))
  let f : ℕ → ℂ := fun q => if q.Prime then mertensSummatory (X / q) else 0
  have hjpos : 0 < j := by omega
  have hj1pos : 0 < j + 1 := by omega
  have hsubset : small ⊆ big := by
    intro q hq
    rcases Finset.mem_Ioc.mp hq with ⟨hRq, hqsmall⟩
    apply Finset.mem_Ioc.mpr
    refine ⟨hRq, ?_⟩
    apply (Nat.le_div_iff_mul_le hjpos).2
    have hmulSmall : q * (j + 1) ≤ X :=
      (Nat.le_div_iff_mul_le hj1pos).1 hqsmall
    have hmulMono : q * j ≤ q * (j + 1) :=
      Nat.mul_le_mul_left q (by omega)
    exact hmulMono.trans hmulSmall
  have hquot : ∀ q ∈ big \ small, q.Prime → X / q = j := by
    intro q hqdiff hqPrime
    rcases Finset.mem_sdiff.mp hqdiff with ⟨hqbig, hqnotSmall⟩
    rcases Finset.mem_Ioc.mp hqbig with ⟨hRq, hqbigUpper⟩
    have hqpos : 0 < q := hqPrime.pos
    have hjle : j ≤ X / q := by
      apply (Nat.le_div_iff_mul_le hqpos).2
      have hmul : q * j ≤ X :=
        (Nat.le_div_iff_mul_le hjpos).1 hqbigUpper
      simpa [Nat.mul_comm] using hmul
    have hsmallLower : X / (j + 1) < q := by
      by_contra hnot
      apply hqnotSmall
      exact Finset.mem_Ioc.mpr ⟨hRq, Nat.le_of_not_gt hnot⟩
    have hlt : X / q < j + 1 := by
      apply (Nat.div_lt_iff_lt_mul hqpos).2
      have hmul : X < q * (j + 1) :=
        (Nat.div_lt_iff_lt_mul hj1pos).1 hsmallLower
      simpa [Nat.mul_comm] using hmul
    omega
  have hlayer :
      (∑ q ∈ big \ small, f q) =
        mertensSummatory j * (((big \ small).filter Nat.Prime).card : ℂ) := by
    calc
      (∑ q ∈ big \ small, f q) =
          ∑ q ∈ (big \ small).filter Nat.Prime, mertensSummatory j := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro q hqdiff
        by_cases hqPrime : q.Prime
        · simp [f, hqPrime, hquot q hqdiff hqPrime]
        · simp [f, hqPrime]
      _ = mertensSummatory j * (((big \ small).filter Nat.Prime).card : ℂ) := by
        simp [nsmul_eq_mul, mul_comm]
  have hpartition :
      (∑ q ∈ big \ small, f q) + ∑ q ∈ small, f q = ∑ q ∈ big, f q := by
    exact Finset.sum_sdiff hsubset
  change (∑ q ∈ big, f q) =
    mertensSummatory j * (((big \ small).filter Nat.Prime).card : ℂ) +
      ∑ q ∈ small, f q
  calc
    (∑ q ∈ big, f q) = (∑ q ∈ big \ small, f q) + ∑ q ∈ small, f q :=
      hpartition.symm
    _ = mertensSummatory j * (((big \ small).filter Nat.Prime).card : ℂ) +
        ∑ q ∈ small, f q := by rw [hlayer]

/-- **Swapped middle hyperbola.**  The whole middle tail is exactly the
cofactor-first sum

`sum_{3 <= c < R} mu(c) * (pi(floor(X_R/c)) - pi(R))`.

The `c=1,2` cancellation here is the internal cofactor-prefix identity
`mu(1)+mu(2)=0`, kept separate from the distinct source pairing `q <-> 2q`.
Distributing the constant `pi(R)` term gives the exact inert-style edge
`-pi(R) * M(R-1)` because `M(2)=0`.  No estimate is used. -/
theorem squareRootMiddleMertensTail_eq_swappedPrimeCounting
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      ∑ c ∈ Finset.Icc 3 (R - 1),
        canonicalMoebiusWeight c *
          ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
            (Nat.primeCounting R : ℂ)) := by
  classical
  let X := squareRootEndpoint R
  let fullQ : Finset ℕ := Finset.Ioc R X
  let middleQ : Finset ℕ := Finset.Ioc R (X / 2)
  let lowC : Finset ℕ := Finset.Icc 3 (R - 1)
  let inner : ℕ → ℂ := fun c =>
    ∑ q ∈ fullQ,
      if q.Prime ∧ c * q ≤ X then canonicalMoebiusWeight c else 0
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hRX : R ≤ X := by
    dsimp [X]
    unfold squareRootEndpoint
    rw [show R ^ 2 = R * R by ring]
    omega
  have hcset :
      Finset.Ico 1 R = ({1, 2} : Finset ℕ) ∪ lowC := by
    ext c
    simp only [lowC, Finset.mem_Ico, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hcdisj : Disjoint ({1, 2} : Finset ℕ) lowC := by
    rw [Finset.disjoint_left]
    intro c hc12 hclow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc12
    rcases Finset.mem_Icc.mp hclow with ⟨hc3, _⟩
    omega
  have hmu1 : canonicalMoebiusWeight 1 = 1 := by
    simp [canonicalMoebiusWeight]
  have hmu2 : canonicalMoebiusWeight 2 = -1 := by
    unfold canonicalMoebiusWeight
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  have hc1 : inner 1 = (((fullQ.filter Nat.Prime).card : ℕ) : ℂ) := by
    unfold inner
    calc
      (∑ q ∈ fullQ,
          if q.Prime ∧ 1 * q ≤ X then canonicalMoebiusWeight 1 else 0) =
        ∑ q ∈ fullQ, if q.Prime then (1 : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          change q ∈ Finset.Ioc R X at hq
          have hqX := (Finset.mem_Ioc.mp hq).2
          by_cases hqPrime : q.Prime
          · rw [if_pos ⟨hqPrime, by simpa using hqX⟩, if_pos hqPrime, hmu1]
          · rw [if_neg (by intro h; exact hqPrime h.1), if_neg hqPrime]
      _ = ∑ q ∈ fullQ.filter Nat.Prime, (1 : ℂ) := by
        rw [Finset.sum_filter]
      _ = (((fullQ.filter Nat.Prime).card : ℕ) : ℂ) := by simp
  have hset2 :
      fullQ.filter (fun q => q.Prime ∧ 2 * q ≤ X) =
        middleQ.filter Nat.Prime := by
    ext q
    simp only [Finset.mem_filter]
    change
      (q ∈ Finset.Ioc R X ∧ (q.Prime ∧ 2 * q ≤ X)) ↔
        (q ∈ Finset.Ioc R (X / 2) ∧ q.Prime)
    constructor
    · rintro ⟨hqfull, hqPrime, htwo⟩
      rcases Finset.mem_Ioc.mp hqfull with ⟨hRq, _hqX⟩
      have hqhalf : q ≤ X / 2 := by
        apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
        simpa [Nat.mul_comm] using htwo
      exact ⟨Finset.mem_Ioc.mpr ⟨hRq, hqhalf⟩, hqPrime⟩
    · rintro ⟨hqmid, hqPrime⟩
      rcases Finset.mem_Ioc.mp hqmid with ⟨hRq, hqhalf⟩
      have htwo : q * 2 ≤ X :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hqhalf
      have hqX : q ≤ X := hqhalf.trans (Nat.div_le_self X 2)
      exact ⟨Finset.mem_Ioc.mpr ⟨hRq, hqX⟩, hqPrime,
        by simpa [Nat.mul_comm] using htwo⟩
  have hc2 : inner 2 = -((squareRootMiddleFibrePrimes R).card : ℂ) := by
    unfold inner
    calc
      (∑ q ∈ fullQ,
          if q.Prime ∧ 2 * q ≤ X then canonicalMoebiusWeight 2 else 0) =
        ∑ q ∈ fullQ.filter (fun q => q.Prime ∧ 2 * q ≤ X),
          canonicalMoebiusWeight 2 := by
            rw [Finset.sum_filter]
      _ = ∑ q ∈ middleQ.filter Nat.Prime, canonicalMoebiusWeight 2 := by
        rw [hset2]
      _ = ∑ q ∈ middleQ.filter Nat.Prime, (-1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact hmu2
      _ = -((middleQ.filter Nat.Prime).card : ℂ) := by
        simp
      _ = -((squareRootMiddleFibrePrimes R).card : ℂ) := by
        simp [squareRootMiddleFibrePrimes, middleQ, X]
  have hallCount := primeCard_Ioc_add_primeCounting_eq hRX
  have hmidCount := squareRootMiddleFibrePrimes_card_add_primeCounting_root R hR
  have htopCount := squareRootTopFibrePrimes_card_add_primeCounting_half R
  have hallC :
      ((fullQ.filter Nat.Prime).card : ℂ) + (Nat.primeCounting R : ℂ) =
        (Nat.primeCounting X : ℂ) := by
    dsimp [fullQ]
    exact_mod_cast hallCount
  have hmidC :
      ((squareRootMiddleFibrePrimes R).card : ℂ) +
          (Nat.primeCounting R : ℂ) =
        (Nat.primeCounting (X / 2) : ℂ) := by
    dsimp [X]
    exact_mod_cast hmidCount
  have htopC :
      ((squareRootTopFibrePrimes R).card : ℂ) +
          (Nat.primeCounting (X / 2) : ℂ) =
        (Nat.primeCounting X : ℂ) := by
    dsimp [X]
    exact_mod_cast htopCount
  have hcardDiff :
      ((fullQ.filter Nat.Prime).card : ℂ) -
          ((squareRootMiddleFibrePrimes R).card : ℂ) =
        ((squareRootTopFibrePrimes R).card : ℂ) := by
    linear_combination hallC - hmidC - htopC
  have h12 :
      (∑ c ∈ ({1, 2} : Finset ℕ), inner c) =
        ((squareRootTopFibrePrimes R).card : ℂ) := by
    simp [hc1, hc2]
    exact hcardDiff
  have hrest :
      (∑ c ∈ lowC, inner c) =
        ∑ c ∈ lowC,
          canonicalMoebiusWeight c *
            ((Nat.primeCounting (X / c) : ℂ) -
              (Nat.primeCounting R : ℂ)) := by
    apply Finset.sum_congr rfl
    intro c hc
    rcases Finset.mem_Icc.mp hc with ⟨hc3, hcR1⟩
    have hcpos : 0 < c := by omega
    have hcR : c < R := by omega
    have hRcLt : R * c < R * R :=
      Nat.mul_lt_mul_of_pos_left hcR (by omega)
    have hRcX : R * c ≤ X := by
      dsimp [X]
      unfold squareRootEndpoint
      rw [show R ^ 2 = R * R by ring]
      omega
    have hRc : R ≤ X / c :=
      (Nat.le_div_iff_mul_le hcpos).2 hRcX
    have hfilter :
        fullQ.filter (fun q => q.Prime ∧ c * q ≤ X) =
          (Finset.Ioc R (X / c)).filter Nat.Prime := by
      ext q
      simp only [Finset.mem_filter]
      change
        (q ∈ Finset.Ioc R X ∧ (q.Prime ∧ c * q ≤ X)) ↔
          (q ∈ Finset.Ioc R (X / c) ∧ q.Prime)
      constructor
      · rintro ⟨hqfull, hqPrime, hmul⟩
        rcases Finset.mem_Ioc.mp hqfull with ⟨hRq, _hqX⟩
        have hqB : q ≤ X / c := by
          apply (Nat.le_div_iff_mul_le hcpos).2
          simpa [Nat.mul_comm] using hmul
        exact ⟨Finset.mem_Ioc.mpr ⟨hRq, hqB⟩, hqPrime⟩
      · rintro ⟨hqBmem, hqPrime⟩
        rcases Finset.mem_Ioc.mp hqBmem with ⟨hRq, hqB⟩
        have hmul : q * c ≤ X :=
          (Nat.le_div_iff_mul_le hcpos).1 hqB
        have hqX : q ≤ X := hqB.trans (Nat.div_le_self X c)
        exact ⟨Finset.mem_Ioc.mpr ⟨hRq, hqX⟩, hqPrime,
          by simpa [Nat.mul_comm] using hmul⟩
    have hcount := primeCard_Ioc_add_primeCounting_eq hRc
    have hcountC :
        (((Finset.Ioc R (X / c)).filter Nat.Prime).card : ℂ) +
            (Nat.primeCounting R : ℂ) =
          (Nat.primeCounting (X / c) : ℂ) := by
      exact_mod_cast hcount
    have hcardC :
        (((Finset.Ioc R (X / c)).filter Nat.Prime).card : ℂ) =
          (Nat.primeCounting (X / c) : ℂ) - (Nat.primeCounting R : ℂ) := by
      linear_combination hcountC
    unfold inner
    calc
      (∑ q ∈ fullQ,
          if q.Prime ∧ c * q ≤ X then canonicalMoebiusWeight c else 0) =
        ∑ q ∈ fullQ.filter (fun q => q.Prime ∧ c * q ≤ X),
          canonicalMoebiusWeight c := by
            rw [Finset.sum_filter]
      _ = ∑ q ∈ (Finset.Ioc R (X / c)).filter Nat.Prime,
          canonicalMoebiusWeight c := by rw [hfilter]
      _ = canonicalMoebiusWeight c *
          (((Finset.Ioc R (X / c)).filter Nat.Prime).card : ℂ) := by
            simp [nsmul_eq_mul, mul_comm]
      _ = canonicalMoebiusWeight c *
          ((Nat.primeCounting (X / c) : ℂ) -
            (Nat.primeCounting R : ℂ)) := by rw [hcardC]
  have hcofactor :
      squareRootTransportCofactorFirst R =
        ((squareRootTopFibrePrimes R).card : ℂ) +
          ∑ c ∈ lowC,
            canonicalMoebiusWeight c *
              ((Nat.primeCounting (X / c) : ℂ) -
                (Nat.primeCounting R : ℂ)) := by
    unfold squareRootTransportCofactorFirst
    change (∑ c ∈ Finset.Ico 1 R, inner c) = _
    rw [hcset, Finset.sum_union hcdisj, h12, hrest]
  have hfull :
      squareRootTransportCofactorFirst R =
        squareRootMiddleMertensTail R +
          ((squareRootTopFibrePrimes R).card : ℂ) := by
    calc
      squareRootTransportCofactorFirst R = squareRootTransportPrimeFirst R :=
        squareRootTransportCofactorFirst_eq_primeFirst R
      _ = squareRootMiddleMertensTail R +
          ((squareRootTopFibrePrimes R).card : ℂ) :=
        squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR
  dsimp [lowC, X] at hcofactor ⊢
  rw [hcofactor] at hfull
  calc
    squareRootMiddleMertensTail R =
        (((squareRootTopFibrePrimes R).card : ℂ) +
          ∑ c ∈ Finset.Icc 3 (R - 1),
            canonicalMoebiusWeight c *
              ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
                (Nat.primeCounting R : ℂ))) -
          ((squareRootTopFibrePrimes R).card : ℂ) := by
            rw [hfull]
            ring
    _ = ∑ c ∈ Finset.Icc 3 (R - 1),
          canonicalMoebiusWeight c *
            ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
              (Nat.primeCounting R : ℂ)) := by ring

/-! ## Weighted middle bias target -/

/-- The middle Mertens tail viewed in the sequential fresh-prime orientation.
Each fresh-prime extension reverses the parent sign, so the oriented throw mass
is the negative of the transport-convention middle tail. -/
def squareRootOrientedMiddleThrowMass (R : ℕ) : ℂ :=
  -squareRootMiddleMertensTail R

/-- The defect of the actual oriented middle throws from the unit model in
which every middle prime fibre contributes `+1`.

If `A_R` denotes the oriented throw mass and `N_mid` the number of middle prime
fibres, this is exactly `N_mid - A_R`. -/
def squareRootMiddleUnitModelDefect (R : ℕ) : ℂ :=
  ((squareRootMiddleFibrePrimes R).card : ℂ) -
    squareRootOrientedMiddleThrowMass R

/-- Complex-valued geometric presentation of the middle-minus-top population
gap.  This is the bias term that the weighted middle throws must absorb; it is
not itself a saving. -/
def squareRootMiddleTopPrimeCountGapMass (R : ℕ) : ℂ :=
  ((squareRootMiddleFibrePrimes R).card : ℂ) -
    ((squareRootTopFibrePrimes R).card : ℂ)

/-- The integer PNT-coordinate gap and the complex geometric gap are the same
quantity after casting. -/
theorem squareRootMiddleTopPrimeCountGap_cast_eq_mass
    (R : ℕ) (hR : 3 ≤ R) :
    ((squareRootMiddleTopPrimeCountGap R : ℤ) : ℂ) =
      squareRootMiddleTopPrimeCountGapMass R := by
  rw [squareRootMiddleTopPrimeCountGap_eq_card_sub R hR]
  unfold squareRootMiddleTopPrimeCountGapMass
  push_cast
  rfl

/-- **Exact weighted middle-bias identity.**  The deficit of the oriented
middle throws from the unit model is the population gap plus the smooth edge,
up to exactly the square-endpoint Mertens residual:

`N_mid - A_R = G_R + S_R - M(X_R)`.

Thus the positive prime-count gap is a deterministic bias that must be absorbed
by the lower-scale Mertens weights; it is not a contraction term. -/
theorem squareRootMiddleUnitModelDefect_eq_gap_add_smooth_sub_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleUnitModelDefect R =
      squareRootMiddleTopPrimeCountGapMass R +
        squareRootSmoothMass (R - 1) - squarePrefixMertens (R - 1) := by
  rw [squarePrefixMertens_eq_smooth_sub_middle_sub_topCard R hR]
  unfold squareRootMiddleUnitModelDefect squareRootOrientedMiddleThrowMass
    squareRootMiddleTopPrimeCountGapMass
  ring

/-- The same identity with the population bias written directly in the exact
integer PNT coordinate from the preceding section. -/
theorem squareRootMiddleUnitModelDefect_eq_primeCountGap_add_smooth_sub_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleUnitModelDefect R =
      ((squareRootMiddleTopPrimeCountGap R : ℤ) : ℂ) +
        squareRootSmoothMass (R - 1) - squarePrefixMertens (R - 1) := by
  rw [squareRootMiddleTopPrimeCountGap_cast_eq_mass R hR]
  exact squareRootMiddleUnitModelDefect_eq_gap_add_smooth_sub_mertens R hR

/-- After removing the deterministic prime-population gap and smooth-edge
correction from the unit-model defect, the remaining weighted-middle bias is
the exact Mertens target.  No division by the middle population is needed. -/
def squareRootMiddleBiasResidual (R : ℕ) : ℂ :=
  squareRootMiddleUnitModelDefect R -
    (squareRootMiddleTopPrimeCountGapMass R + squareRootSmoothMass (R - 1))

/-- **Cross-multiplied average target.**  The centered weighted-middle bias is
exactly the negative square-prefix Mertens value. -/
theorem squareRootMiddleBiasResidual_eq_neg_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleBiasResidual R = -squarePrefixMertens (R - 1) := by
  unfold squareRootMiddleBiasResidual
  rw [squareRootMiddleUnitModelDefect_eq_gap_add_smooth_sub_mertens R hR]
  ring

/-- Norm form: controlling the weighted-middle bias after subtracting the PNT
population tilt and smooth correction is exactly equivalent, with no loss, to
controlling Mertens at the square endpoint. -/
theorem norm_squareRootMiddleBiasResidual_eq_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    ‖squareRootMiddleBiasResidual R‖ = ‖squarePrefixMertens (R - 1)‖ := by
  rw [squareRootMiddleBiasResidual_eq_neg_mertens R hR]
  simp

end RHLean.Proof