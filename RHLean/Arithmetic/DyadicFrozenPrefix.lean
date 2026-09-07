import Mathlib

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Arithmetic

/-- The finite dyadic block `(N,2N]`. -/
def dyadicBlock (N : ℕ) : Finset ℕ := Finset.Icc (N + 1) (2 * N)

/-- The number of multiples of `d` in `(N,2N]`. -/
def dyadicDivisorWeight (N d : ℕ) : ℕ :=
  ((dyadicBlock N).filter fun n => d ∣ n).card

/-- Every proper divisor of an integer in `(N,2N]` lies in the frozen prefix. -/
theorem properDivisor_le_base {N n d : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) (hd : d ∣ n) (hdn : d < n) : d ≤ N := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp_all
  nlinarith

/-- The proper divisors of `n` that lie in the frozen prefix. -/
def frozenProperDivisors (N n : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun d => d ∣ n ∧ d < n

/-- Möbius is reconstructed from its proper-divisor values. -/
theorem moebius_eq_neg_sum_properDivisors {n : ℕ} (hn : 1 < n) :
    μ n = -∑ d ∈ n.divisors.erase n, μ d := by
  have hconv :
      ((ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n) =
        (1 : ArithmeticFunction ℤ) n :=
    congrArg (fun f : ArithmeticFunction ℤ => f n)
      ArithmeticFunction.moebius_mul_coe_zeta
  have hsum : ∑ d ∈ n.divisors, μ d = 0 := by
    rw [ArithmeticFunction.coe_mul_zeta_apply] at hconv
    rw [ArithmeticFunction.one_apply, if_neg hn.ne'] at hconv
    exact hconv
  have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have hsplit : (∑ d ∈ n.divisors.erase n, μ d) + μ n = 0 := by
    rw [Finset.sum_erase_add (s := n.divisors) (f := fun d => μ d) hnmem]
    exact hsum
  linarith

/-- On `(N,2N]`, the frozen proper-divisor set is the full proper-divisor set. -/
theorem frozenProperDivisors_eq {N n : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) :
    frozenProperDivisors N n = n.divisors.erase n := by
  have hn : 1 < n := by omega
  ext d
  simp only [frozenProperDivisors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_erase, Nat.mem_divisors]
  constructor
  · rintro ⟨hdN, hdvd, hdn⟩
    exact ⟨Nat.ne_of_lt hdn, hdvd, by omega⟩
  · rintro ⟨hdn, hdvd, _⟩
    have hle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hlt : d < n := lt_of_le_of_ne hle hdn
    exact ⟨Nat.lt_succ_iff.mpr (properDivisor_le_base hnN hn2 hdvd hlt), hdvd, hlt⟩

/-- Pointwise frozen-prefix reconstruction on the next dyadic block. -/
theorem moebius_eq_neg_frozenPrefixSum {N n : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) :
    μ n = -∑ d ∈ frozenProperDivisors N n, μ d := by
  have hn : 1 < n := by omega
  rw [frozenProperDivisors_eq hnN hn2]
  exact moebius_eq_neg_sum_properDivisors hn

/-- Exact finite divisor-incidence form of the dyadic increment. -/
theorem dyadic_moebius_increment_eq_frozen_weighted_sum (N : ℕ) :
    (∑ n ∈ dyadicBlock N, μ n) =
      -∑ d ∈ Finset.range (N + 1), (dyadicDivisorWeight N d : ℤ) * μ d := by
  classical
  calc
    (∑ n ∈ dyadicBlock N, μ n) =
        ∑ n ∈ dyadicBlock N, -∑ d ∈ frozenProperDivisors N n, μ d := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [dyadicBlock, Finset.mem_Icc] at hn
          exact moebius_eq_neg_frozenPrefixSum hn.1 hn.2
    _ = -∑ d ∈ Finset.range (N + 1),
          ∑ n ∈ dyadicBlock N, if d ∣ n then μ d else 0 := by
          simp only [frozenProperDivisors, Finset.sum_neg_distrib, Finset.sum_filter]
          rw [Finset.sum_comm]
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro n hn
          have hdN : d ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
          have hNn : N < n := by
            exact (Finset.mem_Icc.mp hn).1
          have hdn : d < n := lt_of_le_of_lt hdN hNn
          simp [hdn]
    _ = -∑ d ∈ Finset.range (N + 1), (dyadicDivisorWeight N d : ℤ) * μ d := by
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro d hd
          change (∑ n ∈ dyadicBlock N, if d ∣ n then μ d else 0) =
            (((dyadicBlock N).filter fun n => d ∣ n).card : ℤ) * μ d
          rw [← Finset.sum_filter]
          simp

/-- The finite prime contribution in the new dyadic block. -/
def dyadicPrimeBirths (N : ℕ) : ℕ :=
  ((dyadicBlock N).filter Nat.Prime).card

/-- The inherited composite Möbius mass in the new dyadic block. -/
def dyadicInheritedCompositeMass (N : ℕ) : ℤ :=
  ∑ n ∈ (dyadicBlock N).filter (fun n => ¬ Nat.Prime n), μ n

/-- Exact prime-birth versus inherited-composite decomposition. -/
theorem dyadic_increment_eq_inherited_sub_primeBirths (N : ℕ) :
    (∑ n ∈ dyadicBlock N, μ n) =
      dyadicInheritedCompositeMass N - dyadicPrimeBirths N := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (s := dyadicBlock N) (p := Nat.Prime)]
  have hprime :
      (∑ n ∈ (dyadicBlock N).filter Nat.Prime, μ n) =
        -(dyadicPrimeBirths N : ℤ) := by
    calc
      (∑ n ∈ (dyadicBlock N).filter Nat.Prime, μ n) =
          ∑ _n ∈ (dyadicBlock N).filter Nat.Prime, (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact ArithmeticFunction.moebius_apply_prime (Finset.mem_filter.mp hn).2
      _ = -(dyadicPrimeBirths N : ℤ) := by
            simp [dyadicPrimeBirths]
  rw [hprime]
  change -(dyadicPrimeBirths N : ℤ) + dyadicInheritedCompositeMass N =
    dyadicInheritedCompositeMass N - dyadicPrimeBirths N
  abel

/-- The increment of an integer-valued prefix function across one doubling. -/
def dyadicIncrement (F : ℕ → ℤ) (N : ℕ) : ℤ := F (2 * N) - F N

/-- Exact finite partial-sum identity underlying the infinite dyadic series. -/
theorem dyadic_telescoping_series (F : ℕ → ℤ) (N K : ℕ) :
    F (2 ^ K * N) =
      F N + ∑ j ∈ Finset.range K, dyadicIncrement F (2 ^ j * N) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      calc
        F (2 ^ (K + 1) * N) = F (2 * (2 ^ K * N)) := by
          congr 1
          simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]
        _ = F (2 ^ K * N) + dyadicIncrement F (2 ^ K * N) := by
          simp [dyadicIncrement]
        _ = (F N + ∑ j ∈ Finset.range K, dyadicIncrement F (2 ^ j * N)) +
              dyadicIncrement F (2 ^ K * N) := by rw [ih]
        _ = F N +
              (∑ j ∈ Finset.range K, dyadicIncrement F (2 ^ j * N) +
                dyadicIncrement F (2 ^ K * N)) := by
          exact add_assoc _ _ _

/-- The Möbius prefix, including `0`; the zero term contributes nothing. -/
def moebiusPrefix (N : ℕ) : ℤ := ∑ n ∈ Finset.range (N + 1), μ n

/-- Möbius prefixes are exact partial sums of their permanent dyadic increments. -/
theorem moebiusPrefix_dyadic_series (N K : ℕ) :
    moebiusPrefix (2 ^ K * N) =
      moebiusPrefix N +
        ∑ j ∈ Finset.range K, dyadicIncrement moebiusPrefix (2 ^ j * N) :=
  dyadic_telescoping_series moebiusPrefix N K

/-- A typed finite cancellation premise for the dyadic frozen-prefix operator. -/
def DyadicFrozenPrefixCancellation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |((∑ n ∈ dyadicBlock N, μ n : ℤ) : ℝ)| ≤ ε * N

/-! ## Arbitrary frozen subdoubling runs -/

/-- A half-open physical run `[N,L)`.  When `L ≤ 2N`, every proper divisor of
every site in this run lies strictly below the initial cutoff `N`. -/
def frozenRunBlock (N L : ℕ) : Finset ℕ := Finset.Ico N L

/-- Number of sites in `[N,L)` hit by the old divisor coordinate `d`. -/
def frozenRunDivisorWeight (N L d : ℕ) : ℕ :=
  ((frozenRunBlock N L).filter fun n => d ∣ n).card

/-- Proper divisors of one site read only from the prefix strictly below `N`. -/
def frozenRunProperDivisors (N n : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun d => d ∣ n

/-- In a subdoubling run, every proper divisor lies strictly below the run's
left endpoint.  This is the strict version needed for a genuinely frozen
prefix: no divisor coordinate created during the run can be consulted later in
the same run.  No lower bound on `N` is needed: properness of the divisor
already forces its cofactor to be at least `2`, and the subdoubling ceiling
then halves the site. -/
theorem properDivisor_lt_frozenRunBase {N L n d : ℕ}
    (hL : L ≤ 2 * N)
    (hn : n ∈ frozenRunBlock N L)
    (hd : d ∣ n) (hdn : d < n) : d < N := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 2 ≤ k := by
    by_contra h
    interval_cases k <;> omega
  have hnlt : d * k < 2 * N := by
    exact lt_of_lt_of_le (Finset.mem_Ico.mp hn).2 hL
  nlinarith

/-- On a subdoubling run the strict frozen prefix is exactly the complete set of
proper divisors of every visited site. -/
theorem frozenRunProperDivisors_eq {N L n : ℕ}
    (hN : 2 ≤ N) (hL : L ≤ 2 * N)
    (hn : n ∈ frozenRunBlock N L) :
    frozenRunProperDivisors N n = n.divisors.erase n := by
  have hnLower : N ≤ n := (Finset.mem_Ico.mp hn).1
  have hnpos : 0 < n := by omega
  ext d
  simp only [frozenRunProperDivisors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_erase, Nat.mem_divisors]
  constructor
  · rintro ⟨hdN, hdvd⟩
    have hdn : d < n := lt_of_lt_of_le hdN hnLower
    exact ⟨Nat.ne_of_lt hdn, hdvd, hnpos.ne'⟩
  · rintro ⟨hdne, hdvd, _⟩
    have hle : d ≤ n := Nat.le_of_dvd hnpos hdvd
    have hlt : d < n := lt_of_le_of_ne hle hdne
    exact ⟨properDivisor_lt_frozenRunBase hL hn hdvd hlt, hdvd⟩

/-- Pointwise frozen-prefix reconstruction on an arbitrary subdoubling run. -/
theorem moebius_eq_neg_frozenRunPrefixSum {N L n : ℕ}
    (hN : 2 ≤ N) (hL : L ≤ 2 * N)
    (hn : n ∈ frozenRunBlock N L) :
    μ n = -∑ d ∈ frozenRunProperDivisors N n, μ d := by
  have hnLower : N ≤ n := (Finset.mem_Ico.mp hn).1
  have hn1 : 1 < n := by omega
  rw [frozenRunProperDivisors_eq hN hL hn]
  exact moebius_eq_neg_sum_properDivisors hn1

/-- **Frozen-run identity.**  On every half-open run `[N,L)` with `L ≤ 2N`, the
entire new Möbius mass is one static linear functional of the prefix strictly
below `N`.  No Möbius value created inside the run appears on the right-hand
side. -/
theorem frozenRun_moebius_increment_eq_frozen_weighted_sum
    (N L : ℕ) (hN : 2 ≤ N) (hL : L ≤ 2 * N) :
    (∑ n ∈ frozenRunBlock N L, μ n) =
      -∑ d ∈ Finset.range N, (frozenRunDivisorWeight N L d : ℤ) * μ d := by
  classical
  calc
    (∑ n ∈ frozenRunBlock N L, μ n) =
        ∑ n ∈ frozenRunBlock N L,
          -∑ d ∈ frozenRunProperDivisors N n, μ d := by
            apply Finset.sum_congr rfl
            intro n hn
            exact moebius_eq_neg_frozenRunPrefixSum hN hL hn
    _ = -∑ d ∈ Finset.range N,
          ∑ n ∈ frozenRunBlock N L, if d ∣ n then μ d else 0 := by
            simp only [frozenRunProperDivisors, Finset.sum_neg_distrib,
              Finset.sum_filter]
            rw [Finset.sum_comm]
    _ = -∑ d ∈ Finset.range N,
          (frozenRunDivisorWeight N L d : ℤ) * μ d := by
            apply congrArg Neg.neg
            apply Finset.sum_congr rfl
            intro d _hd
            change (∑ n ∈ frozenRunBlock N L, if d ∣ n then μ d else 0) =
              (((frozenRunBlock N L).filter fun n => d ∣ n).card : ℤ) * μ d
            rw [← Finset.sum_filter]
            simp

/-! ## Static square-run correlation -/

/-- Integer Möbius mass of the repository's half-open complete-square run
`[a^2,(b+1)^2)`. -/
def squareFrozenRunMass (a b : ℕ) : ℤ :=
  ∑ n ∈ frozenRunBlock (a ^ 2) ((b + 1) ^ 2), μ n

/-- Static divisor-incidence correlation of the prefix below `a^2` against the
whole square-run kernel.  This is the exact finite object that the frozen-run
identity exposes. -/
def squareFrozenRunCorrelation (a b : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (a ^ 2),
    (frozenRunDivisorWeight (a ^ 2) ((b + 1) ^ 2) d : ℤ) * μ d

/-- **Square frozen-run identity.**  As long as the entire square run remains
inside the first doubling of its left endpoint, its complete signed mass is the
negative of one static correlation against the Möbius prefix that existed
before the run began. -/
theorem squareFrozenRunMass_eq_neg_staticCorrelation
    (a b : ℕ) (ha : 2 ≤ a)
    (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    squareFrozenRunMass a b = -squareFrozenRunCorrelation a b := by
  unfold squareFrozenRunMass squareFrozenRunCorrelation
  have hbase : 2 ≤ a ^ 2 := by nlinarith
  exact frozenRun_moebius_increment_eq_frozen_weighted_sum
    (a ^ 2) ((b + 1) ^ 2) hbase hsub

/-- Absolute-value form: on a frozen square run, bounding the static correlation
is literally the same as bounding the run mass; no triangle inequality or
covariance relaxation is used. -/
theorem abs_squareFrozenRunMass_eq_abs_staticCorrelation
    (a b : ℕ) (ha : 2 ≤ a)
    (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    |((squareFrozenRunMass a b : ℤ) : ℝ)| =
      |((squareFrozenRunCorrelation a b : ℤ) : ℝ)| := by
  rw [squareFrozenRunMass_eq_neg_staticCorrelation a b ha hsub]
  simp

/-- **Static correlation bound.**  This is the cancellation statement suggested
by the frozen-run geometry.  Uniformly over every nonempty complete-square run
whose physical window stays below the first doubling of its left endpoint, the
single frozen-prefix divisor-incidence correlation has RH-scale size
`O_epsilon(a^(1+epsilon))`.

This is a named open analytic premise only.  The exact identities above show
that it is neither an independence assumption nor a new random-sign model: the
right-hand side uses the actual completed Möbius prefix below `a^2` and a fully
deterministic incidence kernel. -/
def SquareFrozenRunStaticCorrelationBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ,
        2 ≤ a →
        a ≤ b →
        (b + 1) ^ 2 ≤ 2 * (a ^ 2) →
        |((squareFrozenRunCorrelation a b : ℤ) : ℝ)| ≤
          C * Real.rpow (a : ℝ) (1 + ε)


/-! ## The static correlation in closed form

The frozen-run identity turns the new mass of a subdoubling run into a single
pairing of the *already completed* prefix against a deterministic kernel.  This
section makes both halves of that pairing explicit and then says exactly what
the resulting bound is worth.

Three things are proved.

* `frozenRunDivisorWeight_eq_div_sub_div` puts the kernel in closed floor form,
  `w(N,L,d) = ⌊(L-1)/d⌋ - ⌊(N-1)/d⌋`, so the correlation is a literal finite
  floor sum against `μ` and nothing about it is implicit.
* `frozenRunCorrelation_eq_length_add_deep` splits off the `d = 1` atom.  Its
  weight is the full run length, so the correlation always carries one rigid
  deterministic mode of size `L - N`; every cancellation has to come from the
  `d ≥ 2` coordinates.  This is why a random-sign surrogate on the same support
  does not model the object: it leaves the `d = 1` mode uncancelled.
* `frozenRunCorrelation_eq_prefix_sub` identifies the correlation exactly with
  the Möbius prefix increment across the run.

That last identity is the one that fixes the status of the seam.  Together with
`squareFrozenRunMass_eq_neg_staticCorrelation` it gives, with no inequality
anywhere,

```text
|squareFrozenRunCorrelation a b| = |M((b+1)^2) - M(a^2)|.
```

So `SquareFrozenRunStaticCorrelationBoundedStatement` is neither more nor less
than an RH-scale bound on Möbius prefix increments across subdoubling square
windows.  The frozen-prefix geometry has bought a genuine structural
reformulation -- the whole run is one linear functional of a prefix that is
complete before the run starts, with an explicit kernel, so no Möbius value
created during the run is consulted -- but it has not made the analytic content
smaller, and it should not be presented as though it had.
`squareFrozenRunStaticCorrelationBounded_of_moebiusPrefixRHScale` records the
easy half of that equivalence: the premise is implied by the RH-scale Mertens
bound, hence is not stronger than RH.  The converse needs the increments summed
along a subdoubling chain, for which `dyadic_telescoping_series` above is the
exact arithmetic half; it is not attempted here. -/

/-- The Möbius prefix on the half-open window `[0,x)`, matching the half-open
run convention used throughout this section. -/
def moebiusRangePrefix (x : ℕ) : ℤ := ∑ n ∈ Finset.range x, μ n

/-- The half-open prefix agrees with the closed prefix used earlier. -/
theorem moebiusRangePrefix_succ (N : ℕ) :
    moebiusRangePrefix (N + 1) = moebiusPrefix N := rfl

/-- Counting multiples in a half-open window, as a floor difference. -/
private theorem card_filter_dvd_Ioc {x y d : ℕ} (hxy : x ≤ y) :
    ((Finset.Ioc x y).filter fun n => d ∣ n).card = y / d - x / d := by
  classical
  have hdisj : Disjoint ((Finset.Ioc 0 x).filter fun n => d ∣ n)
      ((Finset.Ioc x y).filter fun n => d ∣ n) := by
    refine Finset.disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Ioc] at ha hb
    omega
  have hsplit : ((Finset.Ioc 0 y).filter fun n => d ∣ n).card
      = ((Finset.Ioc 0 x).filter fun n => d ∣ n).card
        + ((Finset.Ioc x y).filter fun n => d ∣ n).card := by
    rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) hxy,
      Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  have h1 := Nat.Ioc_filter_dvd_card_eq_div y d
  have h2 := Nat.Ioc_filter_dvd_card_eq_div x d
  rw [h1, h2] at hsplit
  omega

/-- The half-open run rewritten with a closed right endpoint. -/
theorem frozenRunBlock_eq_Ioc {N L : ℕ} (hN : 1 ≤ N) :
    frozenRunBlock N L = Finset.Ioc (N - 1) (L - 1) := by
  unfold frozenRunBlock
  ext n
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  omega

/-- **Closed form of the frozen-run kernel.**  The divisor coordinate `d` sees
the run exactly `⌊(L-1)/d⌋ - ⌊(N-1)/d⌋` times, so the static correlation is a
literal finite floor sum against the frozen prefix. -/
theorem frozenRunDivisorWeight_eq_div_sub_div {N L d : ℕ}
    (hN : 1 ≤ N) (hNL : N ≤ L) :
    frozenRunDivisorWeight N L d = (L - 1) / d - (N - 1) / d := by
  classical
  unfold frozenRunDivisorWeight
  rw [frozenRunBlock_eq_Ioc hN]
  exact card_filter_dvd_Ioc (by omega)

/-- The `d = 1` coordinate meets every site of the run, so its weight is the
full run length. -/
theorem frozenRunDivisorWeight_one (N L : ℕ) :
    frozenRunDivisorWeight N L 1 = L - N := by
  classical
  have hfilter :
      (frozenRunBlock N L).filter (fun n => (1 : ℕ) ∣ n) = frozenRunBlock N L := by
    ext n
    simp
  unfold frozenRunDivisorWeight
  rw [hfilter]
  unfold frozenRunBlock
  exact Nat.card_Ico N L

/-- The static frozen-prefix correlation at general endpoints. -/
def frozenRunCorrelation (N L : ℕ) : ℤ :=
  ∑ d ∈ Finset.range N, (frozenRunDivisorWeight N L d : ℤ) * μ d

/-- The square correlation is the general one at square endpoints. -/
theorem squareFrozenRunCorrelation_eq_frozenRunCorrelation (a b : ℕ) :
    squareFrozenRunCorrelation a b = frozenRunCorrelation (a ^ 2) ((b + 1) ^ 2) := rfl

/-- **The rigid deterministic mode.**  The correlation always contains the full
run length from the single coordinate `d = 1`; all cancellation must come from
the `d ≥ 2` coordinates.  A random-sign surrogate on the same squarefree support
leaves this mode standing, which is why it does not model the true object. -/
theorem frozenRunCorrelation_eq_length_add_deep (N L : ℕ) (hN : 2 ≤ N) :
    frozenRunCorrelation N L =
      ((L - N : ℕ) : ℤ) +
        ∑ d ∈ Finset.Ico 2 N, (frozenRunDivisorWeight N L d : ℤ) * μ d := by
  classical
  have hsplit :
      ((∑ d ∈ Finset.range 2, (frozenRunDivisorWeight N L d : ℤ) * μ d) +
        ∑ d ∈ Finset.Ico 2 N, (frozenRunDivisorWeight N L d : ℤ) * μ d) =
      ∑ d ∈ Finset.range N, (frozenRunDivisorWeight N L d : ℤ) * μ d :=
    Finset.sum_range_add_sum_Ico _ hN
  have hlow :
      (∑ d ∈ Finset.range 2, (frozenRunDivisorWeight N L d : ℤ) * μ d) =
        ((L - N : ℕ) : ℤ) := by
    simp [Finset.sum_range_succ, frozenRunDivisorWeight_one]
  unfold frozenRunCorrelation
  rw [← hsplit, hlow]

/-- The run mass is the Möbius prefix increment across the run. -/
theorem frozenRunMass_eq_prefix_sub {N L : ℕ} (h : N ≤ L) :
    (∑ n ∈ frozenRunBlock N L, μ n) =
      moebiusRangePrefix L - moebiusRangePrefix N := by
  unfold frozenRunBlock moebiusRangePrefix
  exact Finset.sum_Ico_eq_sub _ h

/-- **The static correlation is the Möbius prefix increment.**  On a subdoubling
run the frozen-prefix correlation is not merely comparable to the prefix
increment across the run; it is that increment, with a sign. -/
theorem frozenRunCorrelation_eq_prefix_sub {N L : ℕ}
    (hN : 2 ≤ N) (hL : L ≤ 2 * N) (hNL : N ≤ L) :
    frozenRunCorrelation N L = moebiusRangePrefix N - moebiusRangePrefix L := by
  have hid := frozenRun_moebius_increment_eq_frozen_weighted_sum N L hN hL
  rw [frozenRunMass_eq_prefix_sub hNL] at hid
  unfold frozenRunCorrelation
  linarith

/-- The square specialization of the prefix identification. -/
theorem squareFrozenRunCorrelation_eq_prefix_sub {a b : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    squareFrozenRunCorrelation a b =
      moebiusRangePrefix (a ^ 2) - moebiusRangePrefix ((b + 1) ^ 2) := by
  have hbase : 2 ≤ a ^ 2 := by nlinarith
  have hNL : a ^ 2 ≤ (b + 1) ^ 2 := by nlinarith
  rw [squareFrozenRunCorrelation_eq_frozenRunCorrelation]
  exact frozenRunCorrelation_eq_prefix_sub hbase hsub hNL

/-- **What the static correlation bound actually asks for.**  In absolute value
the frozen-prefix correlation of a subdoubling square run equals the Möbius
prefix increment across that run, exactly.  Bounding one is bounding the other;
no inequality is spent in passing between them. -/
theorem abs_squareFrozenRunCorrelation_eq_abs_prefix_increment {a b : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    |((squareFrozenRunCorrelation a b : ℤ) : ℝ)| =
      |((moebiusRangePrefix ((b + 1) ^ 2) : ℤ) : ℝ) -
        ((moebiusRangePrefix (a ^ 2) : ℤ) : ℝ)| := by
  rw [squareFrozenRunCorrelation_eq_prefix_sub ha hab hsub]
  push_cast
  rw [abs_sub_comm]

/-- The RH-scale bound on the Möbius prefix, in this module's presentation. -/
def MoebiusPrefixRHScaleBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℕ, 1 ≤ x →
        |((moebiusRangePrefix x : ℤ) : ℝ)| ≤ C * Real.rpow (x : ℝ) ((1 : ℝ) / 2 + ε)

/-- Half the exponent at a square endpoint is the full exponent at its root.

The rewrites run in `^` notation rather than on `Real.rpow` applications:
`Real.rpow_natCast` and `Real.rpow_mul` are stated with `^`, and `rw` matches
syntactically, so the two forms have to be lined up before rewriting even
though they are definitionally equal. -/
private theorem rpow_square_half (a : ℕ) (ε : ℝ) :
    Real.rpow ((a ^ 2 : ℕ) : ℝ) ((1 : ℝ) / 2 + ε / 2) = Real.rpow (a : ℝ) (1 + ε) := by
  have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hcast : ((a ^ 2 : ℕ) : ℝ) = (a : ℝ) ^ (2 : ℕ) := by
    push_cast
    ring
  have hexp : ((2 : ℕ) : ℝ) * ((1 : ℝ) / 2 + ε / 2) = 1 + ε := by
    push_cast
    ring
  have key :
      ((a ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + ε / 2) = (a : ℝ) ^ (1 + ε) := by
    rw [hcast, ← Real.rpow_natCast (a : ℝ) 2, ← Real.rpow_mul ha, hexp]
  exact key

/-- A subdoubling right endpoint costs only the fixed factor `2 ^ (1/2 + eps/2)`. -/
private theorem rpow_run_ceiling (a L : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hL : L ≤ 2 * a ^ 2) :
    Real.rpow (L : ℝ) ((1 : ℝ) / 2 + ε / 2)
      ≤ Real.rpow 2 ((1 : ℝ) / 2 + ε / 2) * Real.rpow (a : ℝ) (1 + ε) := by
  have hs : (0 : ℝ) ≤ (1 : ℝ) / 2 + ε / 2 := by linarith
  have hLle : (L : ℝ) ≤ 2 * ((a ^ 2 : ℕ) : ℝ) := by exact_mod_cast hL
  calc Real.rpow (L : ℝ) ((1 : ℝ) / 2 + ε / 2)
      ≤ Real.rpow (2 * ((a ^ 2 : ℕ) : ℝ)) ((1 : ℝ) / 2 + ε / 2) :=
        Real.rpow_le_rpow (Nat.cast_nonneg L) hLle hs
    _ = Real.rpow 2 ((1 : ℝ) / 2 + ε / 2) *
          Real.rpow ((a ^ 2 : ℕ) : ℝ) ((1 : ℝ) / 2 + ε / 2) :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ = Real.rpow 2 ((1 : ℝ) / 2 + ε / 2) * Real.rpow (a : ℝ) (1 + ε) := by
        rw [rpow_square_half]

/-- **The static correlation bound is not stronger than RH.**  The RH-scale
Möbius prefix bound implies it, with the exponent matching because the window
endpoints are squares: `(a^2)^(1/2 + eps/2) = a^(1 + eps)`.  Together with
`abs_squareFrozenRunCorrelation_eq_abs_prefix_increment`, which is an equality,
this places the named premise exactly at RH scale rather than beyond it. -/
theorem squareFrozenRunStaticCorrelationBounded_of_moebiusPrefixRHScale
    (h : MoebiusPrefixRHScaleBoundedStatement) :
    SquareFrozenRunStaticCorrelationBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := h (ε / 2) (by linarith)
  have hK0 : (0 : ℝ) ≤ Real.rpow 2 ((1 : ℝ) / 2 + ε / 2) :=
    Real.rpow_nonneg (by norm_num) _
  refine ⟨C * (1 + Real.rpow 2 ((1 : ℝ) / 2 + ε / 2)),
    mul_nonneg hC0 (by linarith), ?_⟩
  intro a b ha hab hsub
  have hA : (1 : ℕ) ≤ a ^ 2 := by nlinarith
  have hB : (1 : ℕ) ≤ (b + 1) ^ 2 := by nlinarith
  have hleft := hC (a ^ 2) hA
  have hright := hC ((b + 1) ^ 2) hB
  rw [rpow_square_half] at hleft
  have hright' :
      |((moebiusRangePrefix ((b + 1) ^ 2) : ℤ) : ℝ)|
        ≤ C * (Real.rpow 2 ((1 : ℝ) / 2 + ε / 2) * Real.rpow (a : ℝ) (1 + ε)) :=
    hright.trans
      (mul_le_mul_of_nonneg_left (rpow_run_ceiling a ((b + 1) ^ 2) ε hε.le hsub) hC0)
  calc |((squareFrozenRunCorrelation a b : ℤ) : ℝ)|
      = |((moebiusRangePrefix ((b + 1) ^ 2) : ℤ) : ℝ) -
          ((moebiusRangePrefix (a ^ 2) : ℤ) : ℝ)| :=
        abs_squareFrozenRunCorrelation_eq_abs_prefix_increment ha hab hsub
    _ ≤ |((moebiusRangePrefix ((b + 1) ^ 2) : ℤ) : ℝ)| +
          |((moebiusRangePrefix (a ^ 2) : ℤ) : ℝ)| := abs_sub _ _
    _ ≤ C * (Real.rpow 2 ((1 : ℝ) / 2 + ε / 2) * Real.rpow (a : ℝ) (1 + ε)) +
          C * Real.rpow (a : ℝ) (1 + ε) := by linarith
    _ = (C * (1 + Real.rpow 2 ((1 : ℝ) / 2 + ε / 2))) * Real.rpow (a : ℝ) (1 + ε) := by
        ring

end RHLean.Arithmetic
