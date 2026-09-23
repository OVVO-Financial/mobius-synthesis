import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime
import RHLean.Analysis.RoughWheelFiniteCounting
import RHLean.Analysis.RamanujanDivisorBoundary
import RHLean.Proof.PostRootCovarianceUnconditionalDecayScratch

/-!
# Signed rough-seat correlation of a finite prime wheel

For a finite prime set `S`, let

`K_S(X) = sum_{d | prod S, d <= X} mu(d)`.

Adjoining a fresh prime is exactly one multiplicative finite difference:

`K_{S union {p}}(X) = K_S(X) - K_S(floor(X/p))`.

The full signed wheel then Fubini-reindexes before any norm is taken:

`M(B) = sum_{B/W < n <= B, (n,W)=1} mu(n) * K_S(floor(B/n))`.

Thus every overlap between the exponentially many signed divisor bands is
already collapsed into one integer coefficient on each physical rough seat.
No absolute value, density estimate, or wheel-depth loss occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Signed Mobius mass of wheel divisors admitted by cutoff `X`.  The `if`
form keeps the complete divisor carrier fixed, which makes fresh-prime
refinement an exact fiber split. -/
def primeWheelTruncatedMoebiusKernel (S : Finset ℕ) (X : ℕ) : ℤ :=
  ∑ d ∈ (primorial S).divisors,
    if d ≤ X then (μ d : ℤ) else 0

/-- **Exact fresh-prime recurrence for the signed cutoff kernel.**  The old
divisors and their fresh-`p` children have opposite Mobius signs, so adjoining
`p` differences the old kernel at the reciprocal cutoff. -/
theorem primeWheelTruncatedMoebiusKernel_insert
    (S : Finset ℕ) (p X : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    primeWheelTruncatedMoebiusKernel (insert p S) X =
      primeWheelTruncatedMoebiusKernel S X -
        primeWheelTruncatedMoebiusKernel S (X / p) := by
  classical
  have hcop : Nat.Coprime p (primorial S) :=
    prime_coprime_primorial S p hp hpS hprime
  have hdisj :=
    disjoint_divisors_primorial_mul_image S p hp hpS hprime
  unfold primeWheelTruncatedMoebiusKernel
  rw [divisors_primorial_insert S p hp hpS]
  rw [Finset.sum_union hdisj]
  have hinj : Set.InjOn (fun d : ℕ => p * d) (primorial S).divisors := by
    intro a _ha b _hb hab
    exact Nat.mul_left_cancel hp.pos hab
  have hsecond :
      (∑ d ∈ (primorial S).divisors.image (fun d => p * d),
          if d ≤ X then (μ d : ℤ) else 0) =
        -(∑ d ∈ (primorial S).divisors,
          if d ≤ X / p then (μ d : ℤ) else 0) := by
    rw [Finset.sum_image hinj]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdP : d ∣ primorial S := Nat.dvd_of_mem_divisors hd
    have hcopd : Nat.Coprime p d := hcop.of_dvd_right hdP
    have hmu : μ (p * d) = -μ d := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopd]
      rw [ArithmeticFunction.moebius_apply_prime hp]
      ring
    have hcut : p * d ≤ X ↔ d ≤ X / p := by
      constructor
      · intro h
        apply (Nat.le_div_iff_mul_le hp.pos).2
        simpa [Nat.mul_comm] using h
      · intro h
        have hm := (Nat.le_div_iff_mul_le hp.pos).1 h
        simpa [Nat.mul_comm] using hm
    by_cases hdX : d ≤ X / p
    · have hpdX : p * d ≤ X := hcut.mpr hdX
      simp [hdX, hpdX, hmu]
    · have hpdX : ¬ p * d ≤ X := by
        intro h
        exact hdX (hcut.mp h)
      simp [hdX, hpdX]
  rw [hsecond]
  ring

/-- The recurrence can be read literally as the old cutoff kernel minus its
fresh-prime-scaled child. -/
theorem primeWheelTruncatedMoebiusKernel_insert_sub
    (S : Finset ℕ) (p X : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    primeWheelTruncatedMoebiusKernel (insert p S) X -
        primeWheelTruncatedMoebiusKernel S X =
      -primeWheelTruncatedMoebiusKernel S (X / p) := by
  rw [primeWheelTruncatedMoebiusKernel_insert S p X hp hpS hprime]
  ring

private theorem primeWheelPrimorial_pos
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    0 < RHLean.Arithmetic.primorial S := by
  unfold RHLean.Arithmetic.primorial
  exact Finset.prod_pos fun p hp => (hprime p hp).pos

/-- Once the cutoff contains the complete nontrivial wheel, the signed kernel
vanishes exactly: all Boolean divisor faces have been admitted and their
Mobius mass is zero. -/
theorem primeWheelTruncatedMoebiusKernel_eq_zero_of_primorial_le
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hWne : RHLean.Arithmetic.primorial S ≠ 1) {X : ℕ}
    (hWX : RHLean.Arithmetic.primorial S ≤ X) :
    primeWheelTruncatedMoebiusKernel S X = 0 := by
  have hWpos := primeWheelPrimorial_pos S hprime
  unfold primeWheelTruncatedMoebiusKernel
  have hcut : ∀ d ∈ (RHLean.Arithmetic.primorial S).divisors, d ≤ X := by
    intro d hd
    have hdvd : d ∣ RHLean.Arithmetic.primorial S := Nat.dvd_of_mem_divisors hd
    exact (Nat.le_of_dvd hWpos hdvd).trans hWX
  calc
    (∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
        if d ≤ X then (μ d : ℤ) else 0) =
      ∑ d ∈ (RHLean.Arithmetic.primorial S).divisors, (μ d : ℤ) := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [hcut d hd]
    _ = 0 := by
      rw [RHLean.Analysis.sum_moebius_divisors_eq_one_or_zero]
      simp [hWne]

/-- Removing the harmless zero term writes a rough Mertens prefix on the
positive integer carrier. -/
private theorem roughMertens_eq_sum_Icc_one (W X : ℕ) :
    roughMertens W X =
      ∑ n ∈ Finset.Icc 1 X, roughMoebius W n := by
  unfold roughMertens
  have hset :
      Finset.range (X + 1) = insert 0 (Finset.Icc 1 X) := by
    ext n
    simp
    omega
  rw [hset]
  simp [roughMoebius]

/-- A reciprocal prefix can be padded to the common physical prefix by an
upper-cutoff indicator. -/
private theorem sum_Icc_div_eq_full_cutoff
    (B d : ℕ) (f : ℕ → ℤ) :
    (∑ n ∈ Finset.Icc 1 (B / d), f n) =
      ∑ n ∈ Finset.Icc 1 B, if n ≤ B / d then f n else 0 := by
  have hset :
      Finset.Icc 1 (B / d) =
        (Finset.Icc 1 B).filter (fun n => n ≤ B / d) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨hn1, hnd⟩
      exact ⟨⟨hn1, hnd.trans (Nat.div_le_self B d)⟩, hnd⟩
    · rintro ⟨⟨hn1, _hnB⟩, hnd⟩
      exact ⟨hn1, hnd⟩
  rw [hset, Finset.sum_filter]

/-- **Fubini collapse of the full divisor cube.**  Before restricting to
coprime physical seats, the exact divisor-difference representation is already
one correlation: rough Mobius at `n` times the complete signed truncated wheel
kernel at reciprocal cutoff `floor(B/n)`.

This is the crucial algebraic step: the `2^|S|` signed bands disappear before
any norm is introduced. -/
theorem roughMertens_one_eq_primeWheel_kernelCorrelation
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (B : ℕ) :
    roughMertens 1 B =
      ∑ n ∈ Finset.Icc 1 B,
        roughMoebius (RHLean.Arithmetic.primorial S) n *
          primeWheelTruncatedMoebiusKernel S (B / n) := by
  rw [roughMertens_one_eq_primeWheel_divisorDifference S hprime B]
  simp_rw [roughMertens_eq_sum_Icc_one]
  calc
    (∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
        (μ d : ℤ) *
          ∑ n ∈ Finset.Icc 1 (B / d), roughMoebius (RHLean.Arithmetic.primorial S) n) =
      ∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
        ∑ n ∈ Finset.Icc 1 B,
          if n ≤ B / d then
            (μ d : ℤ) * roughMoebius (RHLean.Arithmetic.primorial S) n
          else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]
      exact sum_Icc_div_eq_full_cutoff B d
        (fun n => (μ d : ℤ) * roughMoebius (RHLean.Arithmetic.primorial S) n)
    _ = ∑ n ∈ Finset.Icc 1 B,
        ∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
          if n ≤ B / d then
            (μ d : ℤ) * roughMoebius (RHLean.Arithmetic.primorial S) n
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 B,
        roughMoebius (RHLean.Arithmetic.primorial S) n *
          primeWheelTruncatedMoebiusKernel S (B / n) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := by
        exact (Finset.mem_Icc.mp hn).1
      unfold primeWheelTruncatedMoebiusKernel
      have hinner :
          (∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
              if n ≤ B / d then
                (μ d : ℤ) * roughMoebius (RHLean.Arithmetic.primorial S) n
              else 0) =
            (∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
              if d ≤ B / n then (μ d : ℤ) else 0) *
                roughMoebius (RHLean.Arithmetic.primorial S) n := by
        calc
          (∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
              if n ≤ B / d then
                (μ d : ℤ) * roughMoebius (RHLean.Arithmetic.primorial S) n
              else 0) =
            ∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
              (if d ≤ B / n then (μ d : ℤ) else 0) *
                roughMoebius (RHLean.Arithmetic.primorial S) n := by
              apply Finset.sum_congr rfl
              intro d hd
              have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
              have hcut : n ≤ B / d ↔ d ≤ B / n := by
                rw [Nat.le_div_iff_mul_le hdpos,
                  Nat.le_div_iff_mul_le hnpos]
                exact ⟨fun h => by simpa [Nat.mul_comm] using h,
                  fun h => by simpa [Nat.mul_comm] using h⟩
              by_cases hdn : d ≤ B / n
              · have hnd : n ≤ B / d := hcut.mpr hdn
                simp [hdn, hnd]
              · have hnd : ¬ n ≤ B / d := by
                  intro h
                  exact hdn (hcut.mp h)
                simp [hdn, hnd]
          _ = (∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
              if d ≤ B / n then (μ d : ℤ) else 0) *
                roughMoebius (RHLean.Arithmetic.primorial S) n := by
              rw [Finset.sum_mul]
      rw [hinner]
      ring

/-- The same identity on the literal coprime physical carrier. -/
theorem roughMertens_one_eq_primeWheel_fullRoughSeatCorrelation
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (B : ℕ) :
    roughMertens 1 B =
      ∑ n ∈ roughWheelInterval (RHLean.Arithmetic.primorial S) 0 B,
        (μ n : ℤ) * primeWheelTruncatedMoebiusKernel S (B / n) := by
  rw [roughMertens_one_eq_primeWheel_kernelCorrelation S hprime B]
  have hset :
      roughWheelInterval (RHLean.Arithmetic.primorial S) 0 B =
        (Finset.Icc 1 B).filter
          (fun n => Nat.Coprime n (RHLean.Arithmetic.primorial S)) := by
    ext n
    simp only [roughWheelInterval, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn0, hnB⟩, hcop⟩
      exact ⟨⟨by omega, hnB⟩, hcop⟩
    · rintro ⟨⟨hn1, hnB⟩, hcop⟩
      exact ⟨⟨by omega, hnB⟩, hcop⟩
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold roughMoebius
  by_cases hcop : Nat.Coprime n (RHLean.Arithmetic.primorial S) <;> simp [hcop]

/-- The final physical carrier: only rough seats above the common anchor
`B/W` are retained, because below that anchor the complete divisor cube has
already entered and its signed kernel is exactly zero. -/
def primeWheelRoughSeatCorrelation (S : Finset ℕ) (B : ℕ) : ℤ :=
  ∑ n ∈ roughWheelInterval (RHLean.Arithmetic.primorial S)
      (B / RHLean.Arithmetic.primorial S) B,
    (μ n : ℤ) * primeWheelTruncatedMoebiusKernel S (B / n)

/-- **Exact rough-seat correlation identity.**  For every nontrivial finite
prime wheel,

`M(B) = sum_{B/W < n <= B, (n,W)=1} mu(n) K_S(floor(B/n))`.

This is the signed estimate target exposed by the prime-wheel block geometry.
All band overlaps have been Fubini-collapsed into `K_S` before any absolute
value is taken. -/
theorem roughMertens_one_eq_primeWheel_roughSeatCorrelation
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hWne : RHLean.Arithmetic.primorial S ≠ 1) (B : ℕ) :
    roughMertens 1 B = primeWheelRoughSeatCorrelation S B := by
  rw [roughMertens_one_eq_primeWheel_fullRoughSeatCorrelation S hprime B]
  unfold primeWheelRoughSeatCorrelation
  have hWpos := primeWheelPrimorial_pos S hprime
  let A := roughWheelInterval (RHLean.Arithmetic.primorial S) 0 B
  let f : ℕ → ℤ := fun n =>
    (μ n : ℤ) * primeWheelTruncatedMoebiusKernel S (B / n)
  have hset :
      roughWheelInterval (RHLean.Arithmetic.primorial S)
          (B / RHLean.Arithmetic.primorial S) B =
        A.filter (fun n => B / RHLean.Arithmetic.primorial S < n) := by
    ext n
    simp only [A, roughWheelInterval, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hnlow, hnB⟩, hcop⟩
      have hnpos : 0 < n :=
        lt_of_le_of_lt (Nat.zero_le (B / RHLean.Arithmetic.primorial S)) hnlow
      exact ⟨⟨⟨hnpos, hnB⟩, hcop⟩, hnlow⟩
    · rintro ⟨⟨⟨_hn0, hnB⟩, hcop⟩, hnlow⟩
      exact ⟨⟨hnlow, hnB⟩, hcop⟩
  have hvanish :
      ∀ n ∈ A, ¬ B / RHLean.Arithmetic.primorial S < n → f n = 0 := by
    intro n hn hnot
    have hnmem : n ∈ roughWheelInterval (RHLean.Arithmetic.primorial S) 0 B := by
      simpa [A] using hn
    have hnIoc := (Finset.mem_filter.mp hnmem).1
    have hnpos : 0 < n := (Finset.mem_Ioc.mp hnIoc).1
    have hnle : n ≤ B / RHLean.Arithmetic.primorial S := by omega
    have hmul : n * RHLean.Arithmetic.primorial S ≤ B :=
      (Nat.le_div_iff_mul_le hWpos).1 hnle
    have hWcut : RHLean.Arithmetic.primorial S ≤ B / n := by
      apply (Nat.le_div_iff_mul_le hnpos).2
      simpa [Nat.mul_comm] using hmul
    have hkzero :=
      primeWheelTruncatedMoebiusKernel_eq_zero_of_primorial_le
        S hprime hWne hWcut
    simp [f, hkzero]
  change (∑ n ∈ A, f n) = _
  calc
    (∑ n ∈ A, f n) =
        ∑ n ∈ A,
          if B / RHLean.Arithmetic.primorial S < n then f n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : B / RHLean.Arithmetic.primorial S < n
      · simp [h]
      · simp [h, hvanish n hn h]
    _ = ∑ n ∈ A.filter
        (fun n => B / RHLean.Arithmetic.primorial S < n), f n := by
      rw [Finset.sum_filter]
    _ = ∑ n ∈ roughWheelInterval (RHLean.Arithmetic.primorial S)
        (B / RHLean.Arithmetic.primorial S) B,
        (μ n : ℤ) * primeWheelTruncatedMoebiusKernel S (B / n) := by
      rw [← hset]

end RHLean.Proof
