import Mathlib

/-!
# Ramanujan sums as divisor-boundary fluctuations

This file isolates the purely arithmetic layer needed after the reduced-
conductor shell collapse.  The Ramanujan kernel is written in its classical
divisor form

`c_q(m-a) = sum_{d | q, m = a mod d} d * mu(q / d)`.

Summing over a finite window and exchanging the two finite sums produces one
residue-class count for every divisor `d | q`.  For `q > 1`, the common bulk
term cancels exactly because

`sum_{d | q} mu(q / d) = 0`.

What remains is a signed sum of explicit divisor-residue boundary defects.  No
Fourier estimate, norm inequality, or asymptotic input is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Classical Ramanujan kernel in divisor form.  The shift is represented by a
natural residue class rather than natural subtraction, so the same definition
handles both unshifted and translated windows. -/
def ramanujanDivisorKernel (q m a : ℕ) : ℤ :=
  ∑ d ∈ q.divisors,
    if Nat.ModEq d m a then
      (d : ℤ) * μ (q / d)
    else 0

/-- Number of points of a finite set lying in one residue class, represented as
an integer-valued indicator sum. -/
def divisorResidueCount
    (I : Finset ℕ) (d a : ℕ) : ℤ :=
  ∑ m ∈ I, if Nat.ModEq d m a then 1 else 0

/-- Boundary defect of one residue class.  A perfectly uniform interval of
`I.card / d` points would make this quantity zero. -/
def divisorResidueBoundary
    (I : Finset ℕ) (d a : ℕ) : ℤ :=
  (d : ℤ) * divisorResidueCount I d a - (I.card : ℤ)

/-- Ramanujan divisor kernel summed over an arbitrary finite set. -/
def ramanujanDivisorSumOn
    (q a : ℕ) (I : Finset ℕ) : ℤ :=
  ∑ m ∈ I, ramanujanDivisorKernel q m a

/-- The sum of the Möbius function over all divisors is the Kronecker delta at
one. -/
theorem sum_moebius_divisors_eq_one_or_zero (q : ℕ) :
    (∑ d ∈ q.divisors, μ d) = if q = 1 then 1 else 0 := by
  calc
    (∑ d ∈ q.divisors, μ d) =
        (((↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
          ArithmeticFunction.moebius) q) := by
            symm
            exact ArithmeticFunction.coe_zeta_mul_apply
    _ = (1 : ArithmeticFunction ℤ) q := by
      rw [ArithmeticFunction.coe_zeta_mul_moebius]
    _ = if q = 1 then 1 else 0 := by
      exact ArithmeticFunction.one_apply

/-- Complementary-divisor form of the same Möbius cancellation. -/
theorem sum_moebius_complementary_divisors_eq_zero
    {q : ℕ} (hq : 1 < q) :
    (∑ d ∈ q.divisors, μ (q / d)) = 0 := by
  calc
    (∑ d ∈ q.divisors, μ (q / d)) =
        ∑ d ∈ q.divisors, μ d := by
          exact Nat.sum_div_divisors q (fun d : ℕ => μ d)
    _ = 0 := by
      rw [sum_moebius_divisors_eq_one_or_zero q]
      simp [Nat.ne_of_gt hq]

/-- Exchange the Ramanujan sum with the finite physical window.  The result is
an exact sum of divisor-dependent residue counts. -/
theorem ramanujanDivisorSumOn_eq_residueCounts
    (q a : ℕ) (I : Finset ℕ) :
    ramanujanDivisorSumOn q a I =
      ∑ d ∈ q.divisors,
        ((d : ℤ) * μ (q / d)) * divisorResidueCount I d a := by
  classical
  unfold ramanujanDivisorSumOn ramanujanDivisorKernel
    divisorResidueCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    (∑ m ∈ I,
        if Nat.ModEq d m a then
          (d : ℤ) * μ (q / d)
        else 0) =
      ∑ m ∈ I,
        ((d : ℤ) * μ (q / d)) *
          (if Nat.ModEq d m a then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro m hm
            by_cases hmod : Nat.ModEq d m a
            · simp [hmod]
            · simp [hmod]
    _ = ((d : ℤ) * μ (q / d)) *
        ∑ m ∈ I, if Nat.ModEq d m a then 1 else 0 := by
          rw [Finset.mul_sum]

/-- Exact bulk cancellation for every nontrivial conductor.  The full interval
Ramanujan sum is nothing but the signed sum of divisor-residue boundary defects.
This is the arithmetic endpoint required before any estimate is attempted. -/
theorem ramanujanDivisorSumOn_eq_boundary
    {q : ℕ} (hq : 1 < q) (a : ℕ) (I : Finset ℕ) :
    ramanujanDivisorSumOn q a I =
      ∑ d ∈ q.divisors,
        μ (q / d) * divisorResidueBoundary I d a := by
  classical
  rw [ramanujanDivisorSumOn_eq_residueCounts]
  have hmu : (∑ d ∈ q.divisors, μ (q / d)) = 0 :=
    sum_moebius_complementary_divisors_eq_zero hq
  unfold divisorResidueBoundary
  calc
    (∑ d ∈ q.divisors,
        ((d : ℤ) * μ (q / d)) * divisorResidueCount I d a) =
      ∑ d ∈ q.divisors,
        (μ (q / d) *
            ((d : ℤ) * divisorResidueCount I d a - (I.card : ℤ)) +
          μ (q / d) * (I.card : ℤ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
    _ =
      (∑ d ∈ q.divisors,
        μ (q / d) *
          ((d : ℤ) * divisorResidueCount I d a - (I.card : ℤ))) +
      ∑ d ∈ q.divisors, μ (q / d) * (I.card : ℤ) := by
        rw [Finset.sum_add_distrib]
    _ =
      (∑ d ∈ q.divisors,
        μ (q / d) *
          ((d : ℤ) * divisorResidueCount I d a - (I.card : ℤ))) +
      (I.card : ℤ) * (∑ d ∈ q.divisors, μ (q / d)) := by
        congr 1
        calc
          (∑ d ∈ q.divisors, μ (q / d) * (I.card : ℤ)) =
              ∑ d ∈ q.divisors, (I.card : ℤ) * μ (q / d) := by
                apply Finset.sum_congr rfl
                intro d hd
                ring
          _ = (I.card : ℤ) * (∑ d ∈ q.divisors, μ (q / d)) := by
            rw [Finset.mul_sum]
    _ =
      ∑ d ∈ q.divisors,
        μ (q / d) *
          ((d : ℤ) * divisorResidueCount I d a - (I.card : ℤ)) := by
            rw [hmu]
            simp

/-- Pinned integer interval specialization of the divisor-form Ramanujan sum. -/
def ramanujanDivisorInterval
    (q a lower upper : ℕ) : ℤ :=
  ramanujanDivisorSumOn q a (Finset.Ioc lower upper)

/-- Pinned interval specialization of one divisor-residue boundary defect. -/
def divisorIntervalBoundary
    (d a lower upper : ℕ) : ℤ :=
  divisorResidueBoundary (Finset.Ioc lower upper) d a

/-- On every nontrivial conductor, a shifted Ramanujan interval is exactly a
finite Möbius-weighted sum of explicit divisor boundary defects. -/
theorem ramanujanDivisorInterval_eq_boundary
    {q : ℕ} (hq : 1 < q)
    (a lower upper : ℕ) :
    ramanujanDivisorInterval q a lower upper =
      ∑ d ∈ q.divisors,
        μ (q / d) * divisorIntervalBoundary d a lower upper := by
  exact ramanujanDivisorSumOn_eq_boundary
    hq a (Finset.Ioc lower upper)

/-- Residue counting is literally the cardinality of the corresponding finite
filter.  This form is useful for short-interval rigidity. -/
theorem divisorResidueCount_eq_filterCard_sharp
    (I : Finset ℕ) (d a : ℕ) :
    divisorResidueCount I d a =
      (((I.filter fun m => Nat.ModEq d m a).card : ℕ) : ℤ) := by
  classical
  unfold divisorResidueCount
  calc
    (∑ m ∈ I, if Nat.ModEq d m a then (1 : ℤ) else 0) =
        ∑ m ∈ I with Nat.ModEq d m a, (1 : ℤ) := by
      rw [Finset.sum_filter]
    _ = (((I.filter fun m => Nat.ModEq d m a).card : ℕ) : ℤ) := by
      simp

/-- **Sharp short-interval boundary bound.**  An interval shorter than one
positive modulus contains at most one point of any fixed residue class.  Hence
the centered residue defect has absolute value at most one modulus, not the
quadratic bound used by the earlier deliberately crude conductor estimate. -/
theorem abs_divisorIntervalBoundary_le_modulus_of_short
    (d a lower upper : ℕ)
    (hlower : lower ≤ upper) (hshort : upper - lower < d) :
    |divisorIntervalBoundary d a lower upper| ≤ (d : ℤ) := by
  classical
  let I : Finset ℕ := Finset.Ioc lower upper
  let F : Finset ℕ := I.filter fun m => Nat.ModEq d m a
  have hupperShort : upper < lower + d := by omega
  have hcardF : F.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro m hm n hn
    have hmData := Finset.mem_filter.mp hm
    have hnData := Finset.mem_filter.mp hn
    have hmI : m ∈ Finset.Ioc lower upper := by simpa [I] using hmData.1
    have hnI : n ∈ Finset.Ioc lower upper := by simpa [I] using hnData.1
    have hmBounds := Finset.mem_Ioc.mp hmI
    have hnBounds := Finset.mem_Ioc.mp hnI
    have hmBig : m ∈ Finset.Ico (lower + 1) (lower + 1 + d) := by
      apply Finset.mem_Ico.mpr
      omega
    have hnBig : n ∈ Finset.Ico (lower + 1) (lower + 1 + d) := by
      apply Finset.mem_Ico.mpr
      omega
    have hmrem : m % d = a % d := by
      simpa [Nat.ModEq] using hmData.2
    have hnrem : n % d = a % d := by
      simpa [Nat.ModEq] using hnData.2
    have hrem : m % d = n % d := hmrem.trans hnrem.symm
    have hinj : Set.InjOn (fun z : ℕ => z % d)
        (↑(Finset.Ico (lower + 1) (lower + 1 + d))) := by
      simpa using Nat.mod_injOn_Ico (lower + 1) d
    exact hinj hmBig hnBig hrem
  have hcount : divisorResidueCount I d a = (F.card : ℤ) := by
    simpa [F] using divisorResidueCount_eq_filterCard_sharp I d a
  have hc0 : (0 : ℤ) ≤ divisorResidueCount I d a := by
    rw [hcount]
    positivity
  have hc1 : divisorResidueCount I d a ≤ 1 := by
    rw [hcount]
    exact_mod_cast hcardF
  have hcardI : I.card = upper - lower := by
    dsimp [I]
    exact Nat.card_Ioc lower upper
  have hrleNat : upper - lower ≤ d := Nat.le_of_lt hshort
  have hrle : (((upper - lower : ℕ) : ℤ)) ≤ (d : ℤ) := by
    exact_mod_cast hrleNat
  unfold divisorIntervalBoundary divisorResidueBoundary
  change
    |(d : ℤ) * divisorResidueCount I d a - (I.card : ℤ)| ≤ (d : ℤ)
  rw [hcardI]
  apply (abs_le).2
  constructor <;> nlinarith

end RHLean.Analysis
