import Mathlib
import RHLean.Proof.LowWheelSequentialPrimeWindows

/-!
# Sequential reciprocal-window telescope

For one fresh prime `p`, the mixed low-wheel cell at physical product
`n = a*(b*k)` is

`1_W(b*k) - 1_W(p*b*k)`,

where `W = primeDilateCofactorWindow p R X a`.

Summing over the residual multiplier `k` makes the sequential saving literal.
Multiplication `k ↦ p*k` is a bijection between

* multipliers whose `p`-dilate lies in `W`, and
* `p`-divisible multipliers whose undilated value lies in `W`.

Therefore those two populations cancel exactly.  The complete fresh-prime
multiplier sum is just the cardinality of the `p`-free residual multipliers in
the same reciprocal window.

This is an exact finite telescope.  It combines the geometric reciprocal window
with the chronological effect of adding one prime, before any norm or estimate.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Residual multipliers whose physical quotient `b*k` lies in the fresh-prime
reciprocal window. -/
def lowWheelPrimeWindowMultiplierSet
    (p R X a b : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun k =>
    b * k ∈ primeDilateCofactorWindow p R X a

/-- Residual multipliers whose `p`-dilated physical quotient lies in the same
window. -/
def lowWheelPrimeWindowDilatedMultiplierSet
    (p R X a b : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun k =>
    p * (b * k) ∈ primeDilateCofactorWindow p R X a

/-- Window multipliers still free of the newly added prime. -/
def lowWheelPrimeWindowFreeMultiplierSet
    (p R X a b : ℕ) : Finset ℕ :=
  (lowWheelPrimeWindowMultiplierSet p R X a b).filter fun k => ¬ p ∣ k

/-- Window multipliers already divisible by the newly added prime. -/
def lowWheelPrimeWindowDivisibleMultiplierSet
    (p R X a b : ℕ) : Finset ℕ :=
  (lowWheelPrimeWindowMultiplierSet p R X a b).filter fun k => p ∣ k

@[simp] theorem mem_lowWheelPrimeWindowMultiplierSet
    {p R X a b k : ℕ} :
    k ∈ lowWheelPrimeWindowMultiplierSet p R X a b ↔
      1 ≤ k ∧ k ≤ X ∧
        b * k ∈ primeDilateCofactorWindow p R X a := by
  simp [lowWheelPrimeWindowMultiplierSet, and_assoc]

@[simp] theorem mem_lowWheelPrimeWindowDilatedMultiplierSet
    {p R X a b k : ℕ} :
    k ∈ lowWheelPrimeWindowDilatedMultiplierSet p R X a b ↔
      1 ≤ k ∧ k ≤ X ∧
        p * (b * k) ∈ primeDilateCofactorWindow p R X a := by
  simp [lowWheelPrimeWindowDilatedMultiplierSet, and_assoc]

@[simp] theorem mem_lowWheelPrimeWindowFreeMultiplierSet
    {p R X a b k : ℕ} :
    k ∈ lowWheelPrimeWindowFreeMultiplierSet p R X a b ↔
      k ∈ lowWheelPrimeWindowMultiplierSet p R X a b ∧ ¬ p ∣ k := by
  simp [lowWheelPrimeWindowFreeMultiplierSet]

@[simp] theorem mem_lowWheelPrimeWindowDivisibleMultiplierSet
    {p R X a b k : ℕ} :
    k ∈ lowWheelPrimeWindowDivisibleMultiplierSet p R X a b ↔
      k ∈ lowWheelPrimeWindowMultiplierSet p R X a b ∧ p ∣ k := by
  simp [lowWheelPrimeWindowDivisibleMultiplierSet]

/-- Multiplication by the fresh prime identifies the dilated multiplier
population with the `p`-divisible part of the undilated window population. -/
theorem card_lowWheelPrimeWindowDilated_eq_divisible
    {p R X a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    (lowWheelPrimeWindowDilatedMultiplierSet p R X a b).card =
      (lowWheelPrimeWindowDivisibleMultiplierSet p R X a b).card := by
  classical
  refine Finset.card_bij (fun k _hk => p * k) ?_ ?_ ?_
  · intro k hk
    rcases mem_lowWheelPrimeWindowDilatedMultiplierSet.mp hk with
      ⟨hk1, _hkX, hwindow⟩
    have hwindow' :
        b * (p * k) ∈ primeDilateCofactorWindow p R X a := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hwindow
    have hqRange := primeDilateCofactorWindow_subset_Ioc p R X a ha hwindow'
    have hpkLeQ : p * k ≤ b * (p * k) := by
      have hb1 : 1 ≤ b := by omega
      simpa using Nat.mul_le_mul_right (p * k) hb1
    have hpkX : p * k ≤ X :=
      hpkLeQ.trans (Finset.mem_Ioc.mp hqRange).2
    have hkpos : 0 < k := by omega
    have hpk1 : 1 ≤ p * k := by
      exact Nat.succ_le_iff.mpr (Nat.mul_pos hp.pos hkpos)
    apply mem_lowWheelPrimeWindowDivisibleMultiplierSet.mpr
    refine ⟨mem_lowWheelPrimeWindowMultiplierSet.mpr ?_, dvd_mul_right p k⟩
    exact ⟨hpk1, hpkX, hwindow'⟩
  · intro k1 _hk1 k2 _hk2 hmul
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmul
  · intro j hj
    rcases mem_lowWheelPrimeWindowDivisibleMultiplierSet.mp hj with
      ⟨hjWindow, hpj⟩
    rcases mem_lowWheelPrimeWindowMultiplierSet.mp hjWindow with
      ⟨hj1, hjX, hwindow⟩
    let k := j / p
    have hjpos : 0 < j := by omega
    have hpLeJ : p ≤ j := Nat.le_of_dvd hjpos hpj
    have hk1 : 1 ≤ k := by
      unfold k
      exact (Nat.one_le_div_iff hp.pos).2 hpLeJ
    have hkX : k ≤ X := by
      unfold k
      exact (Nat.div_le_self j p).trans hjX
    have hcancel : p * k = j := by
      unfold k
      exact Nat.mul_div_cancel' hpj
    have harg : p * (b * k) = b * j := by
      calc
        p * (b * k) = b * (p * k) := by ring
        _ = b * j := by rw [hcancel]
    have hwindow' :
        p * (b * k) ∈ primeDilateCofactorWindow p R X a := by
      rw [harg]
      exact hwindow
    refine ⟨k, mem_lowWheelPrimeWindowDilatedMultiplierSet.mpr
      ⟨hk1, hkX, hwindow'⟩, hcancel⟩

/-- The undilated window multiplier set is the disjoint union of its fresh-prime
free and divisible parts. -/
theorem card_lowWheelPrimeWindowMultiplier_eq_free_add_divisible
    (p R X a b : ℕ) :
    (lowWheelPrimeWindowMultiplierSet p R X a b).card =
      (lowWheelPrimeWindowFreeMultiplierSet p R X a b).card +
        (lowWheelPrimeWindowDivisibleMultiplierSet p R X a b).card := by
  classical
  have hunion :
      lowWheelPrimeWindowFreeMultiplierSet p R X a b ∪
          lowWheelPrimeWindowDivisibleMultiplierSet p R X a b =
        lowWheelPrimeWindowMultiplierSet p R X a b := by
    ext k
    by_cases hpk : p ∣ k <;>
      simp [lowWheelPrimeWindowFreeMultiplierSet,
        lowWheelPrimeWindowDivisibleMultiplierSet, hpk]
  have hdisj :
      Disjoint
        (lowWheelPrimeWindowFreeMultiplierSet p R X a b)
        (lowWheelPrimeWindowDivisibleMultiplierSet p R X a b) := by
    rw [Finset.disjoint_left]
    intro k hkfree hkdiv
    have hnot := (mem_lowWheelPrimeWindowFreeMultiplierSet.mp hkfree).2
    have hyes := (mem_lowWheelPrimeWindowDivisibleMultiplierSet.mp hkdiv).2
    exact hnot hyes
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  exact hcard

/-- Summing a window indicator over the ambient multiplier range gives the
cardinality of the corresponding window multiplier set. -/
theorem sum_lowWheelPrimeWindowIndicator_eq_card
    (p R X a b : ℕ) :
    (∑ k ∈ Finset.Icc 1 X,
        lowWheelPrimeDilateWindowIndicator p R X a (b * k)) =
      ((lowWheelPrimeWindowMultiplierSet p R X a b).card : ℤ) := by
  classical
  unfold lowWheelPrimeDilateWindowIndicator lowWheelPrimeWindowMultiplierSet
  calc
    (∑ k ∈ Finset.Icc 1 X,
        if b * k ∈ primeDilateCofactorWindow p R X a then (1 : ℤ) else 0) =
      ∑ k ∈ (Finset.Icc 1 X).filter
          (fun k => b * k ∈ primeDilateCofactorWindow p R X a), (1 : ℤ) := by
        rw [Finset.sum_filter]
    _ = (((Finset.Icc 1 X).filter
          (fun k => b * k ∈ primeDilateCofactorWindow p R X a)).card : ℤ) := by
      simp

/-- The dilated indicator sum is the cardinality of the dilated multiplier
population. -/
theorem sum_lowWheelPrimeWindowDilatedIndicator_eq_card
    (p R X a b : ℕ) :
    (∑ k ∈ Finset.Icc 1 X,
        lowWheelPrimeDilateWindowIndicator p R X a (p * (b * k))) =
      ((lowWheelPrimeWindowDilatedMultiplierSet p R X a b).card : ℤ) := by
  classical
  unfold lowWheelPrimeDilateWindowIndicator
    lowWheelPrimeWindowDilatedMultiplierSet
  calc
    (∑ k ∈ Finset.Icc 1 X,
        if p * (b * k) ∈ primeDilateCofactorWindow p R X a then
          (1 : ℤ) else 0) =
      ∑ k ∈ (Finset.Icc 1 X).filter
          (fun k => p * (b * k) ∈ primeDilateCofactorWindow p R X a),
        (1 : ℤ) := by
      rw [Finset.sum_filter]
    _ = (((Finset.Icc 1 X).filter
          (fun k => p * (b * k) ∈ primeDilateCofactorWindow p R X a)).card : ℤ) := by
      simp

/-- **Sequential geometric telescope.**  After one prime is added, summing the
mixed cell over the residual multiplier cancels exactly the `p`-divisible
population.  Only `p`-free multipliers in the reciprocal window survive. -/
theorem sum_lowWheelMixedPrimeCell_mul_eq_freeWindowCard
    {p R X a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    (∑ k ∈ Finset.Icc 1 X,
        lowWheelMixedPrimeCell p R X (b * k) (a * (b * k))) =
      ((lowWheelPrimeWindowFreeMultiplierSet p R X a b).card : ℤ) := by
  calc
    (∑ k ∈ Finset.Icc 1 X,
        lowWheelMixedPrimeCell p R X (b * k) (a * (b * k))) =
      ∑ k ∈ Finset.Icc 1 X,
        (lowWheelPrimeDilateWindowIndicator p R X a (b * k) -
          lowWheelPrimeDilateWindowIndicator p R X a (p * (b * k))) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact lowWheelMixedPrimeCell_mul_eq_window_sub_dilate hp ha
    _ = (∑ k ∈ Finset.Icc 1 X,
          lowWheelPrimeDilateWindowIndicator p R X a (b * k)) -
        ∑ k ∈ Finset.Icc 1 X,
          lowWheelPrimeDilateWindowIndicator p R X a (p * (b * k)) := by
      rw [Finset.sum_sub_distrib]
    _ = ((lowWheelPrimeWindowMultiplierSet p R X a b).card : ℤ) -
        ((lowWheelPrimeWindowDilatedMultiplierSet p R X a b).card : ℤ) := by
      rw [sum_lowWheelPrimeWindowIndicator_eq_card,
        sum_lowWheelPrimeWindowDilatedIndicator_eq_card]
    _ = ((lowWheelPrimeWindowFreeMultiplierSet p R X a b).card : ℤ) := by
      rw [card_lowWheelPrimeWindowDilated_eq_divisible hp ha hb]
      have hsplit :=
        card_lowWheelPrimeWindowMultiplier_eq_free_add_divisible p R X a b
      omega

end RHLean.Proof
