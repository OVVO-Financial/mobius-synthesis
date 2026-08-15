import Mathlib
import RHLean.Analysis.NativePNTSignedLogSquarePrimeCells
import RHLean.Arithmetic.MoebiusDoubling

/-!
# Positive dyadic kernel inside the signed second Selberg transform

The raw identity `Lambda_2 = mu * log^2` is split by parity of the Mobius
cofactor.  The odd-cofactor part is retained as one kernel `K`.  Every even
cofactor is either twice an odd cofactor, where Mobius changes sign, or twice
an even cofactor, where the Mobius value is zero.  Consequently

`Lambda_2(d) = K(d)` for odd `d`,

`Lambda_2(d) = K(d) - K(d/2)` for positive even `d`.

Since `Lambda_2` is nonnegative, this recurrence also proves `K(d) >= 0` for
every `d`.  Thus the dyadic cross-endpoint cells arise inside the actual
second-Selberg coefficient, not from an auxiliary scalar good-mass hypothesis.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Odd-Mobius part of the log-square coefficient at product `d`. -/
def nativePNTLambdaTwoOddMobiusKernel (d : ℕ) : ℝ :=
  ∑ m ∈ d.divisors,
    if Odd m then
      (μ : ArithmeticFunction ℝ) m * (Real.log ((d / m : ℕ) : ℝ)) ^ 2
    else 0

/-- Complementary even-Mobius part of the same divisor fibre. -/
def nativePNTLambdaTwoEvenMobiusPart (d : ℕ) : ℝ :=
  ∑ m ∈ d.divisors,
    if Even m then
      (μ : ArithmeticFunction ℝ) m * (Real.log ((d / m : ℕ) : ℝ)) ^ 2
    else 0

private theorem nativePNT_dvd_odd_is_odd
    {m d : ℕ} (hmd : m ∣ d) (hd : Odd d) : Odd m := by
  by_contra hm
  have hmeven : Even m := Nat.not_odd_iff_even.mp hm
  have hdEven : Even d := by
    rcases hmd with ⟨t, rfl⟩
    rcases hmeven with ⟨a, ha⟩
    refine ⟨a * t, ?_⟩
    rw [ha]
    ring
  exact (Nat.not_even_iff_odd.mpr hd) hdEven

private theorem nativePNTMobiusReal_two_mul (m : ℕ) :
    (μ : ArithmeticFunction ℝ) (2 * m) =
      if Odd m then -(μ : ArithmeticFunction ℝ) m else 0 := by
  by_cases hm : Odd m
  · rw [if_pos hm]
    change (((μ (2 * m) : ℤ) : ℝ)) = -(((μ m : ℤ) : ℝ))
    rw [moebius_two_mul_of_odd m hm]
    push_cast
    rfl
  · rw [if_neg hm]
    have heven : Even m := Nat.not_odd_iff_even.mp hm
    have hzero : μ (2 * m) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hsq
      have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
      apply hnot
      rcases heven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    change (((μ (2 * m) : ℤ) : ℝ)) = 0
    rw [hzero]
    simp

/-- The full Mobius log-square coefficient splits exactly by cofactor parity. -/
theorem nativeMobiusLogSquareDivisorFiber_eq_oddKernel_add_evenPart
    (d : ℕ) :
    nativeMobiusLogSquareDivisorFiber d =
      nativePNTLambdaTwoOddMobiusKernel d +
        nativePNTLambdaTwoEvenMobiusPart d := by
  unfold nativeMobiusLogSquareDivisorFiber
    nativePNTLambdaTwoOddMobiusKernel nativePNTLambdaTwoEvenMobiusPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hodd : Odd m
  · have hnotEven : ¬Even m := Nat.not_even_iff_odd.mpr hodd
    simp [hodd, hnotEven]
  · have heven : Even m := Nat.not_odd_iff_even.mp hodd
    simp [hodd, heven]

/-- On an odd product every divisor is odd, so the positive dyadic kernel is
literally `Lambda_2`. -/
theorem nativePNTLambdaTwoOddMobiusKernel_eq_lambdaTwo_of_odd
    (d : ℕ) (hd : Odd d) :
    nativePNTLambdaTwoOddMobiusKernel d = nativeLambdaTwo d := by
  rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo d]
  unfold nativePNTLambdaTwoOddMobiusKernel nativeMobiusLogSquareDivisorFiber
  apply Finset.sum_congr rfl
  intro m hm
  have hmd : m ∣ d := (Nat.mem_divisors.mp hm).1
  have hodd := nativePNT_dvd_odd_is_odd hmd hd
  simp [hodd]

/-- The even cofactor contribution at a positive even product is exactly the
negative odd kernel at half the product. -/
theorem nativePNTLambdaTwoEvenMobiusPart_eq_neg_half
    (d : ℕ) (hdpos : 0 < d) (hdeven : Even d) :
    nativePNTLambdaTwoEvenMobiusPart d =
      -nativePNTLambdaTwoOddMobiusKernel (d / 2) := by
  classical
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  have hdouble : 2 * (d / 2) = d := Nat.two_mul_div_two_of_even hdeven
  have hhalfpos : 0 < d / 2 := by
    have hdgt : 1 < d := Nat.one_lt_of_ne_zero_of_even hdne hdeven
    omega
  unfold nativePNTLambdaTwoEvenMobiusPart nativePNTLambdaTwoOddMobiusKernel
  conv_lhs => rw [← Finset.sum_filter]
  rw [← Finset.sum_neg_distrib]
  symm
  refine Finset.sum_bij (fun r _ => 2 * r) ?_ ?_ ?_ ?_
  · intro r hr
    have hrd : r ∣ d / 2 := (Nat.mem_divisors.mp hr).1
    have h2rd : 2 * r ∣ d := by
      rcases hrd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← hdouble, ht]
      ring
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨h2rd, hdne⟩, even_two_mul r⟩
  · intro r₁ _hr₁ r₂ _hr₂ h
    change 2 * r₁ = 2 * r₂ at h
    omega
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmdMem, hmeven⟩
    have hmd : m ∣ d := (Nat.mem_divisors.mp hmdMem).1
    let r : ℕ := m / 2
    have hmrep : 2 * r = m := by
      dsimp [r]
      exact Nat.two_mul_div_two_of_even hmeven
    have hrd : r ∣ d / 2 := by
      rcases hmd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have hEq : 2 * (d / 2) = 2 * (r * t) := by
        rw [hdouble, ht, ← hmrep]
        ring
      omega
    refine ⟨r, Nat.mem_divisors.mpr ⟨hrd, Nat.ne_of_gt hhalfpos⟩, hmrep⟩
  · intro r _hr
    have hmu := nativePNTMobiusReal_two_mul r
    change
      -(if Odd r then
          (μ : ArithmeticFunction ℝ) r *
            (Real.log (((d / 2) / r : ℕ) : ℝ)) ^ 2
        else 0) =
        (μ : ArithmeticFunction ℝ) (2 * r) *
          (Real.log ((d / (2 * r) : ℕ) : ℝ)) ^ 2
    by_cases hodd : Odd r
    · rw [if_pos hodd]
      rw [if_pos hodd] at hmu
      rw [hmu]
      rw [Nat.div_div_eq_div_mul]
      ring
    · rw [if_neg hodd]
      rw [if_neg hodd] at hmu
      rw [hmu]
      simp

/-- Positive-even coefficient recurrence. -/
theorem nativeLambdaTwo_eq_oddKernel_sub_half_of_even
    (d : ℕ) (hdpos : 0 < d) (hdeven : Even d) :
    nativeLambdaTwo d =
      nativePNTLambdaTwoOddMobiusKernel d -
        nativePNTLambdaTwoOddMobiusKernel (d / 2) := by
  rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo]
  rw [nativeMobiusLogSquareDivisorFiber_eq_oddKernel_add_evenPart,
    nativePNTLambdaTwoEvenMobiusPart_eq_neg_half d hdpos hdeven]
  ring

/-- **Positive dyadic kernel.**  The odd-Mobius log-square kernel is
nonnegative at every product. -/
theorem nativePNTLambdaTwoOddMobiusKernel_nonneg (d : ℕ) :
    0 ≤ nativePNTLambdaTwoOddMobiusKernel d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hd0 : d = 0
      · subst d
        simp [nativePNTLambdaTwoOddMobiusKernel]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        by_cases hodd : Odd d
        · rw [nativePNTLambdaTwoOddMobiusKernel_eq_lambdaTwo_of_odd d hodd]
          exact nativeLambdaTwo_nonneg d (by omega)
        · have heven : Even d := Nat.not_odd_iff_even.mp hodd
          have hhalfLt : d / 2 < d := Nat.div_lt_self hdpos (by norm_num)
          have hhalf0 := ih (d / 2) hhalfLt
          have hrec := nativeLambdaTwo_eq_oddKernel_sub_half_of_even
            d hdpos heven
          have hlam0 := nativeLambdaTwo_nonneg d (by omega)
          linarith

/-! ## Exact dyadic decomposition of the signed Lambda_2 transform -/

/-- The signed `Lambda_2` error transform itself. -/
def nativeLambdaTwoSignedErrorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    nativeLambdaTwo d * nativePNTError (N / d)

/-- Uniform pointwise form of the parity recurrence on positive indices. -/
theorem nativeLambdaTwo_eq_oddKernel_sub_evenHalf
    (d : ℕ) (hd : 1 ≤ d) :
    nativeLambdaTwo d =
      nativePNTLambdaTwoOddMobiusKernel d -
        (if Even d then nativePNTLambdaTwoOddMobiusKernel (d / 2) else 0) := by
  by_cases heven : Even d
  · rw [if_pos heven]
    exact nativeLambdaTwo_eq_oddKernel_sub_half_of_even d (by omega) heven
  · have hodd : Odd d := Nat.not_even_iff_odd.mp heven
    rw [if_neg heven, sub_zero]
    exact (nativePNTLambdaTwoOddMobiusKernel_eq_lambdaTwo_of_odd d hodd).symm

/-- Signed error mass with the positive odd-Mobius coefficient before the even
correction is paired. -/
def nativePNTLambdaTwoOddKernelSignedErrorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    nativePNTLambdaTwoOddMobiusKernel d * nativePNTError (N / d)

/-- The even-index correction before reindexing by `n = 2d`. -/
def nativePNTLambdaTwoOddKernelEvenIndexCorrectionMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    if Even n then
      nativePNTLambdaTwoOddMobiusKernel (n / 2) * nativePNTError (N / n)
    else 0

/-- The same correction reindexed by its half-index. -/
def nativePNTLambdaTwoOddKernelDyadicChildMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / 2),
    nativePNTLambdaTwoOddMobiusKernel d * nativePNTError (N / (2 * d))

/-- Actual dyadic cross-endpoint cell mass over the complete lower half of the
positive odd-Mobius kernel. -/
def nativePNTLambdaTwoOddKernelDyadicCellMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / 2),
    nativePNTLambdaTwoOddMobiusKernel d *
      (nativePNTError (N / d) - nativePNTError (N / (2 * d)))

/-- Unpaired top boundary after every even coefficient has been matched to its
half-index. -/
def nativePNTLambdaTwoOddKernelTopBoundaryMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc (N / 2) N,
    nativePNTLambdaTwoOddMobiusKernel d * nativePNTError (N / d)

/-- Expanding each positive `Lambda_2` coefficient by parity gives the odd
kernel source mass minus the even-index correction, with all signs retained. -/
theorem nativeLambdaTwoSignedErrorMass_eq_oddKernel_sub_evenIndex
    (N : ℕ) :
    nativeLambdaTwoSignedErrorMass N =
      nativePNTLambdaTwoOddKernelSignedErrorMass N -
        nativePNTLambdaTwoOddKernelEvenIndexCorrectionMass N := by
  unfold nativeLambdaTwoSignedErrorMass
    nativePNTLambdaTwoOddKernelSignedErrorMass
    nativePNTLambdaTwoOddKernelEvenIndexCorrectionMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [nativeLambdaTwo_eq_oddKernel_sub_evenHalf n hn1]
  by_cases heven : Even n
  · simp only [if_pos heven]
    ring
  · simp only [if_neg heven]
    ring

/-- The even-index correction is exactly the dyadic child row after the
bijection `n = 2d`. -/
theorem nativePNTLambdaTwoOddKernelEvenIndexCorrectionMass_eq_child
    (N : ℕ) :
    nativePNTLambdaTwoOddKernelEvenIndexCorrectionMass N =
      nativePNTLambdaTwoOddKernelDyadicChildMass N := by
  classical
  unfold nativePNTLambdaTwoOddKernelEvenIndexCorrectionMass
    nativePNTLambdaTwoOddKernelDyadicChildMass
  conv_lhs => rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun d _ => 2 * d) ?_ ?_ ?_ ?_
  · intro d hd
    have hdI := Finset.mem_Icc.mp hd
    have hdpos : 0 < d :=
      lt_of_lt_of_le (by norm_num : 0 < 1) hdI.1
    have h2d1 : 1 ≤ 2 * d :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hdpos))
    have hdN2 : d * 2 ≤ N :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hdI.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨h2d1, by simpa [Nat.mul_comm] using hdN2⟩,
        even_two_mul d⟩
  · intro a _ha b _hb hab
    change 2 * a = 2 * b at hab
    omega
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hneven⟩
    have hnI' := Finset.mem_Icc.mp hnI
    let d : ℕ := n / 2
    have hrep : 2 * d = n := by
      dsimp [d]
      exact Nat.two_mul_div_two_of_even hneven
    have hd1 : 1 ≤ d := by
      by_contra hzero
      have hd0 : d = 0 := by omega
      rw [hd0] at hrep
      omega
    have hdN : d ≤ N / 2 := by
      dsimp [d]
      exact Nat.div_le_div_right hnI'.2
    exact ⟨d, Finset.mem_Icc.mpr ⟨hd1, hdN⟩, hrep⟩
  · intro d _hd
    have hhalf : (2 * d) / 2 = d :=
      Nat.mul_div_cancel_left d (by norm_num : 0 < 2)
    simp [hhalf]

/-- The odd-kernel source row splits exactly into the paired lower half and the
unpaired top boundary. -/
theorem nativePNTLambdaTwoOddKernelSignedErrorMass_eq_lower_add_boundary
    (N : ℕ) :
    nativePNTLambdaTwoOddKernelSignedErrorMass N =
      (∑ d ∈ Finset.Icc 1 (N / 2),
        nativePNTLambdaTwoOddMobiusKernel d * nativePNTError (N / d)) +
        nativePNTLambdaTwoOddKernelTopBoundaryMass N := by
  unfold nativePNTLambdaTwoOddKernelSignedErrorMass
    nativePNTLambdaTwoOddKernelTopBoundaryMass
  have hsets :
      Finset.Icc 1 N = Finset.Icc 1 (N / 2) ∪ Finset.Ioc (N / 2) N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 1 (N / 2)) (Finset.Ioc (N / 2) N) := by
    rw [Finset.disjoint_left]
    intro n hn htop
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Ioc] at htop
    omega
  rw [hsets, Finset.sum_union hdis]

/-- Pairing the complete lower half converts source minus child into the exact
dyadic cross-endpoint cell mass. -/
theorem nativePNTLambdaTwoOddKernel_lower_sub_child_eq_cell
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 (N / 2),
        nativePNTLambdaTwoOddMobiusKernel d * nativePNTError (N / d)) -
      nativePNTLambdaTwoOddKernelDyadicChildMass N =
        nativePNTLambdaTwoOddKernelDyadicCellMass N := by
  unfold nativePNTLambdaTwoOddKernelDyadicChildMass
    nativePNTLambdaTwoOddKernelDyadicCellMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  ring

/-- **Exact dyadic decomposition of the actual signed `Lambda_2` error
transform.**  The positive odd-Mobius cells own the full lower half of the
transform, with only the explicit top boundary left unpaired.  No absolute
value and no scalarized good-mass hypothesis appears. -/
theorem nativeLambdaTwoSignedErrorMass_eq_dyadicCells_add_boundary
    (N : ℕ) :
    nativeLambdaTwoSignedErrorMass N =
      nativePNTLambdaTwoOddKernelDyadicCellMass N +
        nativePNTLambdaTwoOddKernelTopBoundaryMass N := by
  rw [nativeLambdaTwoSignedErrorMass_eq_oddKernel_sub_evenIndex,
    nativePNTLambdaTwoOddKernelEvenIndexCorrectionMass_eq_child,
    nativePNTLambdaTwoOddKernelSignedErrorMass_eq_lower_add_boundary]
  have hcell := nativePNTLambdaTwoOddKernel_lower_sub_child_eq_cell N
  linarith

end RHLean.Analysis
