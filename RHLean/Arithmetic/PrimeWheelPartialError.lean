import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery
import RHLean.Arithmetic.PrimesUpToFrontier

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- The prime-factorization part of `n` supported on primes at most `y`. -/
def primeWheelResolvedFactorization (y n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p : ℕ => p ≤ y) n.factorization

/-- The complementary prime-factorization part, supported on primes above `y`. -/
def primeWheelUnresolvedFactorization (y n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p : ℕ => ¬ p ≤ y) n.factorization

/-- The canonical `y`-resolved factor of `n`, with multiplicities retained. -/
def primeWheelResolvedPart (y n : ℕ) : ℕ :=
  (primeWheelResolvedFactorization y n).prod (fun p e => p ^ e)

/-- The canonical `y`-unresolved factor of `n`, with multiplicities retained. -/
def primeWheelUnresolvedPart (y n : ℕ) : ℕ :=
  (primeWheelUnresolvedFactorization y n).prod (fun p e => p ^ e)

/-- The partially completed corrected wheel through prime cutoff `y`. -/
def partialPrimeWheelSite (y upper n : ℕ) : ℤ :=
  correctedPrimeWheelSite (primesUpTo y) upper n

lemma primeWheelResolvedFactorization_support_prime (y n : ℕ) :
    ∀ p ∈ (primeWheelResolvedFactorization y n).support, Nat.Prime p := by
  intro p hp
  have hpN : p ∈ n.factorization.support := by
    rw [primeWheelResolvedFactorization, Finsupp.support_filter] at hp
    exact (Finset.mem_filter.mp hp).1
  rw [Nat.support_factorization] at hpN
  exact Nat.prime_of_mem_primeFactors hpN

lemma primeWheelUnresolvedFactorization_support_prime (y n : ℕ) :
    ∀ p ∈ (primeWheelUnresolvedFactorization y n).support, Nat.Prime p := by
  intro p hp
  have hpN : p ∈ n.factorization.support := by
    rw [primeWheelUnresolvedFactorization, Finsupp.support_filter] at hp
    exact (Finset.mem_filter.mp hp).1
  rw [Nat.support_factorization] at hpN
  exact Nat.prime_of_mem_primeFactors hpN

@[simp] theorem primeWheelResolvedPart_factorization (y n : ℕ) :
    (primeWheelResolvedPart y n).factorization =
      primeWheelResolvedFactorization y n := by
  unfold primeWheelResolvedPart
  exact Nat.prod_pow_factorization_eq_self
    (primeWheelResolvedFactorization_support_prime y n)

@[simp] theorem primeWheelUnresolvedPart_factorization (y n : ℕ) :
    (primeWheelUnresolvedPart y n).factorization =
      primeWheelUnresolvedFactorization y n := by
  unfold primeWheelUnresolvedPart
  exact Nat.prod_pow_factorization_eq_self
    (primeWheelUnresolvedFactorization_support_prime y n)

lemma primeWheelResolvedPart_ne_zero (y n : ℕ) :
    primeWheelResolvedPart y n ≠ 0 := by
  unfold primeWheelResolvedPart
  rw [Finsupp.prod_ne_zero_iff]
  intro p hp
  apply pow_ne_zero
  exact (primeWheelResolvedFactorization_support_prime y n p hp).ne_zero

lemma primeWheelUnresolvedPart_ne_zero (y n : ℕ) :
    primeWheelUnresolvedPart y n ≠ 0 := by
  unfold primeWheelUnresolvedPart
  rw [Finsupp.prod_ne_zero_iff]
  intro p hp
  apply pow_ne_zero
  exact (primeWheelUnresolvedFactorization_support_prime y n p hp).ne_zero

/-- The resolved and unresolved factors multiply back to `n`. -/
theorem primeWheelResolvedPart_mul_unresolvedPart
    (y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    primeWheelResolvedPart y n * primeWheelUnresolvedPart y n = n := by
  unfold primeWheelResolvedPart primeWheelUnresolvedPart
    primeWheelResolvedFactorization primeWheelUnresolvedFactorization
  calc
    (Finsupp.filter (fun p : ℕ => p ≤ y) n.factorization).prod
          (fun p e => p ^ e) *
        (Finsupp.filter (fun p : ℕ => ¬ p ≤ y) n.factorization).prod
          (fun p e => p ^ e) =
      n.factorization.prod (fun p e => p ^ e) := by
        exact Finsupp.prod_filter_mul_prod_filter_not
          (fun p : ℕ => p ≤ y) n.factorization (fun p e => p ^ e)
    _ = n := Nat.factorization_prod_pow_eq_self hn

lemma primeWheelResolvedPart_primeFactor_le
    {y n p : ℕ} (hp : p ∈ (primeWheelResolvedPart y n).primeFactors) :
    p ≤ y := by
  have hpSupport : p ∈ (primeWheelResolvedFactorization y n).support := by
    rw [← primeWheelResolvedPart_factorization, Nat.support_factorization]
    exact hp
  have hpNe : primeWheelResolvedFactorization y n p ≠ 0 :=
    Finsupp.mem_support_iff.mp hpSupport
  rw [primeWheelResolvedFactorization, Finsupp.filter_apply] at hpNe
  by_contra hpLe
  simp [hpLe] at hpNe

lemma primeWheelUnresolvedPart_primeFactor_gt
    {y n p : ℕ} (hp : p ∈ (primeWheelUnresolvedPart y n).primeFactors) :
    y < p := by
  have hpSupport : p ∈ (primeWheelUnresolvedFactorization y n).support := by
    rw [← primeWheelUnresolvedPart_factorization, Nat.support_factorization]
    exact hp
  have hpNe : primeWheelUnresolvedFactorization y n p ≠ 0 :=
    Finsupp.mem_support_iff.mp hpSupport
  rw [primeWheelUnresolvedFactorization, Finsupp.filter_apply] at hpNe
  by_contra hpGt
  have hpLe : p ≤ y := Nat.le_of_not_gt hpGt
  simp [hpLe] at hpNe

/-- The canonical cutoff factors are coprime because their prime supports are disjoint. -/
theorem primeWheelResolvedPart_coprime_unresolvedPart (y n : ℕ) :
    (primeWheelResolvedPart y n).Coprime (primeWheelUnresolvedPart y n) := by
  rw [← Nat.disjoint_primeFactors
    (primeWheelResolvedPart_ne_zero y n)
    (primeWheelUnresolvedPart_ne_zero y n)]
  rw [Finset.disjoint_left]
  intro p hpA hpB
  exact (Nat.not_lt_of_ge (primeWheelResolvedPart_primeFactor_le hpA))
    (primeWheelUnresolvedPart_primeFactor_gt hpB)

lemma primeWheelResolvedPart_isSmooth (y n : ℕ) :
    IsPrimeWheelSmooth (primesUpTo y) (primeWheelResolvedPart y n) ↔
      Squarefree (primeWheelResolvedPart y n) := by
  constructor
  · exact fun h => h.1
  · intro hsq
    refine ⟨hsq, ?_⟩
    intro p hp
    exact mem_primesUpTo.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, primeWheelResolvedPart_primeFactor_le hp⟩

lemma localPrimeComb_resolvedPart
    {y n p : ℕ} (hn : n ≠ 0) (hp : p ∈ primesUpTo y) :
    localPrimeComb p n = localPrimeComb p (primeWheelResolvedPart y n) := by
  have hpPrime : Nat.Prime p := prime_of_mem_primesUpTo hp
  have hpLe : p ≤ y := (mem_primesUpTo.mp hp).2
  have hfac :
      (primeWheelResolvedPart y n).factorization p = n.factorization p := by
    rw [primeWheelResolvedPart_factorization, primeWheelResolvedFactorization,
      Finsupp.filter_apply, if_pos hpLe]
  have ha0 := primeWheelResolvedPart_ne_zero y n
  have hsq : p ^ 2 ∣ n ↔ p ^ 2 ∣ primeWheelResolvedPart y n := by
    rw [hpPrime.pow_dvd_iff_le_factorization hn,
      hpPrime.pow_dvd_iff_le_factorization ha0, hfac]
  have hdvd : p ∣ n ↔ p ∣ primeWheelResolvedPart y n := by
    rw [hpPrime.dvd_iff_one_le_factorization hn,
      hpPrime.dvd_iff_one_le_factorization ha0, hfac]
  unfold localPrimeComb
  by_cases h2 : p ^ 2 ∣ n
  · have h2a := hsq.mp h2
    simp [h2, h2a]
  · have h2a : ¬ p ^ 2 ∣ primeWheelResolvedPart y n := by
      exact fun h => h2 (hsq.mpr h)
    by_cases h1 : p ∣ n
    · have h1a := hdvd.mp h1
      simp [h2, h2a, h1, h1a]
    · have h1a : ¬ p ∣ primeWheelResolvedPart y n := by
        exact fun h => h1 (hdvd.mpr h)
      simp [h2, h2a, h1, h1a]

/-- The partial raw comb sees exactly the resolved factor of `n`. -/
theorem seededPrimeComb_primesUpTo_eq_neg_moebius_resolvedPart
    (y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    seededPrimeComb (primesUpTo y) n = -μ (primeWheelResolvedPart y n) := by
  have hraw :
      seededPrimeComb (primesUpTo y) n =
        seededPrimeComb (primesUpTo y) (primeWheelResolvedPart y n) := by
    unfold seededPrimeComb
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    exact localPrimeComb_resolvedPart hn hp
  rw [hraw]
  by_cases hsq : Squarefree (primeWheelResolvedPart y n)
  · exact seededPrimeComb_eq_neg_moebius_of_smooth
      (primesUpTo y)
      (fun p hp => prime_of_mem_primesUpTo hp)
      ((primeWheelResolvedPart_isSmooth y n).2 hsq)
  · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push_neg at hsq
    rcases hsq with ⟨p, hpPrime, hpSq⟩
    have hpDvd : p ∣ primeWheelResolvedPart y n :=
      dvd_trans (dvd_mul_right p p) hpSq
    have hpPF : p ∈ (primeWheelResolvedPart y n).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpDvd, primeWheelResolvedPart_ne_zero y n⟩
    have hpLe : p ≤ y := primeWheelResolvedPart_primeFactor_le hpPF
    have hpS : p ∈ primesUpTo y := mem_primesUpTo.mpr ⟨hpPrime, hpLe⟩
    have hlocal : localPrimeComb p (primeWheelResolvedPart y n) = 0 := by
      simp [localPrimeComb, pow_two, hpSq]
    unfold seededPrimeComb
    rw [Finset.prod_eq_zero hpS hlocal]
    simp [hmu]

lemma unresolvedPart_eq_one_iff_all_primeFactors_le
    (y : ℕ) {n : ℕ} :
    primeWheelUnresolvedPart y n = 1 ↔
      ∀ p ∈ n.primeFactors, p ≤ y := by
  constructor
  · intro hb p hp
    have hpNe : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hp
    by_contra hpLe
    have hfac :
        (primeWheelUnresolvedPart y n).factorization p = n.factorization p := by
      rw [primeWheelUnresolvedPart_factorization, primeWheelUnresolvedFactorization,
        Finsupp.filter_apply, if_pos hpLe]
    rw [hb, Nat.factorization_one] at hfac
    simp at hfac
    exact hpNe hfac.symm
  · intro hall
    have hfzero : primeWheelUnresolvedFactorization y n = 0 := by
      ext p
      rw [primeWheelUnresolvedFactorization, Finsupp.filter_apply]
      by_cases hpLe : p ≤ y
      · simp [hpLe]
      · have hpNot : p ∉ n.primeFactors := by
          intro hp
          exact hpLe (hall p hp)
        have hpFac : n.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
          exact hpNot
        simp [hpLe, hpFac]
    have hbFac : (primeWheelUnresolvedPart y n).factorization = 0 := by
      rw [primeWheelUnresolvedPart_factorization, hfzero]
    rcases (Nat.factorization_eq_zero_iff' (primeWheelUnresolvedPart y n)).mp hbFac with
      hb0 | hb1
    · exact False.elim ((primeWheelUnresolvedPart_ne_zero y n) hb0)
    · exact hb1

lemma not_smooth_of_unresolvedPart_ne_one
    (y : ℕ) {n : ℕ}
    (hb : primeWheelUnresolvedPart y n ≠ 1) :
    ¬ IsPrimeWheelSmooth (primesUpTo y) n := by
  intro hsmooth
  apply hb
  exact (unresolvedPart_eq_one_iff_all_primeFactors_le y).2 fun p hp =>
    (mem_primesUpTo.mp (hsmooth.2 p hp)).2

/-- Exact pointwise error formula for a partial prime wheel.

Writing `n = a_y(n) b_y(n)` with `a_y` carrying all prime powers at most `y`
and `b_y` all prime powers above `y`, the partial corrected field is already
exact when `b_y = 1`. Otherwise the smooth correction is absent, the raw field
is `-μ(a_y)`, and the error is `μ(a_y) (1 + μ(b_y))`. -/
theorem partialPrimeWheel_error_eq
    (y upper : ℕ) {n : ℕ}
    (hnpos : 0 < n) (hnupper : n ≤ upper) :
    μ n - partialPrimeWheelSite y upper n =
      if primeWheelUnresolvedPart y n = 1 then 0
      else μ (primeWheelResolvedPart y n) *
        (1 + μ (primeWheelUnresolvedPart y n)) := by
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hab := primeWheelResolvedPart_mul_unresolvedPart y hn
  have hcop := primeWheelResolvedPart_coprime_unresolvedPart y n
  have hmu :
      μ n = μ (primeWheelResolvedPart y n) * μ (primeWheelUnresolvedPart y n) := by
    calc
      μ n = μ (primeWheelResolvedPart y n * primeWheelUnresolvedPart y n) := by
        rw [hab]
      _ = μ (primeWheelResolvedPart y n) * μ (primeWheelUnresolvedPart y n) :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hraw := seededPrimeComb_primesUpTo_eq_neg_moebius_resolvedPart y hn
  by_cases hb : primeWheelUnresolvedPart y n = 1
  · have ha : primeWheelResolvedPart y n = n := by
      simpa [hb] using hab
    have hnSmooth : ∀ p ∈ n.primeFactors, p ≤ y :=
      (unresolvedPart_eq_one_iff_all_primeFactors_le y).1 hb
    have hcorrect : partialPrimeWheelSite y upper n = μ n := by
      unfold partialPrimeWheelSite
      by_cases hsq : Squarefree n
      · have hsmooth : IsPrimeWheelSmooth (primesUpTo y) n := by
          refine ⟨hsq, ?_⟩
          intro p hp
          exact mem_primesUpTo.mpr ⟨Nat.prime_of_mem_primeFactors hp, hnSmooth p hp⟩
        have hrawN : seededPrimeComb (primesUpTo y) n = -μ n := by
          simpa [ha] using hraw
        simp [correctedPrimeWheelSite, primeWheelSmoothCoreSite,
          hnupper, hsmooth, hrawN]
        ring
      · have hnonsmooth : ¬ IsPrimeWheelSmooth (primesUpTo y) n :=
          fun h => hsq h.1
        have hmu0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        have hrawN : seededPrimeComb (primesUpTo y) n = 0 := by
          simpa [ha, hmu0] using hraw
        simp [correctedPrimeWheelSite, primeWheelSmoothCoreSite,
          hnupper, hnonsmooth, hrawN, hmu0]
    simp [hb, hcorrect]
  · have hnonsmooth : ¬ IsPrimeWheelSmooth (primesUpTo y) n :=
      not_smooth_of_unresolvedPart_ne_one y hb
    have hpartial :
        partialPrimeWheelSite y upper n = -μ (primeWheelResolvedPart y n) := by
      unfold partialPrimeWheelSite correctedPrimeWheelSite primeWheelSmoothCoreSite
      simp [hnupper, hnonsmooth, hraw]
    rw [hmu, hpartial]
    simp [hb]
    ring

end RHLean.Arithmetic
