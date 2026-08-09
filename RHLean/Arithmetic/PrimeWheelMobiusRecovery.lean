import Mathlib
import RHLean.Arithmetic.PrimeWheelFiniteSystem
import RHLean.Arithmetic.PrimorialWheelScale
import RHLean.Arithmetic.PrimeFaceMoebius

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

lemma localPrimeComb_eq_ite_dvd_of_squarefree
    {p n : ℕ} (hp : Nat.Prime p) (hsq : Squarefree n) :
    localPrimeComb p n = if p ∣ n then -1 else 1 := by
  have hnot : ¬ p ^ 2 ∣ n := by
    simpa [pow_two] using (Nat.squarefree_iff_prime_squarefree.mp hsq p hp)
  simp [localPrimeComb, hnot]

lemma prod_localPrimeComb_eq_negOnePow_filter_card
    (S : Finset ℕ) (n : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsq : Squarefree n) :
    (∏ p ∈ S, localPrimeComb p n) =
      (-1 : ℤ) ^ (S.filter fun p => p ∣ n).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      have hpPrime : Nat.Prime p := hprime p (Finset.mem_insert_self p S)
      have hSPrime : ∀ q ∈ S, Nat.Prime q := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hpS]
      rw [localPrimeComb_eq_ite_dvd_of_squarefree hpPrime hsq]
      rw [ih hSPrime]
      by_cases hpn : p ∣ n
      · simp [Finset.filter_insert, hpn, hpS, pow_succ]
      · simp [Finset.filter_insert, hpn]

lemma seededPrimeComb_eq_neg_negOnePow_filter_card
    (S : Finset ℕ) (n : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsq : Squarefree n) :
    seededPrimeComb S n =
      -((-1 : ℤ) ^ (S.filter fun p => p ∣ n).card) := by
  rw [seededPrimeComb,
    prod_localPrimeComb_eq_negOnePow_filter_card S n hprime hsq]

lemma moebius_eq_negOnePow_primeFactors_card
    {n : ℕ} (hsq : Squarefree n) :
    μ n = (-1 : ℤ) ^ n.primeFactors.card := by
  have hprime : ∀ p ∈ n.primeFactors, Nat.Prime p := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  have h := moebius_primeFaceProduct_eq_booleanCubeSign n.primeFactors hprime
  unfold primeFaceProduct booleanCubeSign at h
  change μ (n.primeFactors.prod id) = (-1 : ℤ) ^ n.primeFactors.card at h
  have hprod : n.primeFactors.prod id = n := by
    simpa using Nat.prod_primeFactors_of_squarefree hsq
  calc
    μ n = μ (n.primeFactors.prod id) := by
      exact congrArg μ hprod.symm
    _ = (-1 : ℤ) ^ n.primeFactors.card := h

lemma filter_dvd_eq_primeFactors_inter
    (S : Finset ℕ) {n : ℕ} (hn0 : n ≠ 0)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    S.filter (fun p => p ∣ n) = n.primeFactors ∩ S := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hpS, hpdvd⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨hprime p hpS, hpdvd, hn0⟩, hpS⟩
  · rintro ⟨hpf, hpS⟩
    exact ⟨hpS, Nat.dvd_of_mem_primeFactors hpf⟩

lemma seededPrimeComb_eq_neg_moebius_of_smooth
    (S : Finset ℕ) {n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsmooth : IsPrimeWheelSmooth S n) :
    seededPrimeComb S n = -μ n := by
  classical
  have hsq := hsmooth.1
  have hn0 := hsq.ne_zero
  rw [seededPrimeComb_eq_neg_negOnePow_filter_card S n hprime hsq]
  rw [filter_dvd_eq_primeFactors_inter S hn0 hprime]
  have hinter : n.primeFactors ∩ S = n.primeFactors := by
    apply Finset.inter_eq_left.mpr
    exact hsmooth.2
  rw [hinter]
  rw [moebius_eq_negOnePow_primeFactors_card hsq]

/-- Prime-coordinate coverage through a square-root cutoff. -/
def PrimeWheelSqrtCoverage (S : Finset ℕ) (upper : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ≤ Nat.sqrt upper → p ∈ S

lemma large_primeFactors_card_le_one
    (S : Finset ℕ) {upper n : ℕ}
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hnpos : 0 < n) (hnupper : n ≤ upper) :
    (n.primeFactors \ S).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  have hpData := Finset.mem_sdiff.mp hp
  have hqData := Finset.mem_sdiff.mp hq
  have hpMem := Nat.mem_primeFactors.mp hpData.1
  have hqMem := Nat.mem_primeFactors.mp hqData.1
  by_contra hpq
  have hpLarge : Nat.sqrt upper < p := by
    by_contra hle
    exact hpData.2 (hcover p hpMem.1 (Nat.le_of_not_gt hle))
  have hqLarge : Nat.sqrt upper < q := by
    by_contra hle
    exact hqData.2 (hcover q hqMem.1 (Nat.le_of_not_gt hle))
  have hcop : p.Coprime q := by
    rw [hpMem.1.coprime_iff_not_dvd]
    intro hpdq
    exact hpq
      ((Nat.dvd_prime hqMem.1).mp hpdq |>.resolve_left hpMem.1.ne_one)
  have hpqdvd : p * q ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd hpMem.2.1 hqMem.2.1
  have hpqle : p * q ≤ n := Nat.le_of_dvd hnpos hpqdvd
  have hsqrtSq : (Nat.sqrt upper + 1) ^ 2 ≤ p * q := by
    nlinarith
  have hupperlt : upper < (Nat.sqrt upper + 1) ^ 2 :=
    Nat.lt_succ_sqrt' upper
  omega

lemma large_primeFactors_card_eq_one_of_not_smooth
    (S : Finset ℕ) {upper n : ℕ}
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hsq : Squarefree n) (hnupper : n ≤ upper)
    (hnonsmooth : ¬ IsPrimeWheelSmooth S n) :
    (n.primeFactors \ S).card = 1 := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hsq.ne_zero
  have hle := large_primeFactors_card_le_one S hcover hnpos hnupper
  have hne : (n.primeFactors \ S).Nonempty := by
    by_contra hempty
    have hsubset : n.primeFactors ⊆ S := by
      intro p hp
      by_contra hpS
      have hmem : p ∈ n.primeFactors \ S :=
        Finset.mem_sdiff.mpr ⟨hp, hpS⟩
      exact hempty ⟨p, hmem⟩
    exact hnonsmooth ⟨hsq, hsubset⟩
  have hone : 1 ≤ (n.primeFactors \ S).card :=
    Finset.one_le_card.mpr hne
  omega

lemma seededPrimeComb_eq_moebius_of_not_smooth
    (S : Finset ℕ) {upper n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hsq : Squarefree n) (hnupper : n ≤ upper)
    (hnonsmooth : ¬ IsPrimeWheelSmooth S n) :
    seededPrimeComb S n = μ n := by
  classical
  have hn0 := hsq.ne_zero
  rw [seededPrimeComb_eq_neg_negOnePow_filter_card S n hprime hsq]
  rw [filter_dvd_eq_primeFactors_inter S hn0 hprime]
  have hlarge := large_primeFactors_card_eq_one_of_not_smooth
    S hcover hsq hnupper hnonsmooth
  have hcard := Finset.card_sdiff_add_card_inter n.primeFactors S
  have htotal :
      n.primeFactors.card = (n.primeFactors ∩ S).card + 1 := by
    omega
  rw [moebius_eq_negOnePow_primeFactors_card hsq, htotal, pow_succ]
  ring

lemma seededPrimeComb_eq_zero_of_not_squarefree
    (S : Finset ℕ) {upper n : ℕ}
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (hnsq : ¬ Squarefree n) :
    seededPrimeComb S n = 0 := by
  classical
  rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push_neg at hnsq
  rcases hnsq with ⟨p, hpPrime, hpSq⟩
  have hpSqLeN : p * p ≤ n := Nat.le_of_dvd hnpos hpSq
  have hpLe : p ≤ Nat.sqrt upper :=
    Nat.le_sqrt.mpr (hpSqLeN.trans hnupper)
  have hpS : p ∈ S := hcover p hpPrime hpLe
  unfold seededPrimeComb
  have hlocal : localPrimeComb p n = 0 := by
    simp [localPrimeComb, pow_two, hpSq]
  rw [Finset.prod_eq_zero hpS hlocal]
  simp

lemma correctedPrimeWheelSite_eq_moebius
    (S : Finset ℕ) {upper n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hnpos : 0 < n) (hnupper : n ≤ upper) :
    correctedPrimeWheelSite S upper n = μ n := by
  by_cases hsq : Squarefree n
  · by_cases hsmooth : IsPrimeWheelSmooth S n
    · have hraw :=
        seededPrimeComb_eq_neg_moebius_of_smooth S hprime hsmooth
      simp [correctedPrimeWheelSite, primeWheelSmoothCoreSite, hnupper,
        hsmooth, hraw]
      ring
    · have hraw := seededPrimeComb_eq_moebius_of_not_smooth
        S hprime hcover hsq hnupper hsmooth
      simp [correctedPrimeWheelSite, primeWheelSmoothCoreSite, hnupper,
        hsmooth, hraw]
  · have hraw := seededPrimeComb_eq_zero_of_not_squarefree
      S hcover hnpos hnupper hsq
    have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    simp [correctedPrimeWheelSite, primeWheelSmoothCoreSite, hraw, hmu]

theorem primorialWheelSqrtCoverage (k : ℕ) :
    PrimeWheelSqrtCoverage (primorialWheelPrimes k)
      (primorialBlockUpper k) := by
  intro p hp hple
  exact mem_primesUpTo.mpr ⟨hp, hple⟩

/-- Exact pointwise Möbius recovery on every synchronized primorial block. -/
theorem primorialWheel_correctedSite_eq_moebius
    (k n : ℕ)
    (hlower : (primorialWheelSystem k).lower < n)
    (hupper : n ≤ (primorialWheelSystem k).upper) :
    (primorialWheelSystem k).correctedSite n = μ n := by
  unfold PrimeWheelFiniteSystem.correctedSite primorialWheelSystem
  apply correctedPrimeWheelSite_eq_moebius
  · intro p hp
    exact prime_of_mem_primesUpTo hp
  · exact primorialWheelSqrtCoverage k
  · exact Nat.zero_lt_of_lt hlower
  · exact hupper

/-- Canonical arithmetic certificate for the complete primorial wheel family. -/
def primorialWheelArithmeticCertificate (k : ℕ) :
    (primorialWheelSystem k).ArithmeticCertificate where
  corrected_eq_moebius := by
    intro n hlower hupper
    exact primorialWheel_correctedSite_eq_moebius k n hlower hupper

end RHLean.Arithmetic
