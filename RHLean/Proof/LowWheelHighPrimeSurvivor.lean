import Mathlib
import RHLean.Proof.PrimeSieveSquareRootTransport
import RHLean.Analysis.SquareRootTransportRealization

/-!
# High-prime frequencies as low-wheel survivor counts

At the complete square endpoint `X = R^2 - 1`, every composite integer
`q <= X` has a prime divisor strictly below `R`.  Therefore, on the high
interval `R < q <= X`, primality is exactly survival under divisibility by all
primes already present in the low wheel through `R`.

This module records that pointwise equivalence and pushes it directly into the
cofactor-first square-root transport mass.  The upper-prime multiplicity in each
cofactor fibre is thereby rewritten as a finite low-wheel survivor count before
any norm or absolute value is introduced.

No prime-number theorem, density estimate, Strong Mertens input, or analytic
asymptotic appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- A high integer survives the complete low-prime divisibility wheel through
`R` when no prime coordinate at most `R` divides it. -/
def lowWheelHighSurvivor (R q : ℕ) : Prop :=
  ∀ p ∈ primesUpTo R, ¬ p ∣ q

/-- Finite survivor population in the interval `(R,B]`. -/
def lowWheelHighSurvivorSet (R B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc R B).filter (lowWheelHighSurvivor R)

/-- **High prime = low-wheel survivor.**  Below the complete square endpoint,
a composite high integer has least prime factor below `R`; conversely a prime
above `R` is untouched by every low-prime divisibility coordinate. -/
theorem lowWheelHighSurvivor_iff_prime
    {R q : ℕ} (hR : 2 ≤ R) (hRq : R < q)
    (hqX : q ≤ squareRootEndpoint R) :
    lowWheelHighSurvivor R q ↔ q.Prime := by
  constructor
  · intro hsurv
    by_contra hqPrime
    have hqpos : 0 < q := by omega
    have hq1 : q ≠ 1 := by omega
    let p := q.minFac
    have hpPrime : p.Prime := by
      simpa [p] using Nat.minFac_prime hq1
    have hpDvd : p ∣ q := by
      simpa [p] using Nat.minFac_dvd q
    have hpSqLe : p ^ 2 ≤ q := by
      simpa [p] using Nat.minFac_sq_le_self hqpos hqPrime
    have hqLtSq : q < R ^ 2 := by
      unfold squareRootEndpoint at hqX
      have hsqpos : 0 < R ^ 2 := by positivity
      omega
    have hpLtR : p < R := by
      by_contra hnot
      have hRp : R ≤ p := Nat.le_of_not_gt hnot
      have hpow : R ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hRp 2
      omega
    have hpMem : p ∈ primesUpTo R :=
      mem_primesUpTo.mpr ⟨hpPrime, hpLtR.le⟩
    exact hsurv p hpMem hpDvd
  · intro hqPrime p hpMem hpDvd
    have hpPrime : p.Prime := prime_of_mem_primesUpTo hpMem
    have hpR : p ≤ R := (mem_primesUpTo.mp hpMem).2
    have hpq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpDvd
    omega

/-- On every truncated high interval inside the square endpoint, the low-wheel
survivor set is literally the prime set. -/
theorem lowWheelHighSurvivorSet_eq_primeFilter
    (R B : ℕ) (hR : 2 ≤ R) (hB : B ≤ squareRootEndpoint R) :
    lowWheelHighSurvivorSet R B =
      (Finset.Ioc R B).filter Nat.Prime := by
  classical
  ext q
  simp only [lowWheelHighSurvivorSet, Finset.mem_filter]
  constructor
  · rintro ⟨hqI, hsurv⟩
    have hqX : q ≤ squareRootEndpoint R :=
      (Finset.mem_Ioc.mp hqI).2.trans hB
    exact ⟨hqI,
      (lowWheelHighSurvivor_iff_prime hR (Finset.mem_Ioc.mp hqI).1 hqX).mp hsurv⟩
  · rintro ⟨hqI, hprime⟩
    have hqX : q ≤ squareRootEndpoint R :=
      (Finset.mem_Ioc.mp hqI).2.trans hB
    exact ⟨hqI,
      (lowWheelHighSurvivor_iff_prime hR (Finset.mem_Ioc.mp hqI).1 hqX).mpr hprime⟩

/-- Prime transport fibre attached to one low cofactor. -/
def squareRootHighPrimeCofactorSet (R c : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun q =>
    q.Prime ∧ c * q ≤ squareRootEndpoint R

/-- The high-prime fibre of a positive cofactor is exactly the low-wheel
survivor interval up to the reciprocal cutoff `floor(X/c)`. -/
theorem squareRootHighPrimeCofactorSet_eq_lowWheelHighSurvivorSet
    {R c : ℕ} (hR : 2 ≤ R) (hc : c ∈ Finset.Ico 1 R) :
    squareRootHighPrimeCofactorSet R c =
      lowWheelHighSurvivorSet R (squareRootEndpoint R / c) := by
  classical
  have hcpos : 0 < c := by
    have hc1 := (Finset.mem_Ico.mp hc).1
    omega
  ext q
  simp only [squareRootHighPrimeCofactorSet, Finset.mem_filter,
    lowWheelHighSurvivorSet]
  constructor
  · rintro ⟨hqI, hprime, hmul⟩
    have hqDiv : q ≤ squareRootEndpoint R / c := by
      apply (Nat.le_div_iff_mul_le hcpos).2
      simpa [Nat.mul_comm] using hmul
    have hqSurv : lowWheelHighSurvivor R q :=
      (lowWheelHighSurvivor_iff_prime hR
        (Finset.mem_Ioc.mp hqI).1 (Finset.mem_Ioc.mp hqI).2).2 hprime
    exact ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hqI).1, hqDiv⟩, hqSurv⟩
  · rintro ⟨hqI, hsurv⟩
    have hdivX : squareRootEndpoint R / c ≤ squareRootEndpoint R :=
      Nat.div_le_self _ _
    have hqX : q ≤ squareRootEndpoint R :=
      (Finset.mem_Ioc.mp hqI).2.trans hdivX
    have hprime : q.Prime :=
      (lowWheelHighSurvivor_iff_prime hR (Finset.mem_Ioc.mp hqI).1 hqX).1 hsurv
    have hmul : c * q ≤ squareRootEndpoint R := by
      have hqc : q * c ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le hcpos).1 (Finset.mem_Ioc.mp hqI).2
      simpa [Nat.mul_comm] using hqc
    exact ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hqI).1, hqX⟩,
      hprime, hmul⟩

/-- Number of high primes available to the low cofactor `c`, expressed purely
as a low-wheel survivor count. -/
def lowWheelHighPrimeMultiplicity (R c : ℕ) : ℕ :=
  (lowWheelHighSurvivorSet R (squareRootEndpoint R / c)).card

/-- Cofactor-first transport with the high-prime frequency replaced by the
exact finite low-wheel survivor multiplicity. -/
def squareRootTransportLowWheelFrequency (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    (lowWheelHighPrimeMultiplicity R c : ℂ) * canonicalMoebiusWeight c

/-- **Transport frequency realization.**  Every upper-prime multiplicity in
`squareRootTransportCofactorFirst` is exactly a survivor count of the low wheel.
Thus the apparently external high-prime frequency is generated by the same
finite prime coordinates that determine the low Möbius alphabet. -/
theorem squareRootTransportCofactorFirst_eq_lowWheelFrequency
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      squareRootTransportLowWheelFrequency R := by
  classical
  unfold squareRootTransportCofactorFirst squareRootTransportLowWheelFrequency
  apply Finset.sum_congr rfl
  intro c hc
  have hset :=
    squareRootHighPrimeCofactorSet_eq_lowWheelHighSurvivorSet hR hc
  calc
    (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if q.Prime ∧ c * q ≤ squareRootEndpoint R then
          canonicalMoebiusWeight c
        else 0) =
      ∑ q ∈ squareRootHighPrimeCofactorSet R c,
        canonicalMoebiusWeight c := by
          unfold squareRootHighPrimeCofactorSet
          rw [Finset.sum_filter]
    _ = ∑ q ∈ lowWheelHighSurvivorSet R (squareRootEndpoint R / c),
        canonicalMoebiusWeight c := by rw [hset]
    _ = (lowWheelHighPrimeMultiplicity R c : ℂ) *
        canonicalMoebiusWeight c := by
          simp [lowWheelHighPrimeMultiplicity]

end RHLean.Proof
