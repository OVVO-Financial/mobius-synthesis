import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy
import RHLean.Analysis.LargePrimeTTransport

/-!
# Extreme largest-prime support below a finite endpoint

This paper-facing square-block module isolates a simple consequence of the
canonical largest-prime factorization. If `m <= x` and the canonical largest
prime is already above `x / 2`, then the canonical cofactor must be one, so the
source is the prime itself. Consequently every composite source below `x` has
largest prime factor at most `floor (x / 2)`.

No estimate and no external block architecture is used here.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Proof

/-- If `m <= x` and twice its canonical largest prime is already above `x`,
then its canonical cofactor is one. -/
theorem canonicalCofactor_eq_one_of_endpoint_lt_two_mul_largestPrime
    {x m : ℕ} (hmgt : 1 < m) (hmx : m ≤ x)
    (hlarge : x < 2 * canonicalLargestPrimeFactor m) :
    canonicalCofactor m = 1 := by
  have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  have hc1 : 1 ≤ canonicalCofactor m := by
    by_contra hnot
    have hc0 : canonicalCofactor m = 0 := by omega
    have hprod0 := hprod
    rw [hc0] at hprod0
    simp at hprod0
    omega
  by_contra hne
  have hc2 : 2 ≤ canonicalCofactor m := by omega
  have htwo :
      2 * canonicalLargestPrimeFactor m ≤
        canonicalCofactor m * canonicalLargestPrimeFactor m :=
    Nat.mul_le_mul_right (canonicalLargestPrimeFactor m) hc2
  rw [hprod] at htwo
  omega

/-- Hence an extreme-largest-prime source is the prime itself. -/
theorem eq_largestPrimeFactor_of_endpoint_lt_two_mul_largestPrime
    {x m : ℕ} (hmgt : 1 < m) (hmx : m ≤ x)
    (hlarge : x < 2 * canonicalLargestPrimeFactor m) :
    m = canonicalLargestPrimeFactor m := by
  have hc :=
    canonicalCofactor_eq_one_of_endpoint_lt_two_mul_largestPrime
      hmgt hmx hlarge
  have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hprod.symm
    _ = canonicalLargestPrimeFactor m := by rw [hc]; simp

/-- Contrapositive form: any non-prime canonical source below `x` has largest
prime factor at most `x / 2`. For natural `x`, this is exactly the paper's
`floor (x/2)` support bound. -/
theorem canonicalLargestPrimeFactor_le_half_of_ne_largestPrime
    {x m : ℕ} (hmgt : 1 < m) (hmx : m ≤ x)
    (hne : m ≠ canonicalLargestPrimeFactor m) :
    canonicalLargestPrimeFactor m ≤ x / 2 := by
  have htwo : 2 * canonicalLargestPrimeFactor m ≤ x := by
    by_contra hnot
    have hlarge : x < 2 * canonicalLargestPrimeFactor m := by omega
    exact hne
      (eq_largestPrimeFactor_of_endpoint_lt_two_mul_largestPrime
        hmgt hmx hlarge)
  omega

/-- Every nontrivial canonical cofactor below `x` is also at most `x / 2`,
because its canonical prime factor is at least two. -/
theorem canonicalCofactor_le_half_of_le_endpoint
    {x m : ℕ} (hmgt : 1 < m) (hmx : m ≤ x) :
    canonicalCofactor m ≤ x / 2 := by
  have hq2 : 2 ≤ canonicalLargestPrimeFactor m :=
    (canonicalLargestPrimeFactor_prime hmgt).two_le
  have hmul :
      canonicalCofactor m * 2 ≤
        canonicalCofactor m * canonicalLargestPrimeFactor m :=
    Nat.mul_le_mul_left (canonicalCofactor m) hq2
  have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  have htwo : 2 * canonicalCofactor m ≤ x := by
    calc
      2 * canonicalCofactor m = canonicalCofactor m * 2 := by omega
      _ ≤ canonicalCofactor m * canonicalLargestPrimeFactor m := hmul
      _ = m := hprod
      _ ≤ x := hmx
  omega

/-- An actual canonical source in square block `j` whose largest prime lies above the
square-root cutoff `j + 1` automatically supplies native `LargePrimeTransportData`.
This is the first exact bridge from the square-block population to the large-prime
`T` transport layer. -/
theorem canonicalSquareBlock_largePrimeTransportData
    {j m : ℕ}
    (hm : m ∈ canonicalSquareBlock j)
    (hmgt : 1 < m)
    (hlarge : j + 1 < canonicalLargestPrimeFactor m) :
    LargePrimeTransportData (j + 1)
      (canonicalCofactor m) (canonicalLargestPrimeFactor m) := by
  have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  have hc1 : 1 ≤ canonicalCofactor m := by
    by_contra hnot
    have hc0 : canonicalCofactor m = 0 := by omega
    have hprod0 := hprod
    rw [hc0] at hprod0
    simp at hprod0
    omega
  have hmBlock : j ^ 2 ≤ m ∧ m < (j + 1) ^ 2 := by
    simpa [canonicalSquareBlock, Finset.mem_Ico] using hm
  have hcLt : canonicalCofactor m < j + 1 := by
    by_contra hnot
    have hcut : j + 1 ≤ canonicalCofactor m := by omega
    have hmul :
        (j + 1) * (j + 1) ≤
          canonicalCofactor m * canonicalLargestPrimeFactor m :=
      Nat.mul_le_mul hcut (Nat.le_of_lt hlarge)
    rw [hprod] at hmul
    have hsquare : (j + 1) * (j + 1) = (j + 1) ^ 2 := by ring
    rw [hsquare] at hmul
    omega
  exact
    { c_pos := hc1
      c_lt_cutoff := hcLt
      q_prime := canonicalLargestPrimeFactor_prime hmgt
      cutoff_lt_q := hlarge }

/-- The bridge immediately transfers the native large-prime Mobius sign law to the
actual canonical source in the square block. -/
theorem canonicalSquareBlock_largePrime_moebius_flip
    {j m : ℕ}
    (hm : m ∈ canonicalSquareBlock j)
    (hmgt : 1 < m)
    (hlarge : j + 1 < canonicalLargestPrimeFactor m) :
    (ArithmeticFunction.moebius m : ℤ) =
      -(ArithmeticFunction.moebius (canonicalCofactor m) : ℤ) := by
  have hdata :=
    canonicalSquareBlock_largePrimeTransportData hm hmgt hlarge
  calc
    (ArithmeticFunction.moebius m : ℤ) =
        (ArithmeticFunction.moebius
          (canonicalLargestPrimeFactor m * canonicalCofactor m) : ℤ) := by
      rw [mul_comm, canonicalCofactor_mul_largestPrimeFactor hmgt]
    _ = -(ArithmeticFunction.moebius (canonicalCofactor m) : ℤ) :=
      hdata.moebius_mul_eq_neg

end RHLean.Analysis
