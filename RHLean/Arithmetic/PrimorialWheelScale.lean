import Mathlib
import RHLean.Arithmetic.PrimeWheelFiniteSystem
import RHLean.Arithmetic.PrimesUpToFrontier

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Zero-indexed sequence of rational primes. -/
def wheelPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- The first `k` primes multiplied together; `primorialEndpoint 0 = 1`. -/
def primorialEndpoint (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, wheelPrime i

/-- The synchronized primorial block `(W_k,W_{k+1}]`. -/
def primorialBlockLower (k : ℕ) : ℕ := primorialEndpoint k

def primorialBlockUpper (k : ℕ) : ℕ := primorialEndpoint (k + 1)

/-- Square-root prime cutoff used for the block. -/
def primorialWheelCutoff (k : ℕ) : ℕ :=
  Nat.sqrt (primorialBlockUpper k)

/-- Every prime coordinate at most the square-root cutoff. -/
def primorialWheelPrimes (k : ℕ) : Finset ℕ :=
  primesUpTo (primorialWheelCutoff k)

/-- Complete square-sensitive period of the raw comb field. -/
def primorialSquareSensitiveModulus (k : ℕ) : ℕ :=
  ∏ p ∈ primorialWheelPrimes k, p ^ 2

/-- A common torus modulus: a positive multiple of the complete raw period and
strictly larger than the whole arithmetic block. -/
def primorialCommonTorusModulus (k : ℕ) : ℕ :=
  (primorialBlockUpper k + 1) * primorialSquareSensitiveModulus k

/-- Every indexed wheel prime is prime. -/
theorem wheelPrime_prime (k : ℕ) : Nat.Prime (wheelPrime k) := by
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k

@[simp] theorem primorialEndpoint_zero : primorialEndpoint 0 = 1 := by
  simp [primorialEndpoint]

/-- One-step primorial recursion. -/
theorem primorialEndpoint_succ (k : ℕ) :
    primorialEndpoint (k + 1) = primorialEndpoint k * wheelPrime k := by
  unfold primorialEndpoint
  rw [Finset.prod_range_succ]

/-- Every primorial endpoint is positive. -/
theorem primorialEndpoint_pos (k : ℕ) : 0 < primorialEndpoint k := by
  unfold primorialEndpoint
  apply Finset.prod_pos
  intro i hi
  exact (wheelPrime_prime i).pos

/-- Primorial endpoints strictly increase. -/
theorem primorialEndpoint_strictMono : StrictMono primorialEndpoint := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [primorialEndpoint_succ]
  have hW := primorialEndpoint_pos k
  have hp := (wheelPrime_prime k).two_le
  nlinarith

/-- The complete square-sensitive period is positive. -/
theorem primorialSquareSensitiveModulus_pos (k : ℕ) :
    0 < primorialSquareSensitiveModulus k := by
  unfold primorialSquareSensitiveModulus
  apply Finset.prod_pos
  intro p hp
  have hpPrime : Nat.Prime p := prime_of_mem_primesUpTo hp
  exact pow_pos hpPrime.pos 2

/-- The chosen common torus modulus is positive. -/
theorem primorialCommonTorusModulus_pos (k : ℕ) :
    0 < primorialCommonTorusModulus k := by
  unfold primorialCommonTorusModulus
  exact Nat.mul_pos (Nat.succ_pos _) (primorialSquareSensitiveModulus_pos k)

/-- The chosen common torus contains the entire arithmetic block without wrap. -/
theorem primorialBlockUpper_lt_commonTorusModulus (k : ℕ) :
    primorialBlockUpper k < primorialCommonTorusModulus k := by
  unfold primorialCommonTorusModulus
  have hQ : 1 ≤ primorialSquareSensitiveModulus k :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (primorialSquareSensitiveModulus_pos k))
  calc
    primorialBlockUpper k < primorialBlockUpper k + 1 := Nat.lt_succ_self _
    _ ≤ (primorialBlockUpper k + 1) * primorialSquareSensitiveModulus k := by
      simpa using Nat.mul_le_mul_left (primorialBlockUpper k + 1) hQ

/-- Concrete finite wheel system attached to the `k`th primorial block. -/
def primorialWheelSystem (k : ℕ) : PrimeWheelFiniteSystem where
  lower := primorialBlockLower k
  upper := primorialBlockUpper k
  modulus := primorialCommonTorusModulus k
  lower_lt_upper := primorialEndpoint_strictMono (Nat.lt_succ_self k)
  modulus_pos := primorialCommonTorusModulus_pos k
  upper_lt_modulus := primorialBlockUpper_lt_commonTorusModulus k
  primeCoordinates := primorialWheelPrimes k
  primeCoordinates_prime := by
    intro p hp
    exact prime_of_mem_primesUpTo hp

/-- Concrete primorial wheel family used by the harmonic criterion. -/
def primorialWheelFamily : ℕ → PrimeWheelFiniteSystem :=
  primorialWheelSystem

end RHLean.Arithmetic
