import Mathlib
import RHLean.Arithmetic.PrimorialWheelMinimalTorus
import RHLean.Arithmetic.PrimorialWheelScaleGrowth

/-!
# Elementary lower bound for the square-sensitive raw period

No prime-number theorem is needed to compare the natural raw period with the
arithmetic block.  Bertrand's postulate gives, for every `y >= 5`, a prime
`p` with `y/2 < p <= y`.  Since `2` and `p` are distinct members of the full
prime set up to `y`, their product already exceeds `y`.  Squaring then shows
that the complete square-sensitive period exceeds every endpoint whose square
root cutoff is at least five.

For synchronized primorial blocks this applies from index `k = 2` onward.  Thus
the minimal common torus introduced in `PrimorialWheelMinimalTorus` is exactly
the natural CRT period on every nontrivial analytic block after the first two
finite cases.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Product of all primes at most `y`. -/
def primeProductUpTo (y : ℕ) : ℕ :=
  ∏ p ∈ primesUpTo y, p

/-- Bertrand's postulate already forces the product of all primes up to `y` to
strictly exceed `y` for `y >= 5`. -/
theorem lt_primeProductUpTo
    (y : ℕ) (hy : 5 ≤ y) :
    y < primeProductUpTo y := by
  let n := y / 2
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  rcases Nat.bertrand n hn0 with ⟨p, hpPrime, hnp, hp2n⟩
  have hn2 : 2 ≤ n := by
    dsimp [n]
    omega
  have hpgt2 : 2 < p := lt_of_le_of_lt hn2 hnp
  have hpY : p ≤ y := by
    dsimp [n] at hp2n
    omega
  have h2mem : 2 ∈ primesUpTo y :=
    mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩
  have hpmem : p ∈ primesUpTo y :=
    mem_primesUpTo.mpr ⟨hpPrime, hpY⟩
  have hprod :
      2 * p ≤ ∏ q ∈ primesUpTo y, q := by
    exact Finset.mul_le_prod
      (fun q hq => (prime_of_mem_primesUpTo hq).one_le)
      h2mem hpmem (by omega)
  have hylt : y < 2 * p := by
    dsimp [n] at hnp
    omega
  exact hylt.trans_le hprod

/-- The square-sensitive period is the square of the product of its distinct
prime coordinates. -/
theorem primorialSquareSensitiveModulus_eq_primeProductUpTo_sq
    (k : ℕ) :
    primorialSquareSensitiveModulus k =
      (primeProductUpTo (primorialWheelCutoff k)) ^ 2 := by
  unfold primorialSquareSensitiveModulus primorialWheelPrimes
    primeProductUpTo
  exact Finset.prod_pow (primesUpTo (primorialWheelCutoff k)) 2 id

/-- If the square-root cutoff is at least five, the natural raw period already
lies strictly beyond the arithmetic endpoint. -/
theorem primorialBlockUpper_lt_squareSensitiveModulus_of_cutoff
    (k : ℕ) (hcut : 5 ≤ primorialWheelCutoff k) :
    primorialBlockUpper k < primorialSquareSensitiveModulus k := by
  have hprod := lt_primeProductUpTo (primorialWheelCutoff k) hcut
  have hprodSucc :
      primorialWheelCutoff k + 1 ≤
        primeProductUpTo (primorialWheelCutoff k) := by
    omega
  have hsqrt :
      primorialBlockUpper k < (primorialWheelCutoff k + 1) ^ 2 := by
    unfold primorialWheelCutoff
    exact Nat.lt_succ_sqrt' (primorialBlockUpper k)
  rw [primorialSquareSensitiveModulus_eq_primeProductUpTo_sq k]
  exact hsqrt.trans_le (Nat.pow_le_pow_left hprodSucc 2)

/-- The third indexed wheel prime is at least five.  This uses only its primality
and the elementary lower bound `wheelPrime k >= k+2`. -/
theorem five_le_wheelPrime_two : 5 ≤ wheelPrime 2 := by
  have h4 : 4 ≤ wheelPrime 2 := wheelPrime_add_two_le 2
  have hne : wheelPrime 2 ≠ 4 := by
    intro h
    have hp := wheelPrime_prime 2
    rw [h] at hp
    norm_num at hp
  omega

/-- The first three indexed primes already give endpoint at least thirty. -/
theorem thirty_le_primorialEndpoint_three : 30 ≤ primorialEndpoint 3 := by
  have hE2 : 6 ≤ primorialEndpoint 2 := by
    rw [show (2 : ℕ) = 1 + 1 by omega, primorialEndpoint_succ,
      show (1 : ℕ) = 0 + 1 by omega, primorialEndpoint_succ,
      primorialEndpoint_zero]
    have hp0 : 2 ≤ wheelPrime 0 := wheelPrime_add_two_le 0
    have hp1 : 3 ≤ wheelPrime 1 := wheelPrime_add_two_le 1
    nlinarith
  calc
    30 = 6 * 5 := by norm_num
    _ ≤ primorialEndpoint 2 * wheelPrime 2 :=
      Nat.mul_le_mul hE2 five_le_wheelPrime_two
    _ = primorialEndpoint 3 := (primorialEndpoint_succ 2).symm

/-- Every synchronized block from `k=2` onward has right endpoint at least 30. -/
theorem thirty_le_primorialBlockUpper
    {k : ℕ} (hk : 2 ≤ k) :
    30 ≤ primorialBlockUpper k := by
  have hidx : 3 ≤ k + 1 := by omega
  calc
    30 ≤ primorialEndpoint 3 := thirty_le_primorialEndpoint_three
    _ ≤ primorialEndpoint (k + 1) :=
      primorialEndpoint_strictMono.monotone hidx
    _ = primorialBlockUpper k := rfl

/-- Consequently the square-root prime cutoff is at least five from block
`k=2` onward. -/
theorem five_le_primorialWheelCutoff
    {k : ℕ} (hk : 2 ≤ k) :
    5 ≤ primorialWheelCutoff k := by
  unfold primorialWheelCutoff
  apply Nat.le_sqrt.mpr
  have hU := thirty_le_primorialBlockUpper hk
  omega

/-- From block `k=2` onward, the complete square-sensitive raw period already
contains the entire arithmetic block without wrap. -/
theorem primorialBlockUpper_lt_squareSensitiveModulus
    {k : ℕ} (hk : 2 ≤ k) :
    primorialBlockUpper k < primorialSquareSensitiveModulus k := by
  exact primorialBlockUpper_lt_squareSensitiveModulus_of_cutoff
    k (five_le_primorialWheelCutoff hk)

/-- Hence the minimal lift multiplier is exactly one on every block `k>=2`. -/
theorem primorialMinimalLiftMultiplier_eq_one
    {k : ℕ} (hk : 2 ≤ k) :
    primorialMinimalLiftMultiplier k = 1 := by
  unfold primorialMinimalLiftMultiplier
  rw [Nat.div_eq_of_lt (primorialBlockUpper_lt_squareSensitiveModulus hk)]

/-- The minimal common torus is exactly the natural raw CRT period on every
block `k>=2`. -/
theorem primorialMinimalTorusModulus_eq_squareSensitiveModulus
    {k : ℕ} (hk : 2 ≤ k) :
    primorialMinimalTorusModulus k = primorialSquareSensitiveModulus k := by
  unfold primorialMinimalTorusModulus
  rw [primorialMinimalLiftMultiplier_eq_one hk]
  simp

end RHLean.Arithmetic
