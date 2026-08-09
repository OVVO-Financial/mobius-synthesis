import Mathlib
import RHLean.Arithmetic.PrimeFaceProductUniqueness

noncomputable section

namespace RHLean.Arithmetic

/-- The canonical face attached to a natural number is its finite set of prime divisors. -/
def squarefreePrimeFace (n : ℕ) : Finset ℕ :=
  n.primeFactors

/-- A squarefree natural number is the product of its canonical prime face. -/
theorem primeFaceProduct_squarefreePrimeFace
    {n : ℕ} (hn : Squarefree n) :
    primeFaceProduct (squarefreePrimeFace n) = n := by
  simpa [squarefreePrimeFace, primeFaceProduct] using
    Nat.prod_primeFactors_of_squarefree hn

/-- For `n ≤ X`, every coordinate in the canonical squarefree face lies in the
ambient set of primes up to `X`. -/
theorem squarefreePrimeFace_subset_primesUpTo
    {X n : ℕ} (hn : Squarefree n) (hnX : n ≤ X) :
    squarefreePrimeFace n ⊆ primesUpTo X := by
  intro p hp
  have hpData := Nat.mem_primeFactors.mp hp
  have hpPrime : Nat.Prime p := hpData.1
  have hpDvd : p ∣ n := hpData.2.1
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have hpLeN : p ≤ n := Nat.le_of_dvd hnPos hpDvd
  exact mem_primesUpTo.mpr ⟨hpPrime, hpLeN.trans hnX⟩

/-- The canonical face of every squarefree `n ≤ X` is admissible in the full
prime ambient set and represents exactly `n`. -/
theorem squarefreePrimeFace_admissible
    {X n : ℕ} (hn : Squarefree n) (hnX : n ≤ X) :
    primeProductAdmissible (primesUpTo X) X (squarefreePrimeFace n) := by
  constructor
  · exact squarefreePrimeFace_subset_primesUpTo hn hnX
  · rw [primeFaceProduct_squarefreePrimeFace hn]
    exact hnX

/-- Every squarefree integer at most `X` has a unique admissible prime-face
representation. -/
theorem existsUnique_admissiblePrimeFace_of_squarefree
    {X n : ℕ} (hn : Squarefree n) (hnX : n ≤ X) :
    ∃! t : Finset ℕ,
      primeProductAdmissible (primesUpTo X) X t ∧
        primeFaceProduct t = n := by
  refine ⟨squarefreePrimeFace n, ?_, ?_⟩
  · exact ⟨squarefreePrimeFace_admissible hn hnX,
      primeFaceProduct_squarefreePrimeFace hn⟩
  · intro t ht
    apply primeFaceProduct_injective_on_admissible_primesUpTo ht.1
      (squarefreePrimeFace_admissible hn hnX)
    rw [ht.2, primeFaceProduct_squarefreePrimeFace hn]

end RHLean.Arithmetic
