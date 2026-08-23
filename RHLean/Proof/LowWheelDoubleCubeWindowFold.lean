import Mathlib
import RHLean.Proof.LowWheelDoubleCubeSequentialFold
import RHLean.Proof.LowWheelSequentialWindowTelescope

/-!
# Prime-prefix double-cube fold as p-free reciprocal windows

The sequential double-cube recurrence writes the state created by a fresh prime
`p` as a mixed four-corner cell over the previously processed prime cube.  The
window telescope then sums the residual multiplier exactly.

For each old face pair `(u,t)`, with

`a = primeFaceProduct u`, `b = primeFaceProduct t`,

the entire `k`-sum is the number of residual multipliers satisfying

* `b*k` lies in the reciprocal `p`-window attached to `a`, and
* `p ∤ k`.

Thus the chronological effect of adding `p` is already visible as a literal
sieve deletion inside the geometrically shrinking reciprocal window.  No norm
or estimate is introduced.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- **Fresh-prime state = signed p-free reciprocal-window counts.**  The whole
new prime-prefix state has no remaining four-corner or residual-multiplier sum:
each old face pair contributes only the cardinality of its `p`-free geometric
window. -/
theorem lowWheelDoubleCubePrimePrefix_step_eq_freeWindowCards
    (R p : ℕ) (hp : p.Prime) :
    lowWheelDoubleCubeSetTransportLedger R (primesUpTo p) =
      ∑ u ∈ (primesUpTo (p - 1)).powerset,
        ∑ t ∈ (primesUpTo (p - 1)).powerset,
          (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
            ((lowWheelPrimeWindowFreeMultiplierSet
              p R (squareRootEndpoint R)
              (primeFaceProduct u) (primeFaceProduct t)).card : ℂ) := by
  rw [lowWheelDoubleCubePrimePrefix_step R p hp]
  apply Finset.sum_congr rfl
  intro u hu
  have huPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  apply Finset.sum_congr rfl
  intro t ht
  have htPos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  let A : ℂ := (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ)
  have htel :=
    sum_lowWheelMixedPrimeCell_mul_eq_freeWindowCard
      (p := p) (R := R) (X := squareRootEndpoint R)
      (a := primeFaceProduct u) (b := primeFaceProduct t)
      hp huPos htPos
  have htelC :
      (∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
          ((lowWheelMixedPrimeCell p R (squareRootEndpoint R)
            (primeFaceProduct t * k)
            ((primeFaceProduct u * primeFaceProduct t) * k) : ℤ) : ℂ)) =
        ((lowWheelPrimeWindowFreeMultiplierSet
          p R (squareRootEndpoint R)
          (primeFaceProduct u) (primeFaceProduct t)).card : ℂ) := by
    have htel' :
        (∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
            lowWheelMixedPrimeCell p R (squareRootEndpoint R)
              (primeFaceProduct t * k)
              ((primeFaceProduct u * primeFaceProduct t) * k)) =
          ((lowWheelPrimeWindowFreeMultiplierSet
            p R (squareRootEndpoint R)
            (primeFaceProduct u) (primeFaceProduct t)).card : ℤ) := by
      simpa [Nat.mul_assoc] using htel
    exact_mod_cast htel'
  change
    (∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
      A *
        ((lowWheelMixedPrimeCell p R (squareRootEndpoint R)
          (primeFaceProduct t * k)
          ((primeFaceProduct u * primeFaceProduct t) * k) : ℤ) : ℂ)) =
      A *
        ((lowWheelPrimeWindowFreeMultiplierSet
          p R (squareRootEndpoint R)
          (primeFaceProduct u) (primeFaceProduct t)).card : ℂ)
  rw [← htelC]
  rw [Finset.mul_sum]

/-- At a prime root cutoff, the original high transport is therefore a signed
sum of `R`-free reciprocal-window cardinalities over the previously processed
low-prime face pairs. -/
theorem squareRootTransportCofactorFirst_eq_freeWindowCards_of_prime
    (R : ℕ) (hR : 2 ≤ R) (hprime : R.Prime) :
    squareRootTransportCofactorFirst R =
      ∑ u ∈ (primesUpTo (R - 1)).powerset,
        ∑ t ∈ (primesUpTo (R - 1)).powerset,
          (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
            ((lowWheelPrimeWindowFreeMultiplierSet
              R R (squareRootEndpoint R)
              (primeFaceProduct u) (primeFaceProduct t)).card : ℂ) := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelDoubleCube R hR,
    lowWheelDoubleCubeTransportLedger_eq_setLedger,
    lowWheelDoubleCubePrimePrefix_step_eq_freeWindowCards R R hprime]

end RHLean.Proof
