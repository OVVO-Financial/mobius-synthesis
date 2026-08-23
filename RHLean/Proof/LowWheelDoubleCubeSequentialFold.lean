import Mathlib
import RHLean.Proof.LowWheelDoubleCubeTransport
import RHLean.Proof.LowWheelSequentialGeometricSavings

/-!
# Sequential mixed finite-difference fold of the two low-wheel cubes

The full two-cube transport carrier makes the chronology of adding a prime
literal.  For a processed coordinate set `S` and a fresh prime `p ∉ S`, split
both powersets of `insert p S` into their `p`-free and `p`-present halves.
Every old pair of faces `(u,t)` produces exactly four children:

`(u,t)`, `(p+u,t)`, `(u,p+t)`, `(p+u,p+t)`.

Their Boolean signs are `+,-,-,+`.  Their physical products are respectively

`(q,n)`, `(q,pn)`, `(pq,pn)`, `(pq,p^2 n)`

with `q = P(t)k` and `n = P(u)P(t)k`.  Hence the complete state after adjoining
`p` is the mixed four-corner finite difference from
`LowWheelDoubleFaceFiniteDifference` evaluated parent by parent on the old
cube.

When `S = primesUpTo (p-1)`, this is the actual increasing-prime chronology.
The generic shell theorem then says that the fresh state is supported only on
the two adjacent `p`-scaled geometric shells.  The next prime acts on this
already-processed parent cube, so geometric support savings and sequential
prime effects are preserved in the same exact recurrence.

No norm or analytic estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Two-cube state with an arbitrary already-processed prime coordinate set. -/
def lowWheelDoubleCubeSetTransportLedger
    (R : ℕ) (S : Finset ℕ) : ℂ :=
  ∑ u ∈ S.powerset,
    ∑ t ∈ S.powerset,
      ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowWheelDoubleCubeAtom R u t k

/-- The complete low-wheel state is the set-parametrized state at
`S = primesUpTo R`. -/
theorem lowWheelDoubleCubeTransportLedger_eq_setLedger
    (R : ℕ) :
    lowWheelDoubleCubeTransportLedger R =
      lowWheelDoubleCubeSetTransportLedger R (primesUpTo R) := by
  rfl

private theorem sum_double_powerset_insert
    {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (S : Finset α) (p : α) (hp : p ∉ S)
    (f : Finset α → Finset α → β) :
    (∑ u ∈ (insert p S).powerset,
        ∑ t ∈ (insert p S).powerset, f u t) =
      ∑ u ∈ S.powerset,
        ∑ t ∈ S.powerset,
          (f u t + f (insert p u) t +
            f u (insert p t) + f (insert p u) (insert p t)) := by
  classical
  rw [Finset.sum_powerset_insert hp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [Finset.sum_powerset_insert hp, Finset.sum_powerset_insert hp]
  simp only [Finset.sum_add_distrib]
  abel

/-- One physical two-cube atom is its Boolean sign times the corresponding
root/endpoint indicator.  Naming this identity keeps the four-corner proof in
signed algebra rather than repeatedly reopening the cutoff conjunction. -/
private theorem lowWheelDoubleCubeAtom_eq_sign_mul_transportIndicator
    (R k : ℕ) (u t : Finset ℕ) :
    lowWheelDoubleCubeAtom R u t k =
      (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
        ((lowWheelTransportIndicator R (squareRootEndpoint R)
          (primeFaceProduct t * k)
          ((primeFaceProduct u * primeFaceProduct t) * k) : ℤ) : ℂ) := by
  unfold lowWheelDoubleCubeAtom lowWheelTransportIndicator
    lowWheelRootHighIndicator lowWheelEndpointIndicator
  by_cases hq : R < primeFaceProduct t * k
  · by_cases hn :
        (primeFaceProduct u * primeFaceProduct t) * k ≤ squareRootEndpoint R
    · simp [hq, hn]
    · simp [hq, hn]
  · simp [hq]

/-- Four signed children of one old face pair are exactly the mixed physical
prime cell, with the old Boolean sign factored out. -/
theorem lowWheelDoubleCube_fourCorners_eq_mixedPrimeCell
    (R p k : ℕ) {u t : Finset ℕ}
    (hpu : p ∉ u) (hpt : p ∉ t) :
    lowWheelDoubleCubeAtom R u t k +
        lowWheelDoubleCubeAtom R (insert p u) t k +
        lowWheelDoubleCubeAtom R u (insert p t) k +
        lowWheelDoubleCubeAtom R (insert p u) (insert p t) k =
      (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
        ((lowWheelMixedPrimeCell p R (squareRootEndpoint R)
          (primeFaceProduct t * k)
          ((primeFaceProduct u * primeFaceProduct t) * k) : ℤ) : ℂ) := by
  have hprodU :
      primeFaceProduct (insert p u) = p * primeFaceProduct u := by
    simp [primeFaceProduct, hpu]
  have hprodT :
      primeFaceProduct (insert p t) = p * primeFaceProduct t := by
    simp [primeFaceProduct, hpt]
  have hsignU :
      (booleanCubeSign (insert p u) : ℂ) =
        -(booleanCubeSign u : ℂ) := by
    unfold booleanCubeSign
    rw [Finset.card_insert_of_notMem hpu, pow_succ]
    push_cast
    ring
  have hsignT :
      (booleanCubeSign (insert p t) : ℂ) =
        -(booleanCubeSign t : ℂ) := by
    unfold booleanCubeSign
    rw [Finset.card_insert_of_notMem hpt, pow_succ]
    push_cast
    ring
  rw [lowWheelDoubleCubeAtom_eq_sign_mul_transportIndicator,
    lowWheelDoubleCubeAtom_eq_sign_mul_transportIndicator,
    lowWheelDoubleCubeAtom_eq_sign_mul_transportIndicator,
    lowWheelDoubleCubeAtom_eq_sign_mul_transportIndicator]
  rw [hprodU, hprodT, hsignU, hsignT]
  have hqT :
      (p * primeFaceProduct t) * k = p * (primeFaceProduct t * k) := by ring
  have hnU :
      ((p * primeFaceProduct u) * primeFaceProduct t) * k =
        p * ((primeFaceProduct u * primeFaceProduct t) * k) := by ring
  have hnT :
      (primeFaceProduct u * (p * primeFaceProduct t)) * k =
        p * ((primeFaceProduct u * primeFaceProduct t) * k) := by ring
  have hnUT :
      ((p * primeFaceProduct u) * (p * primeFaceProduct t)) * k =
        p * p * ((primeFaceProduct u * primeFaceProduct t) * k) := by ring
  rw [hqT, hnU, hnT, hnUT]
  unfold lowWheelMixedPrimeCell
  push_cast
  ring

/-- **Fresh-prime double-cube recurrence.**  Adjoining one new coordinate to
both signed low-wheel copies replaces the whole new state by the mixed
four-corner derivative evaluated on the old parent cube. -/
theorem lowWheelDoubleCubeSetTransportLedger_insert
    (R p : ℕ) (S : Finset ℕ) (hp : p ∉ S) :
    lowWheelDoubleCubeSetTransportLedger R (insert p S) =
      ∑ u ∈ S.powerset,
        ∑ t ∈ S.powerset,
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
            (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
              ((lowWheelMixedPrimeCell p R (squareRootEndpoint R)
                (primeFaceProduct t * k)
                ((primeFaceProduct u * primeFaceProduct t) * k) : ℤ) : ℂ) := by
  classical
  unfold lowWheelDoubleCubeSetTransportLedger
  rw [sum_double_powerset_insert S p hp]
  apply Finset.sum_congr rfl
  intro u hu
  have hpu : p ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem hu hp
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht hp
  calc
    (∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowWheelDoubleCubeAtom R u t k) +
      (∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowWheelDoubleCubeAtom R (insert p u) t k) +
      (∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowWheelDoubleCubeAtom R u (insert p t) k) +
      (∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowWheelDoubleCubeAtom R (insert p u) (insert p t) k) =
      ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        (lowWheelDoubleCubeAtom R u t k +
          lowWheelDoubleCubeAtom R (insert p u) t k +
          lowWheelDoubleCubeAtom R u (insert p t) k +
          lowWheelDoubleCubeAtom R (insert p u) (insert p t) k) := by
            repeat' rw [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
          ((lowWheelMixedPrimeCell p R (squareRootEndpoint R)
            (primeFaceProduct t * k)
            ((primeFaceProduct u * primeFaceProduct t) * k) : ℤ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact lowWheelDoubleCube_fourCorners_eq_mixedPrimeCell
        R p k hpu hpt

/-- A fresh prime is absent from the previously processed prime prefix. -/
theorem freshPrime_not_mem_primesUpTo_pred
    {p : ℕ} (hp : p.Prime) :
    p ∉ primesUpTo (p - 1) := by
  intro hmem
  have hpLe := (mem_primesUpTo.mp hmem).2
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- **Literal increasing-prime recurrence.**  At a prime coordinate `p`, the
state through `p` is the mixed finite difference over the state space containing
exactly the primes processed before `p`. -/
theorem lowWheelDoubleCubePrimePrefix_step
    (R p : ℕ) (hp : p.Prime) :
    lowWheelDoubleCubeSetTransportLedger R (primesUpTo p) =
      ∑ u ∈ (primesUpTo (p - 1)).powerset,
        ∑ t ∈ (primesUpTo (p - 1)).powerset,
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
            (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
              ((lowWheelMixedPrimeCell p R (squareRootEndpoint R)
                (primeFaceProduct t * k)
                ((primeFaceProduct u * primeFaceProduct t) * k) : ℤ) : ℂ) := by
  rw [primesUpTo_eq_insert_pred_of_prime hp]
  exact lowWheelDoubleCubeSetTransportLedger_insert
    R p (primesUpTo (p - 1)) (freshPrime_not_mem_primesUpTo_pred hp)

/-- Complex-valued shell difference attached to one old physical parent pair. -/
def lowWheelSequentialShellDifferenceC
    (p R X q n : ℕ) : ℂ :=
  ((if R < q ∧ n ≤ X ∧ X < p * n then (1 : ℤ) else 0) -
    (if R < p * q ∧ p * n ≤ X ∧ X < p * p * n then (1 : ℤ) else 0) : ℤ)

/-- **Sequential state with geometric support already exposed.**  Substituting
the exact mixed-cell shell identity into the increasing-prime recurrence shows
that the state created when `p` is admitted has support only on its two adjacent
multiplicative shells. -/
theorem lowWheelDoubleCubePrimePrefix_step_eq_shells
    (R p : ℕ) (hp : p.Prime) :
    lowWheelDoubleCubeSetTransportLedger R (primesUpTo p) =
      ∑ u ∈ (primesUpTo (p - 1)).powerset,
        ∑ t ∈ (primesUpTo (p - 1)).powerset,
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
            (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
              lowWheelSequentialShellDifferenceC p R (squareRootEndpoint R)
                (primeFaceProduct t * k)
                ((primeFaceProduct u * primeFaceProduct t) * k) := by
  rw [lowWheelDoubleCubePrimePrefix_step R p hp]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro t _ht
  apply Finset.sum_congr rfl
  intro k _hk
  rw [lowWheelMixedPrimeCell_eq_sequentialShellDifference hp.one_le]
  unfold lowWheelSequentialShellDifferenceC
  push_cast
  rfl

/-- Full transport at a prime root cutoff can therefore be read directly as the
geometrically localized fresh-prime state at that root coordinate. -/
theorem squareRootTransportCofactorFirst_eq_sequentialShells_of_prime
    (R : ℕ) (hR : 2 ≤ R) (hprime : R.Prime) :
    squareRootTransportCofactorFirst R =
      ∑ u ∈ (primesUpTo (R - 1)).powerset,
        ∑ t ∈ (primesUpTo (R - 1)).powerset,
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
            (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ) *
              lowWheelSequentialShellDifferenceC R R (squareRootEndpoint R)
                (primeFaceProduct t * k)
                ((primeFaceProduct u * primeFaceProduct t) * k) := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelDoubleCube R hR,
    lowWheelDoubleCubeTransportLedger_eq_setLedger,
    lowWheelDoubleCubePrimePrefix_step_eq_shells R R hprime]

end RHLean.Proof
