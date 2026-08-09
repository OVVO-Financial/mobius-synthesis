import Mathlib
import RHLean.Arithmetic.PrimeProductCubeFrontier

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Faces surviving all extensions in a selected coordinate set `A`.
The free face `t` uses only coordinates outside `A`, and the combined face
`A ∪ t` must still lie below the prime-product cutoff. -/
def fullyExtendablePrimeFaces
    (S : Finset ℕ) (X : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact (S \ A).powerset.filter fun t =>
    primeProductAdmissible S X (A ∪ t)

@[simp] theorem mem_fullyExtendablePrimeFaces
    {S A t : Finset ℕ} {X : ℕ} :
    t ∈ fullyExtendablePrimeFaces S X A ↔
      t ⊆ S \ A ∧ primeProductAdmissible S X (A ∪ t) := by
  classical
  simp [fullyExtendablePrimeFaces]

/-- Ordered frontier at the next coordinate `ell`, after all coordinates in
`A` have already been successfully inserted.  These are precisely the free
faces for which `A ∪ t` is admissible but `insert ell A ∪ t` is not. -/
def orderedPrimeProductFrontier
    (S : Finset ℕ) (X : ℕ) (A : Finset ℕ) (ell : ℕ) :
    Finset (Finset ℕ) := by
  classical
  exact (S \ insert ell A).powerset.filter fun t =>
    primeProductAdmissible S X (A ∪ t) ∧
      ¬ primeProductAdmissible S X (insert ell A ∪ t)

@[simp] theorem mem_orderedPrimeProductFrontier
    {S A t : Finset ℕ} {X ell : ℕ} :
    t ∈ orderedPrimeProductFrontier S X A ell ↔
      t ⊆ S \ insert ell A ∧
      primeProductAdmissible S X (A ∪ t) ∧
      ¬ primeProductAdmissible S X (insert ell A ∪ t) := by
  classical
  simp [orderedPrimeProductFrontier]

/-- The product of disjoint selected and free coordinate sets factors exactly. -/
theorem primeFaceProduct_union_of_disjoint
    {A t : Finset ℕ} (hdisj : Disjoint A t) :
    primeFaceProduct (A ∪ t) =
      primeFaceProduct A * primeFaceProduct t := by
  classical
  simp [primeFaceProduct, Finset.prod_union hdisj]

/-- Every surviving fully extendable face forces the selected extension set
itself to remain below the cutoff.  This is the monotonicity consequence needed
to kill the final remainder. -/
theorem selectedFace_admissible_of_fullyExtendable
    {S A t : Finset ℕ} {X : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (ht : t ∈ fullyExtendablePrimeFaces S X A) :
    primeProductAdmissible S X A := by
  have hcombined : primeProductAdmissible S X (A ∪ t) :=
    (mem_fullyExtendablePrimeFaces.mp ht).2
  have hdown : CubeDownwardClosed (primeProductAdmissible S X) :=
    primeProductAdmissible_downward hprime
  exact hdown A (A ∪ t) Finset.subset_union_left hcombined

/-- Once the selected prime product exceeds `X`, no face can survive all of
those extensions.  Thus the final fully extendable remainder is exactly empty. -/
theorem fullyExtendablePrimeFaces_eq_empty_of_cutoff
    {S A : Finset ℕ} {X : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hX : X < primeFaceProduct A) :
    fullyExtendablePrimeFaces S X A = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hAadm : primeProductAdmissible S X A :=
    selectedFace_admissible_of_fullyExtendable hprime ht
  exact (Nat.not_lt_of_ge hAadm.2) hX

/-- Equivalent zero-cardinality form of final remainder exhaustion. -/
theorem fullyExtendablePrimeFaces_card_eq_zero_of_cutoff
    {S A : Finset ℕ} {X : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hX : X < primeFaceProduct A) :
    (fullyExtendablePrimeFaces S X A).card = 0 := by
  rw [fullyExtendablePrimeFaces_eq_empty_of_cutoff hprime hX]
  simp

/-- Consequently every signed sum over the fully extendable remainder vanishes
once the selected prime product crosses the cutoff. -/
theorem sum_fullyExtendablePrimeFaces_eq_zero_of_cutoff
    {S A : Finset ℕ} {X : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hX : X < primeFaceProduct A)
    (f : Finset ℕ → ℤ) :
    ∑ t ∈ fullyExtendablePrimeFaces S X A, f t = 0 := by
  rw [fullyExtendablePrimeFaces_eq_empty_of_cutoff hprime hX]
  simp

end RHLean.Arithmetic
