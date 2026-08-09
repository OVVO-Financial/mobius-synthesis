import Mathlib
import RHLean.Arithmetic.TruncatedBooleanCube

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Product represented by a finite face of prime coordinates. -/
def primeFaceProduct (t : Finset ℕ) : ℕ :=
  t.prod id

/-- Concrete finite support used by the prime-product cube: the face belongs to
`S` and its represented squarefree product lies below the cutoff `X`. -/
def primeProductAdmissible (S : Finset ℕ) (X : ℕ) (t : Finset ℕ) : Prop :=
  t ⊆ S ∧ primeFaceProduct t ≤ X

/-- Prime-product support is downward closed.  The positivity of every prime
coordinate is exactly what makes deleting coordinates decrease the product. -/
theorem primeProductAdmissible_downward
    {S : Finset ℕ} {X : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    CubeDownwardClosed (primeProductAdmissible S X) := by
  intro u v huv hv
  refine ⟨huv.trans hv.1, ?_⟩
  exact le_trans
    (Finset.prod_le_prod_of_subset_of_one_le' huv (by
      intro p hpv hpu
      exact (hprime p (hv.1 hpv)).one_le))
    hv.2

/-- The explicit arithmetic frontier at a fresh prime coordinate `ell`.
A parent face is retained precisely when its product fits below `X`, while
adjoining `ell` crosses the cutoff. -/
def primeProductFirstFailureBoundary
    (S : Finset ℕ) (X ell : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (S.erase ell).powerset.filter fun t =>
    primeFaceProduct t ≤ X ∧ X < ell * primeFaceProduct t

@[simp] theorem mem_primeProductFirstFailureBoundary
    {S : Finset ℕ} {X ell : ℕ} {t : Finset ℕ} :
    t ∈ primeProductFirstFailureBoundary S X ell ↔
      t ⊆ S.erase ell ∧
      primeFaceProduct t ≤ X ∧
      X < ell * primeFaceProduct t := by
  classical
  simp [primeProductFirstFailureBoundary]

/-- The generic first-failure boundary from `TruncatedBooleanCube` is exactly
the concrete prime-product frontier `P(t) ≤ X < ell * P(t)`. -/
theorem firstFailureBoundary_primeProduct_eq
    {S : Finset ℕ} {X ell : ℕ}
    (hell : ell ∈ S) :
    firstFailureBoundary S ell (primeProductAdmissible S X) =
      primeProductFirstFailureBoundary S X ell := by
  classical
  ext t
  simp only [mem_firstFailureBoundary,
    mem_primeProductFirstFailureBoundary]
  constructor
  · intro ht
    refine ⟨ht.1, ht.2.1.2, ?_⟩
    have hell_not_mem : ell ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem
        (Finset.mem_powerset.mpr ht.1) (Finset.notMem_erase ell S)
    have hinsert_subset : insert ell t ⊆ S := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpt
      · exact hell
      · exact (Finset.mem_erase.mp (ht.1 hpt)).2
    have hprod_insert :
        primeFaceProduct (insert ell t) = ell * primeFaceProduct t := by
      simp [primeFaceProduct, hell_not_mem]
    have hnot_le : ¬ primeFaceProduct (insert ell t) ≤ X := by
      intro hle
      exact ht.2.2 ⟨hinsert_subset, hle⟩
    rw [hprod_insert] at hnot_le
    exact Nat.lt_of_not_ge hnot_le
  · intro ht
    refine ⟨ht.1, ⟨?_, ht.2.1⟩, ?_⟩
    · exact fun p hp => (Finset.mem_erase.mp (ht.1 hp)).2
    · intro hchild
      have hell_not_mem : ell ∉ t :=
        Finset.notMem_of_mem_powerset_of_notMem
          (Finset.mem_powerset.mpr ht.1) (Finset.notMem_erase ell S)
      have hprod_insert :
          primeFaceProduct (insert ell t) = ell * primeFaceProduct t := by
        simp [primeFaceProduct, hell_not_mem]
      have hchild_le : primeFaceProduct (insert ell t) ≤ X := hchild.2
      rw [hprod_insert] at hchild_le
      exact (Nat.not_lt_of_ge hchild_le) ht.2.2

/-- Exact arithmetic specialization of the truncated-cube theorem.

The complete alternating prime-product cube below `X` equals the signed frontier
of products that still fit below `X` but whose fresh-`ell` extension crosses it. -/
theorem truncatedPrimeProductCube_eq_frontier
    {S : Finset ℕ} {X ell : ℕ}
    (hell : ell ∈ S)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    truncatedCubeAlternatingSum S (primeProductAdmissible S X) =
      ∑ t ∈ primeProductFirstFailureBoundary S X ell,
        booleanCubeSign t := by
  rw [truncatedCubeAlternatingSum_eq_firstFailureBoundary hell
    (primeProductAdmissible_downward hprime)]
  unfold firstFailureBoundaryAlternatingSum
  rw [firstFailureBoundary_primeProduct_eq hell]

end RHLean.Arithmetic
