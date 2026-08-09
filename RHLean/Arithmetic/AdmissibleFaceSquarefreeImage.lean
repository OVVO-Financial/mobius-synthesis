import Mathlib
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity

open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Arithmetic

/-- The finite set of all faces admitted by the prime-product cutoff at `X`. -/
def admissiblePrimeFaces (X : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (primesUpTo X).powerset.filter
    (primeProductAdmissible (primesUpTo X) X)

/-- The finite set of squarefree natural numbers not exceeding `X`. -/
def squarefreeUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter Squarefree

@[simp] theorem mem_admissiblePrimeFaces {X : ℕ} {t : Finset ℕ} :
    t ∈ admissiblePrimeFaces X ↔
      primeProductAdmissible (primesUpTo X) X t := by
  classical
  constructor
  · intro ht
    exact (Finset.mem_filter.mp ht).2
  · intro ht
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr ht.1, ht⟩

@[simp] theorem mem_squarefreeUpTo {X n : ℕ} :
    n ∈ squarefreeUpTo X ↔ Squarefree n ∧ n ≤ X := by
  simp [squarefreeUpTo, Nat.lt_succ_iff, and_comm]

/-- The product image of the admissible prime faces is exactly the set of
squarefree integers up to the cutoff. -/
theorem image_primeFaceProduct_admissiblePrimeFaces
    (X : ℕ) :
    (admissiblePrimeFaces X).image primeFaceProduct = squarefreeUpTo X := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
    have htAdm : primeProductAdmissible (primesUpTo X) X t :=
      mem_admissiblePrimeFaces.mp ht
    have hmu := moebius_admissiblePrimeFace_eq_booleanCubeSign htAdm
    have hmuNe : μ (primeFaceProduct t) ≠ 0 := by
      rw [hmu]
      simp [booleanCubeSign]
    have hsq : Squarefree (primeFaceProduct t) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    exact mem_squarefreeUpTo.mpr ⟨hsq, htAdm.2⟩
  · intro hn
    have hnData := mem_squarefreeUpTo.mp hn
    let t := squarefreePrimeFace n
    have htAdm : primeProductAdmissible (primesUpTo X) X t :=
      squarefreePrimeFace_admissible hnData.1 hnData.2
    apply Finset.mem_image.mpr
    refine ⟨t, mem_admissiblePrimeFaces.mpr htAdm, ?_⟩
    exact primeFaceProduct_squarefreePrimeFace hnData.1

end RHLean.Arithmetic
