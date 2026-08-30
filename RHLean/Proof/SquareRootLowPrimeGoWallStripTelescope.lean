import Mathlib
import RHLean.Arithmetic.TruncatedCubeMertensPrefix
import RHLean.Proof.LowPrimeParentChildWindowDifference
import RHLean.Proof.SquareRootAncestryRoot
import RHLean.Proof.SquareRootPredecessorPrimeCells

/-!
# Go-wall strip telescope

The first-owner wall is already a no-liberty boundary.  Its old-prime windows
should therefore be treated as boundary strips rather than as another interior
matching problem.

For consecutive old primes `ell < q`, the strip

`F_{q^-}(X/q) - F_{q^-}(X/ell)`

has one exact fresh-prime decomposition.  The moving boundary term telescopes
across consecutive primes, while the sole non-endpoint residual is evaluated at
one additional division by `q`:

`F_{q^-}((X/q)/q)`.

This is the square-dilated Go residual.  Its literal old-face support maps to the
arithmetic child `m = q*c`.  The fresh prime `q` is exactly `P+(m)`, so children
belonging to distinct Go liberties are disjoint by canonical largest-prime
ownership.  Moreover `q*m <= X`: losing one liberty is recorded by one concrete
multiplicative square certificate.

Once the square-dilated cutoff lies below `q`, the predecessor universe is
already complete at that lower scale.  The residual is then exactly the ordinary
integer Mertens prefix at that cutoff.  Thus the genuinely unfinished Go
territory is restricted to the complementary `q^3 <= X` range.

No quantitative estimate is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- One old-prime Go boundary strip, written in the frozen predecessor universe
immediately before `q`. -/
def squareRootLowPrimeGoWallStripMass (ell q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / q) -
    frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / ell)

/-- The moving boundary state after the prime `q` has itself been admitted. -/
def squareRootLowPrimeGoWallBoundaryState (q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo q) (X / q)

/-- The no-liberty residual after one additional attempted `q` contact. -/
def squareRootLowPrimeGoWallSquareResidual (q X : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) ((X / q) / q)

/-- **Exact one-strip Go descent.**  If `ell` is the previous prime coordinate,
so the predecessor universe before `q` is exactly the universe through `ell`,
then the wall strip is the difference of adjacent moving boundary states plus
one square-dilated residual.

This is the quantitative seam: summing consecutive strips can telescope the
first two terms, while the surviving term has lost an additional factor `q` in
scale. -/
theorem squareRootLowPrimeGoWallStripMass_eq_boundaryDiff_add_squareResidual
    {ell q X : ℕ} (hq : q.Prime)
    (hpred : primesUpTo (q - 1) = primesUpTo ell) :
    squareRootLowPrimeGoWallStripMass ell q X =
      squareRootLowPrimeGoWallBoundaryState q X -
        squareRootLowPrimeGoWallBoundaryState ell X +
          squareRootLowPrimeGoWallSquareResidual q X := by
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor q (X / q) hq
  unfold predecessorPrimeMass at hstep
  unfold squareRootLowPrimeGoWallStripMass
    squareRootLowPrimeGoWallBoundaryState
    squareRootLowPrimeGoWallSquareResidual
  rw [hpred]
  rw [hpred] at hstep
  omega

/-- The square residual is literally the predecessor-prime mass at the already
reciprocal cutoff `X/q`. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_predecessorPrimeMass
    (q X : ℕ) :
    squareRootLowPrimeGoWallSquareResidual q X =
      predecessorPrimeMass q (X / q) := by
  rfl

/-- Equivalent `q^2` notation for the square-dilated cutoff. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff
    (q X : ℕ) :
    squareRootLowPrimeGoWallSquareResidual q X =
      frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / (q * q)) := by
  unfold squareRootLowPrimeGoWallSquareResidual
  rw [Nat.div_div_eq_div_mul]

/-! ## Literal support and global Go ownership -/

/-- Old Boolean faces contributing to the square-dilated residual. -/
def squareRootLowPrimeGoWallSquareResidualFaces
    (q X : ℕ) : Finset (Finset ℕ) :=
  ((primesUpTo (q - 1)).powerset).filter fun u =>
    primeFaceProduct u ≤ X / (q * q)

@[simp] theorem mem_squareRootLowPrimeGoWallSquareResidualFaces
    {q X : ℕ} {u : Finset ℕ} :
    u ∈ squareRootLowPrimeGoWallSquareResidualFaces q X ↔
      u ∈ (primesUpTo (q - 1)).powerset ∧
        primeFaceProduct u ≤ X / (q * q) := by
  simp [squareRootLowPrimeGoWallSquareResidualFaces]

/-- Concrete arithmetic children `m=q*c` represented by one square residual. -/
def squareRootLowPrimeGoWallSquareResidualChildren
    (q X : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoWallSquareResidualFaces q X).image fun u =>
    q * primeFaceProduct u

@[simp] theorem mem_squareRootLowPrimeGoWallSquareResidualChildren
    {q X m : ℕ} :
    m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X ↔
      ∃ u ∈ squareRootLowPrimeGoWallSquareResidualFaces q X,
        q * primeFaceProduct u = m := by
  simp [squareRootLowPrimeGoWallSquareResidualChildren]

/-- **Canonical Go owner.**  The prime whose second contact generated the
square residual is recoverable from its arithmetic child as the child's
canonical largest prime factor. -/
theorem squareRootLowPrimeGoWallSquareResidualChild_owner
    {q X m : ℕ} (hq : q.Prime)
    (hm : m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X) :
    canonicalLargestPrimeFactor m = q := by
  rcases mem_squareRootLowPrimeGoWallSquareResidualChildren.mp hm with
    ⟨u, hu, rfl⟩
  have huData := mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu
  have hrough :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hq huData.1
  have hcPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset huData.1
  simpa [Nat.mul_comm] using
    (canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hq hrough)

/-- **Square certificate.**  Every owned Go child still fits after one more
multiplication by its canonical owner: `q*m <= X`.  This is the literal loss of
one further liberty. -/
theorem squareRootLowPrimeGoWallSquareResidualChild_owner_mul_le
    {q X m : ℕ} (hq : q.Prime)
    (hm : m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X) :
    q * m ≤ X := by
  rcases mem_squareRootLowPrimeGoWallSquareResidualChildren.mp hm with
    ⟨u, hu, rfl⟩
  have huCut :=
    (mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu).2
  have hqqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hmul : primeFaceProduct u * (q * q) ≤ X :=
    (Nat.le_div_iff_mul_le hqqPos).1 huCut
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

/-- Distinct Go liberties own disjoint square-residual child populations.  The
prime coordinate is not an external multiplicity: it is encoded in `P+(m)`. -/
theorem squareRootLowPrimeGoWallSquareResidualChildren_disjoint
    {q r X : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    Disjoint (squareRootLowPrimeGoWallSquareResidualChildren q X)
      (squareRootLowPrimeGoWallSquareResidualChildren r X) := by
  rw [Finset.disjoint_left]
  intro m hmq hmr
  have hqOwner := squareRootLowPrimeGoWallSquareResidualChild_owner hq hmq
  have hrOwner := squareRootLowPrimeGoWallSquareResidualChild_owner hr hmr
  exact hqr (hqOwner.symm.trans hrOwner)

/-- Pairwise-disjoint form used when summing the square residuals over an actual
finite prime schedule. -/
theorem squareRootLowPrimeGoWallSquareResidualChildren_pairwiseDisjoint
    (Q : Finset ℕ) (X : ℕ) (hprime : ∀ q ∈ Q, q.Prime) :
    Set.PairwiseDisjoint (↑Q)
      (fun q => squareRootLowPrimeGoWallSquareResidualChildren q X) := by
  intro q hq r hr hqr
  exact squareRootLowPrimeGoWallSquareResidualChildren_disjoint
    (hprime q hq) (hprime r hr) hqr

/-! ## Arithmetic cofactor form and completed Go positions -/

/-- Squarefree cofactors represented by the predecessor cube below `q`. -/
def squareRootLowPrimeGoSmoothCofactors (q B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter fun c =>
    Squarefree c ∧ canonicalLargestPrimeFactor c < q

@[simp] theorem mem_squareRootLowPrimeGoSmoothCofactors
    {q B c : ℕ} :
    c ∈ squareRootLowPrimeGoSmoothCofactors q B ↔
      1 ≤ c ∧ c ≤ B ∧ Squarefree c ∧
        canonicalLargestPrimeFactor c < q := by
  simp [squareRootLowPrimeGoSmoothCofactors, and_assoc]

/-- The literal face support and arithmetic smooth-cofactor support are the same
finite population. -/
theorem squareRootLowPrimeGoWallSquareResidualFaces_image_eq_smoothCofactors
    {q X : ℕ} (hq : q.Prime) :
    (squareRootLowPrimeGoWallSquareResidualFaces q X).image primeFaceProduct =
      squareRootLowPrimeGoSmoothCofactors q (X / (q * q)) := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨u, hu, rfl⟩
    have huData := mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu
    have hprime : ∀ r ∈ u, r.Prime := by
      intro r hr
      have hrOld := (Finset.mem_powerset.mp huData.1) hr
      exact (mem_primesUpTo.mp hrOld).1
    have hmuEq := moebius_primeFaceProduct_eq_booleanCubeSign u hprime
    have hmuNe : μ (primeFaceProduct u) ≠ 0 := by
      rw [hmuEq]
      unfold booleanCubeSign
      exact pow_ne_zero _ (by norm_num)
    have hsq : Squarefree (primeFaceProduct u) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    have hrough :=
      canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hq huData.1
    have hpos : 0 < primeFaceProduct u :=
      primeFaceProduct_pos_of_mem_powerset huData.1
    exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨by omega, huData.2, hsq, hrough⟩
  · intro hc
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hc with
      ⟨hc1, hcB, hsq, hrough⟩
    let u := squarefreePrimeFace c
    have hprod : primeFaceProduct u = c := by
      simpa [u] using primeFaceProduct_squarefreePrimeFace hsq
    have huSub : u ⊆ primesUpTo (q - 1) := by
      intro r hr
      have hrData : r ∈ c.primeFactors := by
        simpa [u, squarefreePrimeFace] using hr
      have hrPrime : r.Prime := (Nat.mem_primeFactors.mp hrData).1
      have hrDvd : r ∣ c := (Nat.mem_primeFactors.mp hrData).2.1
      have hcPos : 0 < c := by omega
      have hrLeC : r ≤ c := Nat.le_of_dvd hcPos hrDvd
      have hcGt : 1 < c := lt_of_lt_of_le hrPrime.one_lt hrLeC
      have hrLeLpf : r ≤ canonicalLargestPrimeFactor c := by
        unfold canonicalLargestPrimeFactor
        rw [dif_pos hcGt]
        exact Finset.le_max' c.primeFactors r hrData
      exact mem_primesUpTo.mpr ⟨hrPrime, by omega⟩
    have huFace : u ∈ squareRootLowPrimeGoWallSquareResidualFaces q X := by
      apply mem_squareRootLowPrimeGoWallSquareResidualFaces.mpr
      refine ⟨Finset.mem_powerset.mpr huSub, ?_⟩
      simpa [hprod] using hcB
    exact Finset.mem_image.mpr ⟨u, huFace, hprod⟩

/-- The frozen square residual is exactly the ordinary Möbius sum over its
squarefree smooth cofactor population. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum
    {q X : ℕ} (hq : q.Prime) :
    squareRootLowPrimeGoWallSquareResidual q X =
      ∑ c ∈ squareRootLowPrimeGoSmoothCofactors q (X / (q * q)), μ c := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  rw [frozenPrimeUniverseMass_eq_cutoffSum]
  have hfilter :
      (∑ u ∈ (primesUpTo (q - 1)).powerset,
          if primeFaceProduct u ≤ X / (q * q) then booleanCubeSign u else 0) =
        ∑ u ∈ squareRootLowPrimeGoWallSquareResidualFaces q X,
          booleanCubeSign u := by
    unfold squareRootLowPrimeGoWallSquareResidualFaces
    rw [Finset.sum_filter]
  rw [hfilter]
  calc
    (∑ u ∈ squareRootLowPrimeGoWallSquareResidualFaces q X,
        booleanCubeSign u) =
      ∑ u ∈ squareRootLowPrimeGoWallSquareResidualFaces q X,
        μ (primeFaceProduct u) := by
          apply Finset.sum_congr rfl
          intro u hu
          symm
          apply moebius_primeFaceProduct_eq_booleanCubeSign
          intro r hr
          have huOld :=
            (mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu).1
          exact (mem_primesUpTo.mp ((Finset.mem_powerset.mp huOld) hr)).1
    _ = ∑ c ∈
        (squareRootLowPrimeGoWallSquareResidualFaces q X).image primeFaceProduct,
          μ c := by
            symm
            apply Finset.sum_image
            intro u hu v hv huv
            apply (primeFaceProduct_eq_iff ?_ ?_).mp huv
            · intro r hr
              have huOld :=
                (mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu).1
              exact (mem_primesUpTo.mp ((Finset.mem_powerset.mp huOld) hr)).1
            · intro r hr
              have hvOld :=
                (mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hv).1
              exact (mem_primesUpTo.mp ((Finset.mem_powerset.mp hvOld) hr)).1
    _ = ∑ c ∈ squareRootLowPrimeGoSmoothCofactors q (X / (q * q)), μ c := by
          rw [squareRootLowPrimeGoWallSquareResidualFaces_image_eq_smoothCofactors hq]

/-- Once the physical cutoff lies below the owner prime, the smoothness
restriction is vacuous. -/
theorem squareRootLowPrimeGoSmoothCofactors_eq_squarefreeUpTo
    {q B : ℕ} (hq : q.Prime) (hBq : B < q) :
    squareRootLowPrimeGoSmoothCofactors q B = squarefreeUpTo B := by
  ext c
  constructor
  · intro hc
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hc with
      ⟨hc1, hcB, hsq, _hrough⟩
    unfold squarefreeUpTo
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hsq⟩
  · intro hc
    unfold squarefreeUpTo at hc
    rcases Finset.mem_filter.mp hc with ⟨hcRange, hsq⟩
    have hcB : c ≤ B := by
      have := Finset.mem_range.mp hcRange
      omega
    have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hsq.ne_zero
    have hrough : canonicalLargestPrimeFactor c < q := by
      by_cases hcEq : c = 1
      · subst c
        simp [canonicalLargestPrimeFactor, hq.one_lt]
      · have hcGt : 1 < c := by omega
        have hlpfLe : canonicalLargestPrimeFactor c ≤ c :=
          Nat.le_of_dvd (by omega) (canonicalLargestPrimeFactor_dvd hcGt)
        omega
    exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨hc1, hcB, hsq, hrough⟩

/-- **Completed Go position = lower-scale Mertens.**  If the square-dilated
cutoff lies below `q`, every possible prime factor is already present in the
predecessor universe. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_mertensSummatoryInt
    {q X : ℕ} (hq : q.Prime) (hcomplete : X / (q * q) < q) :
    squareRootLowPrimeGoWallSquareResidual q X =
      mertensSummatoryInt (X / (q * q)) := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum hq,
    squareRootLowPrimeGoSmoothCofactors_eq_squarefreeUpTo hq hcomplete]
  unfold mertensSummatoryInt
  exact squarefreeMoebiusSum_eq_fullPrefix (X / (q * q))

end RHLean.Proof
