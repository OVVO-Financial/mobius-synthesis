import Mathlib
import RHLean.Proof.LowWheelOthelloRepeatedClassification
import RHLean.Proof.LowWheelFaceTailActiveSupport

/-!
# Canonical opposite move on the lightweight downcross carrier

A downcross state `y=(t,(c,k))` has canonical pivot `p=minFac(c*k)` and tail
`m=k/p`.  For a movable prime `q>=p`, transfer `q` between `t` and `m`, then
restore the same explicit pivot in front of the new tail.

The move preserves the physical product, the canonical least-prime pivot, and
the root-side parent.  It reverses the Boolean sign while keeping the cofactor
fixed.  Most importantly, every prime has the same movable/nonmovable status
at both endpoints.  Hence the least movable prime is itself invariant.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Residual tail after removing the canonical pivot. -/
def lowWheelOthelloDowncrossTail
    (y : LowWheelOthelloTaggedDowncrossState) : ℕ :=
  y.2.2 / lowWheelOthelloDowncrossPivot y

/-- Face/tail coordinates. -/
def lowWheelOthelloFaceTail
    (y : LowWheelOthelloTaggedDowncrossState) : LowWheelFaceTailState :=
  (y.1, lowWheelOthelloDowncrossTail y)

/-- Transfer `q` between face and tail and restore the old explicit pivot. -/
def lowWheelOthelloParentToggleAt
    (q : ℕ) (y : LowWheelOthelloTaggedDowncrossState) :
    LowWheelOthelloTaggedDowncrossState :=
  let u := lowWheelFaceTailToggleAt q (lowWheelOthelloFaceTail y)
  (u.1, (y.2.1, lowWheelOthelloDowncrossPivot y * u.2))

@[simp] theorem lowWheelOthelloParentToggleAt_cofactor
    (q : ℕ) (y : LowWheelOthelloTaggedDowncrossState) :
    (lowWheelOthelloParentToggleAt q y).2.1 = y.2.1 := by
  rfl

/-- The represented root parent in old-pivot coordinates is invariant. -/
theorem lowWheelOthelloParentToggleAt_explicitParent
    {q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hp : 0 < lowWheelOthelloDowncrossPivot y) :
    primeFaceProduct (lowWheelOthelloParentToggleAt q y).1 *
        ((lowWheelOthelloParentToggleAt q y).2.2 /
          lowWheelOthelloDowncrossPivot y) =
      primeFaceProduct y.1 * lowWheelOthelloDowncrossTail y := by
  let u := lowWheelFaceTailToggleAt q (lowWheelOthelloFaceTail y)
  have htail :
      (lowWheelOthelloDowncrossPivot y * u.2) /
          lowWheelOthelloDowncrossPivot y = u.2 := by
    simpa [Nat.mul_comm] using Nat.mul_div_left u.2 hp
  change primeFaceProduct u.1 *
      ((lowWheelOthelloDowncrossPivot y * u.2) /
        lowWheelOthelloDowncrossPivot y) =
    primeFaceProduct y.1 * lowWheelOthelloDowncrossTail y
  rw [htail]
  exact lowWheelFaceTailToggleAt_product q (lowWheelOthelloFaceTail y)

/-- The high-side physical product is invariant. -/
theorem lowWheelOthelloParentToggleAt_highProduct
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R) :
    primeFaceProduct (lowWheelOthelloParentToggleAt q y).1 *
        (lowWheelOthelloParentToggleAt q y).2.2 =
      primeFaceProduct y.1 * y.2.2 := by
  have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2
  have hshell := lowWheelOthelloDowncrossPart_adjacent_shell hx
  have hpk := hshell.2.2.1
  have hk :
      lowWheelOthelloDowncrossPivot y * lowWheelOthelloDowncrossTail y =
        y.2.2 := by
    simpa [lowWheelOthelloDowncrossPivot, lowWheelOthelloDowncrossTail] using
      Nat.mul_div_cancel' hpk
  let u := lowWheelFaceTailToggleAt q (lowWheelOthelloFaceTail y)
  have hparent := lowWheelFaceTailToggleAt_product q
    (lowWheelOthelloFaceTail y)
  have hparent' :
      primeFaceProduct u.1 * u.2 =
        primeFaceProduct y.1 * lowWheelOthelloDowncrossTail y := by
    simpa [u, lowWheelOthelloFaceTail] using hparent
  change primeFaceProduct u.1 *
      (lowWheelOthelloDowncrossPivot y * u.2) =
    primeFaceProduct y.1 * y.2.2
  calc
    primeFaceProduct u.1 * (lowWheelOthelloDowncrossPivot y * u.2) =
        lowWheelOthelloDowncrossPivot y *
          (primeFaceProduct u.1 * u.2) := by ring
    _ = lowWheelOthelloDowncrossPivot y *
        (primeFaceProduct y.1 * lowWheelOthelloDowncrossTail y) := by
          rw [hparent']
    _ = primeFaceProduct y.1 *
        (lowWheelOthelloDowncrossPivot y * lowWheelOthelloDowncrossTail y) := by
          ring
    _ = primeFaceProduct y.1 * y.2.2 := by rw [hk]

/-- Every movable prime belongs to the low-prime universe. -/
theorem lowWheelOthelloMovablePrime_mem_primesUpTo
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    q ∈ primesUpTo R := by
  rcases mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy with ⟨ht, hx⟩
  rcases hq with ⟨hqPrime, _hpq, hactive⟩
  rcases hactive with hface | htail
  · exact (Finset.mem_powerset.mp ht) hface
  · have hshell := lowWheelOthelloDowncrossPart_adjacent_shell hx
    have hp := hshell.1
    have hpk := hshell.2.2.1
    have hparent := hshell.2.2.2.1
    have hkpos : 0 < y.2.2 := by
      have hxF := (mem_lowWheelOthelloDowncrossPart.mp hx).1
      have hkge := (Finset.mem_Icc.mp
        (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.1).1
      omega
    have hpLeK : lowWheelOthelloDowncrossPivot y ≤ y.2.2 :=
      Nat.le_of_dvd hkpos hpk
    have hmpos : 0 < lowWheelOthelloDowncrossTail y := by
      exact Nat.div_pos hpLeK hp.pos
    have hqLeTail : q ≤ lowWheelOthelloDowncrossTail y :=
      Nat.le_of_dvd hmpos htail
    have hPpos : 0 < primeFaceProduct y.1 :=
      primeFaceProduct_pos_of_mem_powerset ht
    have htailLeParent :
        lowWheelOthelloDowncrossTail y ≤
          primeFaceProduct y.1 * lowWheelOthelloDowncrossTail y :=
      Nat.le_mul_of_pos_left _ hPpos
    have hqR : q ≤ R := hqLeTail.trans (htailLeParent.trans hparent)
    exact mem_primesUpTo.mpr ⟨hqPrime, hqR⟩

/-- The moved Boolean face remains a legal low-prime face. -/
theorem lowWheelOthelloParentToggleAt_face_mem
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    (lowWheelOthelloParentToggleAt q y).1 ∈ (primesUpTo R).powerset := by
  rcases mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy with ⟨ht, _hx⟩
  have hqGlobal := lowWheelOthelloMovablePrime_mem_primesUpTo hy hq
  unfold lowWheelOthelloParentToggleAt lowWheelOthelloFaceTail
  dsimp
  unfold lowWheelFaceTailToggleAt
  by_cases hqt : q ∈ y.1
  · simp only [hqt, if_true]
    exact Finset.mem_powerset.mpr
      ((Finset.erase_subset q y.1).trans (Finset.mem_powerset.mp ht))
  · have htail : q ∣ lowWheelOthelloDowncrossTail y := hq.2.2.resolve_left hqt
    simp only [hqt, if_false, htail, if_true]
    apply Finset.mem_powerset.mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hqGlobal
    · exact (Finset.mem_powerset.mp ht) hr

/-- The moved state remains in the physical transport carrier. -/
theorem lowWheelOthelloParentToggleAt_physicalCarrier
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (_hq : LowWheelOthelloMovablePrime y q) :
    LowWheelTransportPairCarrier R
      (lowWheelOthelloParentToggleAt q y).1
      (lowWheelOthelloParentToggleAt q y).2 := by
  have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2
  have hxF := (mem_lowWheelOthelloDowncrossPart.mp hx).1
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  rcases hcarrier with ⟨hc1, hcR, hhigh, htop⟩
  have hprod := lowWheelOthelloParentToggleAt_highProduct (q := q) hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hc1
  · simpa using hcR
  · rw [hprod]
    exact hhigh
  · rw [lowWheelOthelloParentToggleAt_cofactor]
    calc
      y.2.1 * primeFaceProduct (lowWheelOthelloParentToggleAt q y).1 *
          (lowWheelOthelloParentToggleAt q y).2.2 =
        y.2.1 *
          (primeFaceProduct (lowWheelOthelloParentToggleAt q y).1 *
            (lowWheelOthelloParentToggleAt q y).2.2) := by ring
      _ = y.2.1 * (primeFaceProduct y.1 * y.2.2) := by rw [hprod]
      _ = (y.2.1 * primeFaceProduct y.1) * y.2.2 := by ring
      _ ≤ squareRootEndpoint R := htop

/-- Hence the moved state is in the finite physical state set. -/
theorem lowWheelOthelloParentToggleAt_mem_physical
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    (lowWheelOthelloParentToggleAt q y).2 ∈
      lowWheelCanonicalPhysicalStateSet R (lowWheelOthelloParentToggleAt q y).1 := by
  have hcarrier := lowWheelOthelloParentToggleAt_physicalCarrier hy hq
  have hrange := lowWheelTransportPairCarrier_mem_ranges hcarrier
  have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2
  have hxF := (mem_lowWheelOthelloDowncrossPart.mp hx).1
  have hsq := (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.1
  exact mem_lowWheelCanonicalPhysicalStateSet.mpr
    ⟨hrange.1, hrange.2, by simpa using hsq, hcarrier⟩

/-- Canonical least-prime pivot is unchanged by a movable transfer. -/
theorem lowWheelOthelloParentToggleAt_pivot
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    lowWheelOthelloDowncrossPivot (lowWheelOthelloParentToggleAt q y) =
      lowWheelOthelloDowncrossPivot y := by
  have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2
  have hshell := lowWheelOthelloDowncrossPart_adjacent_shell hx
  have hp := hshell.1
  have hpk := hshell.2.2.1
  have hk :
      lowWheelOthelloDowncrossPivot y * lowWheelOthelloDowncrossTail y =
        y.2.2 := by
    simpa [lowWheelOthelloDowncrossPivot, lowWheelOthelloDowncrossTail] using
      Nat.mul_div_cancel' hpk
  have hmin :
      Nat.minFac
          (y.2.1 *
            (lowWheelOthelloDowncrossPivot y * lowWheelOthelloDowncrossTail y)) =
        lowWheelOthelloDowncrossPivot y := by
    rw [hk]
    rfl
  have hpres := lowWheelFaceTailToggleAt_preserves_minFac
    (c := y.2.1) (p := lowWheelOthelloDowncrossPivot y) (q := q)
    (m := lowWheelOthelloDowncrossTail y) (t := y.1)
    hp hq.1 hq.2.1 hmin hq.2.2
  change Nat.minFac
      (y.2.1 *
        (lowWheelOthelloDowncrossPivot y *
          (lowWheelFaceTailToggleAt q (lowWheelOthelloFaceTail y)).2)) =
      lowWheelOthelloDowncrossPivot y
  simpa [lowWheelOthelloFaceTail] using hpres

/-- The actual canonical root parent is invariant. -/
theorem lowWheelOthelloParentToggleAt_parent
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    lowWheelOthelloDowncrossParent (lowWheelOthelloParentToggleAt q y) =
      lowWheelOthelloDowncrossParent y := by
  have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2
  have hp := (lowWheelOthelloDowncrossPart_adjacent_shell hx).1
  have hpivot := lowWheelOthelloParentToggleAt_pivot hy hq
  unfold lowWheelOthelloDowncrossParent
  rw [hpivot]
  simpa [lowWheelOthelloDowncrossTail, lowWheelOthelloDowncrossPivot] using
    (lowWheelOthelloParentToggleAt_explicitParent
      (q := q) (y := y) hp.pos)

/-- The moved state remains on the exact lightweight downcross carrier. -/
theorem lowWheelOthelloParentToggleAt_mem
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    lowWheelOthelloParentToggleAt q y ∈ lowWheelOthelloTaggedDowncrossCarrier R := by
  have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2
  have hsource := mem_lowWheelOthelloDowncrossPart.mp hx
  have hface := lowWheelOthelloParentToggleAt_face_mem hy hq
  have hphysical := lowWheelOthelloParentToggleAt_mem_physical hy hq
  have hpivot := lowWheelOthelloParentToggleAt_pivot hy hq
  apply mem_lowWheelOthelloTaggedDowncrossCarrier.mpr
  refine ⟨hface, mem_lowWheelOthelloDowncrossPart.mpr ⟨hphysical, ?_, ?_⟩⟩
  · change ¬ lowWheelOthelloDowncrossPivot
        (lowWheelOthelloParentToggleAt q y) ∣
        (lowWheelOthelloParentToggleAt q y).2.1
    rw [hpivot, lowWheelOthelloParentToggleAt_cofactor]
    exact hsource.2.1
  · change lowWheelOthelloDowncrossParent (lowWheelOthelloParentToggleAt q y) ≤ R
    rw [lowWheelOthelloParentToggleAt_parent hy hq]
    exact hsource.2.2

/-- A movable transfer is nontrivial. -/
theorem lowWheelOthelloParentToggleAt_ne
    {q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hq : LowWheelOthelloMovablePrime y q) :
    lowWheelOthelloParentToggleAt q y ≠ y := by
  intro heq
  have hfaceEq := congrArg Prod.fst heq
  unfold lowWheelOthelloParentToggleAt lowWheelOthelloFaceTail at hfaceEq
  dsimp at hfaceEq
  by_cases hqt : q ∈ y.1
  · simp only [lowWheelFaceTailToggleAt, hqt, if_true] at hfaceEq
    have hbad : q ∈ y.1.erase q := by
      rw [hfaceEq]
      exact hqt
    exact (Finset.notMem_erase q y.1) hbad
  · have htail : q ∣ lowWheelOthelloDowncrossTail y := hq.2.2.resolve_left hqt
    simp only [lowWheelFaceTailToggleAt, hqt, if_false, htail, if_true] at hfaceEq
    apply hqt
    rw [← hfaceEq]
    exact Finset.mem_insert_self q y.1

/-- The native signed weight reverses under every movable transfer. -/
theorem lowWheelOthelloParentToggleAt_weight_neg
    {q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hq : LowWheelOthelloMovablePrime y q) :
    canonicalMoebiusWeight (lowWheelOthelloParentToggleAt q y).2.1 *
        (booleanCubeSign (lowWheelOthelloParentToggleAt q y).1 : ℂ) =
      -(canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) := by
  rw [lowWheelOthelloParentToggleAt_cofactor]
  unfold lowWheelOthelloParentToggleAt lowWheelOthelloFaceTail
  dsimp
  exact lowWheelFaceTailToggleAt_weight_neg
    (canonicalMoebiusWeight y.2.1) hq.2.2

/-- Face/tail coordinates after moving are literally the fixed-q toggle. -/
theorem lowWheelOthelloFaceTail_parentToggleAt
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    lowWheelOthelloFaceTail (lowWheelOthelloParentToggleAt q y) =
      lowWheelFaceTailToggleAt q (lowWheelOthelloFaceTail y) := by
  have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2
  have hp := (lowWheelOthelloDowncrossPart_adjacent_shell hx).1
  have hpivot := lowWheelOthelloParentToggleAt_pivot hy hq
  let u := lowWheelFaceTailToggleAt q (lowWheelOthelloFaceTail y)
  have hdiv :
      (lowWheelOthelloDowncrossPivot y * u.2) /
          lowWheelOthelloDowncrossPivot y = u.2 := by
    simpa [Nat.mul_comm] using Nat.mul_div_left u.2 hp.pos
  apply Prod.ext
  · rfl
  · unfold lowWheelOthelloFaceTail lowWheelOthelloDowncrossTail
    rw [hpivot]
    change (lowWheelOthelloDowncrossPivot y * u.2) /
        lowWheelOthelloDowncrossPivot y = u.2
    exact hdiv

/-- Every prime has identical movable status at both endpoints. -/
theorem lowWheelOthelloParentToggleAt_movablePrime_iff
    {R q r : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    LowWheelOthelloMovablePrime (lowWheelOthelloParentToggleAt q y) r ↔
      LowWheelOthelloMovablePrime y r := by
  have hpivot := lowWheelOthelloParentToggleAt_pivot hy hq
  have hft := lowWheelOthelloFaceTail_parentToggleAt hy hq
  have hqactiveFT :
      q ∈ (lowWheelOthelloFaceTail y).1 ∨
        q ∣ (lowWheelOthelloFaceTail y).2 := by
    simpa [lowWheelOthelloFaceTail, lowWheelOthelloDowncrossTail] using hq.2.2
  constructor
  · rintro ⟨hrPrime, hpr, hactive⟩
    refine ⟨hrPrime, ?_, ?_⟩
    · rw [hpivot] at hpr
      exact hpr
    · have hsupp := lowWheelFaceTailToggleAt_prime_active_iff
        (x := lowWheelOthelloFaceTail y) hq.1 hrPrime hqactiveFT
      have hactive' :
          r ∈ (lowWheelOthelloFaceTail (lowWheelOthelloParentToggleAt q y)).1 ∨
            r ∣ (lowWheelOthelloFaceTail
              (lowWheelOthelloParentToggleAt q y)).2 := by
        simpa [lowWheelOthelloFaceTail, lowWheelOthelloDowncrossTail] using hactive
      rw [hft] at hactive'
      exact hsupp.mp hactive'
  · rintro ⟨hrPrime, hpr, hactive⟩
    refine ⟨hrPrime, ?_, ?_⟩
    · rw [hpivot]
      exact hpr
    · have hsupp := lowWheelFaceTailToggleAt_prime_active_iff
        (x := lowWheelOthelloFaceTail y) hq.1 hrPrime hqactiveFT
      have hactive' :
          r ∈ (lowWheelFaceTailToggleAt q (lowWheelOthelloFaceTail y)).1 ∨
            r ∣ (lowWheelFaceTailToggleAt q (lowWheelOthelloFaceTail y)).2 :=
        hsupp.mpr <| by
          simpa [lowWheelOthelloFaceTail, lowWheelOthelloDowncrossTail] using hactive
      rw [← hft] at hactive'
      simpa [lowWheelOthelloFaceTail, lowWheelOthelloDowncrossTail] using hactive'

/-- Finite set of all movable prime coordinates. -/
def lowWheelOthelloMovablePrimeSet
    (R : ℕ) (y : LowWheelOthelloTaggedDowncrossState) : Finset ℕ :=
  (primesUpTo R).filter fun q => LowWheelOthelloMovablePrime y q

@[simp] theorem mem_lowWheelOthelloMovablePrimeSet
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState} :
    q ∈ lowWheelOthelloMovablePrimeSet R y ↔
      q ∈ primesUpTo R ∧ LowWheelOthelloMovablePrime y q := by
  simp [lowWheelOthelloMovablePrimeSet]

/-- On an actual carrier state, the finite set is nonempty exactly when a
movable prime exists. -/
theorem lowWheelOthelloMovablePrimeSet_nonempty_iff
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R) :
    (lowWheelOthelloMovablePrimeSet R y).Nonempty ↔
      ∃ q, LowWheelOthelloMovablePrime y q := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, (mem_lowWheelOthelloMovablePrimeSet.mp hq).2⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, mem_lowWheelOthelloMovablePrimeSet.mpr
      ⟨lowWheelOthelloMovablePrime_mem_primesUpTo hy hq, hq⟩⟩

/-- The complete movable-prime set is invariant. -/
theorem lowWheelOthelloMovablePrimeSet_parentToggleAt
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    lowWheelOthelloMovablePrimeSet R (lowWheelOthelloParentToggleAt q y) =
      lowWheelOthelloMovablePrimeSet R y := by
  ext r
  simp only [mem_lowWheelOthelloMovablePrimeSet]
  constructor
  · rintro ⟨hr, hm⟩
    exact ⟨hr, (lowWheelOthelloParentToggleAt_movablePrime_iff hy hq).mp hm⟩
  · rintro ⟨hr, hm⟩
    exact ⟨hr, (lowWheelOthelloParentToggleAt_movablePrime_iff hy hq).mpr hm⟩

/-- Least movable prime, defaulting to one on a frozen state. -/
def lowWheelOthelloOppositePrime
    (R : ℕ) (y : LowWheelOthelloTaggedDowncrossState) : ℕ :=
  if h : (lowWheelOthelloMovablePrimeSet R y).Nonempty then
    (lowWheelOthelloMovablePrimeSet R y).min' h
  else 1

/-- The canonical opposite prime belongs to the candidate set. -/
theorem lowWheelOthelloOppositePrime_mem
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (h : (lowWheelOthelloMovablePrimeSet R y).Nonempty) :
    lowWheelOthelloOppositePrime R y ∈ lowWheelOthelloMovablePrimeSet R y := by
  unfold lowWheelOthelloOppositePrime
  rw [dif_pos h]
  exact Finset.min'_mem _ h

/-- The canonical opposite prime is prime and movable. -/
theorem lowWheelOthelloOppositePrime_data
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (h : (lowWheelOthelloMovablePrimeSet R y).Nonempty) :
    (lowWheelOthelloOppositePrime R y).Prime ∧
      LowWheelOthelloMovablePrime y (lowWheelOthelloOppositePrime R y) := by
  have hm := mem_lowWheelOthelloMovablePrimeSet.mp
    (lowWheelOthelloOppositePrime_mem h)
  exact ⟨hm.2.1, hm.2⟩

/-- The least movable prime is identical at the opposite endpoint. -/
theorem lowWheelOthelloOppositePrime_parentToggleAt
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    lowWheelOthelloOppositePrime R (lowWheelOthelloParentToggleAt q y) =
      lowWheelOthelloOppositePrime R y := by
  have hset := lowWheelOthelloMovablePrimeSet_parentToggleAt hy hq
  unfold lowWheelOthelloOppositePrime
  rw [hset]

end RHLean.Proof
