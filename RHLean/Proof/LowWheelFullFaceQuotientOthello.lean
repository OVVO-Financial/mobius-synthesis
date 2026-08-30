import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.LowWheelCanonicalPairingFrontier
import RHLean.Proof.LowWheelFaceTailActiveSupport

/-!
# Full physical face/quotient Othello involution

The square-root transport has a second exact coordinate direction already on
the complete tagged physical carrier.  For one low prime `q`, move `q` between

* the Boolean face `t`, and
* the whole high quotient `k`.

The product `P(t)*k` is invariant, so both square-root inequalities and the
complete physical product are unchanged.  The cofactor is unchanged and the
Boolean sign reverses.  Choosing the least active low prime produces one
state-dependent involution because active prime support is invariant under its
own transfer.

A stable state has no active prime at all.  Consequently its Boolean face is
empty and its quotient survives divisibility by every prime at most `R`.  This
is the exact top-coordinate endpoint of the second Othello direction.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

abbrev LowWheelFullTaggedPhysicalState :=
  Finset ℕ × LowWheelCofactorQuotientState

/-- The complete physical transport carrier with the Boolean face retained as
an occurrence tag. -/
def lowWheelFullTaggedPhysicalCarrier
    (R : ℕ) : Finset LowWheelFullTaggedPhysicalState := by
  classical
  exact (primesUpTo R).powerset.biUnion fun t =>
    (lowWheelCanonicalPhysicalStateSet R t).image fun x => (t, x)

@[simp] theorem mem_lowWheelFullTaggedPhysicalCarrier
    {R : ℕ} {y : LowWheelFullTaggedPhysicalState} :
    y ∈ lowWheelFullTaggedPhysicalCarrier R ↔
      y.1 ∈ (primesUpTo R).powerset ∧
        y.2 ∈ lowWheelCanonicalPhysicalStateSet R y.1 := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_biUnion.mp hy with ⟨t, ht, hy⟩
    rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
    subst y
    exact ⟨ht, hx⟩
  · intro hy
    rcases hy with ⟨ht, hx⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨y.1, ht, ?_⟩
    exact Finset.mem_image.mpr ⟨y.2, hx, Prod.ext rfl rfl⟩

/-- Native signed weight on the tagged physical carrier. -/
def lowWheelFullTaggedPhysicalWeight
    (y : LowWheelFullTaggedPhysicalState) : ℂ :=
  canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)

/-- Transfer one prime between the face and the whole quotient, leaving the
cofactor untouched. -/
def lowWheelFullFaceQuotientToggleAt
    (q : ℕ) (y : LowWheelFullTaggedPhysicalState) :
    LowWheelFullTaggedPhysicalState :=
  let u := lowWheelFaceTailToggleAt q (y.1, y.2.2)
  (u.1, (y.2.1, u.2))

@[simp] theorem lowWheelFullFaceQuotientToggleAt_cofactor
    (q : ℕ) (y : LowWheelFullTaggedPhysicalState) :
    (lowWheelFullFaceQuotientToggleAt q y).2.1 = y.2.1 := by
  rfl

/-- The high coordinate `P(t)*k` is exactly invariant. -/
theorem lowWheelFullFaceQuotientToggleAt_highProduct
    (q : ℕ) (y : LowWheelFullTaggedPhysicalState) :
    primeFaceProduct (lowWheelFullFaceQuotientToggleAt q y).1 *
        (lowWheelFullFaceQuotientToggleAt q y).2.2 =
      primeFaceProduct y.1 * y.2.2 := by
  simpa [lowWheelFullFaceQuotientToggleAt] using
    (lowWheelFaceTailToggleAt_product q (y.1, y.2.2))

/-- A fixed low-prime transfer keeps the Boolean face inside the same low-prime
universe. -/
theorem lowWheelFullFaceQuotientToggleAt_face_mem
    {R q : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hy : y ∈ lowWheelFullTaggedPhysicalCarrier R)
    (hqGlobal : q ∈ primesUpTo R)
    (hactive : q ∈ y.1 ∨ q ∣ y.2.2) :
    (lowWheelFullFaceQuotientToggleAt q y).1 ∈
      (primesUpTo R).powerset := by
  have ht := (mem_lowWheelFullTaggedPhysicalCarrier.mp hy).1
  unfold lowWheelFullFaceQuotientToggleAt
  dsimp
  unfold lowWheelFaceTailToggleAt
  by_cases hqt : q ∈ y.1
  · simp only [hqt, if_true]
    exact Finset.mem_powerset.mpr
      ((Finset.erase_subset q y.1).trans (Finset.mem_powerset.mp ht))
  · have hqk : q ∣ y.2.2 := hactive.resolve_left hqt
    simp only [hqt, if_false, hqk, if_true]
    apply Finset.mem_powerset.mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hqGlobal
    · exact (Finset.mem_powerset.mp ht) hr

/-- The fixed-prime face/quotient move preserves all physical transport
inequalities. -/
theorem lowWheelFullFaceQuotientToggleAt_physicalCarrier
    {R q : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hy : y ∈ lowWheelFullTaggedPhysicalCarrier R) :
    LowWheelTransportPairCarrier R
      (lowWheelFullFaceQuotientToggleAt q y).1
      (lowWheelFullFaceQuotientToggleAt q y).2 := by
  have hx := (mem_lowWheelFullTaggedPhysicalCarrier.mp hy).2
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hx).2.2.2
  rcases hcarrier with ⟨hc1, hcR, hhigh, htop⟩
  have hprod := lowWheelFullFaceQuotientToggleAt_highProduct q y
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hc1
  · simpa using hcR
  · rw [hprod]
    exact hhigh
  · rw [lowWheelFullFaceQuotientToggleAt_cofactor]
    calc
      y.2.1 * primeFaceProduct (lowWheelFullFaceQuotientToggleAt q y).1 *
          (lowWheelFullFaceQuotientToggleAt q y).2.2 =
        y.2.1 *
          (primeFaceProduct (lowWheelFullFaceQuotientToggleAt q y).1 *
            (lowWheelFullFaceQuotientToggleAt q y).2.2) := by ring
      _ = y.2.1 * (primeFaceProduct y.1 * y.2.2) := by rw [hprod]
      _ = (y.2.1 * primeFaceProduct y.1) * y.2.2 := by ring
      _ ≤ squareRootEndpoint R := htop

/-- Every active fixed-prime face/quotient transfer stays in the complete finite
physical carrier. -/
theorem lowWheelFullFaceQuotientToggleAt_mem
    {R q : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hy : y ∈ lowWheelFullTaggedPhysicalCarrier R)
    (hqGlobal : q ∈ primesUpTo R)
    (hactive : q ∈ y.1 ∨ q ∣ y.2.2) :
    lowWheelFullFaceQuotientToggleAt q y ∈
      lowWheelFullTaggedPhysicalCarrier R := by
  have hface := lowWheelFullFaceQuotientToggleAt_face_mem hy hqGlobal hactive
  have hcarrier := lowWheelFullFaceQuotientToggleAt_physicalCarrier (q := q) hy
  have hrange := lowWheelTransportPairCarrier_mem_ranges hcarrier
  have hx := (mem_lowWheelFullTaggedPhysicalCarrier.mp hy).2
  have hsq := (mem_lowWheelCanonicalPhysicalStateSet.mp hx).2.2.1
  apply mem_lowWheelFullTaggedPhysicalCarrier.mpr
  refine ⟨hface, mem_lowWheelCanonicalPhysicalStateSet.mpr ?_⟩
  exact ⟨hrange.1, hrange.2, by simpa using hsq, hcarrier⟩

/-- A genuinely active fixed-prime transfer is nontrivial. -/
theorem lowWheelFullFaceQuotientToggleAt_ne
    {q : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hactive : q ∈ y.1 ∨ q ∣ y.2.2) :
    lowWheelFullFaceQuotientToggleAt q y ≠ y := by
  intro heq
  have hfaceEq := congrArg Prod.fst heq
  unfold lowWheelFullFaceQuotientToggleAt at hfaceEq
  dsimp at hfaceEq
  by_cases hqt : q ∈ y.1
  · simp only [lowWheelFaceTailToggleAt, hqt, if_true] at hfaceEq
    have hbad : q ∈ y.1.erase q := by
      rw [hfaceEq]
      exact hqt
    exact (Finset.notMem_erase q y.1) hbad
  · have hqk : q ∣ y.2.2 := hactive.resolve_left hqt
    simp only [lowWheelFaceTailToggleAt, hqt, if_false, hqk, if_true] at hfaceEq
    apply hqt
    rw [← hfaceEq]
    exact Finset.mem_insert_self q y.1

/-- A fixed active prime transfer is involutive. -/
theorem lowWheelFullFaceQuotientToggleAt_involutive
    {q : ℕ} (hq : q.Prime) (y : LowWheelFullTaggedPhysicalState) :
    lowWheelFullFaceQuotientToggleAt q
        (lowWheelFullFaceQuotientToggleAt q y) = y := by
  have hft := lowWheelFaceTailToggleAt_involutive hq.pos (y.1, y.2.2)
  unfold lowWheelFullFaceQuotientToggleAt
  dsimp
  have hface :
      (lowWheelFaceTailToggleAt q
        (lowWheelFaceTailToggleAt q (y.1, y.2.2))).1 = y.1 :=
    congrArg (fun z : LowWheelFaceTailState => z.1) hft
  have hquot :
      (lowWheelFaceTailToggleAt q
        (lowWheelFaceTailToggleAt q (y.1, y.2.2))).2 = y.2.2 :=
    congrArg (fun z : LowWheelFaceTailState => z.2) hft
  exact Prod.ext hface (Prod.ext rfl hquot)

/-- Every active fixed-prime transfer reverses the tagged physical weight. -/
theorem lowWheelFullFaceQuotientToggleAt_weight_neg
    {q : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hactive : q ∈ y.1 ∨ q ∣ y.2.2) :
    lowWheelFullTaggedPhysicalWeight
        (lowWheelFullFaceQuotientToggleAt q y) =
      -lowWheelFullTaggedPhysicalWeight y := by
  unfold lowWheelFullTaggedPhysicalWeight
  rw [lowWheelFullFaceQuotientToggleAt_cofactor]
  unfold lowWheelFullFaceQuotientToggleAt
  dsimp
  exact lowWheelFaceTailToggleAt_weight_neg
    (canonicalMoebiusWeight y.2.1) hactive

/-- All active low-prime coordinates on one full physical occurrence. -/
def lowWheelFullActivePrimeSet
    (R : ℕ) (y : LowWheelFullTaggedPhysicalState) : Finset ℕ :=
  (primesUpTo R).filter fun q => q ∈ y.1 ∨ q ∣ y.2.2

@[simp] theorem mem_lowWheelFullActivePrimeSet
    {R q : ℕ} {y : LowWheelFullTaggedPhysicalState} :
    q ∈ lowWheelFullActivePrimeSet R y ↔
      q ∈ primesUpTo R ∧ (q ∈ y.1 ∨ q ∣ y.2.2) := by
  simp [lowWheelFullActivePrimeSet]

/-- The whole active-prime set is invariant under any active fixed-prime
transfer. -/
theorem lowWheelFullActivePrimeSet_toggleAt
    {R q : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hqGlobal : q ∈ primesUpTo R)
    (hactive : q ∈ y.1 ∨ q ∣ y.2.2) :
    lowWheelFullActivePrimeSet R (lowWheelFullFaceQuotientToggleAt q y) =
      lowWheelFullActivePrimeSet R y := by
  have hqPrime := prime_of_mem_primesUpTo hqGlobal
  ext r
  simp only [mem_lowWheelFullActivePrimeSet]
  constructor
  · rintro ⟨hrGlobal, hrActive⟩
    have hrPrime := prime_of_mem_primesUpTo hrGlobal
    have hsupp := lowWheelFaceTailToggleAt_prime_active_iff
      (x := (y.1, y.2.2)) hqPrime hrPrime hactive
    exact ⟨hrGlobal, hsupp.mp (by simpa [lowWheelFullFaceQuotientToggleAt] using hrActive)⟩
  · rintro ⟨hrGlobal, hrActive⟩
    have hrPrime := prime_of_mem_primesUpTo hrGlobal
    have hsupp := lowWheelFaceTailToggleAt_prime_active_iff
      (x := (y.1, y.2.2)) hqPrime hrPrime hactive
    exact ⟨hrGlobal, by
      simpa [lowWheelFullFaceQuotientToggleAt] using hsupp.mpr hrActive⟩

/-- Least active low prime, with irrelevant default one at a stable state. -/
def lowWheelFullOppositePrime
    (R : ℕ) (y : LowWheelFullTaggedPhysicalState) : ℕ :=
  if h : (lowWheelFullActivePrimeSet R y).Nonempty then
    (lowWheelFullActivePrimeSet R y).min' h
  else 1

/-- The selected opposite prime is a genuine active low prime. -/
theorem lowWheelFullOppositePrime_data
    {R : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (h : (lowWheelFullActivePrimeSet R y).Nonempty) :
    lowWheelFullOppositePrime R y ∈ primesUpTo R ∧
      (lowWheelFullOppositePrime R y ∈ y.1 ∨
        lowWheelFullOppositePrime R y ∣ y.2.2) := by
  unfold lowWheelFullOppositePrime
  rw [dif_pos h]
  exact mem_lowWheelFullActivePrimeSet.mp (Finset.min'_mem _ h)

/-- Because active support is invariant, the least active prime is the same at
both endpoints. -/
theorem lowWheelFullOppositePrime_toggleAt
    {R q : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hqGlobal : q ∈ primesUpTo R)
    (hactive : q ∈ y.1 ∨ q ∣ y.2.2) :
    lowWheelFullOppositePrime R (lowWheelFullFaceQuotientToggleAt q y) =
      lowWheelFullOppositePrime R y := by
  have hset := lowWheelFullActivePrimeSet_toggleAt
    (R := R) hqGlobal hactive
  unfold lowWheelFullOppositePrime
  rw [hset]

/-- Total state-dependent second Othello mate on the complete physical carrier. -/
def lowWheelFullFaceQuotientMate
    (R : ℕ) (y : LowWheelFullTaggedPhysicalState) :
    LowWheelFullTaggedPhysicalState :=
  if _h : (lowWheelFullActivePrimeSet R y).Nonempty then
    lowWheelFullFaceQuotientToggleAt (lowWheelFullOppositePrime R y) y
  else y

/-- The total second mate preserves the complete physical carrier. -/
theorem lowWheelFullFaceQuotientMate_mem
    {R : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hy : y ∈ lowWheelFullTaggedPhysicalCarrier R) :
    lowWheelFullFaceQuotientMate R y ∈ lowWheelFullTaggedPhysicalCarrier R := by
  unfold lowWheelFullFaceQuotientMate
  by_cases h : (lowWheelFullActivePrimeSet R y).Nonempty
  · rw [dif_pos h]
    have hq := lowWheelFullOppositePrime_data h
    exact lowWheelFullFaceQuotientToggleAt_mem hy hq.1 hq.2
  · rw [dif_neg h]
    exact hy

/-- The total second mate is involutive on the complete physical carrier. -/
theorem lowWheelFullFaceQuotientMate_involutive
    {R : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (_hy : y ∈ lowWheelFullTaggedPhysicalCarrier R) :
    lowWheelFullFaceQuotientMate R (lowWheelFullFaceQuotientMate R y) = y := by
  unfold lowWheelFullFaceQuotientMate
  by_cases h : (lowWheelFullActivePrimeSet R y).Nonempty
  · rw [dif_pos h]
    let q := lowWheelFullOppositePrime R y
    have hq := lowWheelFullOppositePrime_data h
    have hset := lowWheelFullActivePrimeSet_toggleAt
      (R := R) hq.1 hq.2
    have htarget :
        (lowWheelFullActivePrimeSet R
          (lowWheelFullFaceQuotientToggleAt q y)).Nonempty := by
      rw [hset]
      exact h
    rw [dif_pos htarget]
    have hqSame := lowWheelFullOppositePrime_toggleAt
      (R := R) hq.1 hq.2
    rw [hqSame]
    exact lowWheelFullFaceQuotientToggleAt_involutive
      (prime_of_mem_primesUpTo hq.1) y
  · rw [dif_neg h, dif_neg h]

/-- Every moved second-Othello edge reverses signed weight. -/
theorem lowWheelFullFaceQuotientMate_weight_neg
    {R : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hne : lowWheelFullFaceQuotientMate R y ≠ y) :
    lowWheelFullTaggedPhysicalWeight (lowWheelFullFaceQuotientMate R y) =
      -lowWheelFullTaggedPhysicalWeight y := by
  unfold lowWheelFullFaceQuotientMate at hne ⊢
  by_cases h : (lowWheelFullActivePrimeSet R y).Nonempty
  · rw [dif_pos h] at hne ⊢
    exact lowWheelFullFaceQuotientToggleAt_weight_neg
      (lowWheelFullOppositePrime_data h).2
  · rw [dif_neg h] at hne
    exact (hne rfl).elim

/-- A stable full-carrier state has empty Boolean face. -/
theorem lowWheelFullStable_face_eq_empty
    {R : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hy : y ∈ lowWheelFullTaggedPhysicalCarrier R)
    (hstable : lowWheelFullFaceQuotientMate R y = y) :
    y.1 = ∅ := by
  have hnone : ¬ (lowWheelFullActivePrimeSet R y).Nonempty := by
    intro h
    unfold lowWheelFullFaceQuotientMate at hstable
    rw [dif_pos h] at hstable
    exact lowWheelFullFaceQuotientToggleAt_ne
      (lowWheelFullOppositePrime_data h).2 hstable
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hqt
  have ht := (mem_lowWheelFullTaggedPhysicalCarrier.mp hy).1
  have hqGlobal := (Finset.mem_powerset.mp ht) hqt
  apply hnone
  exact ⟨q, mem_lowWheelFullActivePrimeSet.mpr
    ⟨hqGlobal, Or.inl hqt⟩⟩

/-- A stable full-carrier quotient survives every low-prime divisibility
coordinate. -/
theorem lowWheelFullStable_survivor
    {R : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hstable : lowWheelFullFaceQuotientMate R y = y) :
    ∀ q ∈ primesUpTo R, ¬ q ∣ y.2.2 := by
  have hnone : ¬ (lowWheelFullActivePrimeSet R y).Nonempty := by
    intro h
    unfold lowWheelFullFaceQuotientMate at hstable
    rw [dif_pos h] at hstable
    exact lowWheelFullFaceQuotientToggleAt_ne
      (lowWheelFullOppositePrime_data h).2 hstable
  intro q hqGlobal hqDvd
  apply hnone
  exact ⟨q, mem_lowWheelFullActivePrimeSet.mpr
    ⟨hqGlobal, Or.inr hqDvd⟩⟩

/-- Stable geometry is exactly an empty face with a high low-wheel-surviving
quotient inside the square endpoint. -/
theorem lowWheelFullStable_geometry
    {R : ℕ} {y : LowWheelFullTaggedPhysicalState}
    (hy : y ∈ lowWheelFullTaggedPhysicalCarrier R)
    (hstable : lowWheelFullFaceQuotientMate R y = y) :
    y.1 = ∅ ∧ R < y.2.2 ∧ y.2.2 ≤ squareRootEndpoint R ∧
      (∀ q ∈ primesUpTo R, ¬ q ∣ y.2.2) := by
  have hface := lowWheelFullStable_face_eq_empty hy hstable
  have hx := (mem_lowWheelFullTaggedPhysicalCarrier.mp hy).2
  have hdata := mem_lowWheelCanonicalPhysicalStateSet.mp hx
  have hcarrier := hdata.2.2.2
  have hhigh := hcarrier.2.2.1
  have hqX := (Finset.mem_Icc.mp hdata.2.1).2
  have hsurv := lowWheelFullStable_survivor hstable
  have hhigh' : R < y.2.2 := by
    rw [hface] at hhigh
    simpa [primeFaceProduct] using hhigh
  exact ⟨hface, hhigh', hqX, hsurv⟩

end RHLean.Proof
