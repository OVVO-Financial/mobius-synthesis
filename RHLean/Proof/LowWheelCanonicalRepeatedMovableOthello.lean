import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification
import RHLean.Proof.LowWheelCanonicalDowncrossSignedParentSplit
import RHLean.Proof.LowWheelFaceTailToggle

/-!
# Canonical opposite move on repeated downcross parent fibres

A repeated canonical downcross state carries the root-side parent

`n = P(t) * (k / p)`

with `p = minFac(c*k)`.  The movable-prime condition from
`LowWheelCanonicalRepeatedParentClassification` can be made canonical without
choosing an arbitrary local coordinate: collect exactly the prime divisors
`q >= p` of the invariant parent `n`, and take the least one.

On a genuine downcross state this set is equivalent to the existing
`LowWheelDowncrossMovablePrime` predicate.  Hence it is nonempty precisely on
the movable repeated-parent population.  More importantly, because it depends
only on the canonical pivot and the parent integer, it will be unchanged by
the product-preserving face/tail toggle.  This is the canonicality needed for a
genuine second Othello involution.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Prime coordinates available to the opposite move, expressed only through
the invariant canonical pivot and root-side parent. -/
def lowWheelCanonicalDowncrossMovablePrimeSet
    (R : ℕ) (y : LowWheelTaggedDowncrossState) : Finset ℕ :=
  (primesUpTo R).filter fun q =>
    lowWheelTaggedDowncrossPivot y ≤ q ∧
      q ∣ lowWheelCanonicalDowncrossParent y

@[simp] theorem mem_lowWheelCanonicalDowncrossMovablePrimeSet
    {R q : ℕ} {y : LowWheelTaggedDowncrossState} :
    q ∈ lowWheelCanonicalDowncrossMovablePrimeSet R y ↔
      q ∈ primesUpTo R ∧
        lowWheelTaggedDowncrossPivot y ≤ q ∧
        q ∣ lowWheelCanonicalDowncrossParent y := by
  simp [lowWheelCanonicalDowncrossMovablePrimeSet, and_assoc]

private theorem prime_mem_face_of_dvd_primeFaceProduct
    {R q : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset)
    (hq : q.Prime)
    (hdiv : q ∣ primeFaceProduct t) :
    q ∈ t := by
  change q ∣ t.prod id at hdiv
  rcases (Prime.dvd_finset_prod_iff hq.prime id).mp hdiv with
    ⟨r, hrt, hqr⟩
  have hrPrime : r.Prime :=
    prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hrt)
  have hqrEq : q = r :=
    (Nat.prime_dvd_prime_iff_eq hq hrPrime).mp hqr
  simpa [hqrEq] using hrt

/-- Every previously-classified movable coordinate belongs to the invariant
parent-divisor candidate set. -/
theorem lowWheelDowncrossMovablePrime_mem_candidateSet
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    q ∈ lowWheelCanonicalDowncrossMovablePrimeSet R y := by
  have hdiv : q ∣ lowWheelCanonicalDowncrossParent y := by
    rcases hq.2.2 with hface | htail
    · have hfaceDvd : q ∣ primeFaceProduct y.1 := by
        change q ∣ y.1.prod id
        exact Finset.dvd_prod_of_mem id hface
      unfold lowWheelCanonicalDowncrossParent
      exact dvd_mul_of_dvd_left hfaceDvd _
    · unfold lowWheelCanonicalDowncrossParent
      exact dvd_mul_of_dvd_right htail _
  have hparentPos : 0 < lowWheelCanonicalDowncrossParent y :=
    lowWheelCanonicalDowncrossParent_pos hy
  have hqParent : q ≤ lowWheelCanonicalDowncrossParent y :=
    Nat.le_of_dvd hparentPos hdiv
  have hqR : q ≤ R :=
    hqParent.trans (lowWheelCanonicalDowncrossParent_le_root hy)
  apply mem_lowWheelCanonicalDowncrossMovablePrimeSet.mpr
  exact ⟨mem_primesUpTo.mpr ⟨hq.1, hqR⟩, hq.2.1, hdiv⟩

/-- Conversely, every invariant parent-divisor candidate is an actual
face/quotient movable prime on a genuine downcross state. -/
theorem lowWheelDowncrossMovablePrime_of_mem_candidateSet
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : q ∈ lowWheelCanonicalDowncrossMovablePrimeSet R y) :
    LowWheelDowncrossMovablePrime y q := by
  rcases mem_lowWheelCanonicalDowncrossMovablePrimeSet.mp hq with
    ⟨hqR, hpq, hqParent⟩
  have hqPrime : q.Prime := prime_of_mem_primesUpTo hqR
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨ht, _hx⟩
  unfold lowWheelCanonicalDowncrossParent at hqParent
  rcases hqPrime.dvd_mul.mp hqParent with hfaceDvd | htail
  · exact ⟨hqPrime, hpq,
      Or.inl (prime_mem_face_of_dvd_primeFaceProduct ht hqPrime hfaceDvd)⟩
  · exact ⟨hqPrime, hpq, Or.inr htail⟩

/-- On the tagged downcross carrier, the invariant candidate set is nonempty
exactly when the arithmetic movable-prime predicate is inhabited. -/
theorem lowWheelCanonicalDowncrossMovablePrimeSet_nonempty_iff
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R) :
    (lowWheelCanonicalDowncrossMovablePrimeSet R y).Nonempty ↔
      ∃ q, LowWheelDowncrossMovablePrime y q := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, lowWheelDowncrossMovablePrime_of_mem_candidateSet hy hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, lowWheelDowncrossMovablePrime_mem_candidateSet hy hq⟩

/-- Canonical opposite coordinate: the least prime divisor of the invariant
parent that is no smaller than the canonical pivot.  It is arbitrary only off
the movable carrier, where the mate will never use it. -/
noncomputable def lowWheelCanonicalDowncrossMover
    (R : ℕ) (y : LowWheelTaggedDowncrossState) : ℕ :=
  if h : (lowWheelCanonicalDowncrossMovablePrimeSet R y).Nonempty then
    (lowWheelCanonicalDowncrossMovablePrimeSet R y).min' h
  else
    1

/-- The canonical mover is an actual candidate on every movable repeated state. -/
theorem lowWheelCanonicalDowncrossMover_mem
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedMovablePart R) :
    lowWheelCanonicalDowncrossMover R y ∈
      lowWheelCanonicalDowncrossMovablePrimeSet R y := by
  have hyRepeated := (Finset.mem_filter.mp hy).1
  have hyCarrier := (Finset.mem_filter.mp hyRepeated).1
  have hmov := (Finset.mem_filter.mp hy).2
  have hnonempty :
      (lowWheelCanonicalDowncrossMovablePrimeSet R y).Nonempty :=
    (lowWheelCanonicalDowncrossMovablePrimeSet_nonempty_iff hyCarrier).2 hmov
  unfold lowWheelCanonicalDowncrossMover
  rw [dif_pos hnonempty]
  exact Finset.min'_mem _ hnonempty

/-- Hence the canonical mover satisfies the original arithmetic movable-prime
predicate. -/
theorem lowWheelCanonicalDowncrossMover_movable
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedMovablePart R) :
    LowWheelDowncrossMovablePrime y
      (lowWheelCanonicalDowncrossMover R y) := by
  have hyRepeated := (Finset.mem_filter.mp hy).1
  have hyCarrier := (Finset.mem_filter.mp hyRepeated).1
  exact lowWheelDowncrossMovablePrime_of_mem_candidateSet hyCarrier
    (lowWheelCanonicalDowncrossMover_mem hy)

end RHLean.Proof
