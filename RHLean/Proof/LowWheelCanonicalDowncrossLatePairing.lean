import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.LowWheelCanonicalDowncrossOwnership

/-!
# Canonical pairing of the late-parent downcross population

The `late` half of the canonical downcross ledger consists of first-failure
states whose invariant root-side parent

`a = P(t) * (k/p)`

still has a prime divisor at least the canonical pivot `p = minFac(c*k)`.

The canonical allocation coordinate is the largest prime divisor

`q = P⁺(a)`.

Because `a <= R`, this is an already-existing low-wheel coordinate.  The
late-parent condition implies `p <= q`.  If `q` is absent from the Boolean face,
primality forces it to divide `k/p`; if it is present, it can be moved from the
face into that quotient.  Thus `q` is the unique invariant coordinate for the
face/quotient allocation involution constructed below.

No magnitude or analytic estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

abbrev LowWheelCanonicalDowncrossTaggedState :=
  Finset ℕ × LowWheelCofactorQuotientState

def lowWheelCanonicalDowncrossStateUniverse
    (R : ℕ) : Finset LowWheelCofactorQuotientState :=
  (Finset.Ico 1 R).product (Finset.Icc 1 (squareRootEndpoint R))

def lowWheelCanonicalDowncrossLateTaggedCarrier
    (R : ℕ) : Finset LowWheelCanonicalDowncrossTaggedState :=
  ((primesUpTo R).powerset.product
      (lowWheelCanonicalDowncrossStateUniverse R)).filter fun y =>
    y.2 ∈ lowWheelCanonicalDowncrossLateParentPart R y.1

@[simp] theorem mem_lowWheelCanonicalDowncrossLateTaggedCarrier
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState} :
    y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R ↔
      y.1 ∈ (primesUpTo R).powerset ∧
        y.2 ∈ lowWheelCanonicalDowncrossStateUniverse R ∧
        y.2 ∈ lowWheelCanonicalDowncrossLateParentPart R y.1 := by
  simp [lowWheelCanonicalDowncrossLateTaggedCarrier, and_assoc]

def lowWheelCanonicalDowncrossTaggedParent
    (y : LowWheelCanonicalDowncrossTaggedState) : ℕ :=
  lowWheelCanonicalDowncrossParent y.1 y.2

def lowWheelCanonicalDowncrossLatePrime
    (y : LowWheelCanonicalDowncrossTaggedState) : ℕ :=
  canonicalLargestPrimeFactor (lowWheelCanonicalDowncrossTaggedParent y)

def lowWheelCanonicalDowncrossTaggedWeight
    (y : LowWheelCanonicalDowncrossTaggedState) : ℂ :=
  canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)

theorem lowWheelCanonicalDowncrossLate_parent_one_lt
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    1 < lowWheelCanonicalDowncrossTaggedParent y := by
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  have hdown :=
    (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
  rcases (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).2 with
    ⟨q, hq, _hpq⟩
  rcases Nat.mem_primeFactors.mp hq with ⟨hqPrime, hqDvd, _⟩
  have hparentPos := lowWheelCanonicalDowncrossParent_pos hdown
  have hqLe : q ≤ lowWheelCanonicalDowncrossTaggedParent y :=
    Nat.le_of_dvd hparentPos hqDvd
  exact lt_of_lt_of_le hqPrime.one_lt hqLe

theorem lowWheelCanonicalDowncrossLatePrime_prime
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    (lowWheelCanonicalDowncrossLatePrime y).Prime := by
  exact canonicalLargestPrimeFactor_prime
    (lowWheelCanonicalDowncrossLate_parent_one_lt hy)

theorem lowWheelCanonicalDowncrossLatePrime_dvd_parent
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossLatePrime y ∣
      lowWheelCanonicalDowncrossTaggedParent y := by
  exact canonicalLargestPrimeFactor_dvd
    (lowWheelCanonicalDowncrossLate_parent_one_lt hy)

theorem lowWheelCanonicalDowncrossLate_pivot_le_prime
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossPivot y.2 ≤
      lowWheelCanonicalDowncrossLatePrime y := by
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  rcases (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).2 with
    ⟨q, hq, hpq⟩
  rcases Nat.mem_primeFactors.mp hq with ⟨hqPrime, hqDvd, _⟩
  have hqLe : q ≤ lowWheelCanonicalDowncrossLatePrime y :=
    CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
      (lowWheelCanonicalDowncrossLate_parent_one_lt hy) hqPrime hqDvd
  exact hpq.trans hqLe

theorem lowWheelCanonicalDowncrossLatePrime_mem_primesUpTo
    {R : ℕ} {y : LowWheelCanonicalDowncrossTaggedState}
    (hy : y ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossLatePrime y ∈ primesUpTo R := by
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  have hdown :=
    (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hparentLe : lowWheelCanonicalDowncrossTaggedParent y ≤ R := hgeom.2.2.2.1
  have hparentPos := lowWheelCanonicalDowncrossParent_pos hdown
  have hprimeLeParent :
      lowWheelCanonicalDowncrossLatePrime y ≤
        lowWheelCanonicalDowncrossTaggedParent y :=
    Nat.le_of_dvd hparentPos
      (lowWheelCanonicalDowncrossLatePrime_dvd_parent hy)
  exact mem_primesUpTo.mpr
    ⟨lowWheelCanonicalDowncrossLatePrime_prime hy,
      hprimeLeParent.trans hparentLe⟩

theorem lowWheelCanonicalDowncrossLatePrime_dvd_quotient_of_not_mem_face
    {R : ℕ} {t : Finset ℕ} {c k : ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R)
    (hqt : lowWheelCanonicalDowncrossLatePrime (t, (c, k)) ∉ t) :
    lowWheelCanonicalDowncrossLatePrime (t, (c, k)) ∣
      k / lowWheelCanonicalDowncrossPivot (c, k) := by
  have ht :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).1
  have hqPrime := lowWheelCanonicalDowncrossLatePrime_prime hy
  have hqDvdParent := lowWheelCanonicalDowncrossLatePrime_dvd_parent hy
  unfold lowWheelCanonicalDowncrossTaggedParent at hqDvdParent
  unfold lowWheelCanonicalDowncrossParent at hqDvdParent
  rcases hqPrime.dvd_mul.mp hqDvdParent with hqFace | hqQuot
  · exfalso
    have hqProd : lowWheelCanonicalDowncrossLatePrime (t, (c, k)) ∣
        t.prod id := by
      simpa [primeFaceProduct] using hqFace
    rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqProd with
      ⟨r, hrt, hqr⟩
    have hrPrime : r.Prime :=
      prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hrt)
    have hqrEq : lowWheelCanonicalDowncrossLatePrime (t, (c, k)) = r :=
      (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
    exact hqt (hqrEq ▸ hrt)
  · exact hqQuot

theorem lowWheelCanonicalDowncrossLatePrime_dvd_quotient_of_not_mem_face'
    {R : ℕ} {t : Finset ℕ} {c k : ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R)
    (hqt : lowWheelCanonicalDowncrossLatePrime (t, (c, k)) ∉ t) :
    lowWheelCanonicalDowncrossLatePrime (t, (c, k)) ∣ k := by
  let p := lowWheelCanonicalDowncrossPivot (c, k)
  let q := lowWheelCanonicalDowncrossLatePrime (t, (c, k))
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  have hdown := (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hpk : p ∣ k := by simpa [p] using hgeom.2.2.1
  have hqu : q ∣ k / p := by
    simpa [p, q] using
      lowWheelCanonicalDowncrossLatePrime_dvd_quotient_of_not_mem_face hy hqt
  rcases hqu with ⟨u, hu⟩
  refine ⟨p * u, ?_⟩
  calc
    k = p * (k / p) := (Nat.mul_div_cancel' hpk).symm
    _ = p * (q * u) := by rw [hu]
    _ = q * (p * u) := by ring

def lowWheelCanonicalDowncrossLateMate
    (y : LowWheelCanonicalDowncrossTaggedState) :
    LowWheelCanonicalDowncrossTaggedState :=
  let q := lowWheelCanonicalDowncrossLatePrime y
  if q ∈ y.1 then
    (y.1.erase q, (y.2.1, q * y.2.2))
  else
    (insert q y.1, (y.2.1, y.2.2 / q))

theorem lowWheelCanonicalDowncrossLateMate_highProduct
    {R : ℕ} {t : Finset ℕ} {c k : ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    primeFaceProduct (lowWheelCanonicalDowncrossLateMate (t, (c, k))).1 *
        (lowWheelCanonicalDowncrossLateMate (t, (c, k))).2.2 =
      primeFaceProduct t * k := by
  let q := lowWheelCanonicalDowncrossLatePrime (t, (c, k))
  have hqPrime : q.Prime := by
    simpa [q] using lowWheelCanonicalDowncrossLatePrime_prime hy
  unfold lowWheelCanonicalDowncrossLateMate
  dsimp only
  by_cases hqt : q ∈ t
  · rw [if_pos hqt]
    have hface : q * primeFaceProduct (t.erase q) = primeFaceProduct t := by
      simpa [primeFaceProduct] using Finset.mul_prod_erase t id hqt
    calc
      primeFaceProduct (t.erase q) * (q * k) =
          (q * primeFaceProduct (t.erase q)) * k := by ring
      _ = primeFaceProduct t * k := by rw [hface]
  · rw [if_neg hqt]
    have hqk : q ∣ k := by
      simpa [q] using
        lowWheelCanonicalDowncrossLatePrime_dvd_quotient_of_not_mem_face'
          hy (by simpa [q] using hqt)
    have hkCancel : k / q * q = k := Nat.div_mul_cancel hqk
    have hface : primeFaceProduct (insert q t) = q * primeFaceProduct t := by
      simp [primeFaceProduct, hqt]
    calc
      primeFaceProduct (insert q t) * (k / q) =
          (q * primeFaceProduct t) * (k / q) := by rw [hface]
      _ = primeFaceProduct t * (k / q * q) := by ring
      _ = primeFaceProduct t * k := by rw [hkCancel]

private theorem minFac_eq_of_prime_dvd_and_le_prime_divisors
    {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hle : ∀ r, r.Prime → r ∣ n → p ≤ r) :
    Nat.minFac n = p := by
  have hminLe : Nat.minFac n ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le hpn
  have hn1 : n ≠ 1 := by
    intro hn
    have hp1 : p ∣ 1 := by simpa [hn] using hpn
    have hpEq : p = 1 := Nat.dvd_one.mp hp1
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hminPrime : (Nat.minFac n).Prime := Nat.minFac_prime hn1
  have hminDvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have hpLeMin : p ≤ Nat.minFac n := hle _ hminPrime hminDvd
  exact Nat.le_antisymm hminLe hpLeMin

theorem lowWheelCanonicalDowncrossLateMate_pivot_eq
    {R : ℕ} {t : Finset ℕ} {c k : ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossPivot
        (lowWheelCanonicalDowncrossLateMate (t, (c, k))).2 =
      lowWheelCanonicalDowncrossPivot (c, k) := by
  let p := lowWheelCanonicalDowncrossPivot (c, k)
  let q := lowWheelCanonicalDowncrossLatePrime (t, (c, k))
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  have hdown := (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hp : p.Prime := by simpa [p] using hgeom.1
  have hpk : p ∣ k := by simpa [p] using hgeom.2.2.1
  have hqPrime : q.Prime := by
    simpa [q] using lowWheelCanonicalDowncrossLatePrime_prime hy
  have hpq : p ≤ q := by
    simpa [p, q] using lowWheelCanonicalDowncrossLate_pivot_le_prime hy
  unfold lowWheelCanonicalDowncrossLateMate
  dsimp only
  by_cases hqt : q ∈ t
  · rw [if_pos hqt]
    change Nat.minFac (c * (q * k)) = p
    apply minFac_eq_of_prime_dvd_and_le_prime_divisors hp
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpk q) c
    · intro r hr hrd
      rcases hr.dvd_mul.mp hrd with hrc | hrqk
      · exact Nat.minFac_le_of_dvd hr.two_le
          (dvd_mul_of_dvd_left hrc k)
      · rcases hr.dvd_mul.mp hrqk with hrq | hrk
        · have hrEq : r = q :=
            (Nat.prime_dvd_prime_iff_eq hr hqPrime).mp hrq
          simpa [hrEq] using hpq
        · exact Nat.minFac_le_of_dvd hr.two_le
            (dvd_mul_of_dvd_right hrk c)
  · rw [if_neg hqt]
    have hqu : q ∣ k / p := by
      simpa [p, q] using
        lowWheelCanonicalDowncrossLatePrime_dvd_quotient_of_not_mem_face
          hy (by simpa [q] using hqt)
    rcases hqu with ⟨u, hu⟩
    have hkEq : k = q * (p * u) := by
      calc
        k = p * (k / p) := (Nat.mul_div_cancel' hpk).symm
        _ = p * (q * u) := by rw [hu]
        _ = q * (p * u) := by ring
    have hkDivEq : k / q = p * u := by
      rw [hkEq]
      simp [hqPrime.ne_zero]
    change Nat.minFac (c * (k / q)) = p
    apply minFac_eq_of_prime_dvd_and_le_prime_divisors hp
    · exact dvd_mul_of_dvd_right ⟨u, hkDivEq⟩ c
    · intro r hr hrd
      rcases hr.dvd_mul.mp hrd with hrc | hrdiv
      · exact Nat.minFac_le_of_dvd hr.two_le
          (dvd_mul_of_dvd_left hrc k)
      · have hrk : r ∣ k := by
          rw [hkEq]
          rw [hkDivEq] at hrdiv
          exact dvd_mul_of_dvd_right hrdiv q
        exact Nat.minFac_le_of_dvd hr.two_le
          (dvd_mul_of_dvd_right hrk c)

end RHLean.Proof