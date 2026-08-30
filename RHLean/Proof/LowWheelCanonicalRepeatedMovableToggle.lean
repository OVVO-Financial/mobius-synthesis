import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedMovableOthello

/-!
# Lift the face/tail toggle to canonical downcross states

For a tagged downcross state `y = (t,(c,k))`, put

`p = minFac(c*k)` and `m = k/p`.

A movable coordinate `q >= p` is transferred between `t` and `m`, after which
we reconstruct the quotient as `p*m'`.  The explicit leading copy of `p`
ensures that the canonical least-prime pivot survives the move, while the
face/tail product theorem preserves

`P(t)*m = lowWheelCanonicalDowncrossParent y`.

Thus this is a sign-reversing move on the same root-side parent fibre, not a
reindexing to a different carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Lift a fixed face/tail coordinate transfer back to a tagged downcross state. -/
def lowWheelTaggedDowncrossFaceTailToggleAt
    (q : ℕ) (y : LowWheelTaggedDowncrossState) :
    LowWheelTaggedDowncrossState :=
  let p := lowWheelTaggedDowncrossPivot y
  let z := lowWheelFaceTailToggleAt q (y.1, y.2.2 / p)
  (z.1, (y.2.1, p * z.2))

@[simp] theorem lowWheelTaggedDowncrossFaceTailToggleAt_cofactor
    (q : ℕ) (y : LowWheelTaggedDowncrossState) :
    (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 = y.2.1 := by
  rfl

/-- The original pivot is visibly retained as a divisor of the reconstructed
quotient. -/
theorem lowWheelTaggedDowncrossPivot_dvd_toggledQuotient
    (q : ℕ) (y : LowWheelTaggedDowncrossState) :
    lowWheelTaggedDowncrossPivot y ∣
      (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 := by
  unfold lowWheelTaggedDowncrossFaceTailToggleAt
  exact dvd_mul_right _ _

/-- If `q` is moved out of the face, the new cofactor/quotient product is `q`
times the old product with `k` expanded as `p*(k/p)`. -/
private theorem lowWheelTaggedDowncrossFaceTailToggleAt_product_of_face
    {q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hqt : q ∈ y.1) :
    (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 =
      q * (y.2.1 *
        (lowWheelTaggedDowncrossPivot y *
          (y.2.2 / lowWheelTaggedDowncrossPivot y))) := by
  simp [lowWheelTaggedDowncrossFaceTailToggleAt,
    lowWheelFaceTailToggleAt, hqt]
  ring

/-- If `q` is moved from the tail into the face, multiplying the new
cofactor/quotient product by `q` recovers the expanded old product. -/
private theorem lowWheelTaggedDowncrossFaceTailToggleAt_product_of_tail
    {q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hqt : q ∉ y.1)
    (hqm : q ∣ y.2.2 / lowWheelTaggedDowncrossPivot y) :
    q * ((lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2) =
      y.2.1 *
        (lowWheelTaggedDowncrossPivot y *
          (y.2.2 / lowWheelTaggedDowncrossPivot y)) := by
  have hcancel :
      q * ((y.2.2 / lowWheelTaggedDowncrossPivot y) / q) =
        y.2.2 / lowWheelTaggedDowncrossPivot y :=
    Nat.mul_div_cancel' hqm
  simp only [lowWheelTaggedDowncrossFaceTailToggleAt,
    lowWheelFaceTailToggleAt, hqt, if_false, hqm, if_true]
  calc
    q * (y.2.1 *
        (lowWheelTaggedDowncrossPivot y *
          ((y.2.2 / lowWheelTaggedDowncrossPivot y) / q))) =
      y.2.1 *
        (lowWheelTaggedDowncrossPivot y *
          (q * ((y.2.2 / lowWheelTaggedDowncrossPivot y) / q))) := by ring
    _ = y.2.1 *
        (lowWheelTaggedDowncrossPivot y *
          (y.2.2 / lowWheelTaggedDowncrossPivot y)) := by rw [hcancel]

private theorem minFac_eq_of_prime_dvd_minimal
    {N p : ℕ}
    (hp : p.Prime)
    (hpd : p ∣ N)
    (hmin : ∀ r : ℕ, r.Prime → r ∣ N → p ≤ r) :
    Nat.minFac N = p := by
  have hNne : N ≠ 1 := by
    intro hN
    rw [hN] at hpd
    exact hp.not_dvd_one hpd
  have hminFacPrime : (Nat.minFac N).Prime := Nat.minFac_prime hNne
  have hminFacDvd : Nat.minFac N ∣ N := Nat.minFac_dvd N
  have hle : Nat.minFac N ≤ p := Nat.minFac_le_of_dvd hp.two_le hpd
  have hge : p ≤ Nat.minFac N := hmin _ hminFacPrime hminFacDvd
  omega

/-- **Pivot invariance of the opposite move.**  On a genuine movable downcross
state, transferring any legal `q >= p` between face and tail leaves the
canonical least-prime pivot equal to `p`. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_pivot
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelTaggedDowncrossPivot
        (lowWheelTaggedDowncrossFaceTailToggleAt q y) =
      lowWheelTaggedDowncrossPivot y := by
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨_ht, hx⟩
  rcases lowWheelCanonicalDowncrossPart_adjacent_shell hx with
    ⟨hpRaw, _hpc, hpkRaw, _hdown, _hup⟩
  let p := lowWheelTaggedDowncrossPivot y
  have hp : p.Prime := by
    simpa [p, lowWheelTaggedDowncrossPivot] using hpRaw
  have hpk : p ∣ y.2.2 := by
    simpa [p, lowWheelTaggedDowncrossPivot] using hpkRaw
  have hexpand :
      y.2.1 * (p * (y.2.2 / p)) = y.2.1 * y.2.2 := by
    rw [Nat.mul_div_cancel' hpk]
  have hpDvdOrig : p ∣ y.2.1 * y.2.2 := by
    simpa [p, lowWheelTaggedDowncrossPivot] using
      lowWheelCanonicalCofactorQuotientPivot_dvd y.2.1 y.2.2
  have hOrigMin :
      ∀ r : ℕ, r.Prime → r ∣ y.2.1 * y.2.2 → p ≤ r := by
    intro r hr hrd
    change Nat.minFac (y.2.1 * y.2.2) ≤ r
    exact Nat.minFac_le_of_dvd hr.two_le hrd
  have hpDvdNew : p ∣
      (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 :=
    dvd_mul_of_dvd_right
      (lowWheelTaggedDowncrossPivot_dvd_toggledQuotient q y)
      (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1
  by_cases hqt : q ∈ y.1
  · have hnew :=
      lowWheelTaggedDowncrossFaceTailToggleAt_product_of_face
        (y := y) hqt
    have hnewOrig :
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
            (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 =
          q * (y.2.1 * y.2.2) := by
      calc
        _ = q * (y.2.1 *
            (p * (y.2.2 / p))) := by simpa [p] using hnew
        _ = q * (y.2.1 * y.2.2) := by rw [hexpand]
    have hNewMin :
        ∀ r : ℕ, r.Prime →
          r ∣ (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
            (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 →
          p ≤ r := by
      intro r hr hrd
      rw [hnewOrig] at hrd
      rcases hr.dvd_mul.mp hrd with hrq | hrOrig
      · have hrEq : r = q :=
          (Nat.prime_dvd_prime_iff_eq hr hq.1).mp hrq
        rw [hrEq]
        exact hq.2.1
      · exact hOrigMin r hr hrOrig
    change Nat.minFac
        ((lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
          (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2) = p
    exact minFac_eq_of_prime_dvd_minimal hp hpDvdNew hNewMin
  · have hqm : q ∣ y.2.2 / lowWheelTaggedDowncrossPivot y :=
      hq.2.2.resolve_left hqt
    have hrel :=
      lowWheelTaggedDowncrossFaceTailToggleAt_product_of_tail
        (y := y) hqt hqm
    have hrelOrig :
        q * ((lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
            (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2) =
          y.2.1 * y.2.2 := by
      calc
        _ = y.2.1 *
            (p * (y.2.2 / p)) := by simpa [p] using hrel
        _ = y.2.1 * y.2.2 := hexpand
    have hNewMin :
        ∀ r : ℕ, r.Prime →
          r ∣ (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
            (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 →
          p ≤ r := by
      intro r hr hrd
      have hrOrig : r ∣ y.2.1 * y.2.2 := by
        rw [← hrelOrig]
        exact dvd_mul_of_dvd_right hrd q
      exact hOrigMin r hr hrOrig
    change Nat.minFac
        ((lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
          (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2) = p
    exact minFac_eq_of_prime_dvd_minimal hp hpDvdNew hNewMin

/-- The root-side parent is literally invariant under every legal lifted
face/tail move. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_parent
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelCanonicalDowncrossParent
        (lowWheelTaggedDowncrossFaceTailToggleAt q y) =
      lowWheelCanonicalDowncrossParent y := by
  have hpivot := lowWheelTaggedDowncrossFaceTailToggleAt_pivot hy hq
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    have hyData := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy
    have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hyData.2
    simpa [lowWheelTaggedDowncrossPivot] using hshell.1
  have hprod := lowWheelFaceTailToggleAt_product q
    (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)
  unfold lowWheelCanonicalDowncrossParent
  change primeFaceProduct
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).1 *
      ((lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 /
        lowWheelTaggedDowncrossPivot
          (lowWheelTaggedDowncrossFaceTailToggleAt q y)) =
    primeFaceProduct y.1 *
      (y.2.2 / lowWheelTaggedDowncrossPivot y)
  rw [hpivot]
  change primeFaceProduct
        (lowWheelFaceTailToggleAt q
          (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).1 *
      ((lowWheelTaggedDowncrossPivot y *
          (lowWheelFaceTailToggleAt q
            (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).2) /
        lowWheelTaggedDowncrossPivot y) =
    primeFaceProduct y.1 *
      (y.2.2 / lowWheelTaggedDowncrossPivot y)
  let a :=
    (lowWheelFaceTailToggleAt q
      (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).2
  have hdiv :
      (lowWheelTaggedDowncrossPivot y * a) /
          lowWheelTaggedDowncrossPivot y = a := by
    apply Nat.mul_left_cancel hp.pos
    exact Nat.mul_div_cancel'
      (dvd_mul_right (lowWheelTaggedDowncrossPivot y) a)
  rw [show
      (lowWheelTaggedDowncrossPivot y *
          (lowWheelFaceTailToggleAt q
            (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).2) /
          lowWheelTaggedDowncrossPivot y = a by
        simpa [a] using hdiv]
  simpa using hprod

end RHLean.Proof
