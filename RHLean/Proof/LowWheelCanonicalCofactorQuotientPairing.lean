import Mathlib
import RHLean.Proof.LowWheelCofactorQuotientToggle

/-!
# Canonical least-prime pairing on the cofactor/quotient carrier

The fixed-prime toggle from `LowWheelCofactorQuotientToggle` becomes a genuine
canonical operator by choosing the prime from the state itself:

`p(c,k) = minFac(c*k)`.

The toggle preserves `c*k`, so it preserves its own pivot.  Consequently every
nontrivial squarefree-cofactor state carries a canonical sign-reversing
involution.

The geometry is equally rigid.  If the least prime divides the cofactor, moving
it from `c` into `k` always stays inside the physical transport carrier.  If it
does not divide the cofactor, it must divide `k`; moving it into `c` either stays
inside or crosses the high quotient back through the root cutoff

`P(t)*(k/p) <= R`.

The formerly separate cofactor condition `R <= c*p` is automatically absorbed
by this same quotient downcross at the square endpoint: if both post-toggle
coordinates remained at least root-sized, their invariant product would be at
least `R^2`, beyond the physical ceiling `R^2-1`.

No norm, estimate, or asymptotic input appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Canonical pivot of one cofactor/quotient state: the least prime factor of
the product preserved by the toggle. -/
def lowWheelCanonicalCofactorQuotientPivot
    (x : LowWheelCofactorQuotientState) : ℕ :=
  Nat.minFac (x.1 * x.2)

/-- Canonical cofactor/quotient toggle at the invariant least-prime pivot. -/
def lowWheelCanonicalCofactorQuotientToggle
    (x : LowWheelCofactorQuotientState) : LowWheelCofactorQuotientState :=
  lowWheelCofactorQuotientToggleAt
    (lowWheelCanonicalCofactorQuotientPivot x) x

/-- The canonical toggle preserves the complete cofactor/quotient product. -/
theorem lowWheelCanonicalCofactorQuotientToggle_product
    (x : LowWheelCofactorQuotientState) :
    (lowWheelCanonicalCofactorQuotientToggle x).1 *
        (lowWheelCanonicalCofactorQuotientToggle x).2 = x.1 * x.2 := by
  unfold lowWheelCanonicalCofactorQuotientToggle
  exact lowWheelCofactorQuotientToggleAt_product x

/-- Because the physical product is invariant, the canonical least-prime pivot
is invariant as well. -/
theorem lowWheelCanonicalCofactorQuotientPivot_toggle
    (x : LowWheelCofactorQuotientState) :
    lowWheelCanonicalCofactorQuotientPivot
        (lowWheelCanonicalCofactorQuotientToggle x) =
      lowWheelCanonicalCofactorQuotientPivot x := by
  unfold lowWheelCanonicalCofactorQuotientPivot
  rw [lowWheelCanonicalCofactorQuotientToggle_product]

/-- The canonical pivot is prime on every nontrivial product state. -/
theorem lowWheelCanonicalCofactorQuotientPivot_prime
    {c k : ℕ} (hne : c * k ≠ 1) :
    (lowWheelCanonicalCofactorQuotientPivot (c, k)).Prime := by
  simpa [lowWheelCanonicalCofactorQuotientPivot] using
    Nat.minFac_prime hne

/-- The canonical pivot divides the invariant physical product. -/
theorem lowWheelCanonicalCofactorQuotientPivot_dvd
    (c k : ℕ) :
    lowWheelCanonicalCofactorQuotientPivot (c, k) ∣ c * k := by
  simpa [lowWheelCanonicalCofactorQuotientPivot] using
    Nat.minFac_dvd (c * k)

/-- On a nontrivial state, the canonical prime is active in either the cofactor
or the residual quotient. -/
theorem lowWheelCanonicalCofactorQuotientPivot_active
    {c k : ℕ} (hne : c * k ≠ 1) :
    lowWheelCanonicalCofactorQuotientPivot (c, k) ∣ c ∨
      lowWheelCanonicalCofactorQuotientPivot (c, k) ∣ k := by
  have hp := lowWheelCanonicalCofactorQuotientPivot_prime hne
  exact hp.dvd_mul.mp (lowWheelCanonicalCofactorQuotientPivot_dvd c k)

/-- The canonical toggle reverses the Möbius/Boolean signed weight on every
nontrivial squarefree-cofactor state. -/
theorem lowWheelCanonicalCofactorQuotientToggle_weight_neg
    {c k : ℕ} {t : Finset ℕ}
    (hsq : Squarefree c) (hne : c * k ≠ 1) :
    canonicalMoebiusWeight
        (lowWheelCanonicalCofactorQuotientToggle (c, k)).1 *
        (booleanCubeSign t : ℂ) =
      -(canonicalMoebiusWeight c * (booleanCubeSign t : ℂ)) := by
  unfold lowWheelCanonicalCofactorQuotientToggle
  exact lowWheelCofactorQuotientToggleAt_weight_neg
    (lowWheelCanonicalCofactorQuotientPivot_prime hne) hsq
    (lowWheelCanonicalCofactorQuotientPivot_active hne)

/-- The state-dependent least-prime toggle is a genuine involution on every
nontrivial squarefree-cofactor state. -/
theorem lowWheelCanonicalCofactorQuotientToggle_involutive
    {c k : ℕ} (hsq : Squarefree c) (hne : c * k ≠ 1) :
    lowWheelCanonicalCofactorQuotientToggle
        (lowWheelCanonicalCofactorQuotientToggle (c, k)) = (c, k) := by
  change lowWheelCofactorQuotientToggleAt
      (lowWheelCanonicalCofactorQuotientPivot
        (lowWheelCanonicalCofactorQuotientToggle (c, k)))
      (lowWheelCanonicalCofactorQuotientToggle (c, k)) = (c, k)
  rw [lowWheelCanonicalCofactorQuotientPivot_toggle]
  change lowWheelCofactorQuotientToggleAt
      (lowWheelCanonicalCofactorQuotientPivot (c, k))
      (lowWheelCofactorQuotientToggleAt
        (lowWheelCanonicalCofactorQuotientPivot (c, k)) (c, k)) = (c, k)
  exact lowWheelCofactorQuotientToggleAt_involutive
    (lowWheelCanonicalCofactorQuotientPivot_prime hne) hsq
    (lowWheelCanonicalCofactorQuotientPivot_active hne)

/-- Canonical pairing with the original two-boundary formulation retained for
compatibility. -/
theorem lowWheelCanonicalCofactorQuotientToggle_preserves_or_boundary
    {R c k : ℕ} {t : Finset ℕ}
    (hcarrier : LowWheelTransportPairCarrier R t (c, k))
    (hne : c * k ≠ 1) :
    LowWheelTransportPairCarrier R t
        (lowWheelCanonicalCofactorQuotientToggle (c, k)) ∨
      R ≤ c * lowWheelCanonicalCofactorQuotientPivot (c, k) ∨
      primeFaceProduct t *
          (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) ≤ R := by
  let p := lowWheelCanonicalCofactorQuotientPivot (c, k)
  have hp : p.Prime := by
    simpa [p] using lowWheelCanonicalCofactorQuotientPivot_prime hne
  have hactive : p ∣ c ∨ p ∣ k := by
    simpa [p] using lowWheelCanonicalCofactorQuotientPivot_active hne
  by_cases hpc : p ∣ c
  · left
    unfold lowWheelCanonicalCofactorQuotientToggle
    simpa [p] using
      lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
        hp hcarrier hpc
  · have hpk : p ∣ k := hactive.resolve_left hpc
    unfold lowWheelCanonicalCofactorQuotientToggle
    simpa [p] using
      lowWheelCofactorQuotientToggleAt_preserves_or_boundary_of_dvd_quotient
        hp hcarrier hpc hpk

/-- **Canonical one-sided root frontier.**  The least-prime mate either remains
physical or its post-removal quotient crosses down through the root. -/
theorem lowWheelCanonicalCofactorQuotientToggle_preserves_or_downcross
    {R c k : ℕ} {t : Finset ℕ}
    (hcarrier : LowWheelTransportPairCarrier R t (c, k))
    (hne : c * k ≠ 1) :
    LowWheelTransportPairCarrier R t
        (lowWheelCanonicalCofactorQuotientToggle (c, k)) ∨
      primeFaceProduct t *
          (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) ≤ R := by
  let p := lowWheelCanonicalCofactorQuotientPivot (c, k)
  have hp : p.Prime := by
    simpa [p] using lowWheelCanonicalCofactorQuotientPivot_prime hne
  have hactive : p ∣ c ∨ p ∣ k := by
    simpa [p] using lowWheelCanonicalCofactorQuotientPivot_active hne
  by_cases hpc : p ∣ c
  · left
    unfold lowWheelCanonicalCofactorQuotientToggle
    simpa [p] using
      lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
        hp hcarrier hpc
  · have hpk : p ∣ k := hactive.resolve_left hpc
    unfold lowWheelCanonicalCofactorQuotientToggle
    simpa [p] using
      lowWheelCofactorQuotientToggleAt_preserves_or_downcross_of_dvd_quotient
        hp hcarrier hpc hpk

/-- If the canonical mate is not physical, one of the two original geometric
boundary inequalities holds.  Kept as a compatibility theorem. -/
theorem lowWheelCanonicalCofactorQuotientToggle_boundary_of_not_preserves
    {R c k : ℕ} {t : Finset ℕ}
    (hcarrier : LowWheelTransportPairCarrier R t (c, k))
    (hne : c * k ≠ 1)
    (hnot : ¬ LowWheelTransportPairCarrier R t
      (lowWheelCanonicalCofactorQuotientToggle (c, k))) :
    R ≤ c * lowWheelCanonicalCofactorQuotientPivot (c, k) ∨
      primeFaceProduct t *
          (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) ≤ R := by
  rcases lowWheelCanonicalCofactorQuotientToggle_preserves_or_boundary
      hcarrier hne with hmate | hboundary
  · exact (hnot hmate).elim
  · exact hboundary

/-- **Exact one-sided failure statement.**  A nonphysical canonical mate is
necessarily a quotient root-downcross. -/
theorem lowWheelCanonicalCofactorQuotientToggle_downcross_of_not_preserves
    {R c k : ℕ} {t : Finset ℕ}
    (hcarrier : LowWheelTransportPairCarrier R t (c, k))
    (hne : c * k ≠ 1)
    (hnot : ¬ LowWheelTransportPairCarrier R t
      (lowWheelCanonicalCofactorQuotientToggle (c, k))) :
    primeFaceProduct t *
        (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) ≤ R := by
  rcases lowWheelCanonicalCofactorQuotientToggle_preserves_or_downcross
      hcarrier hne with hmate | hdown
  · exact (hnot hmate).elim
  · exact hdown

end RHLean.Proof
