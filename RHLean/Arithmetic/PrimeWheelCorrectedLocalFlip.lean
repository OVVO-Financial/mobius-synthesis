import Mathlib
import RHLean.Arithmetic.PrimeSquareCollisionPairingFrontier

noncomputable section

open scoped BigOperators

namespace RHLean.Arithmetic

/-!
# Local exponent flips for the corrected prime-wheel field

The collision pairing needs an arithmetic sign theorem for the actual
`raw - 2 * smoothCore` field, not merely for an abstract sign state.  This file
proves that theorem without using Möbius recovery.

If a paired pair of sites differs by the exponent-state flip `0 <-> 1` at one
selected prime `p`, every other local prime comb is unchanged, and membership in
the smooth core is preserved, then the seeded raw field changes sign, the smooth
core changes sign, and hence the corrected field changes sign exactly.

This isolates the remaining physical CRT obligation: construct the site pairing
and verify these local hypotheses on the paired collision classes.  No
identification of collision-slot labels with exponent states is assumed here.
-/

/-- A realized `0 <-> 1` local exponent flip changes the corresponding local
prime comb sign.  The square state is allowed only as the fixed zero state. -/
theorem localPrimeComb_eq_neg_of_exponentFlip
    (p n m : ℕ)
    (hstate :
      localPrimeExponentState p m =
        primeCombExponentFlip (localPrimeExponentState p n)) :
    localPrimeComb p m = -localPrimeComb p n := by
  rw [localPrimeComb_eq_stateValue p m,
    localPrimeComb_eq_stateValue p n, hstate,
    localPrimeCombStateValue_flip]

/-- If exactly one selected prime coordinate performs the exponent-state flip
and every other selected coordinate is unchanged, the complete seeded comb
changes sign. -/
theorem seededPrimeComb_eq_neg_of_single_exponentFlip
    (S : Finset ℕ) (p n m : ℕ)
    (hpS : p ∈ S)
    (hstate :
      localPrimeExponentState p m =
        primeCombExponentFlip (localPrimeExponentState p n))
    (hother : ∀ q ∈ S, q ≠ p →
      localPrimeComb q m = localPrimeComb q n) :
    seededPrimeComb S m = -seededPrimeComb S n := by
  classical
  have hpflip : localPrimeComb p m = -localPrimeComb p n :=
    localPrimeComb_eq_neg_of_exponentFlip p n m hstate
  have hrest :
      (∏ q ∈ S.erase p, localPrimeComb q m) =
        ∏ q ∈ S.erase p, localPrimeComb q n := by
    apply Finset.prod_congr rfl
    intro q hq
    have hqe := Finset.mem_erase.mp hq
    exact hother q hqe.2 hqe.1
  have hmprod :=
    Finset.mul_prod_erase S (fun q => localPrimeComb q m) hpS
  have hnprod :=
    Finset.mul_prod_erase S (fun q => localPrimeComb q n) hpS
  unfold seededPrimeComb
  rw [← hmprod, ← hnprod]
  change
    -(localPrimeComb p m * ∏ q ∈ S.erase p, localPrimeComb q m) =
      - -(localPrimeComb p n * ∏ q ∈ S.erase p, localPrimeComb q n)
  rw [hpflip, hrest]
  ring

/-- Under the same local flip, the smooth-core contribution changes sign as
soon as the paired sites have the same smooth/non-smooth status and both lie
inside the pinned upper cutoff. -/
theorem primeWheelSmoothCoreSite_eq_neg_of_single_exponentFlip
    (S : Finset ℕ) (upper p n m : ℕ)
    (hpS : p ∈ S)
    (hstate :
      localPrimeExponentState p m =
        primeCombExponentFlip (localPrimeExponentState p n))
    (hother : ∀ q ∈ S, q ≠ p →
      localPrimeComb q m = localPrimeComb q n)
    (hnupper : n ≤ upper) (hmupper : m ≤ upper)
    (hsmooth :
      IsPrimeWheelSmooth S m ↔ IsPrimeWheelSmooth S n) :
    primeWheelSmoothCoreSite S upper m =
      -primeWheelSmoothCoreSite S upper n := by
  have hraw := seededPrimeComb_eq_neg_of_single_exponentFlip
    S p n m hpS hstate hother
  by_cases hnSmooth : IsPrimeWheelSmooth S n
  · have hmSmooth : IsPrimeWheelSmooth S m := hsmooth.mpr hnSmooth
    simp [primeWheelSmoothCoreSite, hnupper, hmupper,
      hnSmooth, hmSmooth, hraw]
  · have hmNotSmooth : ¬ IsPrimeWheelSmooth S m := by
      intro hmSmooth
      exact hnSmooth (hsmooth.mp hmSmooth)
    simp [primeWheelSmoothCoreSite, hnupper, hmupper,
      hnSmooth, hmNotSmooth]

/-- **Actual `R - 2H` local sign law.**  A genuine local exponent-state flip at
one selected prime reverses the corrected prime-wheel field whenever all other
local coordinates and smooth-core membership are preserved.  This theorem uses
the seeded and smooth-core definitions directly; it does not route through an
already-known Möbius value. -/
theorem correctedPrimeWheelSite_eq_neg_of_single_exponentFlip
    (S : Finset ℕ) (upper p n m : ℕ)
    (hpS : p ∈ S)
    (hstate :
      localPrimeExponentState p m =
        primeCombExponentFlip (localPrimeExponentState p n))
    (hother : ∀ q ∈ S, q ≠ p →
      localPrimeComb q m = localPrimeComb q n)
    (hnupper : n ≤ upper) (hmupper : m ≤ upper)
    (hsmooth :
      IsPrimeWheelSmooth S m ↔ IsPrimeWheelSmooth S n) :
    correctedPrimeWheelSite S upper m =
      -correctedPrimeWheelSite S upper n := by
  have hraw := seededPrimeComb_eq_neg_of_single_exponentFlip
    S p n m hpS hstate hother
  have hcore := primeWheelSmoothCoreSite_eq_neg_of_single_exponentFlip
    S upper p n m hpS hstate hother hnupper hmupper hsmooth
  unfold correctedPrimeWheelSite
  rw [hraw, hcore]
  ring

/-- Corrected-site weight attached to a physical collision-slot label through
an arbitrary site realization.  The realization is kept explicit because the
CRT slot label and the local exponent state are different data. -/
def correctedCollisionSiteWeight
    (S : Finset ℕ) (upper : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (s : TwoPrimeCollisionState) : ℤ :=
  correctedPrimeWheelSite S upper (site s)

/-- A physical collision-label matching inherits the actual corrected-field
sign reversal once its paired site realization is proved to implement the local
exponent flip, preserve all other local comb coordinates, and preserve smooth
core membership. -/
theorem correctedCollisionSiteWeight_signReversal
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hupper : ∀ s : TwoPrimeCollisionState, site s ≤ upper)
    (hstate : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      localPrimeExponentState p
          (site (collisionExponentStateInvolution s)) =
        primeCombExponentFlip (localPrimeExponentState p (site s)))
    (hother : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      ∀ q ∈ S, q ≠ p →
        localPrimeComb q (site (collisionExponentStateInvolution s)) =
          localPrimeComb q (site s))
    (hsmooth : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      (IsPrimeWheelSmooth S
          (site (collisionExponentStateInvolution s)) ↔
        IsPrimeWheelSmooth S (site s))) :
    ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      correctedCollisionSiteWeight S upper site
          (collisionExponentStateInvolution s) =
        -correctedCollisionSiteWeight S upper site s := by
  intro s hs
  unfold correctedCollisionSiteWeight
  exact correctedPrimeWheelSite_eq_neg_of_single_exponentFlip
    S upper p (site s) (site (collisionExponentStateInvolution s))
    hpS (hstate s hs) (hother s hs)
    (hupper s) (hupper (collisionExponentStateInvolution s))
    (hsmooth s hs)

/-- Once the physical site realization verifies the local exponent-flip
hypotheses, the incomplete CRT prefix is reduced automatically to the tiny fixed
part plus the explicit mate-crosses-cutoff defect. -/
theorem sum_correctedCollisionSiteWeight_prefix_eq_fixed_add_defect
    (S : Finset ℕ) (upper p q K : ℕ)
    (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hupper : ∀ s : TwoPrimeCollisionState, site s ≤ upper)
    (hstate : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      localPrimeExponentState p
          (site (collisionExponentStateInvolution s)) =
        primeCombExponentFlip (localPrimeExponentState p (site s)))
    (hother : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      ∀ r ∈ S, r ≠ p →
        localPrimeComb r (site (collisionExponentStateInvolution s)) =
          localPrimeComb r (site s))
    (hsmooth : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      (IsPrimeWheelSmooth S
          (site (collisionExponentStateInvolution s)) ↔
        IsPrimeWheelSmooth S (site s))) :
    (∑ s ∈ collisionExponentStatePrefixFrontier p q K hcop,
        correctedCollisionSiteWeight S upper site s) =
      (∑ s ∈ collisionInvolutionFixedPart
          (collisionExponentStatePrefixFrontier p q K hcop),
        correctedCollisionSiteWeight S upper site s) +
      ∑ s ∈ collisionInvolutionDefectPart
          (collisionExponentStatePrefixFrontier p q K hcop),
        correctedCollisionSiteWeight S upper site s := by
  apply sum_collisionExponentStatePrefixFrontier_eq_fixed_add_defect
  exact correctedCollisionSiteWeight_signReversal
    S upper p site hpS hupper hstate hother hsmooth

/-! ## Exact fixed-point square kills -/

/-- A square hit from any selected prime coordinate kills the complete seeded
prime comb. -/
theorem seededPrimeComb_eq_zero_of_square_hit
    (S : Finset ℕ) (p n : ℕ)
    (hpS : p ∈ S) (hsq : p ^ 2 ∣ n) :
    seededPrimeComb S n = 0 := by
  classical
  have hlocal : localPrimeComb p n = 0 := by
    simp [localPrimeComb, hsq]
  have hprod :=
    Finset.mul_prod_erase S (fun q => localPrimeComb q n) hpS
  unfold seededPrimeComb
  rw [← hprod]
  simp [hlocal]

/-- The smooth-core contribution also vanishes at a selected-prime square hit,
because its only possible nonzero value is the already-killed seeded comb. -/
theorem primeWheelSmoothCoreSite_eq_zero_of_square_hit
    (S : Finset ℕ) (upper p n : ℕ)
    (hpS : p ∈ S) (hsq : p ^ 2 ∣ n) :
    primeWheelSmoothCoreSite S upper n = 0 := by
  have hseed := seededPrimeComb_eq_zero_of_square_hit S p n hpS hsq
  simp [primeWheelSmoothCoreSite, hseed]

/-- **Exact square-kill law for the corrected field.**  The signed
`raw - 2 * smoothCore` site is zero whenever one selected prime square divides
the site. -/
theorem correctedPrimeWheelSite_eq_zero_of_square_hit
    (S : Finset ℕ) (upper p n : ℕ)
    (hpS : p ∈ S) (hsq : p ^ 2 ∣ n) :
    correctedPrimeWheelSite S upper n = 0 := by
  have hseed := seededPrimeComb_eq_zero_of_square_hit S p n hpS hsq
  have hcore :=
    primeWheelSmoothCoreSite_eq_zero_of_square_hit S upper p n hpS hsq
  simp [correctedPrimeWheelSite, hseed, hcore]

/-- A fixed physical collision label has zero corrected weight as soon as its
site realization forces a square hit from a selected prime coordinate. -/
theorem correctedCollisionSiteWeight_eq_zero_of_fixed_square_hit
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hfixedSquare : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s = s → p ^ 2 ∣ site s) :
    ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s = s →
      correctedCollisionSiteWeight S upper site s = 0 := by
  intro s hs
  unfold correctedCollisionSiteWeight
  exact correctedPrimeWheelSite_eq_zero_of_square_hit
    S upper p (site s) hpS (hfixedSquare s hs)

/-- The entire fixed-label part of an arbitrary collision frontier vanishes
under the physical square-hit hypothesis. -/
theorem sum_correctedCollisionSiteWeight_fixedPart_eq_zero
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hfixedSquare : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s = s → p ^ 2 ∣ site s)
    (F : Finset TwoPrimeCollisionState) :
    (∑ s ∈ collisionInvolutionFixedPart F,
      correctedCollisionSiteWeight S upper site s) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s hs
  have hfix := (Finset.mem_filter.mp hs).2
  exact correctedCollisionSiteWeight_eq_zero_of_fixed_square_hit
    S upper p site hpS hfixedSquare s hfix

/-- **Fixed-point-free physical frontier reduction.**  Once the nonfixed
physical labels satisfy the actual corrected-field sign law and the fixed labels
carry a selected-prime square hit, the full incomplete CRT frontier equals only
the explicit mate-crosses-cutoff defect. -/
theorem sum_correctedCollisionSiteWeight_prefix_eq_defect
    (S : Finset ℕ) (upper p q K : ℕ)
    (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hupper : ∀ s : TwoPrimeCollisionState, site s ≤ upper)
    (hstate : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      localPrimeExponentState p
          (site (collisionExponentStateInvolution s)) =
        primeCombExponentFlip (localPrimeExponentState p (site s)))
    (hother : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      ∀ r ∈ S, r ≠ p →
        localPrimeComb r (site (collisionExponentStateInvolution s)) =
          localPrimeComb r (site s))
    (hsmooth : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      (IsPrimeWheelSmooth S
          (site (collisionExponentStateInvolution s)) ↔
        IsPrimeWheelSmooth S (site s)))
    (hfixedSquare : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s = s → p ^ 2 ∣ site s) :
    (∑ s ∈ collisionExponentStatePrefixFrontier p q K hcop,
        correctedCollisionSiteWeight S upper site s) =
      ∑ s ∈ collisionInvolutionDefectPart
          (collisionExponentStatePrefixFrontier p q K hcop),
        correctedCollisionSiteWeight S upper site s := by
  rw [sum_correctedCollisionSiteWeight_prefix_eq_fixed_add_defect
    S upper p q K hcop site hpS hupper hstate hother hsmooth]
  rw [sum_correctedCollisionSiteWeight_fixedPart_eq_zero
    S upper p site hpS hfixedSquare
    (collisionExponentStatePrefixFrontier p q K hcop)]
  simp

end RHLean.Arithmetic
