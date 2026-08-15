import Mathlib
import RHLean.Proof.PrimeSieveSquareRootTransport
import RHLean.Analysis.PrimeSieveQuotientPNTError

/-!
# Cofactor-first prime windows for the prime-dilate shell tail

The merged prime-dilate compression theorem rewrites every lower-scale Mertens
value `M(floor (x/q))` as the signed mass of the `p`-free shell

```text
floor(x/q) / p < c <= floor(x/q).
```

This module swaps the unresolved prime coordinate `q` with the shell cofactor
`c`.  The parent-inside, `p`-child-outside condition becomes the ordinary
reciprocal prime window

```text
max y (floor (x/(p*c))) < q <= floor (x/c).
```

Thus the post-square-root prime tail is an explicit Mobius-weighted sum of
prime counts on reciprocal windows, with no recursive Mertens value left inside
the prime sum.

The same reindexing is applied to the existing PNT-centered error.  Singleton
Li increments telescope on each reciprocal window, leaving the ordinary
prime-count-minus-Li discrepancy of that window.

At the complete square endpoint `X = R^2 - 1` with cutoff `y = R`, every
nonempty cofactor fibre satisfies `1 <= c < R`.  This is the square-first exact
form intended for the next quantitative attack.

All statements are finite exact identities.  No prime-distribution estimate,
absolute-value bound, power saving, or RH implication is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Arbitrary-prefix cofactor windows -/

/-- `p`-free cofactors large enough to contain every prime-dilate shell at the
prefix `x`. -/
def primeDilateCofactorSupport (p x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun c => ¬ p ∣ c

@[simp] theorem mem_primeDilateCofactorSupport {p x c : ℕ} :
    c ∈ primeDilateCofactorSupport p x ↔
      1 ≤ c ∧ c ≤ x ∧ ¬ p ∣ c := by
  simp [primeDilateCofactorSupport, and_assoc]

/-- Lower endpoint of the prime window attached to a shell cofactor `c`. -/
def primeDilateCofactorWindowLower (p y x c : ℕ) : ℕ :=
  max y (x / (p * c))

/-- Upper endpoint of the prime window attached to a shell cofactor `c`. -/
def primeDilateCofactorWindowUpper (x c : ℕ) : ℕ :=
  x / c

/-- The reciprocal integer window in which `q` sees the parent `c*q` but not
its `p`-dilated child. -/
def primeDilateCofactorWindow (p y x c : ℕ) : Finset ℕ :=
  Finset.Ioc (primeDilateCofactorWindowLower p y x c)
    (primeDilateCofactorWindowUpper x c)

@[simp] theorem mem_primeDilateCofactorWindow {p y x c q : ℕ} :
    q ∈ primeDilateCofactorWindow p y x c ↔
      primeDilateCofactorWindowLower p y x c < q ∧
        q ≤ primeDilateCofactorWindowUpper x c := by
  simp [primeDilateCofactorWindow]

/-- The explicit reciprocal window is exactly the parent-inside,
`p`-child-outside boundary, together with the original unresolved-prime range. -/
theorem mem_primeDilateCofactorWindow_iff_prefixBoundary
    {p y x c q : ℕ} (hp : p.Prime) (hc : 0 < c) :
    q ∈ primeDilateCofactorWindow p y x c ↔
      q ∈ Finset.Ioc y x ∧ IsPrimeDilatePrefixBoundary p x q c := by
  rw [mem_primeDilateCofactorWindow]
  constructor
  · rintro ⟨hlower, hupper⟩
    have hyq : y < q :=
      lt_of_le_of_lt (le_max_left y (x / (p * c))) hlower
    have hdiv : x / (p * c) < q :=
      lt_of_le_of_lt (le_max_right y (x / (p * c))) hlower
    have hparent : c * q ≤ x := by
      have h := (Nat.le_div_iff_mul_le hc).1 hupper
      simpa [Nat.mul_comm] using h
    have hden : 0 < p * c := Nat.mul_pos hp.pos hc
    have hchild : x < primeDilateChildCofactor p c * q := by
      have h := (Nat.div_lt_iff_lt_mul hden).1 hdiv
      simpa [primeDilateChildCofactor, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using h
    have hqx : q ≤ x := hupper.trans (Nat.div_le_self x c)
    exact ⟨Finset.mem_Ioc.mpr ⟨hyq, hqx⟩, ⟨hparent, hchild⟩⟩
  · rintro ⟨hqmem, hboundary⟩
    rcases Finset.mem_Ioc.mp hqmem with ⟨hyq, hqx⟩
    rcases hboundary with ⟨hparent, hchild⟩
    have hupper : q ≤ x / c := by
      apply (Nat.le_div_iff_mul_le hc).2
      simpa [Nat.mul_comm] using hparent
    have hden : 0 < p * c := Nat.mul_pos hp.pos hc
    have hdiv : x / (p * c) < q := by
      apply (Nat.div_lt_iff_lt_mul hden).2
      simpa [primeDilateChildCofactor, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hchild
    exact ⟨max_lt hyq hdiv, hupper⟩

/-- Every explicit cofactor window is contained in the original unresolved
prime-coordinate interval. -/
theorem primeDilateCofactorWindow_subset_Ioc
    (p y x c : ℕ) (_hc : 0 < c) :
    primeDilateCofactorWindow p y x c ⊆ Finset.Ioc y x := by
  intro q hq
  rcases mem_primeDilateCofactorWindow.mp hq with ⟨hlower, hupper⟩
  have hyq : y < q :=
    lt_of_le_of_lt (le_max_left y (x / (p * c))) hlower
  have hqx : q ≤ x := hupper.trans (Nat.div_le_self x c)
  exact Finset.mem_Ioc.mpr ⟨hyq, hqx⟩

/-- Restricting a sum over the unresolved prime range by membership in one
cofactor window is the same as summing directly over that window. -/
theorem sum_Ioc_if_mem_primeDilateCofactorWindow
    (p y x c : ℕ) (hc : 0 < c) (f : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc y x,
      if q ∈ primeDilateCofactorWindow p y x c then f q else 0) =
      ∑ q ∈ primeDilateCofactorWindow p y x c, f q := by
  classical
  have hsubset := primeDilateCofactorWindow_subset_Ioc p y x c hc
  have hfilter :
      (Finset.Ioc y x).filter
          (fun q => q ∈ primeDilateCofactorWindow p y x c) =
        primeDilateCofactorWindow p y x c := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hq
      exact ⟨hsubset hq, hq⟩
  rw [← Finset.sum_filter, hfilter]

/-- In one unresolved `q`-fibre, the #304 prime-dilate shell is exactly the
`p`-free cofactor support restricted by the reciprocal `q`-window. -/
theorem primeDilatePrefixReciprocalShell_eq_support_filter_window
    (p y x q : ℕ) (hp : p.Prime) (hq : q ∈ Finset.Ioc y x) :
    primeDilatePrefixReciprocalShell p x q =
      (primeDilateCofactorSupport p x).filter fun c =>
        q ∈ primeDilateCofactorWindow p y x c := by
  classical
  ext c
  simp only [Finset.mem_filter]
  have hqpos : 0 < q := by
    have := (Finset.mem_Ioc.mp hq).1
    omega
  rw [mem_primeDilatePrefixReciprocalShell_iff_prefixBoundary
    p x q c hp hqpos]
  constructor
  · rintro ⟨hc1, hfree, hboundary⟩
    have hcpos : 0 < c := by omega
    have hq1 : 1 ≤ q := by omega
    have hcx : c ≤ x := by
      calc
        c = c * 1 := by simp
        _ ≤ c * q := Nat.mul_le_mul_left c hq1
        _ ≤ x := hboundary.1
    have hwindow :=
      (mem_primeDilateCofactorWindow_iff_prefixBoundary hp hcpos).2
        ⟨hq, hboundary⟩
    exact ⟨mem_primeDilateCofactorSupport.mpr ⟨hc1, hcx, hfree⟩, hwindow⟩
  · rintro ⟨hsupport, hwindow⟩
    rcases mem_primeDilateCofactorSupport.mp hsupport with
      ⟨hc1, hcx, hfree⟩
    have hcpos : 0 < c := by omega
    have hboundary :=
      (mem_primeDilateCofactorWindow_iff_prefixBoundary hp hcpos).1 hwindow
    exact ⟨hc1, hfree, hboundary.2⟩

/-- Cofactor-first transform of a prime-coordinate weight.  The lower-scale
Mertens value has disappeared; each cofactor is weighted only by the sum of the
coordinate weight on its explicit reciprocal window. -/
def primeDilateCofactorWindowTransform
    (p y x : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c ∈ primeDilateCofactorSupport p x,
    (∑ q ∈ primeDilateCofactorWindow p y x c, a q) *
      canonicalMoebiusWeight c

/-- **Generic cofactor-first reindexing.**  For any weight on the unresolved
prime coordinate, every lower-scale Mertens value can be compressed by #304 and
the resulting finite double sum can be transposed to the explicit cofactor
windows. -/
theorem sum_weight_mul_mertens_div_eq_primeDilateCofactorWindowTransform
    (p y x : ℕ) (hp : p.Prime) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc y x,
      a q * RHLean.Analysis.mertensSummatory (x / q)) =
      primeDilateCofactorWindowTransform p y x a := by
  classical
  unfold primeDilateCofactorWindowTransform
  calc
    (∑ q ∈ Finset.Ioc y x,
        a q * RHLean.Analysis.mertensSummatory (x / q)) =
      ∑ q ∈ Finset.Ioc y x,
        ∑ c ∈ primeDilateCofactorSupport p x,
          if q ∈ primeDilateCofactorWindow p y x c then
            a q * canonicalMoebiusWeight c
          else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            have hmass :
                RHLean.Analysis.mertensSummatory (x / q) =
                  ∑ c ∈ primeDilatePrefixReciprocalShell p x q,
                    canonicalMoebiusWeight c := by
              simpa only [primeDilatePrefixCutoff] using
                (mertensSummatory_primeDilatePrefixCutoff_eq_shellMass
                  p x q hp)
            rw [hmass,
              primeDilatePrefixReciprocalShell_eq_support_filter_window
                p y x q hp hq]
            rw [Finset.mul_sum, Finset.sum_filter]
    _ = ∑ c ∈ primeDilateCofactorSupport p x,
        ∑ q ∈ Finset.Ioc y x,
          if q ∈ primeDilateCofactorWindow p y x c then
            a q * canonicalMoebiusWeight c
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ c ∈ primeDilateCofactorSupport p x,
        (∑ q ∈ primeDilateCofactorWindow p y x c, a q) *
          canonicalMoebiusWeight c := by
            apply Finset.sum_congr rfl
            intro c hc
            have hcpos : 0 < c := by
              have := (mem_primeDilateCofactorSupport.mp hc).1
              omega
            rw [sum_Ioc_if_mem_primeDilateCofactorWindow
              p y x c hcpos (fun q => a q * canonicalMoebiusWeight c)]
            rw [Finset.sum_mul]

/-! ## Prime counts, telescoped Li mass, and discrepancy -/

/-- Exact prime count on one prime-dilate cofactor window, cast to `ℂ` through
the repository's prime indicator. -/
def primeDilateCofactorWindowPrimeCount (p y x c : ℕ) : ℂ :=
  ∑ q ∈ primeDilateCofactorWindow p y x c,
    primeSievePrimeIndicator q

/-- Telescoped logarithmic-integral mass of one prime-dilate cofactor window. -/
def primeDilateCofactorWindowLiMass (p y x c : ℕ) : ℂ :=
  if primeDilateCofactorWindowLower p y x c ≤
      primeDilateCofactorWindowUpper x c then
    ((logarithmicIntegralFromTwo
        (primeDilateCofactorWindowUpper x c : ℝ) -
      logarithmicIntegralFromTwo
        (primeDilateCofactorWindowLower p y x c : ℝ) : ℝ) : ℂ)
  else 0

/-- Singleton Li increments telescope exactly across a prime-dilate cofactor
window. -/
theorem sum_primeSievePNTDensity_primeDilateCofactorWindow
    (p y x c : ℕ) :
    (∑ q ∈ primeDilateCofactorWindow p y x c,
      primeSievePNTDensity q) =
      primeDilateCofactorWindowLiMass p y x c := by
  by_cases h : primeDilateCofactorWindowLower p y x c ≤
      primeDilateCofactorWindowUpper x c
  · unfold primeDilateCofactorWindow
    rw [sum_primeSievePNTDensity_Ioc h]
    simp [primeDilateCofactorWindowLiMass, h]
  · have hle : primeDilateCofactorWindowUpper x c ≤
        primeDilateCofactorWindowLower p y x c := by omega
    rw [primeDilateCofactorWindow, Finset.Ioc_eq_empty_of_le hle]
    simp [primeDilateCofactorWindowLiMass, h]

/-- Prime-count-minus-Li discrepancy on one explicit cofactor window. -/
def primeDilateCofactorWindowDiscrepancy (p y x c : ℕ) : ℂ :=
  primeDilateCofactorWindowPrimeCount p y x c -
    primeDilateCofactorWindowLiMass p y x c

/-- The sum of prime indicator minus singleton Li density on one cofactor window
is its ordinary prime-count-minus-Li discrepancy. -/
theorem sum_primeIndicator_sub_density_primeDilateCofactorWindow
    (p y x c : ℕ) :
    (∑ q ∈ primeDilateCofactorWindow p y x c,
      (primeSievePrimeIndicator q - primeSievePNTDensity q)) =
      primeDilateCofactorWindowDiscrepancy p y x c := by
  unfold primeDilateCofactorWindowDiscrepancy
    primeDilateCofactorWindowPrimeCount
  rw [Finset.sum_sub_distrib,
    sum_primeSievePNTDensity_primeDilateCofactorWindow]

/-- Cofactor-first exact prime-count transform. -/
def primeDilateCofactorPrimeCountTransform (p y x : ℕ) : ℂ :=
  ∑ c ∈ primeDilateCofactorSupport p x,
    primeDilateCofactorWindowPrimeCount p y x c *
      canonicalMoebiusWeight c

/-- Cofactor-first deterministic Li transform. -/
def primeDilateCofactorLiTransform (p y x : ℕ) : ℂ :=
  ∑ c ∈ primeDilateCofactorSupport p x,
    primeDilateCofactorWindowLiMass p y x c *
      canonicalMoebiusWeight c

/-- Cofactor-first PNT discrepancy transform. -/
def primeDilateCofactorDiscrepancyTransform (p y x : ℕ) : ℂ :=
  ∑ c ∈ primeDilateCofactorSupport p x,
    primeDilateCofactorWindowDiscrepancy p y x c *
      canonicalMoebiusWeight c

/-- The exact unresolved Mertens prime tail is a Mobius-weighted sum of ordinary
prime counts on explicit cofactor windows. -/
theorem primeSieveMertensPrimeTail_eq_primeDilateCofactorPrimeCountTransform
    (p y x : ℕ) (hp : p.Prime) :
    primeSieveMertensPrimeTail y x =
      primeDilateCofactorPrimeCountTransform p y x := by
  calc
    primeSieveMertensPrimeTail y x =
        ∑ q ∈ Finset.Ioc y x,
          primeSievePrimeIndicator q *
            RHLean.Analysis.mertensSummatory (x / q) := by
      unfold primeSieveMertensPrimeTail primeSievePrimeIndicator
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hprime : q.Prime <;> simp [hprime]
    _ = primeDilateCofactorWindowTransform p y x primeSievePrimeIndicator :=
      sum_weight_mul_mertens_div_eq_primeDilateCofactorWindowTransform
        p y x hp primeSievePrimeIndicator
    _ = primeDilateCofactorPrimeCountTransform p y x := by
      unfold primeDilateCofactorWindowTransform
        primeDilateCofactorPrimeCountTransform
        primeDilateCofactorWindowPrimeCount
      rfl

/-- The existing deterministic PNT bulk is the same cofactor-window transform
with telescoped Li endpoint masses. -/
theorem primeSievePNTBulk_eq_primeDilateCofactorLiTransform
    (p y x : ℕ) (hp : p.Prime) :
    primeSievePNTBulk y x = primeDilateCofactorLiTransform p y x := by
  unfold primeSievePNTBulk
  rw [sum_weight_mul_mertens_div_eq_primeDilateCofactorWindowTransform
    p y x hp primeSievePNTDensity]
  unfold primeDilateCofactorWindowTransform primeDilateCofactorLiTransform
  apply Finset.sum_congr rfl
  intro c hc
  rw [sum_primeSievePNTDensity_primeDilateCofactorWindow]

/-- **PNT error with no recursive Mertens weight.**  The existing centered error
is exactly a Mobius-weighted sum of ordinary prime-count-minus-Li discrepancies
on the explicit prime-dilate cofactor windows. -/
theorem primeSievePNTError_eq_primeDilateCofactorDiscrepancyTransform
    (p y x : ℕ) (hp : p.Prime) :
    primeSievePNTError y x =
      primeDilateCofactorDiscrepancyTransform p y x := by
  unfold primeSievePNTError
  rw [sum_weight_mul_mertens_div_eq_primeDilateCofactorWindowTransform
    p y x hp (fun q =>
      primeSievePrimeIndicator q - primeSievePNTDensity q)]
  unfold primeDilateCofactorWindowTransform
    primeDilateCofactorDiscrepancyTransform
  apply Finset.sum_congr rfl
  intro c hc
  rw [sum_primeIndicator_sub_density_primeDilateCofactorWindow]

/-- Prime count equals deterministic Li mass plus the cofactor-window PNT error. -/
theorem primeDilateCofactorPrimeCountTransform_eq_li_add_discrepancy
    (p y x : ℕ) :
    primeDilateCofactorPrimeCountTransform p y x =
      primeDilateCofactorLiTransform p y x +
        primeDilateCofactorDiscrepancyTransform p y x := by
  unfold primeDilateCofactorPrimeCountTransform primeDilateCofactorLiTransform
    primeDilateCofactorDiscrepancyTransform
    primeDilateCofactorWindowDiscrepancy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-! ## Complete-square specialization -/

/-- At `X = R^2 - 1`, only `p`-free cofactors strictly below `R` can occur in a
post-square-root prime-dilate shell. -/
def squarePrimeDilateCofactorSupport (p R : ℕ) : Finset ℕ :=
  (Finset.Ico 1 R).filter fun c => ¬ p ∣ c

@[simp] theorem mem_squarePrimeDilateCofactorSupport {p R c : ℕ} :
    c ∈ squarePrimeDilateCofactorSupport p R ↔
      1 ≤ c ∧ c < R ∧ ¬ p ∣ c := by
  simp [squarePrimeDilateCofactorSupport, and_assoc]

/-- Square-specialized cofactor-window transform. -/
def squarePrimeDilateCofactorWindowTransform
    (p R : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c ∈ squarePrimeDilateCofactorSupport p R,
    (∑ q ∈ primeDilateCofactorWindow p R (squareRootEndpoint R) c, a q) *
      canonicalMoebiusWeight c

/-- In a complete-square unresolved prime fibre `R < q`, every cofactor in the
#304 shell is strictly smaller than `R`. -/
theorem primeDilatePrefixReciprocalShell_eq_squareSupport_filter_window
    (p R q : ℕ) (hp : p.Prime) (hR : 0 < R)
    (hq : q ∈ Finset.Ioc R (squareRootEndpoint R)) :
    primeDilatePrefixReciprocalShell p (squareRootEndpoint R) q =
      (squarePrimeDilateCofactorSupport p R).filter fun c =>
        q ∈ primeDilateCofactorWindow p R (squareRootEndpoint R) c := by
  classical
  ext c
  simp only [Finset.mem_filter]
  have hqpos : 0 < q := by
    have := (Finset.mem_Ioc.mp hq).1
    omega
  have hRq : R < q := (Finset.mem_Ioc.mp hq).1
  rw [mem_primeDilatePrefixReciprocalShell_iff_prefixBoundary
    p (squareRootEndpoint R) q c hp hqpos]
  constructor
  · rintro ⟨hc1, hfree, hboundary⟩
    have hcpos : 0 < c := by omega
    have hcR : c < R := by
      by_contra hnot
      have hRc : R ≤ c := Nat.le_of_not_gt hnot
      have hmul1 : R * q ≤ c * q := Nat.mul_le_mul_right q hRc
      have hmul2 : R * R < R * q :=
        Nat.mul_lt_mul_of_pos_left hRq hR
      have hXlt : squareRootEndpoint R < R * R := by
        unfold squareRootEndpoint
        rw [pow_two]
        have hsq : 0 < R * R := Nat.mul_pos hR hR
        omega
      have hbad : R * R ≤ squareRootEndpoint R :=
        (hmul2.trans_le (hmul1.trans hboundary.1)).le
      exact (Nat.not_lt_of_ge hbad) hXlt
    have hwindow :=
      (mem_primeDilateCofactorWindow_iff_prefixBoundary hp hcpos).2
        ⟨hq, hboundary⟩
    exact ⟨mem_squarePrimeDilateCofactorSupport.mpr
      ⟨hc1, hcR, hfree⟩, hwindow⟩
  · rintro ⟨hsupport, hwindow⟩
    rcases mem_squarePrimeDilateCofactorSupport.mp hsupport with
      ⟨hc1, hcR, hfree⟩
    have hcpos : 0 < c := by omega
    have hboundary :=
      (mem_primeDilateCofactorWindow_iff_prefixBoundary hp hcpos).1 hwindow
    exact ⟨hc1, hfree, hboundary.2⟩

/-- **Square-first generic reindexing.**  At a complete square endpoint the
cofactor-first support shrinks from an arbitrary prefix to the strict range
`1 <= c < R`. -/
theorem sum_weight_mul_mertens_square_eq_squarePrimeDilateCofactorWindowTransform
    (p R : ℕ) (hp : p.Prime) (hR : 0 < R) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
      a q * RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)) =
      squarePrimeDilateCofactorWindowTransform p R a := by
  classical
  unfold squarePrimeDilateCofactorWindowTransform
  calc
    (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        a q * RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)) =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        ∑ c ∈ squarePrimeDilateCofactorSupport p R,
          if q ∈ primeDilateCofactorWindow p R (squareRootEndpoint R) c then
            a q * canonicalMoebiusWeight c
          else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            have hmass :
                RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q) =
                  ∑ c ∈ primeDilatePrefixReciprocalShell
                    p (squareRootEndpoint R) q,
                    canonicalMoebiusWeight c := by
              simpa only [primeDilatePrefixCutoff] using
                (mertensSummatory_primeDilatePrefixCutoff_eq_shellMass
                  p (squareRootEndpoint R) q hp)
            rw [hmass,
              primeDilatePrefixReciprocalShell_eq_squareSupport_filter_window
                p R q hp hR hq]
            rw [Finset.mul_sum, Finset.sum_filter]
    _ = ∑ c ∈ squarePrimeDilateCofactorSupport p R,
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q ∈ primeDilateCofactorWindow p R (squareRootEndpoint R) c then
            a q * canonicalMoebiusWeight c
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ c ∈ squarePrimeDilateCofactorSupport p R,
        (∑ q ∈ primeDilateCofactorWindow p R (squareRootEndpoint R) c, a q) *
          canonicalMoebiusWeight c := by
            apply Finset.sum_congr rfl
            intro c hc
            have hcpos : 0 < c := by
              have := (mem_squarePrimeDilateCofactorSupport.mp hc).1
              omega
            rw [sum_Ioc_if_mem_primeDilateCofactorWindow
              p R (squareRootEndpoint R) c hcpos
                (fun q => a q * canonicalMoebiusWeight c)]
            rw [Finset.sum_mul]

/-- Square-root transport as a Mobius-weighted prime-count transform on only
`c < R`. -/
def squarePrimeDilateCofactorPrimeCountTransform (p R : ℕ) : ℂ :=
  ∑ c ∈ squarePrimeDilateCofactorSupport p R,
    primeDilateCofactorWindowPrimeCount p R (squareRootEndpoint R) c *
      canonicalMoebiusWeight c

/-- Square-root deterministic Li transform on only `c < R`. -/
def squarePrimeDilateCofactorLiTransform (p R : ℕ) : ℂ :=
  ∑ c ∈ squarePrimeDilateCofactorSupport p R,
    primeDilateCofactorWindowLiMass p R (squareRootEndpoint R) c *
      canonicalMoebiusWeight c

/-- Square-root prime-count-minus-Li discrepancy transform on only `c < R`. -/
def squarePrimeDilateCofactorDiscrepancyTransform (p R : ℕ) : ℂ :=
  ∑ c ∈ squarePrimeDilateCofactorSupport p R,
    primeDilateCofactorWindowDiscrepancy p R (squareRootEndpoint R) c *
      canonicalMoebiusWeight c

/-- **Exact square transport prime-window identity.**  The original high-prime
transport is a signed sum of ordinary prime counts on the `c < R` reciprocal
windows. -/
theorem squareRootTransportPrimeFirst_eq_squarePrimeDilateCofactorPrimeCountTransform
    (p R : ℕ) (hp : p.Prime) (hR : 0 < R) :
    squareRootTransportPrimeFirst R =
      squarePrimeDilateCofactorPrimeCountTransform p R := by
  rw [squareRootTransportPrimeFirst_eq_mertensTransform R hR]
  calc
    (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if q.Prime then
          RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
        else 0) =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        primeSievePrimeIndicator q *
          RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q) := by
            apply Finset.sum_congr rfl
            intro q hq
            unfold primeSievePrimeIndicator
            by_cases hprime : q.Prime <;> simp [hprime]
    _ = squarePrimeDilateCofactorWindowTransform p R primeSievePrimeIndicator :=
      sum_weight_mul_mertens_square_eq_squarePrimeDilateCofactorWindowTransform
        p R hp hR primeSievePrimeIndicator
    _ = squarePrimeDilateCofactorPrimeCountTransform p R := by
      unfold squarePrimeDilateCofactorWindowTransform
        squarePrimeDilateCofactorPrimeCountTransform
        primeDilateCofactorWindowPrimeCount
      rfl

/-- At the square endpoint, the deterministic PNT bulk is the `c < R` sum of
Li endpoint differences on the same reciprocal windows. -/
theorem primeSievePNTBulk_squareRootEndpoint_eq_squarePrimeDilateCofactorLiTransform
    (p R : ℕ) (hp : p.Prime) (hR : 0 < R) :
    primeSievePNTBulk R (squareRootEndpoint R) =
      squarePrimeDilateCofactorLiTransform p R := by
  unfold primeSievePNTBulk
  rw [sum_weight_mul_mertens_square_eq_squarePrimeDilateCofactorWindowTransform
    p R hp hR primeSievePNTDensity]
  unfold squarePrimeDilateCofactorWindowTransform
    squarePrimeDilateCofactorLiTransform
  apply Finset.sum_congr rfl
  intro c hc
  rw [sum_primeSievePNTDensity_primeDilateCofactorWindow]

/-- **Exact square PNT-error identity.**  The recursive Mertens weights disappear:
the entire centered error is a signed `c < R` sum of ordinary prime-count-minus-
Li discrepancies on explicit reciprocal windows. -/
theorem primeSievePNTError_squareRootEndpoint_eq_squarePrimeDilateCofactorDiscrepancyTransform
    (p R : ℕ) (hp : p.Prime) (hR : 0 < R) :
    primeSievePNTError R (squareRootEndpoint R) =
      squarePrimeDilateCofactorDiscrepancyTransform p R := by
  unfold primeSievePNTError
  rw [sum_weight_mul_mertens_square_eq_squarePrimeDilateCofactorWindowTransform
    p R hp hR (fun q =>
      primeSievePrimeIndicator q - primeSievePNTDensity q)]
  unfold squarePrimeDilateCofactorWindowTransform
    squarePrimeDilateCofactorDiscrepancyTransform
  apply Finset.sum_congr rfl
  intro c hc
  rw [sum_primeIndicator_sub_density_primeDilateCofactorWindow]

/-- The square prime-count transport splits exactly into its deterministic Li
part plus the signed prime-distribution discrepancy that remains for analysis. -/
theorem squarePrimeDilateCofactorPrimeCountTransform_eq_li_add_discrepancy
    (p R : ℕ) :
    squarePrimeDilateCofactorPrimeCountTransform p R =
      squarePrimeDilateCofactorLiTransform p R +
        squarePrimeDilateCofactorDiscrepancyTransform p R := by
  unfold squarePrimeDilateCofactorPrimeCountTransform
    squarePrimeDilateCofactorLiTransform
    squarePrimeDilateCofactorDiscrepancyTransform
    primeDilateCofactorWindowDiscrepancy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring

end RHLean.Analysis
