import Mathlib
import RHLean.Geometry.TwoABDisplacement
import RHLean.Proof.CompleteFermatSieve
import RHLean.Proof.ComplexVerticalIntervalEulerBridge

/-!
# Complex vertical-fibre spacing and Euler transport

This file continues the exact bridge of `ComplexVerticalIntervalEulerBridge`.
It formalizes the additional arithmetic geometry of one fixed squared Fermat
vertical fibre:

* a fixed non-five odd residue modulo twenty has exactly four terminal classes;
* forgetting the parity lane and retaining only the residue modulo ten doubles
  this to eight classes;
* the vertical coordinate has an exact quadratic finite-difference law;
* moving one Euler prime from the high factor to the processed factor produces
  a quadratically growing vertical displacement;
* for a fixed physical child integer, the ordered Euler cut active at one root
  is unique;
* two representations of the same child carry the same signed Möbius charge;
* consecutive cuts meet exactly at the previous Euler completion threshold;
* on a strict subdoubling square run a fixed child cannot pass through two
  successive pivot transitions.

No norm, density estimate, independence hypothesis, PNT input, or RH hypothesis
is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open RHLean.Geometry
open LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

/-! ## Exact terminal-class counts -/

/-- Once the actual residue modulo twenty is fixed, an odd residue away from
five occupies one parity lane and has exactly four terminal Fermat classes. -/
theorem fermatFixedMod20_nonfive_card_four
    (r : Fin 20)
    (hodd : r.val % 2 ≠ 0)
    (hfive : r.val % 5 ≠ 0) :
    (fermatDigitPairsMod20 r.val).card = 4 := by
  rw [fermatDigitPairsMod20_card]
  simp [hodd, hfive]

/-- If only the final decimal digit is retained, the two compatible parity
lanes are unioned and the non-five odd classes have cardinality eight. -/
theorem fermatMod10_nonfive_card_eight
    (r : Fin 10)
    (hodd : r.val % 2 ≠ 0)
    (hfive : r.val ≠ 5) :
    (fermatDigitPairsMod10 r.val).card = 8 := by
  rw [fermatDigitPairsMod10_card]
  simp [hodd, hfive]

/-! ## Quantitative vertical spacing -/

/-- Exact pivot increment on a fixed ordered Euler fibre.  If the low face
product is `a`, increasing the pivot from `p` to `p+h` changes the squared
vertical coordinate by `a^2 h (2p+h)/2`. -/
theorem orderedEulerPivotVerticalHeight_add_displacement
    (c a p h : ℕ) :
    orderedEulerPivotVerticalHeight c a (p + h) -
        orderedEulerPivotVerticalHeight c a p =
      (a : ℝ) ^ 2 * (h : ℝ) * (2 * (p : ℝ) + (h : ℝ)) / 2 := by
  unfold orderedEulerPivotVerticalHeight
  push_cast
  ring

/-- A positive pivot step at a positive pivot moves by at least one full
`a^2` unit vertically.  Thus even unit pivot spacing is quadratically amplified
in the processed low product. -/
theorem orderedEulerPivotVerticalHeight_add_displacement_ge_lowProduct_sq
    {c a p h : ℕ}
    (hp : 1 ≤ p)
    (hh : 1 ≤ h) :
    (a : ℝ) ^ 2 ≤
      orderedEulerPivotVerticalHeight c a (p + h) -
        orderedEulerPivotVerticalHeight c a p := by
  rw [orderedEulerPivotVerticalHeight_add_displacement]
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hcoef :
      (1 : ℝ) ≤ (h : ℝ) * (2 * (p : ℝ) + (h : ℝ)) / 2 := by
    nlinarith
  have ha2 : 0 ≤ (a : ℝ) ^ 2 := sq_nonneg _
  calc
    (a : ℝ) ^ 2 ≤
        (a : ℝ) ^ 2 *
          ((h : ℝ) * (2 * (p : ℝ) + (h : ℝ)) / 2) := by
      simpa using (mul_le_mul_of_nonneg_left hcoef ha2)
    _ = (a : ℝ) ^ 2 * (h : ℝ) *
          (2 * (p : ℝ) + (h : ℝ)) / 2 := by ring

/-- Exact vertical displacement when a factor `r` is moved from the high side
of a fixed product to the processed side:

`(r*c,q) -> (c,r*q)`.

Both pairs have the same product, while the squared vertical coordinate changes
by `((r^2-1)(q^2+c^2))/2`. -/
theorem squareMapY_primeTransfer_displacement
    (c q r : ℝ) :
    squareMapY c (r * q) - squareMapY (r * c) q =
      (r ^ 2 - 1) * (q ^ 2 + c ^ 2) / 2 := by
  unfold squareMapY
  ring

/-- For `r >= 3`, one prime transfer separates the two vertical positions by
at least four times the complete quadratic radius `q^2+c^2`. -/
theorem squareMapY_primeTransfer_displacement_ge_four_sum_sq
    {c q r : ℝ}
    (hr : 3 ≤ r) :
    4 * (q ^ 2 + c ^ 2) ≤
      squareMapY c (r * q) - squareMapY (r * c) q := by
  rw [squareMapY_primeTransfer_displacement]
  have hcoef : (4 : ℝ) ≤ (r ^ 2 - 1) / 2 := by
    nlinarith
  have hsum : 0 ≤ q ^ 2 + c ^ 2 := by positivity
  calc
    4 * (q ^ 2 + c ^ 2) ≤
        ((r ^ 2 - 1) / 2) * (q ^ 2 + c ^ 2) :=
      mul_le_mul_of_nonneg_right hcoef hsum
    _ = (r ^ 2 - 1) * (q ^ 2 + c ^ 2) / 2 := by ring

/-- In particular, the same transfer gap is at least `4 q^2`. -/
theorem squareMapY_primeTransfer_displacement_ge_four_upper_sq
    {c q r : ℝ}
    (hr : 3 ≤ r) :
    4 * q ^ 2 ≤
      squareMapY c (r * q) - squareMapY (r * c) q := by
  calc
    4 * q ^ 2 ≤ 4 * (q ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg c]
    _ ≤ squareMapY c (r * q) - squareMapY (r * c) q :=
      squareMapY_primeTransfer_displacement_ge_four_sum_sq hr

/-- The generic factor-transfer identity applied directly to two ordered-cut
atoms.  `y` is the earlier cut with high factor `r*c`; `z` is the later cut
with upper factor `r*q`. -/
theorem orderedEulerCutVerticalHeight_primeTransfer_displacement
    {y z : OrderedEulerCutTaggedState} {r : ℕ}
    (hc : orderedEulerCutHighCofactor y =
      r * orderedEulerCutHighCofactor z)
    (hq : orderedEulerCutUpperFactor z =
      r * orderedEulerCutUpperFactor y) :
    orderedEulerCutVerticalHeight z - orderedEulerCutVerticalHeight y =
      (((r : ℝ) ^ 2 - 1) *
        ((orderedEulerCutUpperFactor y : ℝ) ^ 2 +
          (orderedEulerCutHighCofactor z : ℝ) ^ 2)) / 2 := by
  unfold orderedEulerCutVerticalHeight
  rw [hc, hq]
  push_cast
  ring

/-- An odd-prime transfer (`r` prime and `r != 2`) therefore has at least
quadratic `4 q^2` vertical separation. -/
theorem orderedEulerCutVerticalHeight_primeTransfer_gap_ge_four_upper_sq
    {y z : OrderedEulerCutTaggedState} {r : ℕ}
    (hrPrime : r.Prime)
    (hrTwo : r ≠ 2)
    (hc : orderedEulerCutHighCofactor y =
      r * orderedEulerCutHighCofactor z)
    (hq : orderedEulerCutUpperFactor z =
      r * orderedEulerCutUpperFactor y) :
    4 * (orderedEulerCutUpperFactor y : ℝ) ^ 2 ≤
      orderedEulerCutVerticalHeight z - orderedEulerCutVerticalHeight y := by
  rw [orderedEulerCutVerticalHeight_primeTransfer_displacement hc hq]
  have hr3 : 3 ≤ r := by
    have hr2 := hrPrime.two_le
    omega
  have hr3R : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
  have h := squareMapY_primeTransfer_displacement_ge_four_upper_sq
    (c := (orderedEulerCutHighCofactor z : ℝ))
    (q := (orderedEulerCutUpperFactor y : ℝ))
    (r := (r : ℝ)) hr3R
  rw [squareMapY_primeTransfer_displacement] at h
  exact h

/-! ## The fixed-child ordered chain -/

/-- Any actual occurrence has already crossed its low-product threshold. -/
theorem orderedEulerCutOccursAt_lowProduct_le
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hocc : OrderedEulerCutOccursAt R y) :
    orderedEulerCutLowProduct y ≤ R := by
  have hlife := (orderedEulerCutOccursAt_iff_lifetime hy).1 hocc
  have hbirth := hlife.1
  unfold orderedEulerCutBirthRoot at hbirth
  exact (Nat.max_le.mp hbirth).1

/-- The pivot itself is not one of the already-processed face primes. -/
theorem orderedEulerCutPivot_not_mem_face
    {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y) :
    orderedEulerCutPivot y ∉ y.1 := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨_hp, _hc, _hsq, _hpc, hfaces, _hrough⟩
  change p ∉ t
  intro hpt
  exact (Nat.lt_irrefl p) (hfaces p hpt).2

/-- Every processed face prime divides the physical child and lies below the
pivot. -/
theorem orderedEulerCut_facePrime_dvd_child_lt_pivot
    {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    {r : ℕ}
    (hr : r ∈ y.1) :
    r.Prime ∧
      r ∣ orderedEulerCutChildInteger y ∧
      r < orderedEulerCutPivot y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨_hp, _hc, _hsq, _hpc, hfaces, _hrough⟩
  have hdata := hfaces r hr
  have hrprod : r ∣ primeFaceProduct t := by
    unfold primeFaceProduct
    exact Finset.dvd_prod_of_mem id hr
  have hrchild : r ∣ c * (p * primeFaceProduct t) := by
    rcases hrprod with ⟨k, hk⟩
    refine ⟨c * (p * k), ?_⟩
    rw [hk]
    ring
  exact ⟨hdata.1, hrchild, hdata.2⟩

/-- Conversely, every prime divisor of the physical child strictly below the
pivot is already present in the processed face. -/
theorem orderedEulerCut_prime_mem_face_of_dvd_child_lt_pivot
    {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    {r : ℕ}
    (hrPrime : r.Prime)
    (hrDvd : r ∣ orderedEulerCutChildInteger y)
    (hrLt : r < orderedEulerCutPivot y) :
    r ∈ y.1 := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨hp, hc1, _hcsq, _hpc, hfaces, hrough⟩
  change r ∣ c * (p * primeFaceProduct t) at hrDvd
  change r < p at hrLt
  rcases hrPrime.dvd_mul.mp hrDvd with hrc | hrpa
  · have hc0 : c ≠ 0 := by omega
    have hrMem : r ∈ c.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrPrime, hrc, hc0⟩
    have hpr : p < r := hrough r hrMem
    omega
  · rcases hrPrime.dvd_mul.mp hrpa with hrp | hra
    · have hre : r = p :=
        (Nat.prime_dvd_prime_iff_eq hrPrime hp).mp hrp
      omega
    · have hra' : r ∣ t.prod id := by
        simpa [primeFaceProduct] using hra
      rcases (Prime.dvd_finset_prod_iff hrPrime.prime id).mp hra' with
        ⟨q, hqt, hrq⟩
      have hqPrime := (hfaces q hqt).1
      have hre : r = q :=
        (Nat.prime_dvd_prime_iff_eq hrPrime hqPrime).mp hrq
      exact hre ▸ hqt

/-- The pivot always divides its physical child. -/
theorem orderedEulerCutPivot_dvd_child
    (y : OrderedEulerCutTaggedState) :
    orderedEulerCutPivot y ∣ orderedEulerCutChildInteger y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p ∣ c * (p * primeFaceProduct t)
  refine ⟨c * primeFaceProduct t, ?_⟩
  ring

/-- For two cuts of the same physical child, an earlier pivot forces its full
completion factor to divide the later processed low product. -/
theorem orderedEulerCutUpperFactor_dvd_lowProduct_of_same_child_of_pivot_lt
    {y z : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hz : OrderedEulerCutShape z)
    (hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z)
    (hpiv : orderedEulerCutPivot y < orderedEulerCutPivot z) :
    orderedEulerCutUpperFactor y ∣ orderedEulerCutLowProduct z := by
  have hsub : insert (orderedEulerCutPivot y) y.1 ⊆ z.1 := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hre | hrFace
    · subst r
      apply orderedEulerCut_prime_mem_face_of_dvd_child_lt_pivot hz hy.1
      · rw [← hchild]
        exact orderedEulerCutPivot_dvd_child y
      · exact hpiv
    · have hdata := orderedEulerCut_facePrime_dvd_child_lt_pivot hy hrFace
      apply orderedEulerCut_prime_mem_face_of_dvd_child_lt_pivot hz hdata.1
      · rw [← hchild]
        exact hdata.2.1
      · exact lt_trans hdata.2.2 hpiv
  have hprod :
      primeFaceProduct (insert (orderedEulerCutPivot y) y.1) ∣
        primeFaceProduct z.1 := by
    unfold primeFaceProduct
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  have hpNot := orderedEulerCutPivot_not_mem_face hy
  have hleft :
      primeFaceProduct (insert (orderedEulerCutPivot y) y.1) =
        orderedEulerCutUpperFactor y := by
    simp [primeFaceProduct, orderedEulerCutUpperFactor,
      orderedEulerCutDeathRoot, orderedEulerCutLowProduct, hpNot]
  rw [hleft] at hprod
  simpa [orderedEulerCutLowProduct] using hprod

/-- Divisibility gives the corresponding threshold order. -/
theorem orderedEulerCutUpperFactor_le_lowProduct_of_same_child_of_pivot_lt
    {y z : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hz : OrderedEulerCutShape z)
    (hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z)
    (hpiv : orderedEulerCutPivot y < orderedEulerCutPivot z) :
    orderedEulerCutUpperFactor y ≤ orderedEulerCutLowProduct z := by
  exact Nat.le_of_dvd (orderedEulerCutLowProduct_pos hz)
    (orderedEulerCutUpperFactor_dvd_lowProduct_of_same_child_of_pivot_lt
      hy hz hchild hpiv)

/-- Two active cuts at the same root and on the same physical child must have
the same pivot.  Distinct pivots have disjoint root threshold windows. -/
theorem orderedEulerCutPivot_eq_of_same_child_active
    {R : ℕ} {y z : OrderedEulerCutTaggedState}
    (hyMem : y ∈ orderedEulerCutCarrier R)
    (hzMem : z ∈ orderedEulerCutCarrier R)
    (hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z) :
    orderedEulerCutPivot y = orderedEulerCutPivot z := by
  have hy := orderedEulerCutShape_of_mem_carrier hyMem
  have hz := orderedEulerCutShape_of_mem_carrier hzMem
  have hyOcc := mem_orderedEulerCutCarrier.mp hyMem
  have hzOcc := mem_orderedEulerCutCarrier.mp hzMem
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle :=
      orderedEulerCutUpperFactor_le_lowProduct_of_same_child_of_pivot_lt
        hy hz hchild hlt
    have hyUpper := (orderedEulerCutOccursAt_factor_window hy hyOcc).2
    have hzLow := orderedEulerCutOccursAt_lowProduct_le hz hzOcc
    omega
  · have hle :=
      orderedEulerCutUpperFactor_le_lowProduct_of_same_child_of_pivot_lt
        hz hy hchild.symm hgt
    have hzUpper := (orderedEulerCutOccursAt_factor_window hz hzOcc).2
    have hyLow := orderedEulerCutOccursAt_lowProduct_le hy hyOcc
    omega

/-- Same child and same pivot determine the complete low prime face. -/
theorem orderedEulerCutFace_eq_of_same_child_same_pivot
    {y z : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hz : OrderedEulerCutShape z)
    (hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z)
    (hpivot : orderedEulerCutPivot y = orderedEulerCutPivot z) :
    y.1 = z.1 := by
  apply Finset.ext
  intro r
  constructor
  · intro hry
    have hdata := orderedEulerCut_facePrime_dvd_child_lt_pivot hy hry
    apply orderedEulerCut_prime_mem_face_of_dvd_child_lt_pivot hz hdata.1
    · rw [← hchild]
      exact hdata.2.1
    · simpa [hpivot] using hdata.2.2
  · intro hrz
    have hdata := orderedEulerCut_facePrime_dvd_child_lt_pivot hz hrz
    apply orderedEulerCut_prime_mem_face_of_dvd_child_lt_pivot hy hdata.1
    · rw [hchild]
      exact hdata.2.1
    · simpa [hpivot] using hdata.2.2

/-- **One active atom per physical vertical line.**  On the finite ordered-cut
carrier at a fixed root, the physical child integer is injective. -/
theorem orderedEulerCutChildInteger_injective_on_carrier
    {R : ℕ} {y z : OrderedEulerCutTaggedState}
    (hyMem : y ∈ orderedEulerCutCarrier R)
    (hzMem : z ∈ orderedEulerCutCarrier R)
    (hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z) :
    y = z := by
  have hy := orderedEulerCutShape_of_mem_carrier hyMem
  have hz := orderedEulerCutShape_of_mem_carrier hzMem
  have hpivot := orderedEulerCutPivot_eq_of_same_child_active hyMem hzMem hchild
  have hface := orderedEulerCutFace_eq_of_same_child_same_pivot
    hy hz hchild hpivot
  rcases y with ⟨t, ⟨c, p⟩⟩
  rcases z with ⟨u, ⟨d, q⟩⟩
  change p = q at hpivot
  change t = u at hface
  subst u
  subst q
  change c * (p * primeFaceProduct t) =
    d * (p * primeFaceProduct t) at hchild
  have hright : 0 < p * primeFaceProduct t := by
    have hpPrime : p.Prime := hy.1
    have haPos : 0 < primeFaceProduct t := by
      simpa [orderedEulerCutLowProduct] using orderedEulerCutLowProduct_pos hy
    exact Nat.mul_pos hpPrime.pos haPos
  have hcd : c = d := Nat.mul_right_cancel hright hchild
  subst d
  rfl

/-- The child-coordinate map is injective on the complete endpoint carrier. -/
theorem orderedEulerCutChildInteger_injOn_carrier (R : ℕ) :
    Set.InjOn orderedEulerCutChildInteger (orderedEulerCutCarrier R : Set _) := by
  intro y hy z hz hchild
  exact orderedEulerCutChildInteger_injective_on_carrier hy hz hchild

/-- Equal physical children carry equal ordered-cut weights.  The signed charge
is therefore conserved when the representative cut changes. -/
theorem orderedEulerCutWeight_eq_of_same_child
    {y z : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hz : OrderedEulerCutShape z)
    (hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z) :
    orderedEulerCutWeight y = orderedEulerCutWeight z := by
  have hySign := orderedEulerCutChildWeight_eq_neg hy
  have hzSign := orderedEulerCutChildWeight_eq_neg hz
  have hneg : -orderedEulerCutWeight y = -orderedEulerCutWeight z := by
    rw [← hySign, ← hzSign, hchild]
  exact neg_injective hneg

/-- Consecutive on-child cuts mean that there is no prime divisor of the common
child strictly between their pivots. -/
def OrderedEulerCutsConsecutiveOnChild
    (y z : OrderedEulerCutTaggedState) : Prop :=
  orderedEulerCutChildInteger y = orderedEulerCutChildInteger z ∧
    orderedEulerCutPivot y < orderedEulerCutPivot z ∧
    ∀ r : ℕ, r.Prime → r ∣ orderedEulerCutChildInteger y →
      orderedEulerCutPivot y < r → r < orderedEulerCutPivot z → False

/-- **Adjacent Euler thresholds meet exactly.**  For consecutive cuts of the
same child, the later low product equals the earlier completion factor:
`A_{j+1} = q_j`. -/
theorem orderedEulerCutLowProduct_eq_upperFactor_of_consecutive_same_child
    {y z : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hz : OrderedEulerCutShape z)
    (hconsecutive : OrderedEulerCutsConsecutiveOnChild y z) :
    orderedEulerCutLowProduct z = orderedEulerCutUpperFactor y := by
  rcases hconsecutive with ⟨hchild, hpiv, hbetween⟩
  have hforward : insert (orderedEulerCutPivot y) y.1 ⊆ z.1 := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hre | hrFace
    · subst r
      apply orderedEulerCut_prime_mem_face_of_dvd_child_lt_pivot hz hy.1
      · rw [← hchild]
        exact orderedEulerCutPivot_dvd_child y
      · exact hpiv
    · have hdata := orderedEulerCut_facePrime_dvd_child_lt_pivot hy hrFace
      apply orderedEulerCut_prime_mem_face_of_dvd_child_lt_pivot hz hdata.1
      · rw [← hchild]
        exact hdata.2.1
      · exact lt_trans hdata.2.2 hpiv
  have hback : z.1 ⊆ insert (orderedEulerCutPivot y) y.1 := by
    intro r hrz
    have hdata := orderedEulerCut_facePrime_dvd_child_lt_pivot hz hrz
    have hrDvdY : r ∣ orderedEulerCutChildInteger y := by
      rw [hchild]
      exact hdata.2.1
    by_cases hlt : r < orderedEulerCutPivot y
    · exact Finset.mem_insert_of_mem
        (orderedEulerCut_prime_mem_face_of_dvd_child_lt_pivot
          hy hdata.1 hrDvdY hlt)
    · have hge : orderedEulerCutPivot y ≤ r := Nat.le_of_not_gt hlt
      by_cases heq : r = orderedEulerCutPivot y
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · have hpyr : orderedEulerCutPivot y < r := by omega
        exact False.elim
          (hbetween r hdata.1 hrDvdY hpyr hdata.2.2)
  have hface : z.1 = insert (orderedEulerCutPivot y) y.1 :=
    Finset.Subset.antisymm hback hforward
  have hpNot := orderedEulerCutPivot_not_mem_face hy
  change primeFaceProduct z.1 =
    orderedEulerCutPivot y * primeFaceProduct y.1
  rw [hface]
  simp [primeFaceProduct, hpNot]

/-! ## Reindexing by conserved child charge -/

/-- Physical child integers active at one root. -/
def orderedEulerCutActiveChildren (R : ℕ) : Finset ℕ :=
  (orderedEulerCutCarrier R).image orderedEulerCutChildInteger

/-- The conserved signed charge carried by a physical child line. -/
def orderedEulerCutChildCharge (n : ℕ) : ℂ :=
  -canonicalMoebiusWeight n

/-- The endpoint vertical mass can be reindexed without multiplicity by child
integer, because there is at most one active atom on each vertical line. -/
theorem signedVerticalIntervalEndpointMass_eq_sum_activeChildCharges
    (R : ℕ) :
    signedVerticalIntervalEndpointMass R =
      ∑ n ∈ orderedEulerCutActiveChildren R, orderedEulerCutChildCharge n := by
  unfold signedVerticalIntervalEndpointMass orderedEulerCutActiveChildren
    orderedEulerCutChildCharge
  calc
    (∑ y ∈ orderedEulerCutCarrier R, orderedEulerCutWeight y) =
        ∑ y ∈ orderedEulerCutCarrier R,
          -canonicalMoebiusWeight (orderedEulerCutChildInteger y) := by
      apply Finset.sum_congr rfl
      intro y hyMem
      have hshape := orderedEulerCutShape_of_mem_carrier hyMem
      have hsign := orderedEulerCutChildWeight_eq_neg hshape
      have hneg := congrArg Neg.neg hsign
      simpa using hneg.symm
    _ = ∑ n ∈ (orderedEulerCutCarrier R).image orderedEulerCutChildInteger,
        -canonicalMoebiusWeight n := by
      symm
      apply Finset.sum_image
      intro y hyMem z hzMem hchild
      exact orderedEulerCutChildInteger_injective_on_carrier hyMem hzMem hchild

/-- Consequently the run mass is exactly the difference of the conserved child
charges at its two endpoints. -/
theorem signedVerticalIntervalMass_eq_activeChildChargeDifference
    (a b : ℕ) :
    signedVerticalIntervalMass a b =
      (∑ n ∈ orderedEulerCutActiveChildren (b + 1),
        orderedEulerCutChildCharge n) -
      ∑ n ∈ orderedEulerCutActiveChildren a,
        orderedEulerCutChildCharge n := by
  unfold signedVerticalIntervalMass
  rw [signedVerticalIntervalEndpointMass_eq_sum_activeChildCharges,
    signedVerticalIntervalEndpointMass_eq_sum_activeChildCharges]

/-- Endpoint contribution of one physical child line. -/
def orderedEulerCutChildEndpointCharge (R n : ℕ) : ℂ :=
  if n ∈ orderedEulerCutActiveChildren R then orderedEulerCutChildCharge n else 0

/-- A child active at both endpoints contributes zero to the endpoint change:
internal vertical transport cancels from the scalar ledger. -/
theorem orderedEulerCutChildTransport_cancels
    {a b n : ℕ}
    (ha : n ∈ orderedEulerCutActiveChildren a)
    (hb : n ∈ orderedEulerCutActiveChildren (b + 1)) :
    orderedEulerCutChildEndpointCharge (b + 1) n -
      orderedEulerCutChildEndpointCharge a n = 0 := by
  simp [orderedEulerCutChildEndpointCharge, ha, hb]

/-- A newly active child contributes exactly its conserved charge. -/
theorem orderedEulerCutChildBirthContribution
    {a b n : ℕ}
    (ha : n ∉ orderedEulerCutActiveChildren a)
    (hb : n ∈ orderedEulerCutActiveChildren (b + 1)) :
    orderedEulerCutChildEndpointCharge (b + 1) n -
      orderedEulerCutChildEndpointCharge a n = orderedEulerCutChildCharge n := by
  simp [orderedEulerCutChildEndpointCharge, ha, hb]

/-- A child which leaves the active set contributes the negative of its
conserved charge. -/
theorem orderedEulerCutChildDeathContribution
    {a b n : ℕ}
    (ha : n ∈ orderedEulerCutActiveChildren a)
    (hb : n ∉ orderedEulerCutActiveChildren (b + 1)) :
    orderedEulerCutChildEndpointCharge (b + 1) n -
      orderedEulerCutChildEndpointCharge a n = -orderedEulerCutChildCharge n := by
  simp [orderedEulerCutChildEndpointCharge, ha, hb]

/-! ## At most one pivot transition on a strict subdoubling run -/

/-- Strict subdoubling in square time implies the root interval itself is
strictly less than a factor of two. -/
theorem succ_lt_two_mul_of_square_subdoubling
    {a b : ℕ}
    (hsub : (b + 1) ^ 2 < 2 * a ^ 2) :
    b + 1 < 2 * a := by
  by_contra hnot
  have hge : 2 * a ≤ b + 1 := Nat.le_of_not_gt hnot
  have hsquare : (2 * a) ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left hge 2
  nlinarith

/-- Three strictly increasing pivots on one physical child force at least a
factor-two separation between the first completion threshold and the third low
threshold. -/
theorem orderedEulerCut_twoTransition_span
    {y z w : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hz : OrderedEulerCutShape z)
    (hw : OrderedEulerCutShape w)
    (hchildYZ : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z)
    (hchildZW : orderedEulerCutChildInteger z = orderedEulerCutChildInteger w)
    (hpYZ : orderedEulerCutPivot y < orderedEulerCutPivot z)
    (hpZW : orderedEulerCutPivot z < orderedEulerCutPivot w) :
    2 * orderedEulerCutUpperFactor y ≤ orderedEulerCutLowProduct w := by
  have h1 := orderedEulerCutUpperFactor_le_lowProduct_of_same_child_of_pivot_lt
    hy hz hchildYZ hpYZ
  have h2 := orderedEulerCutUpperFactor_le_lowProduct_of_same_child_of_pivot_lt
    hz hw hchildZW hpZW
  have hp2 : 2 ≤ orderedEulerCutPivot z := hz.1.two_le
  have hmid :
      2 * orderedEulerCutLowProduct z ≤ orderedEulerCutUpperFactor z := by
    change 2 * orderedEulerCutLowProduct z ≤
      orderedEulerCutPivot z * orderedEulerCutLowProduct z
    exact Nat.mul_le_mul_right (orderedEulerCutLowProduct z) hp2
  exact le_trans (Nat.mul_le_mul_left 2 h1) (le_trans hmid h2)

/-- **One-transition theorem.**  On a strict subdoubling square run, a fixed
physical child cannot move through two successive ordered Euler pivot changes.
Equivalently, there do not exist three same-child cuts with increasing pivots
such that the first is active at the initial root and the third is active at
the final root. -/
theorem orderedEulerCut_atMostOneTransition_of_subdoubling
    {a b : ℕ} {y z w : OrderedEulerCutTaggedState}
    (hsub : (b + 1) ^ 2 < 2 * a ^ 2)
    (hy : OrderedEulerCutShape y)
    (hz : OrderedEulerCutShape z)
    (hw : OrderedEulerCutShape w)
    (hyOcc : OrderedEulerCutOccursAt a y)
    (hwOcc : OrderedEulerCutOccursAt (b + 1) w)
    (hchildYZ : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z)
    (hchildZW : orderedEulerCutChildInteger z = orderedEulerCutChildInteger w)
    (hpYZ : orderedEulerCutPivot y < orderedEulerCutPivot z)
    (hpZW : orderedEulerCutPivot z < orderedEulerCutPivot w) :
    False := by
  have hspan := orderedEulerCut_twoTransition_span
    hy hz hw hchildYZ hchildZW hpYZ hpZW
  have hyUpper := (orderedEulerCutOccursAt_factor_window hy hyOcc).2
  have hwLow := orderedEulerCutOccursAt_lowProduct_le hw hwOcc
  have hroot := succ_lt_two_mul_of_square_subdoubling hsub
  omega

end RHLean.Proof