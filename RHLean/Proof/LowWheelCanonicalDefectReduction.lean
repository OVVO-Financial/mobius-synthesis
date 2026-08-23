import Mathlib
import RHLean.Proof.LowWheelCanonicalPairingFrontier
import RHLean.Analysis.SquareRootMiddleSequentialCoherence

/-!
# Canonical transport defect reduction

The least-prime cofactor/quotient involution from
`LowWheelCanonicalPairingFrontier` cancels every interior transport state.  This
file pushes that cancellation through the complete low-wheel face sum.

The only fixed cofactor/quotient state is `(1,1)`.  Summed over the Boolean face
`t`, those fixed states are exactly the already-smooth squarefree population in
`(R,R^2-1]`.  Consequently the complete high transport has the exact form

`transport = smooth - M(R) + canonicalDefect`.

Subtracting transport from smooth therefore removes both large populations and
leaves the endpoint identity

`M(R^2-1) = M(R) - canonicalDefect`.

Every term of `canonicalDefect` lies on the single quotient root-downcross
frontier of the canonical least-prime toggle.  The apparent cofactor boundary
is absorbed by the square-endpoint product ceiling.  In fact the abstract
missing-mate predicate can be removed completely: the defect is exactly the
physical insertion state whose least-prime pivot is absent from the cofactor
and whose pivot-removal quotient has crossed down through the root.  Hence the
survivor is an adjacent multiplicative shell state

`P(t)*(k/p) <= R < P(t)*p*(k/p)`.

Thus the remaining fixed-amplification problem is a signed estimate on one
genuine first-failure frontier ledger, not on the full transport or a union of
unrelated boundaries.

No norm, PNT estimate, asymptotic, or RH input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- On a positive cofactor, the canonical least-prime toggle is fixed exactly
at the product-one state. -/
theorem lowWheelCanonicalToggle_eq_self_iff_product_eq_one
    {c k : ℕ} (hc : 0 < c) :
    lowWheelCanonicalCofactorQuotientToggle (c, k) = (c, k) ↔
      c * k = 1 := by
  constructor
  · intro hfix
    by_contra hprod
    let p := lowWheelCanonicalCofactorQuotientPivot (c, k)
    have hp : p.Prime := by
      simpa [p] using lowWheelCanonicalCofactorQuotientPivot_prime hprod
    have hactive : p ∣ c ∨ p ∣ k := by
      simpa [p] using lowWheelCanonicalCofactorQuotientPivot_active hprod
    change lowWheelCofactorQuotientToggleAt p (c, k) = (c, k) at hfix
    unfold lowWheelCofactorQuotientToggleAt at hfix
    by_cases hpc : p ∣ c
    · simp only [hpc, if_true] at hfix
      have hfirst : c / p = c := congrArg Prod.fst hfix
      have hlt : c / p < c := Nat.div_lt_self hc hp.one_lt
      omega
    · have hpk : p ∣ k := hactive.resolve_left hpc
      simp only [hpc, if_false, hpk, if_true] at hfix
      have hfirst : c * p = c := congrArg Prod.fst hfix
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith
  · exact lowWheelCanonicalToggle_eq_self_of_product_eq_one

/-- In the actual physical carrier the fixed part is either the singleton
`(1,1)` or empty, according to whether the low-wheel face itself lies in the
high square shell. -/
theorem lowWheelCanonicalPhysicalFixedPart_eq_singleton_or_empty
    (R : ℕ) (hR : 2 ≤ R) (t : Finset ℕ) :
    lowWheelCanonicalFixedPart (lowWheelCanonicalPhysicalStateSet R t) =
      if R < primeFaceProduct t ∧
          primeFaceProduct t ≤ squareRootEndpoint R then
        ({(1, 1)} : Finset LowWheelCofactorQuotientState)
      else
        ∅ := by
  classical
  by_cases hgeom :
      R < primeFaceProduct t ∧ primeFaceProduct t ≤ squareRootEndpoint R
  · rw [if_pos hgeom]
    ext x
    rcases x with ⟨c, k⟩
    constructor
    · intro hx
      have hdata := Finset.mem_filter.mp hx
      have hmem := mem_lowWheelCanonicalPhysicalStateSet.mp hdata.1
      have hcpos : 0 < c := by
        have hc1 := (Finset.mem_Ico.mp hmem.1).1
        omega
      have hprod :=
        (lowWheelCanonicalToggle_eq_self_iff_product_eq_one hcpos).mp hdata.2
      have hkpos : 0 < k := by
        by_contra hk
        have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
        subst k
        simp at hprod
      have hcLe : c ≤ 1 := by
        have hmul : c * 1 ≤ c * k :=
          Nat.mul_le_mul_left c (by omega : 1 ≤ k)
        simpa [hprod] using hmul
      have hcEq : c = 1 := by omega
      subst c
      have hkEq : k = 1 := by simpa using hprod
      subst k
      simp
    · intro hx
      have hxone : (c, k) = (1, 1) := by simpa using hx
      cases hxone
      apply Finset.mem_filter.mpr
      constructor
      · apply mem_lowWheelCanonicalPhysicalStateSet.mpr
        refine ⟨Finset.mem_Ico.mpr ⟨by norm_num, by omega⟩, ?_, by simp, ?_⟩
        · apply Finset.mem_Icc.mpr
          constructor
          · norm_num
          · omega
        · exact ⟨by norm_num, by omega, by simpa using hgeom.1,
            by simpa using hgeom.2⟩
      · exact lowWheelCanonicalToggle_eq_self_of_product_eq_one (by norm_num)
  · rw [if_neg hgeom]
    ext x
    constructor
    · intro hx
      have hdata := Finset.mem_filter.mp hx
      have hmem := mem_lowWheelCanonicalPhysicalStateSet.mp hdata.1
      have hcpos : 0 < x.1 := by
        have hc1 := (Finset.mem_Ico.mp hmem.1).1
        omega
      have hprod :=
        (lowWheelCanonicalToggle_eq_self_iff_product_eq_one hcpos).mp hdata.2
      have hkpos : 0 < x.2 := by
        by_contra hk
        have hk0 : x.2 = 0 := Nat.eq_zero_of_not_pos hk
        rw [hk0] at hprod
        simp at hprod
      have hcLe : x.1 ≤ 1 := by
        have hmul : x.1 * 1 ≤ x.1 * x.2 :=
          Nat.mul_le_mul_left x.1 (by omega : 1 ≤ x.2)
        simpa [hprod] using hmul
      have hcEq : x.1 = 1 := by omega
      have hkEq : x.2 = 1 := by simpa [hcEq] using hprod
      have hxone : x = (1, 1) := Prod.ext hcEq hkEq
      subst x
      have hcarrier := hmem.2.2.2
      exfalso
      apply hgeom
      constructor
      · simpa [LowWheelTransportPairCarrier] using hcarrier.2.2.1
      · simpa [LowWheelTransportPairCarrier] using hcarrier.2.2.2
    · simp

/-- Fixed mass in one Boolean face. -/
theorem sum_lowWheelCanonicalPhysicalFixedPart
    (R : ℕ) (hR : 2 ≤ R) (t : Finset ℕ) :
    (∑ x ∈ lowWheelCanonicalFixedPart (lowWheelCanonicalPhysicalStateSet R t),
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      if R < primeFaceProduct t ∧
          primeFaceProduct t ≤ squareRootEndpoint R then
        (booleanCubeSign t : ℂ)
      else
        0 := by
  rw [lowWheelCanonicalPhysicalFixedPart_eq_singleton_or_empty R hR t]
  split_ifs with hgeom
  · simp [canonicalMoebiusWeight]
  · simp

/-- Full physical transport carrier after the cofactor/quotient coordinates are
made explicit. -/
def lowWheelCanonicalPhysicalLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelCanonicalPhysicalStateSet R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- Global fixed-state contribution of the canonical pairing. -/
def lowWheelCanonicalFixedLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelCanonicalFixedPart (lowWheelCanonicalPhysicalStateSet R t),
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- Global mate-crosses-geometry contribution. -/
def lowWheelCanonicalDefectLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelCanonicalDefectPart (lowWheelCanonicalPhysicalStateSet R t),
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- Interior pair cancellation survives the complete low-wheel face sum. -/
theorem lowWheelCanonicalPhysicalLedger_eq_fixed_add_defect (R : ℕ) :
    lowWheelCanonicalPhysicalLedger R =
      lowWheelCanonicalFixedLedger R + lowWheelCanonicalDefectLedger R := by
  unfold lowWheelCanonicalPhysicalLedger lowWheelCanonicalFixedLedger
    lowWheelCanonicalDefectLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  exact sum_lowWheelCanonicalPhysicalState_eq_fixed_add_defect R t

/-- For one fixed old face, the actual physical `(c,k)` carrier is exactly the
quotient interval used by the transport triple ledger, after the harmless
nonsquarefree cofactors (whose Möbius weight is zero) are removed. -/
theorem sum_lowWheelCanonicalPhysicalState_eq_tripleFiber
    (R : ℕ) {t : Finset ℕ} (ht : t ∈ (primesUpTo R).powerset) :
    (∑ x ∈ lowWheelCanonicalPhysicalStateSet R t,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ c ∈ Finset.Ico 1 R,
        ∑ _k ∈ Finset.Ioc
            (R / primeFaceProduct t)
            (squareRootEndpoint R / (c * primeFaceProduct t)),
          canonicalMoebiusWeight c * (booleanCubeSign t : ℂ) := by
  classical
  unfold lowWheelCanonicalPhysicalStateSet
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro c hc
  have hcpos : 0 < c := by
    have hc1 := (Finset.mem_Ico.mp hc).1
    omega
  have hset :
      (Finset.Icc 1 (squareRootEndpoint R)).filter
          (fun k => LowWheelTransportPairCarrier R t (c, k)) =
        Finset.Ioc
          (R / primeFaceProduct t)
          (squareRootEndpoint R / (c * primeFaceProduct t)) := by
    ext k
    have hinterval := mem_lowWheelTransport_quotientInterval_iff
      (R := R) (c := c) (k := k) (t := t) hcpos ht
    constructor
    · intro hk
      have hdata := Finset.mem_filter.mp hk
      have hcarrier := hdata.2
      apply hinterval.mpr
      exact ⟨hcarrier.2.2.1, hcarrier.2.2.2⟩
    · intro hk
      have hbounds := hinterval.mp hk
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · have hkLower := (Finset.mem_Ioc.mp hk).1
          have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hkLower
          exact Nat.succ_le_iff.mpr hkpos
        · have hkUpper := (Finset.mem_Ioc.mp hk).2
          exact hkUpper.trans (Nat.div_le_self _ _)
      · have hcData := Finset.mem_Ico.mp hc
        exact ⟨hcData.1, hcData.2, hbounds.1, hbounds.2⟩
  by_cases hsq : Squarefree c
  · simp only [hsq, true_and]
    rw [← Finset.sum_filter, hset]
  · have hmu : μ c = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    simp [hsq, canonicalMoebiusWeight, hmu]

/-- The physical carrier is exactly the prime-count-free transport triple
ledger. -/
theorem lowWheelCanonicalPhysicalLedger_eq_tripleLedger (R : ℕ) :
    lowWheelCanonicalPhysicalLedger R = lowWheelTransportTripleLedger R := by
  unfold lowWheelCanonicalPhysicalLedger lowWheelTransportTripleLedger
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  exact sum_lowWheelCanonicalPhysicalState_eq_tripleFiber R ht

/-- Hence the original high transport itself is the physical carrier on which
the canonical involution acts. -/
theorem squareRootTransportCofactorFirst_eq_canonicalPhysicalLedger
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R = lowWheelCanonicalPhysicalLedger R := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelTransportTripleLedger R hR,
    lowWheelCanonicalPhysicalLedger_eq_tripleLedger]

/-- The global fixed contribution is the finite smooth universe above the root:
`F_R(X_R) - F_R(R)`. -/
theorem lowWheelCanonicalFixedLedger_eq_frozenDifference
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelCanonicalFixedLedger R =
      ((frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R) : ℤ) : ℂ) -
        ((frozenPrimeUniverseMass (primesUpTo R) R : ℤ) : ℂ) := by
  unfold lowWheelCanonicalFixedLedger
  simp_rw [sum_lowWheelCanonicalPhysicalFixedPart R hR]
  rw [frozenPrimeUniverseMass_eq_cutoffSum,
    frozenPrimeUniverseMass_eq_cutoffSum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  have hRX : R ≤ squareRootEndpoint R := by
    have htwo : R + 1 ≤ 2 * R := by omega
    have hmul : 2 * R ≤ R * R := Nat.mul_le_mul_right R hR
    have hplus : R + 1 ≤ R ^ 2 := by
      calc
        R + 1 ≤ 2 * R := htwo
        _ ≤ R * R := hmul
        _ = R ^ 2 := by ring
    unfold squareRootEndpoint
    omega
  by_cases hX : primeFaceProduct t ≤ squareRootEndpoint R
  · by_cases hsmall : primeFaceProduct t ≤ R
    · have hnot : ¬ R < primeFaceProduct t := Nat.not_lt.mpr hsmall
      simp [hX, hsmall, hnot]
    · have hhigh : R < primeFaceProduct t := Nat.lt_of_not_ge hsmall
      simp [hX, hsmall, hhigh]
  · have hsmall : ¬ primeFaceProduct t ≤ R := by
      intro h
      exact hX (h.trans hRX)
    have hhigh : R < primeFaceProduct t := Nat.lt_of_not_ge hsmall
    simp [hX, hsmall, hhigh]

/-- The fixed carrier is exactly `smooth - M(R)`. -/
theorem lowWheelCanonicalFixedLedger_eq_smooth_sub_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalFixedLedger R =
      squareRootSmoothMass (R - 1) - mertensSummatory R := by
  rw [lowWheelCanonicalFixedLedger_eq_frozenDifference R (by omega)]
  rw [squareRootFrozenPrimeUniverseMass_eq_smooth R hR]
  rw [frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens (X := R) (Y := R) le_rfl]

/-- **Transport defect reduction.**  All interior transport mass has disappeared:
the original high transport is smooth mass minus the lower Mertens prefix, plus
only the canonical root-crossing defect. -/
theorem squareRootTransportCofactorFirst_eq_smooth_sub_mertens_add_defect
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTransportCofactorFirst R =
      squareRootSmoothMass (R - 1) - mertensSummatory R +
        lowWheelCanonicalDefectLedger R := by
  rw [squareRootTransportCofactorFirst_eq_canonicalPhysicalLedger R (by omega),
    lowWheelCanonicalPhysicalLedger_eq_fixed_add_defect,
    lowWheelCanonicalFixedLedger_eq_smooth_sub_mertens R hR]

/-- **Endpoint as a pure canonical boundary defect.**  At a complete square,
the two large smooth/transport populations cancel exactly, leaving the lower
Mertens state at `R` minus the explicit mate-crosses-root ledger. -/
theorem squarePrefixMertens_eq_mertens_sub_canonicalDefect
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) =
      mertensSummatory R - lowWheelCanonicalDefectLedger R := by
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_pred_eq_cofactorFirst R (by omega),
    squareRootTransportCofactorFirst_eq_smooth_sub_mertens_add_defect R hR]
  ring

/-- Shifted form matching the fixed-amplification Mertens numerator. -/
theorem squarePrefixMertens_sub_one_eq_lower_sub_canonicalDefect
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) - 1 =
      (mertensSummatory R - 1) - lowWheelCanonicalDefectLedger R := by
  rw [squarePrefixMertens_eq_mertens_sub_canonicalDefect R hR]
  ring

/-- Every state contributing to the remaining global defect lies on one of the
original two root-crossing surfaces.  Retained for compatibility. -/
theorem lowWheelCanonicalDefectLedger_state_boundary
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDefectPart
      (lowWheelCanonicalPhysicalStateSet R t)) :
    R ≤ x.1 * lowWheelCanonicalCofactorQuotientPivot x ∨
      primeFaceProduct t *
          (x.2 / lowWheelCanonicalCofactorQuotientPivot x) ≤ R :=
  lowWheelCanonicalPhysicalDefect_boundary hx

/-- **Surviving defect reduced to one frontier.**  Every state in the endpoint
defect ledger is a canonical quotient root-downcross. -/
theorem lowWheelCanonicalDefectLedger_state_downcross
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDefectPart
      (lowWheelCanonicalPhysicalStateSet R t)) :
    primeFaceProduct t *
        (x.2 / lowWheelCanonicalCofactorQuotientPivot x) ≤ R :=
  lowWheelCanonicalPhysicalDefect_downcross hx

/-! ## Remove the abstract missing-mate predicate -/

/-- Explicit one-sided carrier for the surviving defect.  A state is retained
exactly when it is physical, the canonical pivot is not already in the cofactor
(removal states always pair), and removing that pivot from the quotient crosses
back through the root. -/
def lowWheelCanonicalDowncrossPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalPhysicalStateSet R t).filter fun x =>
    ¬ lowWheelCanonicalCofactorQuotientPivot x ∣ x.1 ∧
      primeFaceProduct t *
          (x.2 / lowWheelCanonicalCofactorQuotientPivot x) ≤ R

@[simp] theorem mem_lowWheelCanonicalDowncrossPart
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelCanonicalDowncrossPart R t ↔
      x ∈ lowWheelCanonicalPhysicalStateSet R t ∧
      ¬ lowWheelCanonicalCofactorQuotientPivot x ∣ x.1 ∧
      primeFaceProduct t *
          (x.2 / lowWheelCanonicalCofactorQuotientPivot x) ≤ R := by
  simp [lowWheelCanonicalDowncrossPart]

/-- A genuine defect can never point in the removal direction: if its canonical
pivot divided the cofactor, the existing removal theorem would put the mate
back in the physical carrier. -/
theorem lowWheelCanonicalPhysicalDefect_pivot_not_dvd_cofactor
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDefectPart
      (lowWheelCanonicalPhysicalStateSet R t)) :
    ¬ lowWheelCanonicalCofactorQuotientPivot (c, k) ∣ c := by
  have hdata := Finset.mem_filter.mp hx
  have hxF := hdata.1
  have hnotmate := hdata.2
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  have hprod : c * k ≠ 1 := by
    intro hone
    have hfix := lowWheelCanonicalToggle_eq_self_of_product_eq_one hone
    apply hnotmate
    rw [hfix]
    exact hxF
  intro hpc
  have hp := lowWheelCanonicalCofactorQuotientPivot_prime hprod
  have hmateCarrier : LowWheelTransportPairCarrier R t
      (lowWheelCanonicalCofactorQuotientToggle (c, k)) := by
    unfold lowWheelCanonicalCofactorQuotientToggle
    exact lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
      hp hcarrier hpc
  exact hnotmate
    (lowWheelCanonicalToggle_mem_physical_of_carrier hxF hprod hmateCarrier)

/-- **Exact defect identification.**  The abstract missing-mate defect is exactly
the explicit one-sided downcross carrier. -/
theorem lowWheelCanonicalDefectPart_eq_downcrossPart
    (R : ℕ) (t : Finset ℕ) :
    lowWheelCanonicalDefectPart (lowWheelCanonicalPhysicalStateSet R t) =
      lowWheelCanonicalDowncrossPart R t := by
  classical
  ext x
  rcases x with ⟨c, k⟩
  constructor
  · intro hx
    apply mem_lowWheelCanonicalDowncrossPart.mpr
    exact ⟨(Finset.mem_filter.mp hx).1,
      lowWheelCanonicalPhysicalDefect_pivot_not_dvd_cofactor hx,
      lowWheelCanonicalPhysicalDefect_downcross hx⟩
  · intro hx
    rcases mem_lowWheelCanonicalDowncrossPart.mp hx with
      ⟨hxF, hpc, hdown⟩
    apply Finset.mem_filter.mpr
    refine ⟨hxF, ?_⟩
    intro hmate
    have hprod : c * k ≠ 1 := by
      intro hone
      apply hpc
      unfold lowWheelCanonicalCofactorQuotientPivot
      rw [hone]
      simp
    have hactive := lowWheelCanonicalCofactorQuotientPivot_active hprod
    have hpk := hactive.resolve_left hpc
    have hmateCarrier :=
      (mem_lowWheelCanonicalPhysicalStateSet.mp hmate).2.2.2
    change LowWheelTransportPairCarrier R t
      (lowWheelCofactorQuotientToggleAt
        (lowWheelCanonicalCofactorQuotientPivot (c, k)) (c, k)) at hmateCarrier
    unfold lowWheelCofactorQuotientToggleAt at hmateCarrier
    simp only [hpc, if_false, hpk, if_true] at hmateCarrier
    exact (Nat.not_lt_of_ge hdown) hmateCarrier.2.2.1

/-- Every explicit downcross state is literally an adjacent multiplicative
least-prime shell.  The source lies above the root, while removing its canonical
pivot drops the quotient side to or below the root. -/
theorem lowWheelCanonicalDowncrossPart_adjacent_shell
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossPart R t) :
    (lowWheelCanonicalCofactorQuotientPivot (c, k)).Prime ∧
      ¬ lowWheelCanonicalCofactorQuotientPivot (c, k) ∣ c ∧
      lowWheelCanonicalCofactorQuotientPivot (c, k) ∣ k ∧
      primeFaceProduct t *
          (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) ≤ R ∧
      R < primeFaceProduct t *
          (lowWheelCanonicalCofactorQuotientPivot (c, k) *
            (k / lowWheelCanonicalCofactorQuotientPivot (c, k))) := by
  rcases mem_lowWheelCanonicalDowncrossPart.mp hx with
    ⟨hxF, hpc, hdown⟩
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  have hprod : c * k ≠ 1 := by
    intro hone
    apply hpc
    unfold lowWheelCanonicalCofactorQuotientPivot
    rw [hone]
    simp
  have hp := lowWheelCanonicalCofactorQuotientPivot_prime hprod
  have hactive := lowWheelCanonicalCofactorQuotientPivot_active hprod
  have hpk := hactive.resolve_left hpc
  refine ⟨hp, hpc, hpk, hdown, ?_⟩
  have hkCancel :
      lowWheelCanonicalCofactorQuotientPivot (c, k) *
          (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) = k :=
    Nat.mul_div_cancel' hpk
  rw [hkCancel]
  exact hcarrier.2.2.1

/-- Global signed ledger on the explicit one-sided first-failure carrier. -/
def lowWheelCanonicalDowncrossLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelCanonicalDowncrossPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- The former canonical defect ledger contains no additional states: it is
exactly the explicit quotient-downcross ledger. -/
theorem lowWheelCanonicalDefectLedger_eq_downcrossLedger (R : ℕ) :
    lowWheelCanonicalDefectLedger R = lowWheelCanonicalDowncrossLedger R := by
  unfold lowWheelCanonicalDefectLedger lowWheelCanonicalDowncrossLedger
  apply Finset.sum_congr rfl
  intro t _ht
  rw [lowWheelCanonicalDefectPart_eq_downcrossPart R t]

/-- **Endpoint with the surviving defect fully explicit.**  No missing-mate
predicate remains: the complete square endpoint is the lower Mertens state
minus one signed adjacent root-downcross ledger. -/
theorem squarePrefixMertens_eq_mertens_sub_canonicalDowncross
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) =
      mertensSummatory R - lowWheelCanonicalDowncrossLedger R := by
  rw [squarePrefixMertens_eq_mertens_sub_canonicalDefect R hR,
    lowWheelCanonicalDefectLedger_eq_downcrossLedger]

/-- Shifted endpoint form with the same explicit adjacent-shell residual. -/
theorem squarePrefixMertens_sub_one_eq_lower_sub_canonicalDowncross
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) - 1 =
      (mertensSummatory R - 1) - lowWheelCanonicalDowncrossLedger R := by
  rw [squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR]
  ring

end RHLean.Proof
