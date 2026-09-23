import RHLean.Proof.LowWheelFrozenSquareResidualQ2Telescope

/-!
# Parent-product reassembly of the frozen q^2 square residual

After an earlier layer the low-side square residual is an exact signed sum over
source scales `A`, square owners `q`, and stripped daughters `d`.  The remaining
outer factor `mu(A)` must not be treated as a selected-prime surrogate: it is
part of the true Mobius sign of the arithmetic product `A*d`.

This file starts that parent reassembly without taking a norm.  It proves that
every `(A,d)` occurring in a q^2 daughter window is realized by a genuine
ordered Euler cut at the original root, with child integer exactly `A*d`.
Consequently the product carries the exact true Mobius weight

`mu(A*d) = mu(A) * mu(d)`.

The same realization gives the two geometric facts needed downstream:
`R < A*d` and `q^2*(A*d) <= X_R`.  Finally, uniqueness of the ordered Euler
cut proves that for a fixed owner `q` the product map `(A,d) |-> A*d` is
injective across *different source scales*.  Thus the next Fubini step may
collapse the outer source-scale parity into an honest Mobius carrier without
multiplicity.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- A stripped q^2 daughter at a represented source scale is a genuine ordered
Euler-cut child at the old root.  The construction also works for `d=1`, so the
terminal daughter is not silently discarded. -/
theorem lowWheelFrozenSquareResidualDaughter_realizedCut
    {R A q d : ℕ}
    (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (hd : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q) :
    ∃ z ∈ orderedEulerCutCarrier R,
      lowWheelFrozenSecondContactSourceScale z = A ∧
      z.2.1 = d ∧
      orderedEulerCutChildInteger z = A * d := by
  rcases Finset.mem_image.mp hA with ⟨y, hySecond, hyA⟩
  have hyFrozen := (Finset.mem_filter.mp hySecond).1
  have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  have ho := orderedEulerCutShape_of_mem_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hyFrozen)
  rcases Finset.mem_filter.mp hd with ⟨hdIcc, hdSq, hdRough, _hdLt⟩
  rcases Finset.mem_Icc.mp hdIcc with ⟨hd1, hdUpper⟩
  let p := lowWheelTaggedDowncrossPivot y
  let z : LowWheelTaggedDowncrossState := (y.1, (d, p))
  have hpA : canonicalLargestPrimeFactor A = p := by
    rw [← hyA]
    exact lowWheelFrozenSecondContact_sourceScale_largestPrime hySecond
  have hrough : RoughAbove p d := by
    simpa [hpA] using hdRough
  have hzShape : OrderedEulerCutShape z := by
    refine ⟨hs.2.1, hd1, hdSq,
      RoughAbove.not_dvd hs.2.1 hd1 hrough, ?_, hrough⟩
    intro r hr
    exact ⟨(ho.2.2.2.2.1 r hr).1,
      lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hr⟩
  have hpivot : lowWheelTaggedDowncrossPivot z = p :=
    orderedEulerCutShape_canonicalPivot hzShape
  have hzA : lowWheelFrozenSecondContactSourceScale z = A := by
    change lowWheelTaggedDowncrossPivot z * primeFaceProduct y.1 = A
    rw [hpivot]
    simpa [p, lowWheelFrozenSecondContactSourceScale] using hyA
  have hApos : 0 < A :=
    (Nat.zero_le R).trans_lt (lowWheelFrozenSourceScale_root_lt hA)
  have hBroot := lowWheelFrozenSourceScale_cutoff_lt_root hA
  have hdB : d ≤ squareRootEndpoint R / A := by
    exact hdUpper.trans (Nat.div_le_self _ _)
  have hzChild : orderedEulerCutChildInteger z ≤ squareRootEndpoint R := by
    change d * (p * primeFaceProduct y.1) ≤ squareRootEndpoint R
    have hbase : p * primeFaceProduct y.1 = A := by
      simpa [p, lowWheelFrozenSecondContactSourceScale] using hyA
    rw [hbase]
    exact (Nat.le_div_iff_mul_le hApos).1 hdB
  have hzSqrt := (orderedEulerCutChild_le_endpoint_iff hzShape).1 hzChild
  have hzBirth : orderedEulerCutBirthRoot z ≤ R := by
    change max (primeFaceProduct y.1)
      (max (d + 1) (Nat.sqrt (orderedEulerCutChildInteger z) + 1)) ≤ R
    exact max_le
      (lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root hyFrozen)
      (max_le (by omega) (by omega))
  have hzDeath : R < orderedEulerCutDeathRoot z := by
    change R < p * primeFaceProduct y.1
    have hroot := lowWheelFrozenSourceScale_root_lt hA
    have hbase : p * primeFaceProduct y.1 = A := by
      simpa [p, lowWheelFrozenSecondContactSourceScale] using hyA
    rw [hbase]
    exact hroot
  have hzCarrier : z ∈ orderedEulerCutCarrier R :=
    mem_orderedEulerCutCarrier_iff_shape_lifetime.mpr
      ⟨hzShape, hzBirth, hzDeath⟩
  have hchildEq : orderedEulerCutChildInteger z = A * d := by
    change d * (p * primeFaceProduct y.1) = A * d
    have hbase : p * primeFaceProduct y.1 = A := by
      simpa [p, lowWheelFrozenSecondContactSourceScale] using hyA
    rw [hbase]
    ac_rfl
  exact ⟨z, hzCarrier, hzA, rfl, hchildEq⟩

/-- The remaining source-scale sign in an earlier layer is exactly the true Mobius sign of
the parent product.  This is the parity-completion step: no finite selected
Mobius field is substituted. -/
theorem lowWheelFrozenSquareResidualDaughter_productWeight
    {R A q d : ℕ}
    (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (hd : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q) :
    canonicalMoebiusWeight (A * d) =
      canonicalMoebiusWeight A * canonicalMoebiusWeight d := by
  rcases Finset.mem_image.mp hA with ⟨y, hySecond, hyA⟩
  have hyFrozen := (Finset.mem_filter.mp hySecond).1
  have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  have ho := orderedEulerCutShape_of_mem_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hyFrozen)
  rcases Finset.mem_filter.mp hd with ⟨hdIcc, hdSq, hdRough, _hdLt⟩
  have hd1 := (Finset.mem_Icc.mp hdIcc).1
  let p := lowWheelTaggedDowncrossPivot y
  let z : LowWheelTaggedDowncrossState := (y.1, (d, p))
  have hpA : canonicalLargestPrimeFactor A = p := by
    rw [← hyA]
    exact lowWheelFrozenSecondContact_sourceScale_largestPrime hySecond
  have hrough : RoughAbove p d := by
    simpa [hpA] using hdRough
  have hzShape : OrderedEulerCutShape z := by
    refine ⟨hs.2.1, hd1, hdSq,
      RoughAbove.not_dvd hs.2.1 hd1 hrough, ?_, hrough⟩
    intro r hr
    exact ⟨(ho.2.2.2.2.1 r hr).1,
      lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hr⟩
  have hchild : orderedEulerCutChildInteger z = A * d := by
    change d * (p * primeFaceProduct y.1) = A * d
    have hbase : p * primeFaceProduct y.1 = A := by
      simpa [p, lowWheelFrozenSecondContactSourceScale] using hyA
    rw [hbase]
    ac_rfl
  have hflip := orderedEulerCutChildWeight_eq_neg hzShape
  have hscale :=
    lowWheelFrozenSecondContactSourceScale_moebius_eq_neg_faceSign hySecond
  have hscaleA : canonicalMoebiusWeight A = -(booleanCubeSign y.1 : ℂ) := by
    simpa [hyA] using hscale
  calc
    canonicalMoebiusWeight (A * d) =
        canonicalMoebiusWeight (orderedEulerCutChildInteger z) := by rw [hchild]
    _ = -orderedEulerCutWeight z := hflip
    _ = -(canonicalMoebiusWeight d * (booleanCubeSign y.1 : ℂ)) := by rfl
    _ = canonicalMoebiusWeight A * canonicalMoebiusWeight d := by
      rw [hscaleA]
      ring

/-- Every reassembled daughter product is strictly above the old root. -/
theorem lowWheelFrozenSquareResidualDaughter_product_root_lt
    {R A q d : ℕ}
    (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (hd : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q) :
    R < A * d := by
  have hroot := lowWheelFrozenSourceScale_root_lt hA
  have hd1 : 1 ≤ d :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hle : A ≤ A * d := by
    simpa using Nat.mul_le_mul_left A hd1
  exact hroot.trans_le hle

/-- The same product lies at the genuine square-dilated owner cutoff. -/
theorem lowWheelFrozenSquareResidualDaughter_ownerSquare_mul_product_le_endpoint
    {R A q d : ℕ}
    (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (hd : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q) :
    q * q * (A * d) ≤ squareRootEndpoint R := by
  rcases Finset.mem_filter.mp hd with ⟨hdIcc, _hdSq, _hdRough, hdLt⟩
  have hdUpper := (Finset.mem_Icc.mp hdIcc).2
  have hApos : 0 < A :=
    (Nat.zero_le R).trans_lt (lowWheelFrozenSourceScale_root_lt hA)
  have hqPos : 0 < q := by omega
  have hqqPos : 0 < q * q := Nat.mul_pos hqPos hqPos
  have hq2d : q * q * d ≤ squareRootEndpoint R / A := by
    have h := (Nat.le_div_iff_mul_le hqqPos).1 hdUpper
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hmul : A * (q * q * d) ≤ squareRootEndpoint R := by
    have hdiv := Nat.div_mul_le_self (squareRootEndpoint R) A
    have hscaled := Nat.mul_le_mul_left A hq2d
    exact hscaled.trans (by simpa [Nat.mul_comm] using hdiv)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul

/-- For a fixed square owner `q`, two source-scale/daughter pairs cannot map to
the same arithmetic product.  The proof is physical: both products are genuine
ordered-Euler children, and that carrier has one atom per child integer. -/
theorem lowWheelFrozenSquareResidualDaughter_product_injective_fixedOwner
    {R q A d A' d' : ℕ}
    (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (hd : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q)
    (hA' : A' ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (hd' : d' ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A') (squareRootEndpoint R / A') q)
    (hprod : A * d = A' * d') :
    A = A' ∧ d = d' := by
  rcases lowWheelFrozenSquareResidualDaughter_realizedCut hA hd with
    ⟨z, hz, hzA, hzd, hzchild⟩
  rcases lowWheelFrozenSquareResidualDaughter_realizedCut hA' hd' with
    ⟨w, hw, hwA, hwd, hwchild⟩
  have hchild : orderedEulerCutChildInteger z = orderedEulerCutChildInteger w := by
    rw [hzchild, hwchild]
    exact hprod
  have hzw := orderedEulerCutChildInteger_injective_on_carrier hz hw hchild
  constructor
  · calc
      A = lowWheelFrozenSecondContactSourceScale z := hzA.symm
      _ = lowWheelFrozenSecondContactSourceScale w := congrArg _ hzw
      _ = A' := hwA
  · calc
      d = z.2.1 := hzd.symm
      _ = w.2.1 := congrArg (fun u : LowWheelTaggedDowncrossState => u.2.1) hzw
      _ = d' := hwd

end RHLean.Proof
