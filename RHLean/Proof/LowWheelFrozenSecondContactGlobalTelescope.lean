import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactWindowReassembly
import RHLean.Proof.LowWheelCanonicalRepeatedFrozenCofactorMate
import RHLean.Arithmetic.PrimeFaceMoebius

/-!
# Global telescope for the saturated frozen second-contact ledger

The saturated object must not be estimated owner-by-owner.  This
module takes the opposite order of operations: first sum the complete signed
owner windows, then telescope their moving upper endpoints globally.

For

`D_q = F_{q^-}(X_R/q) - F_{q^-}(max R (X_R/q^2))`,

the entire `X_R/q` column is exactly the upper-column telescope already proved
for the frozen Euler universe.  Hence

`sum_q D_q = 1 - F_{R-1}(X_R)
               - sum_q F_{q^-}(max R (X_R/q^2))`.

No norm, owner count, PNT input, Mertens hypothesis, or asymptotic estimate is
introduced.  This is the global signed Stokes form of the ledger.

The final lemmas also record a structural limitation of the current ordinary
prime-toggle matching on the arithmetic child carrier: multiplying by a factor
strictly above the canonical largest-prime owner immediately crosses the
physical endpoint, while deleting the canonical owner destroys the
second-contact inequality.  Thus any surviving local toggle edge is necessarily
below the old owner; cancellation which changes the old owner must come from a
different global reassembly, not from another pass of the same local matching.

The last sections add two genuinely smaller coordinates.  First, for a child
`n` with owner `q=P+(n)`, the reciprocal depth `k=floor(X_R/n)` satisfies
`q*k<R` and hence `k^2<R`.  Second, every source `y=(t,(c,p))` carries the
strict source scale `A=p*P(t)>R` with `B=floor(X_R/A)<R`, and its cofactor is a
literal second contact `q*d<=B<q^2*d`.  The source-scale fibres are then
reassembled signed before any norm is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Global saturated upper-column telescope.**  Summing the owner windows
before descending them consumes the entire moving upper column in one shot.
Only one root-floored lower column remains. -/
theorem lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_rootFlooredLowerColumn
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ q ∈ primesUpTo (R - 1),
      lowWheelFrozenSecondContactHighOwnerWindowMass R q) =
      (1 - frozenPrimeUniverseMass (primesUpTo (R - 1))
        (squareRootEndpoint R)) -
        ∑ q ∈ primesUpTo (R - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q))) := by
  have hX : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    omega
  calc
    (∑ q ∈ primesUpTo (R - 1),
        lowWheelFrozenSecondContactHighOwnerWindowMass R q) =
      ∑ q ∈ primesUpTo (R - 1),
        (frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q) -
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q)))) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqData := mem_primesUpTo.mp hq
      have hqR : q < R := by omega
      have he := lowWheelFrozenSecondContactHighOwnerWindow_endpoints
        hqData.1 hqR
      unfold lowWheelFrozenSecondContactHighOwnerWindowMass
      exact frozenPrimeUniverseWindowMass_eq_sub he.2
    _ = (∑ q ∈ primesUpTo (R - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q)) -
        ∑ q ∈ primesUpTo (R - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q))) := by
      rw [Finset.sum_sub_distrib]
    _ = (1 - frozenPrimeUniverseMass (primesUpTo (R - 1))
          (squareRootEndpoint R)) -
        ∑ q ∈ primesUpTo (R - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q))) := by
      rw [frozenPrimeUniverse_upperColumn_telescope
        (squareRootEndpoint R) (R - 1) hX]

/-- Multiplying a child by anything strictly larger than its canonical
largest-prime owner necessarily crosses the square endpoint, so it cannot stay
in the arithmetic child carrier. -/
theorem lowWheelFrozenSecondContactArithmeticChild_mul_gt_owner_not_mem
    {R n p : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R)
    (hp : canonicalLargestPrimeFactor n < p) :
    p * n ∉ lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  intro hpn
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, _hsq, _hqR, hsecond, _hroot⟩
  have hnPos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hgrow :
      n * canonicalLargestPrimeFactor n < n * p :=
    Nat.mul_lt_mul_of_pos_left hp hnPos
  have hcross : squareRootEndpoint R < p * n := by
    calc
      squareRootEndpoint R < n * canonicalLargestPrimeFactor n := hsecond
      _ < n * p := hgrow
      _ = p * n := by ac_rfl
  have hpnUpper :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hpn).1).2
  omega

/-- Deleting the canonical largest-prime owner from a child destroys the
second-contact wall: the new owner is strictly smaller, while the old child was
already at or below the physical endpoint. -/
theorem lowWheelFrozenSecondContactArithmeticChild_canonicalCofactor_not_mem
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    canonicalCofactor n ∉ lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  intro hcMem
  let q := canonicalLargestPrimeFactor n
  let c := canonicalCofactor n
  have hborn : q ∈ squareRootBornPartnerSet R c ∧
      R < c ∧ squareRootEndpoint R < q * q * c ∧ c * q = n := by
    simpa [q, c] using
      lowWheelFrozenSecondContactArithmeticChild_bornTail_data hn
  rcases Finset.mem_filter.mp hborn.1 with
    ⟨_hqRange, _hqPrime, hrough, _hqLeC, _hupper⟩
  have hcPos : 0 < c := by omega
  have hnewGrow :
      c * canonicalLargestPrimeFactor c < c * q :=
    Nat.mul_lt_mul_of_pos_left hrough hcPos
  rcases Finset.mem_filter.mp hn with ⟨hnIcc, _⟩
  have hnUpper := (Finset.mem_Icc.mp hnIcc).2
  rcases Finset.mem_filter.mp hcMem with
    ⟨_hcIcc, _hcsq, _hrR, hcSecond, _hcRoot⟩
  have htooHigh : squareRootEndpoint R < n := by
    calc
      squareRootEndpoint R <
          c * canonicalLargestPrimeFactor c := by
            simpa [c] using hcSecond
      _ < c * q := hnewGrow
      _ = n := hborn.2.2.2
  omega

/-- Consequently, a fresh multiplicative edge which remains inside the
carrier can only use a coordinate strictly below the old canonical owner. -/
theorem lowWheelFrozenSecondContactArithmeticChild_fresh_mul_mem_forces_lt_owner
    {R n p : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R)
    (hfresh : ¬ p ∣ n)
    (hpn : p * n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    p < canonicalLargestPrimeFactor n := by
  have hle : p ≤ canonicalLargestPrimeFactor n := by
    by_contra hnot
    have hgt : canonicalLargestPrimeFactor n < p := Nat.lt_of_not_ge hnot
    exact (lowWheelFrozenSecondContactArithmeticChild_mul_gt_owner_not_mem hn hgt) hpn
  by_contra hnot
  have hownerLe : canonicalLargestPrimeFactor n ≤ p := Nat.le_of_not_gt hnot
  have heq : p = canonicalLargestPrimeFactor n := Nat.le_antisymm hle hownerLe
  have hnLower :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hn1 : 1 < n := by omega
  have hdiv : canonicalLargestPrimeFactor n ∣ n :=
    canonicalLargestPrimeFactor_dvd hn1
  apply hfresh
  simpa [heq] using hdiv

/-! ## Reciprocal-depth descent coordinate -/

/-- The reciprocal depth `floor(X_R/n)` is strictly below the canonical owner.
This is the quotient form of the second-contact wall `X_R < n*P+(n)`. -/
theorem lowWheelFrozenSecondContactArithmeticChild_reciprocalDepth_lt_owner
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    squareRootEndpoint R / n < canonicalLargestPrimeFactor n := by
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, _hsq, _hqR, hsecond, _hroot⟩
  have hnPos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  apply (Nat.div_lt_iff_lt_mul hnPos).2
  simpa [Nat.mul_comm] using hsecond

/-- The stronger hyperbolic localization: owner times reciprocal depth is still
strictly below the root.  This combines the post-root cofactor wall
`R*P+(n) < n` with `n*floor(X_R/n) <= X_R < R^2`. -/
theorem lowWheelFrozenSecondContactArithmeticChild_owner_mul_reciprocalDepth_lt_root
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    canonicalLargestPrimeFactor n * (squareRootEndpoint R / n) < R := by
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, _hsq, hqR, _hsecond, hroot⟩
  have hnPos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hn1 : 1 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hRPos : 0 < R := hqPrime.pos.trans hqR
  let k := squareRootEndpoint R / n
  by_cases hk : k = 0
  · simp [k, hk, hRPos]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    have hleft :
        (R * canonicalLargestPrimeFactor n) * k < n * k :=
      Nat.mul_lt_mul_of_pos_right hroot hkPos
    have hnk : n * k ≤ squareRootEndpoint R := by
      simpa [k, Nat.mul_comm] using Nat.div_mul_le_self (squareRootEndpoint R) n
    have hXlt : squareRootEndpoint R < R * R := by
      unfold squareRootEndpoint
      have hsqNe : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRPos)
      simpa [pow_two] using Nat.pred_lt hsqNe
    have hmul :
        R * (canonicalLargestPrimeFactor n * k) < R * R := by
      calc
        R * (canonicalLargestPrimeFactor n * k) =
            (R * canonicalLargestPrimeFactor n) * k := by ring
        _ < n * k := hleft
        _ ≤ squareRootEndpoint R := hnk
        _ < R * R := hXlt
    have hkRoot : canonicalLargestPrimeFactor n * k < R :=
      Nat.lt_of_mul_lt_mul_left hmul
    simpa [k] using hkRoot

/-- The child itself lies beyond the geometric mean of the root and square
endpoint: `R*X_R < n^2`.  This is the product form of the two walls. -/
theorem lowWheelFrozenSecondContactArithmeticChild_root_mul_endpoint_lt_sq
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    R * squareRootEndpoint R < n * n := by
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, _hsq, hqR, hsecond, hroot⟩
  have hnPos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hn1 : 1 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hRPos : 0 < R := hqPrime.pos.trans hqR
  calc
    R * squareRootEndpoint R <
        R * (n * canonicalLargestPrimeFactor n) :=
      Nat.mul_lt_mul_of_pos_left hsecond hRPos
    _ = n * (R * canonicalLargestPrimeFactor n) := by ring
    _ < n * n := Nat.mul_lt_mul_of_pos_left hroot hnPos

/-- **Sub-square-root reciprocal depth.**  Every child belongs to a
reciprocal layer `k` with `k^2 < R`.  This is the exponent-changing support
localization: the saturated second-contact population begins in only the first
square-root many reciprocal depths. -/
theorem lowWheelFrozenSecondContactArithmeticChild_reciprocalDepth_sq_lt_root
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    (squareRootEndpoint R / n) * (squareRootEndpoint R / n) < R := by
  let k := squareRootEndpoint R / n
  have hkq : k < canonicalLargestPrimeFactor n := by
    simpa [k] using
      lowWheelFrozenSecondContactArithmeticChild_reciprocalDepth_lt_owner hn
  have hqk : canonicalLargestPrimeFactor n * k < R := by
    simpa [k] using
      lowWheelFrozenSecondContactArithmeticChild_owner_mul_reciprocalDepth_lt_root hn
  by_cases hk : k = 0
  · have hkZero : squareRootEndpoint R / n = 0 := by
      simpa [k] using hk
    rw [hkZero]
    have hn1 : 1 < n := by
      have hnLower :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      omega
    have hqR := (Finset.mem_filter.mp hn).2.2.1
    have hqPrime := canonicalLargestPrimeFactor_prime hn1
    have hRPos : 0 < R := hqPrime.pos.trans hqR
    simpa using hRPos
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    have hkk : k * k < canonicalLargestPrimeFactor n * k :=
      Nat.mul_lt_mul_of_pos_right hkq hkPos
    exact hkk.trans hqk

/-- Removing a positive divisor from an integer can only increase reciprocal
depth by at least that divisor.  This generic floor inequality is the monotone
engine for descending-owner induction. -/
theorem reciprocalDepth_mul_divisor_le_strippedDepth
    {X n r : ℕ} (hn : 0 < n) (hr : 0 < r) (hrDvd : r ∣ n) :
    r * (X / n) ≤ X / (n / r) := by
  have hrLe : r ≤ n := Nat.le_of_dvd hn hrDvd
  have hquotPos : 0 < n / r := Nat.div_pos hrLe hr
  apply (Nat.le_div_iff_mul_le hquotPos).2
  calc
    r * (X / n) * (n / r) =
        (X / n) * ((n / r) * r) := by ring
    _ = (X / n) * n := by rw [Nat.div_mul_cancel hrDvd]
    _ ≤ X := Nat.div_mul_le_self X n

/-! ## Intrinsic lower-scale exit carried by every source -/

/-- **Strict source-scale descent.**  A frozen second-contact source already
contains its own smaller cutoff.  If

`A = p * P(t)`

is its root-crossing/death coordinate and

`B = floor(X_R / A)`,

then the frozen cofactor `c` lies in the exact largest-prime exit shell

`c <= B < P+(c) * c`,

and the new cutoff is strictly below the old root, `B < R`.

Thus the second-contact obstruction at the square endpoint `R^2-1` is
pointwise a multiplicative endpoint crossing at a genuinely smaller numerical
scale.  No sum, norm, density input, or analytic estimate is used. -/
theorem lowWheelFrozenSecondContact_source_lowerScaleExit
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
    let B := squareRootEndpoint R / A
    let q := lowWheelFrozenCofactorTopPrime y
    y.2.1 ≤ B ∧ B < q * y.2.1 ∧ B < R := by
  rcases Finset.mem_filter.mp hy with ⟨hyFrozen, hsecond⟩
  let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
  let B := squareRootEndpoint R / A
  let q := lowWheelFrozenCofactorTopPrime y
  have hAroot : R < A := by
    simpa [A] using
      lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root hyFrozen
  have hApos : 0 < A := by omega
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen with
    ⟨_hk, _hpPrime, _hpNotC, _hsq, hcgt, hcR⟩
  have hRpos : 0 < R := by omega
  have htop :
      primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) ≤
        squareRootEndpoint R :=
    lowWheelFrozenProductOneFace_le_endpoint hyFrozen
  have hprod := lowWheelCanonicalRepeatedFrozenProductOneFace_product hyFrozen
  have hcA : y.2.1 * A ≤ squareRootEndpoint R := by
    calc
      y.2.1 * A =
          y.2.1 * lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
        simp [A]
        ring
      _ = primeFaceProduct
          (lowWheelCanonicalRepeatedFrozenProductOneFace y) := hprod.symm
      _ ≤ squareRootEndpoint R := htop
  have hcB : y.2.1 ≤ B := by
    unfold B
    exact (Nat.le_div_iff_mul_le hApos).2 hcA
  have hqca :
      squareRootEndpoint R < (q * y.2.1) * A := by
    calc
      squareRootEndpoint R <
          q * primeFaceProduct
            (lowWheelCanonicalRepeatedFrozenProductOneFace y) := by
        simpa [q] using hsecond
      _ = (q * y.2.1) * A := by
        rw [hprod]
        simp [A]
        ring
  have hBq : B < q * y.2.1 := by
    unfold B
    exact (Nat.div_lt_iff_lt_mul hApos).2 hqca
  have hXltRR : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hsqNe : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hsqNe
  have hRRltRA : R * R < R * A :=
    Nat.mul_lt_mul_of_pos_left hAroot hRpos
  have hXltRA : squareRootEndpoint R < R * A :=
    hXltRR.trans hRRltRA
  have hBR : B < R := by
    unfold B
    exact (Nat.div_lt_iff_lt_mul hApos).2 hXltRA
  exact ⟨hcB, hBq, hBR⟩

/-- **Factorized strict source-scale descent.**  The smaller-cutoff exit is
literally a second-contact shell.  Writing the frozen cofactor as
`c = q*d`, where `q = P+(c)` and `d` is its canonical cofactor, gives

`q*d <= B < q^2*d`,  with `B < R`.

Moreover `d` is squarefree and has strictly smaller largest-prime owner.  Thus
this is not merely a smaller numerical cutoff: it is the same descending-owner
Euler geometry on a strict predecessor coordinate, with no norm or estimate. -/
theorem lowWheelFrozenSecondContact_source_lowerScaleSecondContact
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
    let B := squareRootEndpoint R / A
    let c := y.2.1
    let q := lowWheelFrozenCofactorTopPrime y
    let d := canonicalCofactor c
    q.Prime ∧ Squarefree d ∧ canonicalLargestPrimeFactor d < q ∧
      q * d = c ∧ q * d ≤ B ∧ B < q * q * d ∧ B < R := by
  rcases Finset.mem_filter.mp hy with ⟨hyFrozen, _hsecond⟩
  let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
  let B := squareRootEndpoint R / A
  let c := y.2.1
  let q := lowWheelFrozenCofactorTopPrime y
  let d := canonicalCofactor c
  have hexit : c ≤ B ∧ B < q * c ∧ B < R := by
    simpa [A, B, c, q] using
      (lowWheelFrozenSecondContact_source_lowerScaleExit hy)
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen with
    ⟨_hk, _hpPrime, _hpNotC, hcsqRaw, hcgtRaw, _hcR⟩
  have hcsq : Squarefree c := by simpa [c] using hcsqRaw
  have hcgt : 1 < c := by simpa [c] using hcgtRaw
  have hqPrime : q.Prime := by
    simpa [q] using (lowWheelFrozenCofactorTopPrime_data hyFrozen).1
  have hfactor0 : d * q = c := by
    simpa [d, q, c, lowWheelFrozenCofactorTopPrime] using
      (canonicalCofactor_mul_largestPrimeFactor hcgt)
  have hfactor : q * d = c := by
    simpa [Nat.mul_comm] using hfactor0
  have hdSq : Squarefree d := by
    apply hcsq.squarefree_of_dvd
    exact ⟨q, hfactor0.symm⟩
  have hrough : canonicalLargestPrimeFactor d < q := by
    simpa [d, q, c, lowWheelFrozenCofactorTopPrime] using
      (canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hcgt hcsq)
  have hqdB : q * d ≤ B := by
    calc
      q * d = c := hfactor
      _ ≤ B := hexit.1
  have hBqqd : B < q * q * d := by
    calc
      B < q * c := hexit.2.1
      _ = q * (q * d) := by rw [hfactor]
      _ = q * q * d := by ring
  exact ⟨hqPrime, hdSq, hrough, hfactor, hqdB, hBqqd, hexit.2.2⟩

/-! ## Signed source-scale reassembly -/

/-- Root-crossing/death scale carried by a frozen second-contact source. -/
def lowWheelFrozenSecondContactSourceScale
    (y : LowWheelTaggedDowncrossState) : ℕ :=
  lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1

/-- Source scales actually represented at root `R`. -/
def lowWheelFrozenSecondContactSourceScaleSet (R : ℕ) : Finset ℕ :=
  (lowWheelCanonicalRepeatedFrozenSecondContactPart R).image
    lowWheelFrozenSecondContactSourceScale

/-- Exact source fibre at one represented scale `A`. -/
def lowWheelFrozenSecondContactSourceScaleFiber
    (R A : ℕ) : Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenSecondContactPart R).filter fun y =>
    lowWheelFrozenSecondContactSourceScale y = A

@[simp] theorem mem_lowWheelFrozenSecondContactSourceScaleFiber
    {R A : ℕ} {y : LowWheelTaggedDowncrossState} :
    y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A ↔
      y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R ∧
        lowWheelFrozenSecondContactSourceScale y = A := by
  simp [lowWheelFrozenSecondContactSourceScaleFiber]

/-- Cofactors represented in one fixed source-scale fibre. -/
def lowWheelFrozenSecondContactSourceScaleCofactors
    (R A : ℕ) : Finset ℕ :=
  (lowWheelFrozenSecondContactSourceScaleFiber R A).image fun y => y.2.1

/-- Signed Möbius mass of the fixed-scale cofactor image. -/
def lowWheelFrozenSecondContactSourceScaleCofactorMass
    (R A : ℕ) : ℂ :=
  ∑ c ∈ lowWheelFrozenSecondContactSourceScaleCofactors R A,
    canonicalMoebiusWeight c

/-- The source scale is literally the prime-face product obtained by adjoining
the frozen pivot to the old Boolean face. -/
theorem lowWheelFrozenSecondContactSourceScale_eq_insertPivotFaceProduct
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    lowWheelFrozenSecondContactSourceScale y =
      primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1) := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hp
    have hlt :=
      lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hp
    exact (Nat.lt_irrefl _) hlt
  simp [lowWheelFrozenSecondContactSourceScale, primeFaceProduct, hpNot]

/-- **Fixed-scale sign law.**  The old Boolean-face sign is determined by the
single arithmetic integer `A=p*P(t)`: `mu(A)=-sign(t)`. -/
theorem lowWheelFrozenSecondContactSourceScale_moebius_eq_neg_faceSign
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) =
      -(booleanCubeSign y.1 : ℂ) := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  have hfrozen := (Finset.mem_filter.mp hyFrozen).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have ht := (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).1
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hp
    have hlt :=
      lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hp
    exact (Nat.lt_irrefl _) hlt
  have hprime :
      ∀ r ∈ insert (lowWheelTaggedDowncrossPivot y) y.1, r.Prime := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hr | hr
    · subst r
      exact hsource.2.1
    · exact prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hr)
  have hmu := moebius_primeFaceProduct_eq_booleanCubeSign
    (insert (lowWheelTaggedDowncrossPivot y) y.1) hprime
  have hsign :
      booleanCubeSign (insert (lowWheelTaggedDowncrossPivot y) y.1) =
        -booleanCubeSign y.1 := by
    unfold booleanCubeSign
    rw [Finset.card_insert_of_notMem hpNot, pow_succ]
    ring
  have hmuZ :
      μ (lowWheelFrozenSecondContactSourceScale y) =
        -booleanCubeSign y.1 := by
    calc
      μ (lowWheelFrozenSecondContactSourceScale y) =
          μ (primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1)) := by
        rw [lowWheelFrozenSecondContactSourceScale_eq_insertPivotFaceProduct hy]
      _ = booleanCubeSign (insert (lowWheelTaggedDowncrossPivot y) y.1) := hmu
      _ = -booleanCubeSign y.1 := hsign
  simpa [canonicalMoebiusWeight] using
    congrArg (fun z : ℤ => (z : ℂ)) hmuZ

/-- The complete source charge at fixed scale is the cofactor Möbius weight
multiplied by the fixed arithmetic sign `-mu(A)`. -/
theorem lowWheelFrozenSecondContactSource_weight_eq_neg_scale_mul_cofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
      -(canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
        canonicalMoebiusWeight y.2.1) := by
  rw [lowWheelFrozenSecondContactSourceScale_moebius_eq_neg_faceSign hy]
  ring

/-- The physical child integer factors exactly as cofactor times source scale. -/
theorem lowWheelFrozenSecondContact_child_eq_cofactor_mul_sourceScale
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    orderedEulerCutChildInteger y =
      y.2.1 * lowWheelFrozenSecondContactSourceScale y := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  calc
    orderedEulerCutChildInteger y =
        y.2.1 *
          (lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1) := by
      simp only [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct]
      rw [hsource.1]
    _ = y.2.1 * lowWheelFrozenSecondContactSourceScale y := by
      rfl

/-- **No multiplicity at fixed source scale.**  If two sources have the same
`A` and the same cofactor `c`, then their physical child integers are both
`c*A`, so ordered-Euler uniqueness recovers the source itself. -/
theorem lowWheelFrozenSecondContactSourceScaleFiber_cofactor_injOn
    (R A : ℕ) :
    Set.InjOn (fun y : LowWheelTaggedDowncrossState => y.2.1)
      (lowWheelFrozenSecondContactSourceScaleFiber R A :
        Set LowWheelTaggedDowncrossState) := by
  intro y hy z hz hcofactor
  have hcofactor' : y.2.1 = z.2.1 := by simpa using hcofactor
  have hyd := mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hy
  have hzd := mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hz
  have hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z := by
    calc
      orderedEulerCutChildInteger y =
          y.2.1 * lowWheelFrozenSecondContactSourceScale y :=
        lowWheelFrozenSecondContact_child_eq_cofactor_mul_sourceScale hyd.1
      _ = y.2.1 * A := by rw [hyd.2]
      _ = z.2.1 * A := by rw [hcofactor']
      _ = z.2.1 * lowWheelFrozenSecondContactSourceScale z := by rw [hzd.2]
      _ = orderedEulerCutChildInteger z :=
        (lowWheelFrozenSecondContact_child_eq_cofactor_mul_sourceScale hzd.1).symm
  have hyFrozen := (Finset.mem_filter.mp hyd.1).1
  have hzFrozen := (Finset.mem_filter.mp hzd.1).1
  exact orderedEulerCutChildInteger_injective_on_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hyFrozen)
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hzFrozen)
    hchild

/-- Reindexing one fixed-`A` fibre by its cofactor loses no multiplicity. -/
theorem lowWheelFrozenSecondContactSourceScaleCofactorMass_eq_source_sum
    (R A : ℕ) :
    lowWheelFrozenSecondContactSourceScaleCofactorMass R A =
      ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        canonicalMoebiusWeight y.2.1 := by
  unfold lowWheelFrozenSecondContactSourceScaleCofactorMass
    lowWheelFrozenSecondContactSourceScaleCofactors
  rw [Finset.sum_image]
  intro y hy z hz heq
  exact lowWheelFrozenSecondContactSourceScaleFiber_cofactor_injOn R A hy hz heq

/-- **Exact signed fixed-scale recurrence.**  Every source in the `A` fibre has
the same outer sign `-mu(A)`, and the inner object is the ordinary signed
Möbius mass of its cofactor image. -/
theorem lowWheelFrozenSecondContactSourceScaleFiber_sum_eq
    (R A : ℕ) :
    (∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      -(canonicalMoebiusWeight A *
        lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
  calc
    (∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        -(canonicalMoebiusWeight A * canonicalMoebiusWeight y.2.1) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyd := mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hy
      calc
        canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
            -(canonicalMoebiusWeight
                (lowWheelFrozenSecondContactSourceScale y) *
              canonicalMoebiusWeight y.2.1) :=
          lowWheelFrozenSecondContactSource_weight_eq_neg_scale_mul_cofactor hyd.1
        _ = -(canonicalMoebiusWeight A * canonicalMoebiusWeight y.2.1) := by
          rw [hyd.2]
    _ = -(∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        canonicalMoebiusWeight A * canonicalMoebiusWeight y.2.1) := by
      rw [Finset.sum_neg_distrib]
    _ = -(canonicalMoebiusWeight A *
        (∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
          canonicalMoebiusWeight y.2.1)) := by
      rw [Finset.mul_sum]
    _ = -(canonicalMoebiusWeight A *
        lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
      rw [lowWheelFrozenSecondContactSourceScaleCofactorMass_eq_source_sum]

/-- The complete source ledger is the sum of its exact source-scale fibres. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_sourceScaleFibers
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
          canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) := by
  have hmaps :
      ∀ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
        lowWheelFrozenSecondContactSourceScale y ∈
          lowWheelFrozenSecondContactSourceScaleSet R := by
    intro y hy
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun y => canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ))
  simpa [lowWheelFrozenSecondContactSourceScaleFiber] using hfib.symm

/-- **Global strict-scale signed reassembly.**  The entire frozen second-contact
source ledger is a signed sum of cofactor masses indexed by the arithmetic
source scale `A`.  No absolute value has been taken. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_neg_sourceScaleCofactorMass
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      -(∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        canonicalMoebiusWeight A *
          lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
  rw [lowWheelFrozenSecondContactSource_sum_eq_sourceScaleFibers]
  calc
    (∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
          canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        -(canonicalMoebiusWeight A *
          lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
      apply Finset.sum_congr rfl
      intro A _hA
      exact lowWheelFrozenSecondContactSourceScaleFiber_sum_eq R A
    _ = -(∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        canonicalMoebiusWeight A *
          lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
      rw [Finset.sum_neg_distrib]

/-- **Every fixed-scale cofactor is a strict lower-scale second contact.**
For `c` represented in the `A` fibre, put `B=floor(X_R/A)`, `q=P+(c)`, and
`d=c/q`.  Then `q*d <= B < q^2*d`, `P+(d)<q`, and crucially `B<R`. -/
theorem lowWheelFrozenSecondContactSourceScaleCofactor_lowerScaleSecondContact
    {R A c : ℕ}
    (hc : c ∈ lowWheelFrozenSecondContactSourceScaleCofactors R A) :
    let B := squareRootEndpoint R / A
    let q := canonicalLargestPrimeFactor c
    let d := canonicalCofactor c
    q.Prime ∧ Squarefree d ∧ canonicalLargestPrimeFactor d < q ∧
      q * d = c ∧ q * d ≤ B ∧ B < q * q * d ∧ B < R := by
  rcases Finset.mem_image.mp hc with ⟨y, hyFiber, rfl⟩
  have hyd := mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hyFiber
  have hscale :
      lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 = A := by
    simpa [lowWheelFrozenSecondContactSourceScale] using hyd.2
  have h := lowWheelFrozenSecondContact_source_lowerScaleSecondContact hyd.1
  simpa [lowWheelFrozenCofactorTopPrime, hscale] using h

end RHLean.Proof
