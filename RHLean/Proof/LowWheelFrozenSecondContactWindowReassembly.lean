import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactDescent
import RHLean.Proof.LowWheelFrozenSecondContactWindowDescent
import RHLean.Proof.SquareRootLowPrimeBornSquareBoundary
import RHLean.Proof.SquareRootLowPrimeGoHyperbolicStripRecursion
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierSaturation

/-!
# Window-difference recurrence and child-owner reassembly of the frozen
second-contact ledger

`LowWheelFrozenSecondContactDescent` hands one second-contact owner `q` a single
signed native Go window

`D_q = F_{q^-}(X_R/q) - F_{q^-}(X_R/q^2)`,

with `X_R = squareRootEndpoint R`.  This file performs, without any estimate,
the two exact moves that must precede any attempt to bound the ledger.

## The two identities

The first subtracts the recursive Go law at both endpoints of one window.  Both
copies of the completed anchor `M(q-1)` and both fixed lower-prefix columns
cancel identically, leaving only strictly smaller owners:

`D_q = -sum_{r<q} (F_{r^-}(X_R/(q*r)) - F_{r^-}(X_R/(q^2*r)))`.

The second interchanges the finite double sum so that the *child* owner `r`,
not the source owner `q`, indexes the outer column.

## The gate, and why the carrier had to be tightened

The endpoint form of the Go law requires the *lower* cutoff to be unfinished at
its own owner, i.e. `q <= X_R/q^2`.  `..._gate_iff_cube_le` proves that this is
exactly the cube condition `q^3 <= X_R`.  On the `X_R/q^2` carrier only owners
inside that gate cancel both anchors; outside it
`..._eq_mertensGap_sub_childOwnerWindowSum` exhibits a surviving *unrestricted*
Mertens gap `M(q-1) - M(X_R/q^2)`, a terminal leaf of the original open problem
rather than a descended one.

That defect is a property of the carrier, not of the object.
`LowWheelFrozenSecondContactWindowDescent` raises the lower endpoint to
`max R (X_R/q^2)` -- the image really does lie above the root -- and on that
`lowWheelFrozenSecondContactHighOwnerWindow` the owner sits below the lower
cutoff for free, so the cube gate disappears and both anchors cancel at every
prime owner below the root.

The theorems kept here are therefore about the *superseded* `X_R/q^2` carrier.
They are retained as the recorded no-go: they say exactly what the loose
endpoint costs, and
`EMPIRICAL_DIAGNOSTICS.md` measures
it -- `~0.3 R^2/(log R)^2` with constant sign on the loose carrier against a
sign-changing `~R` on the saturated one.  Do not reintroduce the `X_R/q^2`
endpoint.

No norm, cardinality estimate, density input, PNT input, Mertens hypothesis, or
RH-scale bound is introduced here.  Every statement is a finite identity.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## The fourth-power gate on one owner -/

/-- The lower endpoint of the second-contact window is still unfinished at its
own owner exactly when the owner cube fits under the physical endpoint. -/
theorem lowWheelFrozenSecondContactOwner_gate_iff_cube_le
    {R q : ℕ} (hq : q.Prime) :
    q ≤ squareRootEndpoint R / (q * q) ↔ q ^ 3 ≤ squareRootEndpoint R := by
  have hcube : q * (q * q) = q ^ 3 := by ring
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos hq.pos hq.pos), hcube]

/-- Inside the gate the upper endpoint is unfinished as well. -/
theorem lowWheelFrozenSecondContactOwner_upper_unfinished_of_gate
    {R q : ℕ} (hq : q.Prime)
    (hgate : q ≤ squareRootEndpoint R / (q * q)) :
    q ≤ squareRootEndpoint R / q :=
  hgate.trans (Nat.div_le_div_left (by nlinarith [hq.two_le]) hq.pos)

/-! ## First identity: the window-difference Go recurrence -/

/-- **Exact window-difference Go recurrence.**  Subtracting the recursive Go law
at the two endpoints of one second-contact owner window cancels both copies of
the completed anchor `M(q-1)` and both fixed lower-prefix columns.  What remains
is a single signed sum of strictly smaller-owner windows, at the two inherited
cutoffs `X_R/(q*r)` and `X_R/(q*q*r)`.

Neither `F_{q^-}(X_R/q)` nor `F_{q^-}(X_R/q^2)` is bounded separately; the
identity is applied to their difference only. -/
theorem lowWheelFrozenSecondContactOwnerWindowMass_eq_neg_childOwnerWindowSum
    {R q : ℕ} (hq : q.Prime)
    (hgate : q ^ 3 ≤ squareRootEndpoint R) :
    lowWheelFrozenSecondContactOwnerWindowMass R q =
      -∑ r ∈ primesUpTo (q - 1),
        (frozenPrimeUniverseMass (primesUpTo (r - 1))
            (squareRootEndpoint R / (q * r)) -
          frozenPrimeUniverseMass (primesUpTo (r - 1))
            (squareRootEndpoint R / (q * q * r))) := by
  have hL : q ≤ squareRootEndpoint R / (q * q) :=
    (lowWheelFrozenSecondContactOwner_gate_iff_cube_le hq).2 hgate
  have hU : q ≤ squareRootEndpoint R / q :=
    lowWheelFrozenSecondContactOwner_upper_unfinished_of_gate hq hL
  rw [lowWheelFrozenSecondContactOwnerWindowMass_eq_frozenDifference hq,
    frozenPrimeUniverseMass_sub_eq_neg_smallerOwnerStripSum hq hU hL]
  simp only [Nat.div_div_eq_div_mul]

/-- **Outside the gate the lower anchor does not cancel.**  When the owner cube
already exceeds the physical endpoint, the lower cutoff `X_R/q^2` has completed
below `q`, and the exact window carries a residual *unrestricted* Mertens gap
`M(q-1) - M(X_R/q^2)`.

This is recorded as a separate theorem precisely because it is the failure mode:
a terminal leaf of this shape is the original Mertens problem, not a descended
window. -/
theorem lowWheelFrozenSecondContactOwnerWindowMass_eq_mertensGap_sub_childOwnerWindowSum
    {R q : ℕ} (hq : q.Prime)
    (hsquare : q ^ 2 ≤ squareRootEndpoint R)
    (hgate : squareRootEndpoint R < q ^ 3) :
    lowWheelFrozenSecondContactOwnerWindowMass R q =
      (mertensSummatoryInt (q - 1) -
          mertensSummatoryInt (squareRootEndpoint R / (q * q))) -
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1))
              (squareRootEndpoint R / (q * r)) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  have hU : q ≤ squareRootEndpoint R / q := by
    have hsq : q * q ≤ squareRootEndpoint R := by
      calc q * q = q ^ 2 := by ring
        _ ≤ squareRootEndpoint R := hsquare
    exact (Nat.le_div_iff_mul_le hq.pos).2 hsq
  have hLlt : squareRootEndpoint R / (q * q) < q := by
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hq.pos hq.pos)).2
    calc squareRootEndpoint R < q ^ 3 := hgate
      _ = q * (q * q) := by ring
  rw [lowWheelFrozenSecondContactOwnerWindowMass_eq_frozenDifference hq,
    frozenPrimeUniverseMass_sub_eq_mertensGap_sub_smallerOwnerStrips hq hU hLlt]
  simp only [Nat.div_div_eq_div_mul]

/-! ## Second identity: global reassembly by the child owner -/

/-- The second-contact owners below the root whose window admits the
base-cancelling recurrence, i.e. those inside the cube gate. -/
def lowWheelFrozenSecondContactGatedOwners (R : ℕ) : Finset ℕ :=
  (primesUpTo (R - 1)).filter fun q => q ^ 3 ≤ squareRootEndpoint R

theorem mem_lowWheelFrozenSecondContactGatedOwners {R q : ℕ} :
    q ∈ lowWheelFrozenSecondContactGatedOwners R ↔
      q.Prime ∧ q ≤ R - 1 ∧ q ^ 3 ≤ squareRootEndpoint R := by
  simp [lowWheelFrozenSecondContactGatedOwners, and_assoc]

/-- The predecessor prime universe of an owner below the root is the root
universe cut at that owner. -/
theorem primesUpTo_pred_eq_primesUpTo_root_filter_lt
    {R q : ℕ} (hq : q.Prime) (hqR : q ≤ R - 1) :
    primesUpTo (q - 1) = (primesUpTo (R - 1)).filter fun r => r < q := by
  have h2 := hq.two_le
  ext r
  simp only [Finset.mem_filter, mem_primesUpTo]
  constructor
  · rintro ⟨hrPrime, hrq⟩
    exact ⟨⟨hrPrime, by omega⟩, by omega⟩
  · rintro ⟨⟨hrPrime, _hrR⟩, hrq⟩
    exact ⟨hrPrime, by omega⟩

/-- **Global reassembly by the child owner.**  Substituting the window-difference
recurrence into the gated ledger and interchanging the two finite sums makes the
*child* owner `r` index the outer column.  Each fixed-`r` column collects every
inherited window `(X_R/(q^2*r), X_R/(q*r)]` contributed by the source owners
`q > r`.

The identity is exact: no term is bounded, dropped, or replaced by its absolute
value.  It is the last exact move available before an estimate, and it is what
must be inspected for further cancellation before any triangle inequality. -/
theorem lowWheelFrozenSecondContactGatedLedger_eq_neg_childOwnerReassembly
    (R : ℕ) :
    ∑ q ∈ lowWheelFrozenSecondContactGatedOwners R,
        lowWheelFrozenSecondContactOwnerWindowMass R q =
      -∑ r ∈ primesUpTo (R - 1),
          ∑ q ∈ (lowWheelFrozenSecondContactGatedOwners R).filter
              fun q => r < q,
            (frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r)) -
              frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r))) := by
  have hstep :
      ∀ q ∈ lowWheelFrozenSecondContactGatedOwners R,
        lowWheelFrozenSecondContactOwnerWindowMass R q =
          -∑ r ∈ primesUpTo (R - 1),
            (if r < q then
              frozenPrimeUniverseMass (primesUpTo (r - 1))
                  (squareRootEndpoint R / (q * r)) -
                frozenPrimeUniverseMass (primesUpTo (r - 1))
                  (squareRootEndpoint R / (q * q * r))
             else 0) := by
    intro q hqMem
    obtain ⟨hqPrime, hqR, hgate⟩ :=
      mem_lowWheelFrozenSecondContactGatedOwners.mp hqMem
    rw [lowWheelFrozenSecondContactOwnerWindowMass_eq_neg_childOwnerWindowSum
        hqPrime hgate,
      primesUpTo_pred_eq_primesUpTo_root_filter_lt hqPrime hqR,
      Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [← Finset.sum_filter]

/-! ## Saturated cross-column flattening -/

/-- The single physical integer population underlying all saturated
child-owner columns.  The child-owner label is deliberately forgotten before
any norm is taken. -/
def lowWheelFrozenSecondContactCrossColumnChildCarrier (R : ℕ) : Finset ℕ :=
  (lowWheelCanonicalRepeatedFrozenSecondContactPart R).image
    orderedEulerCutChildInteger

@[simp] theorem mem_lowWheelFrozenSecondContactCrossColumnChildCarrier
    {R n : ℕ} :
    n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R ↔
      ∃ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
        orderedEulerCutChildInteger y = n := by
  simp [lowWheelFrozenSecondContactCrossColumnChildCarrier]

private theorem frozenSecondContact_mem_orderedEulerCutCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    y ∈ orderedEulerCutCarrier R :=
  lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier
    (Finset.mem_filter.mp hy).1

/-- **Global signed flattening.**  Before any norm, the original saturated
second-contact source ledger is exactly the negative ordinary Möbius mass of
its physical child-integer population. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_neg_crossColumnChildMass
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      -∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
        canonicalMoebiusWeight n := by
  calc
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
        ∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
          -canonicalMoebiusWeight (orderedEulerCutChildInteger y) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hcar := frozenSecondContact_mem_orderedEulerCutCarrier hy
      have hshape := orderedEulerCutShape_of_mem_carrier hcar
      have hflip := orderedEulerCutChildWeight_eq_neg hshape
      change orderedEulerCutWeight y =
        -canonicalMoebiusWeight (orderedEulerCutChildInteger y)
      rw [hflip]
      simp
    _ = -(∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
          canonicalMoebiusWeight (orderedEulerCutChildInteger y)) := by
      rw [Finset.sum_neg_distrib]
    _ = -∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
          canonicalMoebiusWeight n := by
      congr 1
      unfold lowWheelFrozenSecondContactCrossColumnChildCarrier
      rw [Finset.sum_image]
      intro y hy z hz hchild
      exact orderedEulerCutChildInteger_injective_on_carrier
        (frozenSecondContact_mem_orderedEulerCutCarrier hy)
        (frozenSecondContact_mem_orderedEulerCutCarrier hz)
        hchild

/-- **Cross-column reassembly on one carrier.**  The sum of all saturated
child-owner columns is the ordinary Möbius mass of the common physical child
population.  There is no per-column absolute value anywhere in the identity. -/
theorem lowWheelFrozenSecondContactChildOwnerColumns_eq_crossColumnChildMass
    (R : ℕ) :
    ((∑ r ∈ primesUpTo (R - 1),
        lowWheelFrozenSecondContactChildOwnerColumn R r : ℤ) : ℂ) =
      ∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
        canonicalMoebiusWeight n := by
  have hchild :=
    lowWheelFrozenSecondContactSource_sum_eq_neg_crossColumnChildMass R
  have hcols := lowWheelFrozenSecondContactSource_sum_eq_neg_childOwnerColumns R
  have hneg :
      -((∑ r ∈ primesUpTo (R - 1),
          lowWheelFrozenSecondContactChildOwnerColumn R r : ℤ) : ℂ) =
        -(∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
          canonicalMoebiusWeight n) := by
    exact hcols.symm.trans hchild
  have h := congrArg (fun z : ℂ => -z) hneg
  simpa using h

/-- Integer-valued form of the same exact reassembly. -/
theorem lowWheelFrozenSecondContactChildOwnerColumns_eq_crossColumnMobiusSum
    (R : ℕ) :
    (∑ r ∈ primesUpTo (R - 1),
      lowWheelFrozenSecondContactChildOwnerColumn R r) =
      ∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R, μ n := by
  have h := lowWheelFrozenSecondContactChildOwnerColumns_eq_crossColumnChildMass R
  have hcast :
      (((∑ r ∈ primesUpTo (R - 1),
          lowWheelFrozenSecondContactChildOwnerColumn R r) : ℤ) : ℂ) =
        (((∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
          μ n) : ℤ) : ℂ) := by
    simpa [canonicalMoebiusWeight] using h
  exact_mod_cast hcast

/-! ## Independent arithmetic form of the cross-column carrier -/

/-- The same population with every owner/window coordinate eliminated.
For `q = P⁺(n)`, the two strict inequalities are exactly the second-contact
upper wall `X_R < n*q` and the root floor `R*q < n`. -/
def lowWheelFrozenSecondContactArithmeticChildCarrier (R : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (squareRootEndpoint R)).filter fun n =>
    Squarefree n ∧
      canonicalLargestPrimeFactor n < R ∧
      squareRootEndpoint R < n * canonicalLargestPrimeFactor n ∧
      R * canonicalLargestPrimeFactor n < n

/-- **Closed-form carrier identification.**  The multiplicity-free physical
child image is exactly the squarefree integer population selected only by the
largest-prime coordinate and the two physical walls. -/
theorem lowWheelFrozenSecondContactCrossColumnChildCarrier_eq_arithmetic
    (R : ℕ) :
    lowWheelFrozenSecondContactCrossColumnChildCarrier R =
      lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  ext n
  constructor
  · intro hn
    rcases mem_lowWheelFrozenSecondContactCrossColumnChildCarrier.mp hn with
      ⟨y, hy, rfl⟩
    have hyFrozen := (Finset.mem_filter.mp hy).1
    have hmap := lowWheelFrozenSecondContactParentMap_mem hy
    rw [mem_lowWheelFrozenSecondContactParentCarrier] at hmap
    rcases lowWheelFrozenCofactorTopPrime_data hyFrozen with
      ⟨hqPrime, hqDvd, _hpq⟩
    rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen with
      ⟨_hk, _hpPrime, _hpNotC, _hsq, hcgt, hcR⟩
    have hqLeC : lowWheelFrozenCofactorTopPrime y ≤ y.2.1 :=
      Nat.le_of_dvd (by omega) hqDvd
    have hqR : lowWheelFrozenCofactorTopPrime y < R := hqLeC.trans_lt hcR
    have hR : 2 ≤ R := by
      have hqTwo := hqPrime.two_le
      omega
    have hactive : orderedEulerCutChildInteger y ∈ orderedEulerCutActiveChildren R := by
      unfold orderedEulerCutActiveChildren
      exact Finset.mem_image.mpr
        ⟨y, frozenSecondContact_mem_orderedEulerCutCarrier hy, rfl⟩
    have hshell :=
      (mem_orderedEulerCutActiveChildren_iff_squarefreeShell hR).1 hactive
    have hqLargest := lowWheelFrozenCofactorTopPrime_eq_childLargest hyFrozen
    have hchild := lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct hyFrozen
    have hupper :
        lowWheelFrozenCofactorTopPrime y *
            primeFaceProduct (lowWheelFrozenSecondContactParentFace y) ≤
          squareRootEndpoint R := by
      simpa [lowWheelFrozenSecondContactParentMap] using hmap.2.2.2.2.1
    have hhigh :
        squareRootEndpoint R <
          lowWheelFrozenCofactorTopPrime y * lowWheelFrozenCofactorTopPrime y *
            primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := by
      simpa [lowWheelFrozenSecondContactParentMap] using hmap.2.2.2.2.2
    have hroot := lowWheelFrozenSecondContactParentFace_root_lt hyFrozen
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hshell.2.2, ?_, ?_, ?_⟩
    · rw [hchild]
      exact hupper
    · rw [← hqLargest]
      exact hqR
    · rw [← hqLargest, hchild]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hhigh
    · rw [← hqLargest, hchild]
      have hmul := (Nat.mul_lt_mul_left hqPrime.pos).2 hroot
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  · intro hn
    rcases Finset.mem_filter.mp hn with
      ⟨hnIcc, hsq, hqR0, hsecond0, hrootWall0⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨hn2, hnUpperRaw⟩
    have hn1 : 1 < n := by omega
    let q := canonicalLargestPrimeFactor n
    let c := canonicalCofactor n
    let V := squarefreePrimeFace c
    have hdata : CanonicalGapAncestryBridge.CanonicalSourceData q c := by
      simpa [q, c] using
        CanonicalGapAncestryBridge.canonicalSourceData_of_squarefree hsq hn1
    rcases hdata with ⟨hqPrime, hc1, hcsq, _hcop, hdom⟩
    have hqR : q < R := by simpa [q] using hqR0
    have hprod : c * q = n := by
      simpa [c, q] using canonicalCofactor_mul_largestPrimeFactor hn1
    have hVprod : primeFaceProduct V = c := by
      simpa [V] using primeFaceProduct_squarefreePrimeFace hcsq
    have hVpred : V ∈ (primesUpTo (q - 1)).powerset := by
      apply Finset.mem_powerset.mpr
      intro p hp
      have hpFactors : p ∈ c.primeFactors := by
        simpa [V, squarefreePrimeFace] using hp
      have hpData := Nat.mem_primeFactors.mp hpFactors
      exact mem_primesUpTo.mpr
        ⟨hpData.1, by
          have hlt := hdom p hpData.1 hpData.2.1
          omega⟩
    have hrootWall := hrootWall0
    change R * q < n at hrootWall
    rw [← hprod] at hrootWall
    have hroot : R < c := by
      apply (Nat.mul_lt_mul_left hqPrime.pos).1
      simpa [Nat.mul_comm] using hrootWall
    have hsecond := hsecond0
    change squareRootEndpoint R < n * q at hsecond
    rw [← hprod] at hsecond
    have hann : squareRootEndpoint R / (q * q) < c := by
      apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hqPrime.pos hqPrime.pos)).2
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsecond
    have hnUpper : c * q ≤ squareRootEndpoint R := by
      rw [hprod]
      exact hnUpperRaw
    have hupp : c ≤ squareRootEndpoint R / q :=
      (Nat.le_div_iff_mul_le hqPrime.pos).2 hnUpper
    have hrootV : R < primeFaceProduct V := by
      rw [hVprod]
      exact hroot
    have hannV : squareRootEndpoint R / (q * q) < primeFaceProduct V := by
      rw [hVprod]
      exact hann
    have huppV : primeFaceProduct V ≤ squareRootEndpoint R / q := by
      rw [hVprod]
      exact hupp
    have hVwindow : V ∈ lowWheelFrozenSecondContactHighOwnerWindow R q := by
      unfold lowWheelFrozenSecondContactHighOwnerWindow
      apply mem_frozenPrimeUniverseWindowFaces.mpr
      exact ⟨hVpred, max_lt hrootV hannV, huppV⟩
    rcases lowWheelFrozenSecondContactParentMap_surjOn_highOwnerWindow
        hqPrime hqR hVwindow with ⟨y, hy, hmap⟩
    apply mem_lowWheelFrozenSecondContactCrossColumnChildCarrier.mpr
    refine ⟨y, hy, ?_⟩
    have hyFrozen := (Finset.mem_filter.mp hy).1
    have howner : lowWheelFrozenCofactorTopPrime y = q := by
      simpa [lowWheelFrozenSecondContactParentMap] using congrArg Prod.fst hmap
    have hface : lowWheelFrozenSecondContactParentFace y = V := by
      simpa [lowWheelFrozenSecondContactParentMap] using congrArg Prod.snd hmap
    rw [lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct hyFrozen,
      howner, hface, hVprod]
    simpa [Nat.mul_comm] using hprod

/-- The child-owner sum in the independent arithmetic coordinates. -/
theorem lowWheelFrozenSecondContactChildOwnerColumns_eq_arithmeticMobiusSum
    (R : ℕ) :
    (∑ r ∈ primesUpTo (R - 1),
      lowWheelFrozenSecondContactChildOwnerColumn R r) =
      ∑ n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R, μ n := by
  rw [lowWheelFrozenSecondContactChildOwnerColumns_eq_crossColumnMobiusSum,
    lowWheelFrozenSecondContactCrossColumnChildCarrier_eq_arithmetic]

/-- The complete saturated second-contact ledger itself, with all column and
window tags removed. -/
theorem lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_neg_arithmeticMobiusSum
    (R : ℕ) :
    (∑ q ∈ primesUpTo (R - 1),
      lowWheelFrozenSecondContactHighOwnerWindowMass R q) =
      -∑ n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R, μ n := by
  rw [lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_neg_childOwnerColumns,
    lowWheelFrozenSecondContactChildOwnerColumns_eq_arithmeticMobiusSum]

/-- **Born-fibre second-contact tail.**  Every atom of the global arithmetic
carrier has the unique canonical factorization `n = c*q`, with `q = P+(n)` a
literal born partner of `c`.  The root floor makes the cofactor itself
post-root, and the remaining wall is exactly the repeated-owner second contact
`X_R < q^2*c`.

This places the complete cross-column population inside the repository's native
born-response coordinate before any processed-seat lift or norm is attempted. -/
theorem lowWheelFrozenSecondContactArithmeticChild_bornTail_data
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    let q := canonicalLargestPrimeFactor n
    let c := canonicalCofactor n
    q ∈ squareRootBornPartnerSet R c ∧
      R < c ∧
      squareRootEndpoint R < q * q * c ∧
      c * q = n := by
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, hsq, hqR0, hsecond0, hrootWall0⟩
  rcases Finset.mem_Icc.mp hnIcc with ⟨hn2, hnUpperRaw⟩
  have hn1 : 1 < n := by omega
  let q := canonicalLargestPrimeFactor n
  let c := canonicalCofactor n
  have hdata : CanonicalGapAncestryBridge.CanonicalSourceData q c := by
    simpa [q, c] using
      CanonicalGapAncestryBridge.canonicalSourceData_of_squarefree hsq hn1
  rcases hdata with ⟨hqPrime, _hc1, _hcsq, _hcop, hdom⟩
  have hqR : q < R := by simpa [q] using hqR0
  have hprod : c * q = n := by
    simpa [c, q] using canonicalCofactor_mul_largestPrimeFactor hn1
  have hrootWall := hrootWall0
  change R * q < n at hrootWall
  rw [← hprod] at hrootWall
  have hroot : R < c := by
    apply (Nat.mul_lt_mul_left hqPrime.pos).1
    simpa [Nat.mul_comm] using hrootWall
  have hcgt : 1 < c := by
    have hqTwo := hqPrime.two_le
    omega
  have hrough : canonicalLargestPrimeFactor c < q := by
    have hpPrime : (canonicalLargestPrimeFactor c).Prime :=
      canonicalLargestPrimeFactor_prime hcgt
    have hpDvd : canonicalLargestPrimeFactor c ∣ c :=
      canonicalLargestPrimeFactor_dvd hcgt
    exact hdom (canonicalLargestPrimeFactor c) hpPrime hpDvd
  have hqLeC : q ≤ c := by omega
  have hupper : c * q ≤ squareRootEndpoint R := by
    rw [hprod]
    exact hnUpperRaw
  have hborn : q ∈ squareRootBornPartnerSet R c := by
    unfold squareRootBornPartnerSet
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqR.le⟩,
      hqPrime, hrough, hqLeC, hupper⟩
  have hsecond := hsecond0
  change squareRootEndpoint R < n * q at hsecond
  rw [← hprod] at hsecond
  have hsecond' : squareRootEndpoint R < q * q * c := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsecond
  exact ⟨hborn, hroot, hsecond', hprod⟩

/-! ## Whole-carrier Othello pairing and terminal boundary -/

/-- Every prime below the root is processed as one global matching coordinate.
The matching is performed on the complete arithmetic carrier, not separately in
source-owner or child-owner columns. -/
def lowWheelFrozenSecondContactCrossColumnPrimeList (R : ℕ) : List ℕ :=
  squareRootLowPrimeFreshPrimeList 1 (R - 1)

theorem prime_of_mem_lowWheelFrozenSecondContactCrossColumnPrimeList
    {R p : ℕ} (hp : p ∈ lowWheelFrozenSecondContactCrossColumnPrimeList R) :
    p.Prime := by
  exact prime_of_mem_squareRootLowPrimeFreshPrimeList hp

/-- The literal terminal population after every prime below `R` has been given
a chance to pair opposite Möbius signs on the full cross-column carrier. -/
def lowWheelFrozenSecondContactCrossColumnTerminalBoundary (R : ℕ) : Finset ℕ :=
  squareRootLowPrimeResponseMatchingFrontier
    (lowWheelFrozenSecondContactCrossColumnPrimeList R)
    (lowWheelFrozenSecondContactArithmeticChildCarrier R)

/-- Matching only removes states; the terminal boundary is a subcarrier of the
exact arithmetic population. -/
theorem lowWheelFrozenSecondContactCrossColumnTerminalBoundary_subset
    (R : ℕ) :
    lowWheelFrozenSecondContactCrossColumnTerminalBoundary R ⊆
      lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  unfold lowWheelFrozenSecondContactCrossColumnTerminalBoundary
  exact squareRootLowPrimeResponseMatchingFrontier_subset _ _

/-- **True terminality in every processed prime direction.**  No complete
`p`-edge survives in the terminal boundary for any prime below the root that was
processed by the global matching. -/
theorem lowWheelFrozenSecondContactCrossColumnTerminalBoundary_pair_free
    {R p n : ℕ}
    (hp : p ∈ lowWheelFrozenSecondContactCrossColumnPrimeList R)
    (hn : n ∈ lowWheelFrozenSecondContactCrossColumnTerminalBoundary R)
    (hnot : ¬ p ∣ n) :
    p * n ∉ lowWheelFrozenSecondContactCrossColumnTerminalBoundary R := by
  unfold lowWheelFrozenSecondContactCrossColumnTerminalBoundary at hn ⊢
  exact squareRootLowPrimeResponseMatchingFrontier_pair_free
    (lowWheelFrozenSecondContactCrossColumnPrimeList R)
    (lowWheelFrozenSecondContactArithmeticChildCarrier R) hp hn hnot

/-- **Global terminal-boundary reassembly.**  All matched cross-column pairs
cancel before any absolute value is taken.  The complete arithmetic Möbius mass
is exactly the signed mass of the terminal frontier after all primes below the
root have been processed. -/
theorem lowWheelFrozenSecondContactArithmeticMobiusSum_eq_terminalBoundary
    (R : ℕ) :
    (∑ n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R, μ n) =
      ∑ n ∈ lowWheelFrozenSecondContactCrossColumnTerminalBoundary R, μ n := by
  unfold lowWheelFrozenSecondContactCrossColumnTerminalBoundary
  apply squareRootLowPrimeResponse_moebiusSum_eq_matchingFrontier
  intro p hp
  exact prime_of_mem_lowWheelFrozenSecondContactCrossColumnPrimeList hp

/-- The exact population removed in opposite-sign pairs by the global matching. -/
def lowWheelFrozenSecondContactCrossColumnPairedPopulation (R : ℕ) : Finset ℕ :=
  lowWheelFrozenSecondContactArithmeticChildCarrier R \
    lowWheelFrozenSecondContactCrossColumnTerminalBoundary R

/-- The complete paired population has zero signed Möbius mass.  This is the
literal cross-column cancellation population requested before any norm. -/
theorem lowWheelFrozenSecondContactCrossColumnPairedPopulation_moebiusSum_eq_zero
    (R : ℕ) :
    (∑ n ∈ lowWheelFrozenSecondContactCrossColumnPairedPopulation R, μ n) = 0 := by
  have hsub := lowWheelFrozenSecondContactCrossColumnTerminalBoundary_subset R
  have hsplit :
      (∑ n ∈ lowWheelFrozenSecondContactCrossColumnPairedPopulation R, μ n) +
          (∑ n ∈ lowWheelFrozenSecondContactCrossColumnTerminalBoundary R, μ n) =
        ∑ n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R, μ n := by
    unfold lowWheelFrozenSecondContactCrossColumnPairedPopulation
    exact Finset.sum_sdiff hsub
  calc
    (∑ n ∈ lowWheelFrozenSecondContactCrossColumnPairedPopulation R, μ n) =
        ((∑ n ∈ lowWheelFrozenSecondContactCrossColumnPairedPopulation R, μ n) +
          ∑ n ∈ lowWheelFrozenSecondContactCrossColumnTerminalBoundary R, μ n) -
            ∑ n ∈ lowWheelFrozenSecondContactCrossColumnTerminalBoundary R, μ n := by
              ring
    _ = (∑ n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R, μ n) -
          ∑ n ∈ lowWheelFrozenSecondContactCrossColumnTerminalBoundary R, μ n := by
            rw [hsplit]
    _ = 0 := by
      rw [lowWheelFrozenSecondContactArithmeticMobiusSum_eq_terminalBoundary]
      ring

/-- **Requested signed reassembly.**  The entire saturated ledger is the
negative signed Möbius mass of one terminal cross-column boundary.  No
per-column absolute value appears anywhere in the derivation. -/
theorem lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_neg_terminalBoundary
    (R : ℕ) :
    (∑ q ∈ primesUpTo (R - 1),
      lowWheelFrozenSecondContactHighOwnerWindowMass R q) =
      -∑ n ∈ lowWheelFrozenSecondContactCrossColumnTerminalBoundary R, μ n := by
  rw [lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_neg_arithmeticMobiusSum,
    lowWheelFrozenSecondContactArithmeticMobiusSum_eq_terminalBoundary]

/-- Only after the exact global pairing is complete do we take an absolute
value.  Therefore an `R polylog R` cardinality bound on this terminal frontier
is sufficient for the desired epsilon-scale bound. -/
theorem abs_lowWheelFrozenSecondContactHighOwnerWindowMass_sum_le_terminalBoundaryCard
    (R : ℕ) :
    |∑ q ∈ primesUpTo (R - 1),
      lowWheelFrozenSecondContactHighOwnerWindowMass R q| ≤
      ((lowWheelFrozenSecondContactCrossColumnTerminalBoundary R).card : ℤ) := by
  rw [lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_neg_terminalBoundary,
    abs_neg]
  exact abs_moebiusSum_le_card
    (lowWheelFrozenSecondContactCrossColumnTerminalBoundary R)

end RHLean.Proof