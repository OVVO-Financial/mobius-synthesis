import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoAncestryClock

/-!
# The Go second-boundary defect lives only in the fourth-power owner band

For a full birth-boundary child `n = r*d`, the existing Go geometry proves
`n < q^2`.  A surviving second-boundary defect simultaneously satisfies
`X < q^2*n`.  Therefore every such defect forces

`X < q^4`.

Combined with the unfinished-owner condition `q^3 <= X`, every genuinely live
two-boundary defect lies in the strict band

`q^3 <= X < q^4`.

After the `r`-coordinate is recombined, the surviving edge carries the exposed
parent arithmetic source

`m = q*d`.

This source is canonical: `P+(m) = q`.  Its active parent clock and inactive
child clock imply the `r`-free second-contact shell

`q*m <= X < q^2*m`,

while the birth-boundary geometry gives `m < q^2`.  Equivalently, at a fixed
owner `q`, every exposed parent core lies in the explicit no-liberty interval

`X/q^3 < d < q`.

Hence every raw defect maps into one finite arithmetic boundary depending only
on `m` and its canonical largest prime factor.  In particular

`X < m^3 < X^2`.

The forgotten `r`-coordinate is not discarded: it survives as an exact prime
liberty multiplicity over each fixed parent source.  In unfinished territory
the full birth condition is redundant, and the admissible `r`-fibre is exactly

`max(P+(d), X/(q^2*d)) < r < q`,  with `r` prime.

Thus the raw defect mass is a weighted boundary mass, with no estimate or norm
inserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- A surviving Go second-boundary defect forces the physical cutoff below the
fourth power of its outer owner. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_ownerFourth_gt
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    X < q ^ 4 := by
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_lt_ownerSquare hq hrq hfull
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hupper : q * q * (r * d) < q * q * (q * q) :=
    Nat.mul_lt_mul_of_pos_left hchild hq2Pos
  calc
    X < q * q * (r * d) := hsecond
    _ < q * q * (q * q) := hupper
    _ = q ^ 4 := by ring

/-- Hence every genuinely unfinished owner carrying a surviving two-boundary
defect lies in the narrow power band `q^3 <= X < q^4`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_ownerPowerBand
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    q ^ 3 ≤ X ∧ X < q ^ 4 := by
  exact ⟨hcube,
    squareRootLowPrimeGoSecondBoundaryDefect_ownerFourth_gt hq hr hrq hd⟩

/-- A surviving two-boundary edge has one exposed parent arithmetic source
`m = q*d`.  Its largest prime factor is exactly the outer Go owner and the
source lies strictly below the owner square.  Thus the outer coordinate is
recoverable from `m`; there is no additional `q` multiplicity in this source
encoding. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_coordinates
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    canonicalLargestPrimeFactor (q * d) = q ∧ q * d < q ^ 2 := by
  have hfull : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hroot :=
    squareRootLowPrimeGoFullBirthBoundary_parent_canonicalRoot hq hr hrq hfull
  have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).1
  have hdPos : 0 < d := by omega
  have hroughQ : canonicalLargestPrimeFactor d < q := by
    rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull with
      ⟨_hd1, _hdq, _hsq, hroughR, _hlower⟩
    exact hroughR.trans hrq
  constructor
  · have howner :=
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hdPos hq hroughQ
    simpa [Nat.mul_comm] using howner
  · rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_left hroot.2 hq.pos

/-- The exposed parent source itself lies on an `r`-free second-contact shell.
The parent clock is active at `q*m`; the defect child enters after `X`, and
`r < q` enlarges that inactive clock to the canonical upper wall `q^2*m`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_contactShell
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    q * (q * d) ≤ X ∧ X < q ^ 2 * (q * d) := by
  have hfull : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hparentClock :=
    squareRootLowPrimeGoFullBirthBoundary_parentClock_le hq hcube hfull
  have hparent : q * (q * d) ≤ X := by
    simpa [squareRootLowPrimeGoAncestryClock, Nat.mul_assoc] using hparentClock
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hdPos : 0 < d := by
    have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).1
    omega
  have hrdLt : r * d < q * d :=
    Nat.mul_lt_mul_of_pos_right hrq hdPos
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hupper : q * q * (r * d) < q * q * (q * d) :=
    Nat.mul_lt_mul_of_pos_left hrdLt hq2Pos
  refine ⟨hparent, ?_⟩
  calc
    X < q * q * (r * d) := hsecond
    _ < q * q * (q * d) := hupper
    _ = q ^ 2 * (q * d) := by ring

/-- **Fixed-owner no-liberty interval.**  Once the interior prime `r` is
forgotten, every surviving parent core at owner `q` lies in the literal finite
interval

`X / q^3 < d < q`.

This is an exact boundary statement, not an estimate. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentCore_interval
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    X / q ^ 3 < d ∧ d < q := by
  have hfull : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hdlt :=
    (squareRootLowPrimeGoFullBirthBoundary_parent_canonicalRoot
      hq hr hrq hfull).2
  have hcontact :=
    squareRootLowPrimeGoSecondBoundaryDefect_parentSource_contactShell
      hq hr hrq hcube hd
  have hq3Pos : 0 < q ^ 3 := pow_pos hq.pos 3
  constructor
  · apply (Nat.div_lt_iff_lt_mul hq3Pos).2
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcontact.2
  · exact hdlt

/-- The finite fixed-owner parent-core slice itself. -/
def squareRootLowPrimeGoExposedParentCoreBoundary (q X : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun d => X / q ^ 3 < d

/-- Every exact second-boundary defect lands in the fixed-owner no-liberty
slice after forgetting the interior prime `r`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentCore_mem_boundary
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    d ∈ squareRootLowPrimeGoExposedParentCoreBoundary q X := by
  have hi := squareRootLowPrimeGoSecondBoundaryDefect_parentCore_interval
    hq hr hrq hcube hd
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi.2, hi.1⟩

/-! ## Exact weighted flattening of the interior prime coordinate -/

/-- The exact `r`-fibre over a fixed outer owner `q` and parent core `d`.
Every point of this fibre carries the same arithmetic source weight `μ(q*d)`. -/
def squareRootLowPrimeGoDefectPrimeFiber (q X d : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun r =>
    r.Prime ∧ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r

@[simp] theorem mem_squareRootLowPrimeGoDefectPrimeFiber
    {q X d r : ℕ} :
    r ∈ squareRootLowPrimeGoDefectPrimeFiber q X d ↔
      r < q ∧ r.Prime ∧
        d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r := by
  simp [squareRootLowPrimeGoDefectPrimeFiber, and_assoc]

/-- In the unfinished owner band, the full birth inequality is redundant and
the surviving interior-prime fibre is exactly one strict prime interval.
Writing `m=q*d`, the moving lower endpoint is `floor(X/(q*m))`. -/
theorem squareRootLowPrimeGoDefectPrimeFiber_eq_primeGap
    {q X d : ℕ} (hq : q.Prime) (hcube : q ^ 3 ≤ X)
    (hd1 : 1 ≤ d) (hdq : d ≤ q - 1) (hsq : Squarefree d) :
    squareRootLowPrimeGoDefectPrimeFiber q X d =
      (Finset.Ioo
        (max (canonicalLargestPrimeFactor d) (X / (q * q * d))) q).filter Nat.Prime := by
  classical
  ext r
  constructor
  · intro hrmem
    rcases mem_squareRootLowPrimeGoDefectPrimeFiber.mp hrmem with
      ⟨hrq, hrPrime, hdDefect⟩
    rcases mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hdDefect with
      ⟨hfull, hphysical⟩
    have hrough :=
      (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).2.2.2.1
    have hdPos : 0 < d := by omega
    have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
    have hq2dPos : 0 < q * q * d := Nat.mul_pos hq2Pos hdPos
    have hXdiv : X / (q * q) < d * r :=
      (Nat.div_lt_iff_lt_mul hrPrime.pos).1 hphysical
    have hX : X < (d * r) * (q * q) :=
      (Nat.div_lt_iff_lt_mul hq2Pos).1 hXdiv
    have hgap : X / (q * q * d) < r := by
      apply (Nat.div_lt_iff_lt_mul hq2dPos).2
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hX
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioo.mpr ⟨?_, hrq⟩, hrPrime⟩
    exact (max_lt_iff).2 ⟨hrough, hgap⟩
  · intro hrmem
    rcases Finset.mem_filter.mp hrmem with ⟨hrIoo, hrPrime⟩
    rcases Finset.mem_Ioo.mp hrIoo with ⟨hlower, hrq⟩
    have hrough : canonicalLargestPrimeFactor d < r :=
      (max_lt_iff.mp hlower).1
    have hgap : X / (q * q * d) < r :=
      (max_lt_iff.mp hlower).2
    have hdPos : 0 < d := by omega
    have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
    have hq2dPos : 0 < q * q * d := Nat.mul_pos hq2Pos hdPos
    have hX : X < r * (q * q * d) :=
      (Nat.div_lt_iff_lt_mul hq2dPos).1 hgap
    have hXdiv : X / (q * q) < d * r := by
      apply (Nat.div_lt_iff_lt_mul hq2Pos).2
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hX
    have hphysical : X / (q * q) / r < d :=
      (Nat.div_lt_iff_lt_mul hrPrime.pos).2 hXdiv
    have hqleCut : q ≤ X / (q * q) := by
      apply (Nat.le_div_iff_mul_le hq2Pos).2
      calc
        q * (q * q) = q ^ 3 := by ring
        _ ≤ X := hcube
    have hbirthMul : q - 1 < d * r := by omega
    have hbirth : (q - 1) / r < d :=
      (Nat.div_lt_iff_lt_mul hrPrime.pos).2 hbirthMul
    apply mem_squareRootLowPrimeGoDefectPrimeFiber.mpr
    refine ⟨hrq, hrPrime, ?_⟩
    apply mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mpr
    exact ⟨mem_squareRootLowPrimeGoFullBirthBoundaryParents.mpr
      ⟨hd1, hdq, hsq, hrough, hbirth⟩, hphysical⟩

/-- Exact number of prime liberties remaining above the exposed parent source. -/
def squareRootLowPrimeGoDefectLibertyMultiplicity (q X d : ℕ) : ℕ :=
  (squareRootLowPrimeGoDefectPrimeFiber q X d).card

/-- The liberty multiplicity is literally the cardinality of the strict prime
interval from the moving lower endpoint to the owner `q`. -/
theorem squareRootLowPrimeGoDefectLibertyMultiplicity_eq_primeGapCard
    {q X d : ℕ} (hq : q.Prime) (hcube : q ^ 3 ≤ X)
    (hd1 : 1 ≤ d) (hdq : d ≤ q - 1) (hsq : Squarefree d) :
    squareRootLowPrimeGoDefectLibertyMultiplicity q X d =
      ((Finset.Ioo
        (max (canonicalLargestPrimeFactor d) (X / (q * q * d))) q).filter Nat.Prime).card := by
  unfold squareRootLowPrimeGoDefectLibertyMultiplicity
  rw [squareRootLowPrimeGoDefectPrimeFiber_eq_primeGap hq hcube hd1 hdq hsq]

/-- Every prime in a fixed defect fibre carries exactly the same source sign.
This is the weighted Othello flattening: multiplicity changes, sign does not. -/
theorem squareRootLowPrimeGoDefectPrimeFiber_edgeValue_eq_parentSource
    {q X d r : ℕ} (hq : q.Prime) (hcube : q ^ 3 ≤ X)
    (hrmem : r ∈ squareRootLowPrimeGoDefectPrimeFiber q X d) :
    squareRootLowPrimeGoAncestryEdgeValue q X r d = (μ (q * d) : ℤ) := by
  rcases mem_squareRootLowPrimeGoDefectPrimeFiber.mp hrmem with
    ⟨hrq, hrPrime, hdDefect⟩
  exact squareRootLowPrimeGoAncestryEdgeValue_eq_parentWeight_of_defect
    hq hrPrime hrq hcube hdDefect

/-- Rectangular presentation of the exact fixed-owner raw defect mass.  The
indicator is precisely the fourth-power cutoff predicate; no absolute value is taken. -/
def squareRootLowPrimeGoOwnerRawDefectMass (q X : ℕ) : ℤ :=
  ∑ r ∈ Finset.range q, ∑ d ∈ Finset.range q,
    if r.Prime ∧ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r then
      (μ (q * d) : ℤ)
    else 0

/-- The same mass after forgetting `r`: each parent source is multiplied by its
exact prime-liberty multiplicity. -/
def squareRootLowPrimeGoOwnerWeightedBoundaryMass (q X : ℕ) : ℤ :=
  ∑ d ∈ Finset.range q,
    (squareRootLowPrimeGoDefectLibertyMultiplicity q X d) • (μ (q * d) : ℤ)

/-- **Exact weighted flattening.**  Summing the raw second-boundary defects over
`r` and then `d` is identically the same as summing once over parent cores with
the exact liberty multiplicity.  This is finite Fubini, not an estimate. -/
theorem squareRootLowPrimeGoOwnerRawDefectMass_eq_weightedBoundaryMass
    (q X : ℕ) :
    squareRootLowPrimeGoOwnerRawDefectMass q X =
      squareRootLowPrimeGoOwnerWeightedBoundaryMass q X := by
  classical
  unfold squareRootLowPrimeGoOwnerRawDefectMass
    squareRootLowPrimeGoOwnerWeightedBoundaryMass
    squareRootLowPrimeGoDefectLibertyMultiplicity
    squareRootLowPrimeGoDefectPrimeFiber
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp

/-- A finite `r`-free boundary containing every exposed parent source.  The
predicate depends only on the arithmetic source `m` and its canonical largest
prime factor. -/
def squareRootLowPrimeGoExposedParentBoundary (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter fun m =>
    let q := canonicalLargestPrimeFactor m
    q ^ 3 ≤ X ∧ X < q ^ 4 ∧
      q * m ≤ X ∧ X < q ^ 2 * m ∧ m < q ^ 2

/-- Every surviving two-boundary defect maps to the finite canonical exposed
parent boundary after forgetting the interior prime `r`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_mem_boundary
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    q * d ∈ squareRootLowPrimeGoExposedParentBoundary X := by
  have hcoords :=
    squareRootLowPrimeGoSecondBoundaryDefect_parentSource_coordinates
      hq hr hrq hd
  have hcontact :=
    squareRootLowPrimeGoSecondBoundaryDefect_parentSource_contactShell
      hq hr hrq hcube hd
  have hfourth :=
    squareRootLowPrimeGoSecondBoundaryDefect_ownerFourth_gt hq hr hrq hd
  have hmLeQm : q * d ≤ q * (q * d) := by
    calc
      q * d = 1 * (q * d) := by simp
      _ ≤ q * (q * d) := Nat.mul_le_mul_right (q * d) hq.one_le
  have hmLeX : q * d ≤ X := hmLeQm.trans hcontact.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
  dsimp
  rw [hcoords.1]
  exact ⟨hcube, hfourth, hcontact.1, hcontact.2, hcoords.2⟩

/-- The same finite boundary is a genuine cubic shell: every exposed parent
source lies strictly above `X^(1/3)` and below `X^(2/3)`, stated integrally as
`X < m^3 < X^2`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_cubeShell
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    X < (q * d) ^ 3 ∧ (q * d) ^ 3 < X ^ 2 := by
  have hcontact :=
    squareRootLowPrimeGoSecondBoundaryDefect_parentSource_contactShell
      hq hr hrq hcube hd
  have hsource :=
    (squareRootLowPrimeGoSecondBoundaryDefect_parentSource_coordinates
      hq hr hrq hd).2
  have hsourceCube : (q * d) ^ 3 < (q ^ 2) ^ 3 :=
    Nat.pow_lt_pow_left hsource (by omega)
  have hownerSquare : (q ^ 3) ^ 2 ≤ X ^ 2 :=
    Nat.pow_le_pow_left hcube 2
  have hdCube : d ≤ d ^ 3 :=
    Nat.le_self_pow (by norm_num : 3 ≠ 0) d
  have hlower : X < (q * d) ^ 3 := by
    calc
      X < q ^ 2 * (q * d) := hcontact.2
      _ = q ^ 3 * d := by ring
      _ ≤ q ^ 3 * d ^ 3 := Nat.mul_le_mul_left (q ^ 3) hdCube
      _ = (q * d) ^ 3 := by ring
  refine ⟨hlower, ?_⟩
  calc
    (q * d) ^ 3 < (q ^ 2) ^ 3 := hsourceCube
    _ = (q ^ 3) ^ 2 := by ring
    _ ≤ X ^ 2 := hownerSquare

/-- Upper half of the cubic shell, retained as a convenient standalone API. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_parentSource_cube_lt_cutoffSquare
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    (q * d) ^ 3 < X ^ 2 :=
  (squareRootLowPrimeGoSecondBoundaryDefect_parentSource_cubeShell
    hq hr hrq hcube hd).2

end RHLean.Proof
