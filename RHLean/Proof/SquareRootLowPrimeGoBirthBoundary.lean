import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoOwnerFibers
import RHLean.Proof.SquareRootLowPrimeDefectThresholdBridge

/-!
# Recursive Go descent terminates on the born first-failure boundary

Fix the outer Go owner `q`.  After stripping the unique next-largest prime
`r = P+(c)`, a parent `d` in the recursive strip satisfies

`(q-1)/r < d`, equivalently `q <= r*d`.

There are then exactly two cases.

* `q <= d`: the same outer prime `q` remains a born partner after stripping
  `r`, so the state is genuinely interior and may descend again.
* `d < q`: the outer prime is born at the child `r*d` but not at the parent
  `d`.  This is exactly the repository's born birth boundary, hence the generic
  first-failure threshold `d <= q-1 < r*d`.

Thus the recursive Go law does not end in an ad hoc frozen state.  It ends at a
native multiplicative first-failure shell already used by the low-wheel
finite-difference machinery.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Parents where the fixed outer `q`-birth is lost on stripping `r`. -/
def squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
    (q B r : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSmallerOwnerParentStrip q B r).filter fun d => d < q

/-- Parents where the fixed outer `q`-birth remains interior after stripping
`r`. -/
def squareRootLowPrimeGoSmallerOwnerInteriorParents
    (q B r : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSmallerOwnerParentStrip q B r).filter fun d => q ≤ d

@[simp] theorem mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
    {q B r d : ℕ} :
    d ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q B r ↔
      d ∈ squareRootLowPrimeGoSmallerOwnerParentStrip q B r ∧ d < q := by
  simp [squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents]

@[simp] theorem mem_squareRootLowPrimeGoSmallerOwnerInteriorParents
    {q B r d : ℕ} :
    d ∈ squareRootLowPrimeGoSmallerOwnerInteriorParents q B r ↔
      d ∈ squareRootLowPrimeGoSmallerOwnerParentStrip q B r ∧ q ≤ d := by
  simp [squareRootLowPrimeGoSmallerOwnerInteriorParents]

/-- The recursive parent strip is exactly boundary plus persistent interior. -/
theorem squareRootLowPrimeGoSmallerOwnerParentStrip_eq_boundary_union_interior
    (q B r : ℕ) :
    squareRootLowPrimeGoSmallerOwnerParentStrip q B r =
      squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q B r ∪
        squareRootLowPrimeGoSmallerOwnerInteriorParents q B r := by
  ext d
  simp only [Finset.mem_union,
    mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents,
    mem_squareRootLowPrimeGoSmallerOwnerInteriorParents]
  constructor
  · intro hd
    by_cases hdq : d < q
    · exact Or.inl ⟨hd, hdq⟩
    · exact Or.inr ⟨hd, Nat.le_of_not_gt hdq⟩
  · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd

/-- The two cases are disjoint. -/
theorem squareRootLowPrimeGoSmallerOwnerBoundary_disjoint_interior
    (q B r : ℕ) :
    Disjoint (squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q B r)
      (squareRootLowPrimeGoSmallerOwnerInteriorParents q B r) := by
  rw [Finset.disjoint_left]
  intro d hdBoundary hdInterior
  have hb :=
    (mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents.mp hdBoundary).2
  have hi :=
    (mem_squareRootLowPrimeGoSmallerOwnerInteriorParents.mp hdInterior).2
  omega

/-- **Boundary parents are exactly multiplicative first-failure crossings.**
The lower quotient inequality in the Go strip is equivalent to crossing the
fixed predecessor threshold `q-1` when `r` is restored. -/
theorem squareRootLowPrimeGoBirthBoundary_thresholdCrosses
    {q B r d : ℕ} (hr : r.Prime)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q B r) :
    squareRootLowPrimeThresholdCrosses r (q - 1) d := by
  rcases mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents.mp hd with
    ⟨hdStrip, hdq⟩
  have hlower :=
    (mem_squareRootLowPrimeGoSmallerOwnerParentStrip.mp hdStrip).2
  unfold squareRootLowPrimeThresholdCrosses
  constructor
  · omega
  · simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul hr.pos).1 hlower

/-- At the square-dilated cutoff, the outer owner `q` is genuinely a born
partner of every reconstructed recursive child.  This records the extra
`q^2` physical-scale saving rather than discarding it. -/
theorem squareRootLowPrimeGoSquareParent_outerOwner_bornAtChild
    {R q r d : ℕ} (hq : q.Prime) (hqR : q ≤ R)
    (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerParentStrip q
      (squareRootEndpoint R / (q * q)) r) :
    q ∈ squareRootBornPartnerSet R (r * d) := by
  have hchild := squareRootLowPrimeGoSmallerOwnerParent_child_mem
    hq hr hrq hd
  rcases mem_squareRootLowPrimeGoSmallerOwnerChildren.mp hchild with
    ⟨hchildSmooth, hqchild, _howner⟩
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hchildSmooth with
    ⟨_hchildOne, hchildCutoff, _hchildSq, hchildRough⟩
  have hqqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hsecondContact : (r * d) * (q * q) ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hqqPos).1 hchildCutoff
  have hqLeQQ : q ≤ q * q := by
    have hqOne : 1 ≤ q := hq.one_le
    simpa [one_mul] using Nat.mul_le_mul_left q hqOne
  have hproduct : (r * d) * q ≤ squareRootEndpoint R := by
    exact (Nat.mul_le_mul_left (r * d) hqLeQQ).trans hsecondContact
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hq.two_le, hqR⟩,
    hq, hchildRough, hqchild, hproduct⟩

/-- **Scale collapse at the stopping boundary.**  A terminal recursive child
`c = r*d` is simultaneously below `q^2` (because `r,d < q`) and satisfies the
second-contact inequality `c*q^2 <= R^2-1`.  Therefore `c^2 < R^2`, hence
`c < R`. -/
theorem squareRootLowPrimeGoSquareBirthBoundary_child_lt_root
    {R q r d : ℕ} (hq : q.Prime) (hqR : q ≤ R)
    (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
      (squareRootEndpoint R / (q * q)) r) :
    r * d < R := by
  have hdStrip :=
    (mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents.mp hd).1
  have hdq :=
    (mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents.mp hd).2
  have hchild := squareRootLowPrimeGoSmallerOwnerParent_child_mem
    hq hr hrq hdStrip
  have hchildSmooth :=
    (mem_squareRootLowPrimeGoSmallerOwnerChildren.mp hchild).1
  have hchildCutoff :=
    (mem_squareRootLowPrimeGoSmoothCofactors.mp hchildSmooth).2.1
  have hdSmooth :=
    (mem_squareRootLowPrimeGoSmallerOwnerParentStrip.mp hdStrip).1
  have hdOne := (mem_squareRootLowPrimeGoSmoothCofactors.mp hdSmooth).1
  have hdPos : 0 < d := by omega
  have hchildPos : 0 < r * d := Nat.mul_pos hr.pos hdPos
  have hchildLtQQ : r * d < q * q := by
    calc
      r * d < q * d := Nat.mul_lt_mul_of_pos_right hrq hdPos
      _ < q * q := Nat.mul_lt_mul_of_pos_left hdq hq.pos
  have hqqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hsecondContact : (r * d) * (q * q) ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hqqPos).1 hchildCutoff
  have hchildSqLt : (r * d) * (r * d) < (r * d) * (q * q) :=
    Nat.mul_lt_mul_of_pos_left hchildLtQQ hchildPos
  by_contra hnot
  have hRchild : R ≤ r * d := Nat.le_of_not_gt hnot
  have hRRle : R * R ≤ (r * d) * (r * d) :=
    Nat.mul_le_mul hRchild hRchild
  have hendpointLt : squareRootEndpoint R < R * R := by
    have hRpos : 0 < R := lt_of_lt_of_le hq.pos hqR
    unfold squareRootEndpoint
    simpa [pow_two] using Nat.sub_lt (Nat.mul_pos hRpos hRpos) (by omega : 0 < 1)
  omega

/-- **Go boundary = born birth boundary.**  Once the stripped parent falls below
`q`, the fixed outer owner is lost for exactly one reason: the numerical birth
condition. -/
theorem squareRootLowPrimeGoSquareBirthBoundary_mem_bornBoundary
    {R q r d : ℕ} (hq : q.Prime) (hqR : q ≤ R)
    (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
      (squareRootEndpoint R / (q * q)) r) :
    q ∈ squareRootBornPartnerBirthBoundary R d (r * d) := by
  have hdStrip :=
    (mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents.mp hd).1
  have hdq :=
    (mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents.mp hd).2
  apply mem_squareRootBornPartnerBirthBoundary.mpr
  exact ⟨squareRootLowPrimeGoSquareParent_outerOwner_bornAtChild
    hq hqR hr hrq hdStrip, hdq⟩

/-- **Interior persistence.**  If the stripped parent is still at least `q`,
the same outer `q` remains a born partner after stripping `r`; this is the
literal reason the recursion may continue. -/
theorem squareRootLowPrimeGoSquareInterior_outerOwner_bornAtParent
    {R q r d : ℕ} (hq : q.Prime) (hqR : q ≤ R)
    (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerInteriorParents q
      (squareRootEndpoint R / (q * q)) r) :
    q ∈ squareRootBornPartnerSet R d := by
  have hdStrip :=
    (mem_squareRootLowPrimeGoSmallerOwnerInteriorParents.mp hd).1
  have hqd :=
    (mem_squareRootLowPrimeGoSmallerOwnerInteriorParents.mp hd).2
  have hupper := squareRootLowPrimeGoSquareParent_outerOwner_bornAtChild
    hq hqR hr hrq hdStrip
  have hdSmooth :=
    (mem_squareRootLowPrimeGoSmallerOwnerParentStrip.mp hdStrip).1
  have hdPos : 0 < d := by
    have hdOne := (mem_squareRootLowPrimeGoSmoothCofactors.mp hdSmooth).1
    omega
  have hdiv : d ∣ r * d := ⟨r, by ring⟩
  exact (mem_squareRootBornPartnerSet_of_dvd_iff_order hdPos hdiv hupper).2 hqd

end RHLean.Proof
