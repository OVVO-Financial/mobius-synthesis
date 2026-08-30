import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell

/-!
# The Go two-boundary shell is a canonical ancestry clock crossing

Fix an unfinished outer owner `q`.  A full recursive stopping edge has the form

`d -> r*d`,  with `d < q <= r*d` and `P+(d) < r < q`.

For the repository's canonical ancestry flow with distinguished prime `q`, the
parent core `d` is therefore transport-oriented and the child core `r*d` is
smooth-oriented.  Its canonical parent is exactly `d`, and the source Möbius
weights reverse sign.

The square-dilated Go wall is the monotone clock

`C_q(c) = q^2*c`.

In the unfinished region `q^3 <= X`, every stopping parent automatically has
`C_q(d) <= X`.  The actual Go terminal population has `C_q(r*d) <= X`, so both
ends of the ancestry edge are active and cancel.  Its complement has
`X < C_q(r*d)`, so only the parent is active.  Thus the remaining defect is
literally the activity interval of one sign-reversing canonical ancestry edge.

This is an exact signed identity, not a cardinality estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- A squarefree rough core below `q` carries the native canonical source data
with distinguished prime `q`. -/
theorem squareRootLowPrimeGo_canonicalSourceData_of_rough
    {q c : ℕ} (hq : q.Prime) (hc1 : 1 <= c) (hsq : Squarefree c)
    (hrough : canonicalLargestPrimeFactor c < q) :
    CanonicalSourceData q c := by
  have hnotdvd : ¬ q ∣ c := by
    intro hdiv
    by_cases hcOne : c = 1
    · subst c
      exact hq.not_dvd_one hdiv
    · have hcgt : 1 < c := by omega
      have hle := prime_dvd_le_canonicalLargestPrimeFactor hcgt hq hdiv
      omega
  have hcop : Nat.Coprime q c := hq.coprime_iff_not_dvd.mpr hnotdvd
  refine ⟨hq, hc1, hsq, hcop, ?_⟩
  intro p hp hpc
  by_cases hcOne : c = 1
  · subst c
    exact (hp.not_dvd_one hpc).elim
  · have hcgt : 1 < c := by omega
    have hle := prime_dvd_le_canonicalLargestPrimeFactor hcgt hp hpc
    omega

/-- Every full Go birth-boundary parent is a transport-oriented ancestry root
for the fixed distinguished owner `q`. -/
theorem squareRootLowPrimeGoFullBirthBoundary_parent_canonicalRoot
    {q r d : ℕ} (hq : q.Prime) (_hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    CanonicalSourceData q d ∧ d < q := by
  rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd with
    ⟨hd1, hdq1, hsq, hroughR, _hlower⟩
  have hroughQ : canonicalLargestPrimeFactor d < q := hroughR.trans hrq
  exact ⟨squareRootLowPrimeGo_canonicalSourceData_of_rough
      hq hd1 hsq hroughQ,
    by omega⟩

/-- Restoring the smaller owner `r` produces a smooth-oriented ancestry child
for distinguished prime `q`. -/
theorem squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    CanonicalSourceData q (r * d) ∧ q < r * d := by
  rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd with
    ⟨hd1, _hdq1, hsq, hroughR, hlower⟩
  have hdPos : 0 < d := by omega
  have hrNotDvd : ¬ r ∣ d := by
    intro hdiv
    by_cases hdOne : d = 1
    · subst d
      exact hr.not_dvd_one hdiv
    · have hdgt : 1 < d := by omega
      have hle := prime_dvd_le_canonicalLargestPrimeFactor hdgt hr hdiv
      omega
  have hmuD : μ d ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
  have hcop : Nat.Coprime r d :=
    (hr.coprime_iff_not_dvd).2 hrNotDvd
  have hmuChild : μ (r * d) ≠ 0 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hr]
    exact mul_ne_zero (by norm_num) hmuD
  have hsqChild : Squarefree (r * d) :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuChild
  have hlpfChild : canonicalLargestPrimeFactor (r * d) = r := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hdPos hr hroughR
    simpa [Nat.mul_comm] using h
  have hroughQ : canonicalLargestPrimeFactor (r * d) < q := by
    rw [hlpfChild]
    exact hrq
  have hchild1 : 1 <= r * d := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hr.ne_zero (Nat.ne_of_gt hdPos))
  have hqChild : q <= r * d :=
    squareRootLowPrimeGoFullBirthBoundary_outer_le_child hr hd
  have hqNotEq : q ≠ r * d := by
    intro heq
    have hqDvd : q ∣ r * d := by rw [← heq]
    rcases hq.dvd_mul.mp hqDvd with hqr | hqd
    · have hrLeq : q ≤ r := Nat.le_of_dvd hr.pos hqr
      omega
    · by_cases hdOne : d = 1
      · subst d
        exact hq.not_dvd_one hqd
      · have hdgt : 1 < d := by omega
        have hqLe := prime_dvd_le_canonicalLargestPrimeFactor hdgt hq hqd
        omega
  exact ⟨squareRootLowPrimeGo_canonicalSourceData_of_rough
      hq hchild1 hsqChild hroughQ,
    lt_of_le_of_ne hqChild hqNotEq⟩

/-- The canonical ancestry parent of the smooth child core `r*d` is literally
`d`. -/
theorem squareRootLowPrimeGoFullBirthBoundary_child_canonicalCofactor
    {q r d : ℕ} (hr : r.Prime)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    canonicalCofactor (r * d) = d := by
  rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd with
    ⟨hd1, _hdq1, _hsq, hroughR, _hlower⟩
  have hdPos : 0 < d := by omega
  have h := canonicalCofactor_mul_prime_eq_of_rough hdPos hr hroughR
  simpa [Nat.mul_comm] using h

/-- The source weights on the ancestry root/child edge are exact opposites. -/
theorem squareRootLowPrimeGoFullBirthBoundary_source_moebius_cancel
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    (μ (q * (r * d)) : ℤ) = -(μ (q * d) : ℤ) := by
  have hparent := squareRootLowPrimeGoFullBirthBoundary_parent_canonicalRoot
    hq hr hrq hd
  have hchild := squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth
    hq hr hrq hd
  have hqCopD := hparent.1.2.2.2.1
  have hqCopChild := hchild.1.2.2.2.1
  have hcofactor := squareRootLowPrimeGoFullBirthBoundary_child_canonicalCofactor
    hr hd
  have hsqChild := hchild.1.2.2.1
  have hchildGt : 1 < r * d := lt_trans hq.one_lt hchild.2
  have hstrip : (μ (r * d) : ℤ) = -(μ d : ℤ) := by
    simpa [hcofactor] using canonicalSignedParent_moebius hsqChild hchildGt
  calc
    (μ (q * (r * d)) : ℤ) = μ q * μ (r * d) :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqCopChild
    _ = μ q * (-μ d) := by rw [hstrip]
    _ = -(μ q * μ d) := by ring
    _ = -(μ (q * d) : ℤ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqCopD]

/-- Second-contact ancestry clock on a core with fixed distinguished prime `q`. -/
def squareRootLowPrimeGoAncestryClock (q c : ℕ) : ℕ :=
  q * q * c

/-- In the unfinished region, every full stopping parent is already active for
the second-contact ancestry clock. -/
theorem squareRootLowPrimeGoFullBirthBoundary_parentClock_le
    {q X r d : ℕ} (hq : q.Prime) (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    squareRootLowPrimeGoAncestryClock q d ≤ X := by
  have hdq1 :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).2.1
  have hqTwo : 2 ≤ q := hq.two_le
  have hdq : d < q := by omega
  have hlt : q * q * d < q ^ 3 := by
    calc
      q * q * d < q * q * q := Nat.mul_lt_mul_of_pos_left hdq (Nat.mul_pos hq.pos hq.pos)
      _ = q ^ 3 := by ring
  exact hlt.le.trans hcube

/-- Actual Go terminal parents are precisely the full ancestry edges whose
smooth child is still active for the second-contact clock. -/
theorem squareRootLowPrimeGoTerminalParent_childClock_le
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
      (X / (q * q)) r) :
    squareRootLowPrimeGoAncestryClock q (r * d) ≤ X := by
  have hdStrip :=
    (mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents.mp hd).1
  have hdSmooth :=
    (mem_squareRootLowPrimeGoSmallerOwnerParentStrip.mp hdStrip).1
  have hdCut := (mem_squareRootLowPrimeGoSmoothCofactors.mp hdSmooth).2.1
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hrdCut : r * d ≤ X / (q * q) := by
    have h := (Nat.le_div_iff_mul_le hr.pos).1 hdCut
    simpa [Nat.mul_comm] using h
  have h := (Nat.le_div_iff_mul_le hq2Pos).1 hrdCut
  simpa [squareRootLowPrimeGoAncestryClock,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- The complementary two-boundary defect is exactly a smooth child entering
after the second-contact clock cutoff. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_childClock_gt
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    X < squareRootLowPrimeGoAncestryClock q (r * d) := by
  have h := squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt
    hq hr hd
  simpa [squareRootLowPrimeGoAncestryClock, Nat.mul_assoc] using h

/-- One full stopping ancestry edge evaluated at the second-contact clock. -/
def squareRootLowPrimeGoAncestryEdgeValue
    (q X r d : ℕ) : ℤ :=
  (μ (q * d) : ℤ) * (if squareRootLowPrimeGoAncestryClock q d ≤ X then 1 else 0) +
    (μ (q * (r * d)) : ℤ) *
      (if squareRootLowPrimeGoAncestryClock q (r * d) ≤ X then 1 else 0)

/-- If both ends of the stopping edge are inside the physical clock, their
opposite source weights cancel exactly. -/
theorem squareRootLowPrimeGoAncestryEdgeValue_eq_zero_of_terminal
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
      (X / (q * q)) r) :
    squareRootLowPrimeGoAncestryEdgeValue q X r d = 0 := by
  have hfull : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r := by
    have hfilter :=
      squareRootLowPrimeGoBirthBoundaryParents_eq_full_filter_physical q X r
    rw [hfilter] at hd
    exact (Finset.mem_filter.mp hd).1
  have hparent := squareRootLowPrimeGoFullBirthBoundary_parentClock_le
    hq hcube hfull
  have hchild := squareRootLowPrimeGoTerminalParent_childClock_le hq hr hd
  have hcancel := squareRootLowPrimeGoFullBirthBoundary_source_moebius_cancel
    hq hr hrq hfull
  unfold squareRootLowPrimeGoAncestryEdgeValue
  simp [hparent, hchild, hcancel]

/-- **Two-boundary Go defect = one ancestry activity interval.**  On a defect
edge the parent has entered but the child has not, so the edge value is exactly
the parent source weight. -/
theorem squareRootLowPrimeGoAncestryEdgeValue_eq_parentWeight_of_defect
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (_hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    squareRootLowPrimeGoAncestryEdgeValue q X r d =
      (μ (q * d) : ℤ) := by
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hparent := squareRootLowPrimeGoFullBirthBoundary_parentClock_le
    hq hcube hfull
  have hchildGt := squareRootLowPrimeGoSecondBoundaryDefect_childClock_gt
    hq hr hd
  have hchildNot : ¬ squareRootLowPrimeGoAncestryClock q (r * d) ≤ X :=
    Nat.not_le_of_gt hchildGt
  unfold squareRootLowPrimeGoAncestryEdgeValue
  simp [hparent, hchildNot]

/-- The parent ancestry source weight is the negative of the original Go-parent
Möbius weight, since the fixed outer owner `q` is fresh above every factor of
`d`. -/
theorem squareRootLowPrimeGoFullBirthBoundary_parentSourceWeight_eq_neg
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    (μ (q * d) : ℤ) = -(μ d : ℤ) := by
  have hparent := squareRootLowPrimeGoFullBirthBoundary_parent_canonicalRoot
    hq hr hrq hd
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    hparent.1.2.2.2.1,
    ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- Consequently the surviving defect edge carries exactly the negative of the
Go boundary-parent sign. -/
theorem squareRootLowPrimeGoAncestryEdgeValue_eq_neg_goWeight_of_defect
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    squareRootLowPrimeGoAncestryEdgeValue q X r d = -(μ d : ℤ) := by
  rw [squareRootLowPrimeGoAncestryEdgeValue_eq_parentWeight_of_defect
      hq hr hrq hcube hd,
    squareRootLowPrimeGoFullBirthBoundary_parentSourceWeight_eq_neg
      hq hr hrq
      (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1]

end RHLean.Proof
