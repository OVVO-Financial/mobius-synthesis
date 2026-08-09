import Mathlib
import RHLean.Proof.CanonicalGapAncestryQuadraticClosure
import RHLean.Proof.SquareRootAncestrySuccessor

/-!
# Zero-cutoff collapse of the projected ancestry renewal

The repository's terminal projected renewal was kept in a three-component form
for arbitrary nonnegative height cutoff `Λ`:

`V_high = U_high - S_low-to-high - S_high-to-high`.

At the canonical terminal choice `Λ = 0`, that bookkeeping collapses exactly.
Every admissible source has distinct canonical largest-prime and cofactor
coordinates, hence nonzero canonical height.  Therefore every nonzero source
weight is high, the low source field vanishes, and the projected renewal is just
the native two-term renewal

`V = U - S V`.

Consequently the six-term projected Gram reduces identically to the three-term
root/successor Gram

`E(U) + E(SV) - 2 <U,SV>`.

This is an exact simplification only.  No bound is placed on either diagonal or
the cross term separately; the remaining analytic obligation is still the full
signed quadratic form.
-/

noncomputable section

namespace RHLean.Proof

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryGram
open CanonicalGapAncestryHighRealization
open CanonicalGapAncestryProjectedRenewal
open CanonicalGapAncestryQuadraticClosure

/-- An admissible canonical source cannot have zero height.  The displayed
largest prime cannot equal the core because it strictly dominates every prime
divisor of that core. -/
theorem sourceAdmissible_not_low_zero
    {B : ℕ} (s : SourceIndex B) (hadm : SourceAdmissible s) :
    ¬ IsCanonicalLowHeight 0 (sourceClock B s) (sourceProduct s) := by
  rcases hadm with ⟨hqPrime, hc1, hsq, hcop, hdom⟩
  have hadm' : SourceAdmissible s := ⟨hqPrime, hc1, hsq, hcop, hdom⟩
  have hqeq := sourcePrime_eq_canonicalLargestPrimeFactor s hadm'
  have hceq := sourceCore_eq_canonicalCofactor s hadm'
  have hqc_ne : sourcePrime s ≠ sourceCore s := by
    intro heq
    have hqdiv : sourcePrime s ∣ sourceCore s := by rw [heq]
    exact (lt_irrefl (sourcePrime s))
      (hdom (sourcePrime s) hqPrime hqdiv)
  intro hlow
  have habs : abs (canonicalHeightTwice (sourceProduct s)) ≤ 0 := by
    simpa [IsCanonicalLowHeight] using hlow
  have hheight : canonicalHeightTwice (sourceProduct s) = 0 :=
    abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
  unfold canonicalHeightTwice at hheight
  rw [← hqeq, ← hceq] at hheight
  have hsqeq :
      ((sourcePrime s : ℝ) ^ 2) = ((sourceCore s : ℝ) ^ 2) := by
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq with hsame | hneg
  · apply hqc_ne
    exact_mod_cast hsame
  · have hqpos : 0 < (sourcePrime s : ℝ) := by
      exact_mod_cast hqPrime.pos
    have hcpos : 0 < (sourceCore s : ℝ) := by
      exact_mod_cast (show 0 < sourceCore s by omega)
    nlinarith

/-- Any field that vanishes outside the admissible source universe has zero
low projection at cutoff zero. -/
private theorem sourceLowProjector_zero_of_supported
    {B : ℕ} (f : SourceIndex B → ℤ)
    (hsupport : ∀ s, ¬ SourceAdmissible s → f s = 0) :
    sourceLowProjector 0 B f = 0 := by
  funext s
  by_cases hadm : SourceAdmissible s
  · have hnot := sourceAdmissible_not_low_zero s hadm
    simp [sourceLowProjector, hnot]
  · have hz := hsupport s hadm
    simp [sourceLowProjector, hz]

/-- The actual bounded source weight has no low component at cutoff zero. -/
theorem sourceLowField_zero_eq_zero (B : ℕ) :
    sourceLowField 0 B = 0 := by
  unfold sourceLowField
  apply sourceLowProjector_zero_of_supported
  intro s hadm
  simp [boundedSourceFlow, sourceWeight, hadm]

/-- Hence the high source field is the entire source weight field. -/
theorem sourceHighField_zero_eq_weight (B : ℕ) :
    sourceHighField 0 B = (boundedSourceFlow B).weight := by
  have hsplit := sourceLowProjector_add_sourceHighProjector
    0 B (boundedSourceFlow B).weight
  have hlow := sourceLowField_zero_eq_zero B
  unfold sourceLowField at hlow
  unfold sourceHighField
  rw [hlow, zero_add] at hsplit
  exact hsplit

/-- The root field also vanishes off the admissible source universe. -/
private theorem sourceRootField_zero_off_admissible
    {B : ℕ} (s : SourceIndex B) (hadm : ¬ SourceAdmissible s) :
    (boundedSourceFlow B).rootField s = 0 := by
  unfold boundedSourceFlow ParentFlow.rootField
  cases hparent : sourceParent s <;>
    simp [hparent, sourceWeight, hadm]

/-- The high-projected root at cutoff zero is the complete root field. -/
theorem sourceHighRootField_zero_eq_rootField (B : ℕ) :
    sourceHighRootField 0 B = (boundedSourceFlow B).rootField := by
  unfold sourceHighRootField
  have hlow :
      sourceLowProjector 0 B (boundedSourceFlow B).rootField = 0 := by
    apply sourceLowProjector_zero_of_supported
    exact sourceRootField_zero_off_admissible
  have hsplit := sourceLowProjector_add_sourceHighProjector
    0 B (boundedSourceFlow B).rootField
  rw [hlow, zero_add] at hsplit
  exact hsplit

/-- With no low source field, low-to-high forcing vanishes identically. -/
theorem sourceLowToHighSuccessorField_zero_eq_zero (B : ℕ) :
    sourceLowToHighSuccessorField 0 B = 0 := by
  unfold sourceLowToHighSuccessorField
  rw [sourceLowField_zero_eq_zero]
  simp

/-- The remaining high-to-high successor is the complete native successor
operator.  This is deduced by comparing the projected and native renewals, so
no independent support argument is needed. -/
theorem sourceHighToHighSuccessorField_zero_eq_successor (B : ℕ) :
    sourceHighToHighSuccessorField 0 B =
      (boundedSourceFlow B).successorOperator (boundedSourceFlow B).weight := by
  have hproj := sourceHighField_eq_projectedRenewal 0 B
  rw [sourceHighField_zero_eq_weight,
    sourceHighRootField_zero_eq_rootField,
    sourceLowToHighSuccessorField_zero_eq_zero, sub_zero] at hproj
  have hnative := weight_eq_root_sub_successor (boundedSourceFlow B)
  have heq :
      (boundedSourceFlow B).rootField -
          sourceHighToHighSuccessorField 0 B =
        (boundedSourceFlow B).rootField -
          (boundedSourceFlow B).successorOperator (boundedSourceFlow B).weight :=
    hproj.symm.trans hnative
  funext s
  have hs := congrFun heq s
  simp only [Pi.sub_apply] at hs
  linarith

/-- Clock-pushed high prefix at zero cutoff is the complete source prefix. -/
theorem sourceHighPrefix_zero_eq_sourcePrefix (B x : ℕ) :
    sourceHighPrefix 0 B x = sourcePrefix B x := by
  unfold sourceHighPrefix sourcePrefix
  change clockPushforward (sourceClock B) x (sourceHighField 0 B) = _
  rw [sourceHighField_zero_eq_weight]

/-- Clock-pushed projected root at zero cutoff is the native ancestry root. -/
theorem sourceHighRootPrefix_zero_eq_sourceRootPrefix (B x : ℕ) :
    sourceHighRootPrefix 0 B x = sourceRootPrefix B x := by
  unfold sourceHighRootPrefix sourceRootPrefix
  rw [sourceHighRootField_zero_eq_rootField]

/-- The low-to-high prefix vanishes at zero cutoff. -/
theorem sourceLowToHighSuccessorPrefix_zero_eq_zero (B x : ℕ) :
    sourceLowToHighSuccessorPrefix 0 B x = 0 := by
  unfold sourceLowToHighSuccessorPrefix
  rw [sourceLowToHighSuccessorField_zero_eq_zero]
  simp

/-- The high-to-high projected prefix is the native successor prefix. -/
theorem sourceHighToHighSuccessorPrefix_zero_eq_sourceSuccessorPrefix
    (B x : ℕ) :
    sourceHighToHighSuccessorPrefix 0 B x = sourceSuccessorPrefix B x := by
  unfold sourceHighToHighSuccessorPrefix sourceSuccessorPrefix
  rw [sourceHighToHighSuccessorField_zero_eq_successor]

/-- Native two-component root path on a translated square-root-clock window. -/
def zeroCutoffRootWindowPath (B N : ℕ) : ℕ → ℤ := fun r =>
  sourceRootPrefix B (N + r)

/-- Native two-component successor path on the same window. -/
def zeroCutoffSuccessorWindowPath (B N : ℕ) : ℕ → ℤ := fun r =>
  sourceSuccessorPrefix B (N + r)

/-- The projected three-component paths collapse exactly at cutoff zero. -/
theorem zeroCutoff_projected_window_paths (B N : ℕ) :
    sourceHighRootWindowPath 0 B N = zeroCutoffRootWindowPath B N ∧
    sourceLowToHighSuccessorWindowPath 0 B N = 0 ∧
    sourceHighToHighSuccessorWindowPath 0 B N =
      zeroCutoffSuccessorWindowPath B N := by
  constructor
  · funext r
    exact sourceHighRootPrefix_zero_eq_sourceRootPrefix B (N + r)
  constructor
  · funext r
    exact sourceLowToHighSuccessorPrefix_zero_eq_zero B (N + r)
  · funext r
    exact sourceHighToHighSuccessorPrefix_zero_eq_sourceSuccessorPrefix B (N + r)

/-- The irreducible two-component Gram value at the canonical zero cutoff.  The
cross term is retained with its forced negative sign. -/
def zeroCutoffRenewalGramValue (B N H : ℕ) : ℤ :=
  windowPathEnergy H (zeroCutoffRootWindowPath B N) +
    windowPathEnergy H (zeroCutoffSuccessorWindowPath B N) -
    2 * windowPathCrossEnergy H
      (zeroCutoffRootWindowPath B N)
      (zeroCutoffSuccessorWindowPath B N)

/-- The six-term projected Gram is literally the two-component Gram at
`Λ = 0`; four terms vanish or merge by equality, not by estimates. -/
theorem projectedRenewalGramValue_zero_eq_zeroCutoff
    (B N H : ℕ) :
    projectedRenewalGramValue 0 B N H =
      zeroCutoffRenewalGramValue B N H := by
  rcases zeroCutoff_projected_window_paths B N with ⟨hroot, hlow, hhigh⟩
  unfold projectedRenewalGramValue zeroCutoffRenewalGramValue
  rw [hroot, hlow, hhigh]
  simp [windowPathEnergy, windowPathCrossEnergy]

/-- The zero-cutoff Gram is exactly the energy of the native two-term renewal
path `root - successor`. -/
theorem zeroCutoffRenewalGramValue_eq_energy_sub
    (B N H : ℕ) :
    zeroCutoffRenewalGramValue B N H =
      windowPathEnergy H (fun r =>
        zeroCutoffRootWindowPath B N r -
          zeroCutoffSuccessorWindowPath B N r) := by
  unfold zeroCutoffRenewalGramValue windowPathEnergy windowPathCrossEnergy
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- The analytic statement remaining after all zero-cutoff exact
simplifications.  It retains the complete root/successor cancellation. -/
def ZeroCutoffRenewalQuadraticBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        ∃ B : ℕ,
          (∀ r ∈ Finset.range H,
            RHLean.Analysis.squarePrefixEndpoint (N + r) ≤ B) ∧
          ((zeroCutoffRenewalGramValue B N H : ℤ) : ℝ) ≤
            C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The new two-term statement is exactly the existing projected-renewal
obligation at `Λ = 0`. -/
theorem zeroCutoffRenewalQuadraticBounded_iff_projected :
    ZeroCutoffRenewalQuadraticBoundedStatement ↔
      ProjectedRenewalQuadraticBoundedStatement 0 := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rcases hbound N H hH hHN with ⟨B, hB, hgram⟩
    refine ⟨B, hB, ?_⟩
    rw [projectedRenewalGramValue_zero_eq_zeroCutoff]
    exact hgram
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rcases hbound N H hH hHN with ⟨B, hB, hgram⟩
    refine ⟨B, hB, ?_⟩
    rw [← projectedRenewalGramValue_zero_eq_zeroCutoff]
    exact hgram

end RHLean.Proof
