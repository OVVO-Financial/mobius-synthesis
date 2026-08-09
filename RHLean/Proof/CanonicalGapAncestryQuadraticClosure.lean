import RHLean.Proof.CanonicalGapAncestryProjectedRenewal
import RHLean.Analysis.CanonicalHighSectorBridge

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryQuadraticClosure

open CanonicalGapAncestryGram
open CanonicalGapAncestryHighRealization
open CanonicalGapAncestryProjectedRenewal

/-!
# Projected ancestry quadratic closure

This module closes the exact formal route selected by the ancestry experiments.
The projected high path is the signed combination

```text
root - low-to-high forcing - high-to-high transport.
```

The analytic object is therefore the complete six-term Gram quadratic form.  In
particular, the two successor diagonals are not bounded separately and no cross
term is discarded.  The final theorem proves that a translated-window bound for
this exact quadratic form is equivalent to the native canonical high-sector
statement `(HS)`, and hence to RH once the ordinary classical Mertens criterion
is supplied.

The quadratic bound remains an explicitly named proposition.  This file proves
an exact reduction, not the open analytic estimate.
-/

/-- The complete signed Gram value of the projected renewal.  Every diagonal and
cross term from the exact identity is retained with its forced sign. -/
def projectedRenewalGramValue
    (Λ : ℝ) (B N H : ℕ) : ℤ :=
  windowPathEnergy H (sourceHighRootWindowPath Λ B N) +
    windowPathEnergy H (sourceLowToHighSuccessorWindowPath Λ B N) +
    windowPathEnergy H (sourceHighToHighSuccessorWindowPath Λ B N) -
    2 * windowPathCrossEnergy H
      (sourceHighRootWindowPath Λ B N)
      (sourceLowToHighSuccessorWindowPath Λ B N) -
    2 * windowPathCrossEnergy H
      (sourceHighRootWindowPath Λ B N)
      (sourceHighToHighSuccessorWindowPath Λ B N) +
    2 * windowPathCrossEnergy H
      (sourceLowToHighSuccessorWindowPath Λ B N)
      (sourceHighToHighSuccessorWindowPath Λ B N)

/-- The projected-renewal Gram value is exactly the energy of the actual high
source path.  This is special-vector cancellation in the complete quadratic
form, not an entrywise sign assertion. -/
theorem sourceHighWindowEnergy_eq_projectedRenewalGramValue
    (Λ : ℝ) (B N H : ℕ) :
    windowPathEnergy H (sourceHighWindowPath Λ B N) =
      projectedRenewalGramValue Λ B N H := by
  simpa [projectedRenewalGramValue] using
    sourceHighWindowEnergy_eq_projectedRenewalGram Λ B N H

/-- Squared complex norm of an integer cast, expressed in the native integer
quadratic form. -/
private theorem norm_intCast_complex_sq (z : ℤ) :
    ‖((z : ℤ) : ℂ)‖ ^ 2 = ((z * z : ℤ) : ℝ) := by
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply]

/-- The local complex energy of the bounded high source prefix is the real cast
of its integer path energy. -/
theorem localSequenceEnergy_sourceHighPrefix_eq_windowPathEnergy
    (Λ : ℝ) (B N H : ℕ) :
    RHLean.Analysis.localSequenceEnergy
        (fun n => ((sourceHighPrefix Λ B n : ℤ) : ℂ)) N H =
      ((windowPathEnergy H (sourceHighWindowPath Λ B N) : ℤ) : ℝ) := by
  unfold RHLean.Analysis.localSequenceEnergy
    windowPathEnergy windowPathCrossEnergy sourceHighWindowPath
  push_cast
  apply Finset.sum_congr rfl
  intro r _hr
  simpa using norm_intCast_complex_sq (sourceHighPrefix Λ B (N + r))

/-- Exact local-energy realization by the complete projected-renewal Gram value. -/
theorem localSequenceEnergy_sourceHighPrefix_eq_projectedRenewalGramValue
    (Λ : ℝ) (B N H : ℕ) :
    RHLean.Analysis.localSequenceEnergy
        (fun n => ((sourceHighPrefix Λ B n : ℤ) : ℂ)) N H =
      ((projectedRenewalGramValue Λ B N H : ℤ) : ℝ) := by
  calc
    RHLean.Analysis.localSequenceEnergy
        (fun n => ((sourceHighPrefix Λ B n : ℤ) : ℂ)) N H =
        ((windowPathEnergy H (sourceHighWindowPath Λ B N) : ℤ) : ℝ) :=
      localSequenceEnergy_sourceHighPrefix_eq_windowPathEnergy Λ B N H
    _ = ((projectedRenewalGramValue Λ B N H : ℤ) : ℝ) := by
      rw [sourceHighWindowEnergy_eq_projectedRenewalGramValue]

/-- A canonical finite source cutoff covering every square-prefix endpoint in a
translated window.  A sum is used so no separate monotonicity lemma is needed. -/
def windowSourceBound (N H : ℕ) : ℕ :=
  Finset.sum (Finset.range H) fun r =>
    RHLean.Analysis.squarePrefixEndpoint (N + r)

/-- Every endpoint occurring in the window is bounded by `windowSourceBound`. -/
theorem squarePrefixEndpoint_le_windowSourceBound
    {N H r : ℕ} (hr : r ∈ Finset.range H) :
    RHLean.Analysis.squarePrefixEndpoint (N + r) ≤ windowSourceBound N H := by
  unfold windowSourceBound
  exact Finset.single_le_sum
    (s := Finset.range H)
    (f := fun t => RHLean.Analysis.squarePrefixEndpoint (N + t))
    (fun _ _ => Nat.zero_le _) hr

/-- The final experiment-led analytic statement.  For each translated window,
the bounded source universe may be enlarged only enough to realize that window;
the complete signed projected-renewal Gram value must then satisfy the RH-scale
quadratic bound.

All six Gram terms remain inside this proposition.  It is not a sum of positive
component-energy estimates. -/
def ProjectedRenewalQuadraticBoundedStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        ∃ B : ℕ,
          (∀ r ∈ Finset.range H,
            RHLean.Analysis.squarePrefixEndpoint (N + r) ≤ B) ∧
          ((projectedRenewalGramValue Λ B N H : ℤ) : ℝ) ≤
            C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The complete projected-renewal quadratic bound is exactly canonical `(HS)`.
The forward direction uses any supplied finite realization; the reverse
direction chooses the canonical window cutoff. -/
theorem projectedRenewalQuadraticBounded_iff_canonicalHigh
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ProjectedRenewalQuadraticBoundedStatement Λ ↔
      CanonicalHighUniformLocalBoundedStatement Λ := by
  constructor
  · intro hquad ε hε
    rcases hquad ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rcases hbound N H hH hHN with ⟨B, hB, hgram⟩
    calc
      RHLean.Analysis.localSequenceEnergy (canonicalHighPrefix Λ) N H =
          RHLean.Analysis.localSequenceEnergy
            (fun n => ((sourceHighPrefix Λ B n : ℤ) : ℂ)) N H :=
        (localSequenceEnergy_sourceHighPrefix_eq_canonicalHighPrefix hΛ hB).symm
      _ = ((projectedRenewalGramValue Λ B N H : ℤ) : ℝ) :=
        localSequenceEnergy_sourceHighPrefix_eq_projectedRenewalGramValue
          Λ B N H
      _ ≤ C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := hgram
  · intro hhigh ε hε
    rcases hhigh ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    let B := windowSourceBound N H
    have hB : ∀ r ∈ Finset.range H,
        RHLean.Analysis.squarePrefixEndpoint (N + r) ≤ B := by
      intro r hr
      exact squarePrefixEndpoint_le_windowSourceBound hr
    refine ⟨B, hB, ?_⟩
    calc
      ((projectedRenewalGramValue Λ B N H : ℤ) : ℝ) =
          RHLean.Analysis.localSequenceEnergy
            (fun n => ((sourceHighPrefix Λ B n : ℤ) : ℂ)) N H :=
        (localSequenceEnergy_sourceHighPrefix_eq_projectedRenewalGramValue
          Λ B N H).symm
      _ = RHLean.Analysis.localSequenceEnergy (canonicalHighPrefix Λ) N H :=
        localSequenceEnergy_sourceHighPrefix_eq_canonicalHighPrefix hΛ hB
      _ ≤ C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) :=
        hbound N H hH hHN

/-- Terminal formal route: the exact projected-renewal Gram estimate is
 equivalent to RH, conditional only on the ordinary classical Mertens criterion
 already exposed by the project. -/
theorem projectedRenewalQuadraticBounded_iff_riemannHypothesis
    (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    ProjectedRenewalQuadraticBoundedStatement Λ ↔
      RHLean.Analysis.RiemannHypothesisStatement := by
  calc
    ProjectedRenewalQuadraticBoundedStatement Λ ↔
        CanonicalHighUniformLocalBoundedStatement Λ :=
      projectedRenewalQuadraticBounded_iff_canonicalHigh hΛ
    _ ↔ RHLean.Analysis.RiemannHypothesisStatement :=
      canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized
        Λ criterion

end CanonicalGapAncestryQuadraticClosure

end RHLean.Proof
