import RHLean.Proof.CanonicalGapAncestryHighRealization

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryProjectedRenewal

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryGram
open CanonicalGapAncestryHighRealization

/-!
# Projected canonical ancestry renewal

This module projects the exact finite ancestry renewal equation into the native
canonical high-height sector. The successor pullback is split by the height of
the parent field before the result is projected at the child:

```text
V_high = U_high - S_low-to-high - S_high-to-high.
```

The low-to-high term is retained explicitly. Thus the formal high sector is not
silently treated as closed under the successor flow. The final section records
the full raw and centered three-component Gram ledgers. No analytic estimate is
asserted.
-/

/-! ## Projected source fields -/

/-- Low-height part of the bounded source weight field. -/
def sourceLowField (Λ : ℝ) (B : ℕ) : SourceIndex B → ℤ :=
  sourceLowProjector Λ B (boundedSourceFlow B).weight

/-- High-height part of the bounded source weight field. -/
def sourceHighField (Λ : ℝ) (B : ℕ) : SourceIndex B → ℤ :=
  sourceHighProjector Λ B (boundedSourceFlow B).weight

/-- High-height part of the transport-root field. -/
def sourceHighRootField (Λ : ℝ) (B : ℕ) : SourceIndex B → ℤ :=
  sourceHighProjector Λ B (boundedSourceFlow B).rootField

/-- Values pulled from low-height parents and landing at high-height children. -/
def sourceLowToHighSuccessorField
    (Λ : ℝ) (B : ℕ) : SourceIndex B → ℤ :=
  sourceHighProjector Λ B
    ((boundedSourceFlow B).successorOperator (sourceLowField Λ B))

/-- Values pulled from high-height parents and landing at high-height children. -/
def sourceHighToHighSuccessorField
    (Λ : ℝ) (B : ℕ) : SourceIndex B → ℤ :=
  sourceHighProjector Λ B
    ((boundedSourceFlow B).successorOperator (sourceHighField Λ B))

/-- Exact projected renewal. Both the high-to-high transport and the low-to-high
forcing are retained. -/
theorem sourceHighField_eq_projectedRenewal (Λ : ℝ) (B : ℕ) :
    sourceHighField Λ B =
      sourceHighRootField Λ B -
        sourceLowToHighSuccessorField Λ B -
        sourceHighToHighSuccessorField Λ B := by
  unfold sourceHighField sourceHighRootField sourceLowToHighSuccessorField
    sourceHighToHighSuccessorField sourceLowField
  have hrenew := weight_eq_root_sub_successor (boundedSourceFlow B)
  have hsplit :=
    sourceLowProjector_add_sourceHighProjector Λ B
      (boundedSourceFlow B).weight
  calc
    sourceHighProjector Λ B (boundedSourceFlow B).weight =
        sourceHighProjector Λ B
          ((boundedSourceFlow B).rootField -
            (boundedSourceFlow B).successorOperator
              (boundedSourceFlow B).weight) := by
      exact congrArg (sourceHighProjector Λ B) hrenew
    _ = sourceHighProjector Λ B (boundedSourceFlow B).rootField -
          sourceHighProjector Λ B
            ((boundedSourceFlow B).successorOperator
              (boundedSourceFlow B).weight) := by
      rw [map_sub]
    _ = sourceHighProjector Λ B (boundedSourceFlow B).rootField -
          sourceHighProjector Λ B
            ((boundedSourceFlow B).successorOperator
              (sourceLowProjector Λ B (boundedSourceFlow B).weight +
                sourceHighProjector Λ B (boundedSourceFlow B).weight)) := by
      rw [hsplit]
    _ = sourceHighProjector Λ B (boundedSourceFlow B).rootField -
          sourceHighProjector Λ B
            ((boundedSourceFlow B).successorOperator
                (sourceLowProjector Λ B (boundedSourceFlow B).weight) +
              (boundedSourceFlow B).successorOperator
                (sourceHighProjector Λ B (boundedSourceFlow B).weight)) := by
      rw [map_add]
    _ = sourceHighProjector Λ B (boundedSourceFlow B).rootField -
          (sourceHighProjector Λ B
              ((boundedSourceFlow B).successorOperator
                (sourceLowProjector Λ B (boundedSourceFlow B).weight)) +
            sourceHighProjector Λ B
              ((boundedSourceFlow B).successorOperator
                (sourceHighProjector Λ B (boundedSourceFlow B).weight))) := by
      rw [map_add]
    _ = sourceHighProjector Λ B (boundedSourceFlow B).rootField -
          sourceHighProjector Λ B
            ((boundedSourceFlow B).successorOperator
              (sourceLowProjector Λ B (boundedSourceFlow B).weight)) -
          sourceHighProjector Λ B
            ((boundedSourceFlow B).successorOperator
              (sourceHighProjector Λ B (boundedSourceFlow B).weight)) := by
      abel

/-! ## Clock-pushed projected renewal -/

/-- Clock-pushed projected transport-root contribution. -/
def sourceHighRootPrefix (Λ : ℝ) (B x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x (sourceHighRootField Λ B)

/-- Clock-pushed low-to-high forcing contribution. -/
def sourceLowToHighSuccessorPrefix (Λ : ℝ) (B x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x
    (sourceLowToHighSuccessorField Λ B)

/-- Clock-pushed high-to-high transport contribution. -/
def sourceHighToHighSuccessorPrefix (Λ : ℝ) (B x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x
    (sourceHighToHighSuccessorField Λ B)

/-- The projected renewal survives the native square-root clock pushforward. -/
theorem sourceHighPrefix_eq_projectedRenewal
    (Λ : ℝ) (B x : ℕ) :
    sourceHighPrefix Λ B x =
      sourceHighRootPrefix Λ B x -
        sourceLowToHighSuccessorPrefix Λ B x -
        sourceHighToHighSuccessorPrefix Λ B x := by
  unfold sourceHighRootPrefix sourceLowToHighSuccessorPrefix
    sourceHighToHighSuccessorPrefix
  change
    clockPushforward (sourceClock B) x (sourceHighField Λ B) = _
  rw [sourceHighField_eq_projectedRenewal, map_sub, map_sub]

/-- Actual projected root path in a window beginning at `N`. -/
def sourceHighRootWindowPath (Λ : ℝ) (B N : ℕ) : ℕ → ℤ := fun r =>
  sourceHighRootPrefix Λ B (N + r)

/-- Actual low-to-high forcing path in a window beginning at `N`. -/
def sourceLowToHighSuccessorWindowPath
    (Λ : ℝ) (B N : ℕ) : ℕ → ℤ := fun r =>
  sourceLowToHighSuccessorPrefix Λ B (N + r)

/-- Actual high-to-high transport path in a window beginning at `N`. -/
def sourceHighToHighSuccessorWindowPath
    (Λ : ℝ) (B N : ℕ) : ℕ → ℤ := fun r =>
  sourceHighToHighSuccessorPrefix Λ B (N + r)

/-- Exact pathwise projected renewal with inherited backlog retained in all three
components. -/
theorem sourceHighWindowPath_eq_projectedRenewal
    (Λ : ℝ) (B N : ℕ) :
    sourceHighWindowPath Λ B N = fun r =>
      sourceHighRootWindowPath Λ B N r -
        sourceLowToHighSuccessorWindowPath Λ B N r -
        sourceHighToHighSuccessorWindowPath Λ B N r := by
  funext r
  unfold sourceHighWindowPath sourceHighRootWindowPath
    sourceLowToHighSuccessorWindowPath sourceHighToHighSuccessorWindowPath
  exact sourceHighPrefix_eq_projectedRenewal Λ B (N + r)

/-! ## Three-component Gram algebra -/

/-- Cross energy is additive over subtraction in its first argument. -/
theorem windowPathCrossEnergy_sub_left
    (H : ℕ) (a b c : ℕ → ℤ) :
    windowPathCrossEnergy H (fun r => a r - b r) c =
      windowPathCrossEnergy H a c - windowPathCrossEnergy H b c := by
  unfold windowPathCrossEnergy
  calc
    (∑ r ∈ Finset.range H, (a r - b r) * c r) =
        ∑ r ∈ Finset.range H, (a r * c r - b r * c r) := by
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = (∑ r ∈ Finset.range H, a r * c r) -
          ∑ r ∈ Finset.range H, b r * c r := by
      rw [Finset.sum_sub_distrib]

/-- Cross energy is additive over subtraction in its second argument. -/
theorem windowPathCrossEnergy_sub_right
    (H : ℕ) (a b c : ℕ → ℤ) :
    windowPathCrossEnergy H a (fun r => b r - c r) =
      windowPathCrossEnergy H a b - windowPathCrossEnergy H a c := by
  unfold windowPathCrossEnergy
  calc
    (∑ r ∈ Finset.range H, a r * (b r - c r)) =
        ∑ r ∈ Finset.range H, (a r * b r - a r * c r) := by
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = (∑ r ∈ Finset.range H, a r * b r) -
          ∑ r ∈ Finset.range H, a r * c r := by
      rw [Finset.sum_sub_distrib]

/-- Full raw Gram expansion of a three-component difference. -/
theorem windowPathEnergy_sub_sub
    (H : ℕ) (a b c : ℕ → ℤ) :
    windowPathEnergy H (fun r => a r - b r - c r) =
      windowPathEnergy H a + windowPathEnergy H b + windowPathEnergy H c -
        2 * windowPathCrossEnergy H a b -
        2 * windowPathCrossEnergy H a c +
        2 * windowPathCrossEnergy H b c := by
  unfold windowPathEnergy
  simp only [windowPathCrossEnergy_sub_left,
    windowPathCrossEnergy_sub_right]
  rw [windowPathCrossEnergy_comm H b a,
    windowPathCrossEnergy_comm H c a,
    windowPathCrossEnergy_comm H c b]
  ring

/-- Full centered Gram expansion of a three-component difference. -/
theorem centeredWindowEnergy_sub_sub
    (H : ℕ) (a b c : ℕ → ℤ) :
    centeredWindowEnergy H (fun r => a r - b r - c r) =
      centeredWindowEnergy H a + centeredWindowEnergy H b +
        centeredWindowEnergy H c -
        2 * centeredWindowCrossEnergy H a b -
        2 * centeredWindowCrossEnergy H a c +
        2 * centeredWindowCrossEnergy H b c := by
  have hpath :
      centeredWindowPath H (fun r => a r - b r - c r) = fun r =>
        centeredWindowPath H a r - centeredWindowPath H b r -
          centeredWindowPath H c r := by
    funext r
    unfold centeredWindowPath
    ring
  simpa [centeredWindowEnergy, centeredWindowCrossEnergy, hpath] using
    windowPathEnergy_sub_sub H
      (centeredWindowPath H a)
      (centeredWindowPath H b)
      (centeredWindowPath H c)

/-- Full raw projected-renewal Gram ledger. The low-to-high and high-to-high
cross term is retained with its positive sign. -/
theorem sourceHighWindowEnergy_eq_projectedRenewalGram
    (Λ : ℝ) (B N H : ℕ) :
    windowPathEnergy H (sourceHighWindowPath Λ B N) =
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
          (sourceHighToHighSuccessorWindowPath Λ B N) := by
  rw [sourceHighWindowPath_eq_projectedRenewal]
  exact windowPathEnergy_sub_sub H
    (sourceHighRootWindowPath Λ B N)
    (sourceLowToHighSuccessorWindowPath Λ B N)
    (sourceHighToHighSuccessorWindowPath Λ B N)

/-- Full centered projected-renewal Gram ledger after removal of each component's
coherent endpoint mode. -/
theorem sourceHighWindowCenteredEnergy_eq_projectedRenewalGram
    (Λ : ℝ) (B N H : ℕ) :
    centeredWindowEnergy H (sourceHighWindowPath Λ B N) =
      centeredWindowEnergy H (sourceHighRootWindowPath Λ B N) +
        centeredWindowEnergy H
          (sourceLowToHighSuccessorWindowPath Λ B N) +
        centeredWindowEnergy H
          (sourceHighToHighSuccessorWindowPath Λ B N) -
        2 * centeredWindowCrossEnergy H
          (sourceHighRootWindowPath Λ B N)
          (sourceLowToHighSuccessorWindowPath Λ B N) -
        2 * centeredWindowCrossEnergy H
          (sourceHighRootWindowPath Λ B N)
          (sourceHighToHighSuccessorWindowPath Λ B N) +
        2 * centeredWindowCrossEnergy H
          (sourceLowToHighSuccessorWindowPath Λ B N)
          (sourceHighToHighSuccessorWindowPath Λ B N) := by
  rw [sourceHighWindowPath_eq_projectedRenewal]
  exact centeredWindowEnergy_sub_sub H
    (sourceHighRootWindowPath Λ B N)
    (sourceLowToHighSuccessorWindowPath Λ B N)
    (sourceHighToHighSuccessorWindowPath Λ B N)

end CanonicalGapAncestryProjectedRenewal

end RHLean.Proof
