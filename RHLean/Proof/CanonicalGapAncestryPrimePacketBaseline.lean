import RHLean.Proof.CanonicalGapAncestryPrimePacketRenewal

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryPrimePackets

open CanonicalGapAncestryFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryHighRealization

/-!
# Partial-baseline algebra for canonical prime packets

This module keeps near-diagonal packets coupled to the root and adds and
subtracts a supplied fixed model only on scale-separated packets. It also proves
that the recombined expression is independent of the supplied model.
-/

/-! ## Generic partial-baseline algebra -/

section PartialBaseline

variable {M : Type*} [AddCommGroup M]

/-- Scale-separated packet sum `j + L ≤ k`. -/
def farPacketSum
    (scaleBound L k : ℕ) (packet : ℕ → ℕ → M) : M :=
  ∑ j ∈ Finset.range (scaleBound + 1),
    if j + L ≤ k then packet j k else 0

/-- Near-diagonal packet sum, retaining the complement of `j + L ≤ k`. -/
def nearPacketSum
    (scaleBound L k : ℕ) (packet : ℕ → ℕ → M) : M :=
  ∑ j ∈ Finset.range (scaleBound + 1),
    if j + L ≤ k then 0 else packet j k

/-- The complete packet fiber splits exactly into its near and far parts. -/
theorem packetSum_eq_near_add_far
    (scaleBound L k : ℕ) (packet : ℕ → ℕ → M) :
    (∑ j ∈ Finset.range (scaleBound + 1), packet j k) =
      nearPacketSum scaleBound L k packet +
        farPacketSum scaleBound L k packet := by
  classical
  unfold nearPacketSum farPacketSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hfar : j + L ≤ k <;> simp [hfar]

/-- Root minus near actual packets minus the modeled far packets. -/
def partialMainFiber
    (scaleBound L k : ℕ)
    (root : ℕ → M) (actual model : ℕ → ℕ → M) : M :=
  root k - nearPacketSum scaleBound L k actual -
    farPacketSum scaleBound L k model

/-- Total discrepancy between actual and modeled far packets. -/
def farPacketDiscrepancyFiber
    (scaleBound L k : ℕ)
    (actual model : ℕ → ℕ → M) : M :=
  farPacketSum scaleBound L k actual -
    farPacketSum scaleBound L k model

/-- Exact non-circular partial-baseline identity.  Near packets remain coupled
to the root, and the same fixed far model is added and subtracted. -/
theorem packetFiber_eq_partialMain_sub_farDiscrepancy
    (scaleBound L k : ℕ)
    (root : ℕ → M) (actual model : ℕ → ℕ → M) :
    root k - (∑ j ∈ Finset.range (scaleBound + 1), actual j k) =
      partialMainFiber scaleBound L k root actual model -
        farPacketDiscrepancyFiber scaleBound L k actual model := by
  rw [packetSum_eq_near_add_far]
  unfold partialMainFiber farPacketDiscrepancyFiber
  abel

/-- The recombined partial-baseline expression is independent of the supplied
model.  A baseline only redistributes the same exact fiber between its main
defect and far discrepancy. -/
theorem partialBaseline_combination_independent
    (scaleBound L k : ℕ)
    (root : ℕ → M) (actual model₁ model₂ : ℕ → ℕ → M) :
    partialMainFiber scaleBound L k root actual model₁ -
        farPacketDiscrepancyFiber scaleBound L k actual model₁ =
      partialMainFiber scaleBound L k root actual model₂ -
        farPacketDiscrepancyFiber scaleBound L k actual model₂ := by
  rw [← packetFiber_eq_partialMain_sub_farDiscrepancy
      scaleBound L k root actual model₁,
    ← packetFiber_eq_partialMain_sub_farDiscrepancy
      scaleBound L k root actual model₂]

end PartialBaseline

/-! ## Partial baseline on the concrete projected packet window -/

/-- A fixed real-valued model for packet `(j,k)` at window offset `r`.
The exact layer places no existential quantifier over this object. -/
abbrev PrimePacketWindowModel := ℕ → ℕ → ℕ → ℝ

/-- Real cast of one root packet window path. -/
def sourceHighRootQPacketRealWindowPath
    (Λ : ℝ) (B k N : ℕ) : ℕ → ℝ := fun r =>
  (sourceHighRootQPacketWindowPath Λ B k N r : ℝ)

/-- Real cast of one complete projected successor packet window path. -/
def sourceProjectedSuccessorPQPacketRealWindowPath
    (Λ : ℝ) (B j k N : ℕ) : ℕ → ℝ := fun r =>
  (sourceProjectedSuccessorPQPacketWindowPath Λ B j k N r : ℝ)

/-- Near-coupled coherent defect for one distinguished-prime fiber. -/
def projectedPrimePacketPartialMainWindowPath
    (model : PrimePacketWindowModel) (L : ℕ)
    (Λ : ℝ) (B k N : ℕ) : ℕ → ℝ := fun r =>
  partialMainFiber B L k
    (fun k' => sourceHighRootQPacketRealWindowPath Λ B k' N r)
    (fun j' k' =>
      sourceProjectedSuccessorPQPacketRealWindowPath Λ B j' k' N r)
    (fun j' k' => model j' k' r)

/-- Scale-separated actual-minus-model discrepancy for one `q`-fiber. -/
def projectedPrimePacketFarDiscrepancyWindowPath
    (model : PrimePacketWindowModel) (L : ℕ)
    (Λ : ℝ) (B k N : ℕ) : ℕ → ℝ := fun r =>
  farPacketDiscrepancyFiber B L k
    (fun j' k' =>
      sourceProjectedSuccessorPQPacketRealWindowPath Λ B j' k' N r)
    (fun j' k' => model j' k' r)

/-- Real-cast form of the exact fibered packet renewal. -/
theorem sourceHighWindowPath_real_eq_primePacketRenewal
    (Λ : ℝ) (B N r : ℕ) :
    (sourceHighWindowPath Λ B N r : ℝ) =
      ∑ k ∈ Finset.range (B + 1),
        (sourceHighRootQPacketRealWindowPath Λ B k N r -
          ∑ j ∈ Finset.range (B + 1),
            sourceProjectedSuccessorPQPacketRealWindowPath Λ B j k N r) := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (congrFun (sourceHighWindowPath_eq_primePacketRenewal Λ B N) r)
  simpa [sourceHighRootQPacketRealWindowPath,
    sourceProjectedSuccessorPQPacketRealWindowPath] using h

/-- Fully exact partial-baseline decomposition.  The model is fixed by the
caller; no estimate and no existence claim is included. -/
theorem sourceHighWindowPath_real_eq_partialBaseline
    (model : PrimePacketWindowModel) (L : ℕ)
    (Λ : ℝ) (B N : ℕ) :
    (fun r => (sourceHighWindowPath Λ B N r : ℝ)) = fun r =>
      ∑ k ∈ Finset.range (B + 1),
        (projectedPrimePacketPartialMainWindowPath model L Λ B k N r -
          projectedPrimePacketFarDiscrepancyWindowPath model L Λ B k N r) := by
  funext r
  rw [sourceHighWindowPath_real_eq_primePacketRenewal]
  apply Finset.sum_congr rfl
  intro k _hk
  exact packetFiber_eq_partialMain_sub_farDiscrepancy B L k
    (fun k' => sourceHighRootQPacketRealWindowPath Λ B k' N r)
    (fun j' k' =>
      sourceProjectedSuccessorPQPacketRealWindowPath Λ B j' k' N r)
    (fun j' k' => model j' k' r)

end CanonicalGapAncestryPrimePackets

end RHLean.Proof
