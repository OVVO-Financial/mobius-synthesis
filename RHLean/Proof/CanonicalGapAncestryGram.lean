import RHLean.Proof.CanonicalGapAncestryEnergyBridge

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryGram

open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge
open CanonicalGapPrefixGram

/-!
# Actual-window Gram ledger for canonical ancestry generations

This module records the full finite Gram expansion of the actual successor-generation
paths supplied by `CanonicalGapAncestryEnergyBridge`. The paths retain inherited
backlog. Both the raw path energy and the mean-zero bridge energy retain every signed
cross-generation term. No analytic estimate is asserted.
-/

/-! ## Generic finite path Gram forms -/

/-- Bilinear Gram form of two integer-valued paths on offsets `r < H`. -/
def windowPathCrossEnergy (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  ∑ r ∈ Finset.range H, a r * b r

/-- Quadratic energy of one integer-valued path on offsets `r < H`. -/
def windowPathEnergy (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  windowPathCrossEnergy H a a

/-- Path cross energy is symmetric. -/
theorem windowPathCrossEnergy_comm (H : ℕ) (a b : ℕ → ℤ) :
    windowPathCrossEnergy H a b = windowPathCrossEnergy H b a := by
  unfold windowPathCrossEnergy
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- Path cross energy distributes over a finite sum in its first argument. -/
theorem windowPathCrossEnergy_sum_left
    {ι : Type*} (H : ℕ) (s : Finset ι)
    (f : ι → ℕ → ℤ) (b : ℕ → ℤ) :
    windowPathCrossEnergy H (fun r => ∑ i ∈ s, f i r) b =
      ∑ i ∈ s, windowPathCrossEnergy H (f i) b := by
  classical
  unfold windowPathCrossEnergy
  calc
    (∑ r ∈ Finset.range H, (∑ i ∈ s, f i r) * b r) =
        ∑ r ∈ Finset.range H, ∑ i ∈ s, f i r * b r := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [Finset.sum_mul]
    _ = ∑ i ∈ s, ∑ r ∈ Finset.range H, f i r * b r := by
          rw [Finset.sum_comm]

/-- Path cross energy distributes over a finite sum in its second argument. -/
theorem windowPathCrossEnergy_sum_right
    {ι : Type*} (H : ℕ) (s : Finset ι)
    (a : ℕ → ℤ) (f : ι → ℕ → ℤ) :
    windowPathCrossEnergy H a (fun r => ∑ i ∈ s, f i r) =
      ∑ i ∈ s, windowPathCrossEnergy H a (f i) := by
  classical
  unfold windowPathCrossEnergy
  calc
    (∑ r ∈ Finset.range H, a r * (∑ i ∈ s, f i r)) =
        ∑ r ∈ Finset.range H, ∑ i ∈ s, a r * f i r := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ r ∈ Finset.range H, a r * f i r := by
          rw [Finset.sum_comm]

/-- Full finite Gram expansion. Every diagonal and cross term is retained. -/
theorem windowPathEnergy_sum
    {ι : Type*} (H : ℕ) (s : Finset ι) (f : ι → ℕ → ℤ) :
    windowPathEnergy H (fun r => ∑ i ∈ s, f i r) =
      ∑ i ∈ s, ∑ j ∈ s, windowPathCrossEnergy H (f i) (f j) := by
  classical
  unfold windowPathEnergy
  rw [windowPathCrossEnergy_sum_left]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [windowPathCrossEnergy_sum_right]

/-- The generic path form specializes definitionally to the existing prefix Gram
form when the path is a finite prefix-sum path. -/
theorem windowPathCrossEnergy_prefixSum
    (H : ℕ) (a b : ℕ → ℤ) :
    windowPathCrossEnergy H (prefixSum H a) (prefixSum H b) =
      prefixCrossEnergy H a b := by
  rfl

/-- The corresponding quadratic specialization. -/
theorem windowPathEnergy_prefixSum (H : ℕ) (a : ℕ → ℤ) :
    windowPathEnergy H (prefixSum H a) = prefixEnergy H a := by
  rfl

/-! ## Mean-zero path bridge -/

/-- Integer-scaled mean-zero bridge of an actual path. Unlike centering only the
post-origin increments, this definition retains inherited backlog before removing
the coherent endpoint mode. -/
def centeredWindowPath (H : ℕ) (a : ℕ → ℤ) (r : ℕ) : ℤ :=
  (H : ℤ) * a r - ((r + 1 : ℕ) : ℤ) * a (H - 1)

/-- Centering commutes with finite path sums. -/
theorem centeredWindowPath_sum
    {ι : Type*} (H : ℕ) (s : Finset ι)
    (f : ι → ℕ → ℤ) (r : ℕ) :
    centeredWindowPath H (fun t => ∑ i ∈ s, f i t) r =
      ∑ i ∈ s, centeredWindowPath H (f i) r := by
  classical
  simp only [centeredWindowPath, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The centered path is pinned to zero at the right endpoint. -/
theorem centeredWindowPath_last_eq_zero
    {H : ℕ} (hH : 1 ≤ H) (a : ℕ → ℤ) :
    centeredWindowPath H a (H - 1) = 0 := by
  unfold centeredWindowPath
  have hlast : H - 1 + 1 = H := by omega
  rw [hlast]
  ring

/-- Bilinear Gram form after removal of each path's coherent endpoint mode. -/
def centeredWindowCrossEnergy (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  windowPathCrossEnergy H (centeredWindowPath H a) (centeredWindowPath H b)

/-- Quadratic centered-path energy. -/
def centeredWindowEnergy (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  centeredWindowCrossEnergy H a a

/-- The path bridge specializes definitionally to the increment bridge formalized
in `CanonicalGapPrefixGram`. -/
theorem centeredWindowPath_prefixSum_eq_bridgePrefix
    (H : ℕ) (a : ℕ → ℤ) (r : ℕ) :
    centeredWindowPath H (prefixSum H a) r = bridgePrefix H a r := by
  rfl

/-- Bilinear compatibility with the existing bridge Gram form. -/
theorem centeredWindowCrossEnergy_prefixSum
    (H : ℕ) (a b : ℕ → ℤ) :
    centeredWindowCrossEnergy H (prefixSum H a) (prefixSum H b) =
      bridgeCrossEnergy H a b := by
  rfl

/-- Quadratic compatibility with the existing bridge energy. -/
theorem centeredWindowEnergy_prefixSum (H : ℕ) (a : ℕ → ℤ) :
    centeredWindowEnergy H (prefixSum H a) = bridgeEnergy H a := by
  rfl

/-- Full finite centered Gram expansion. Every signed fluctuation cross term is
retained after the coherent endpoint modes are removed. -/
theorem centeredWindowEnergy_sum
    {ι : Type*} (H : ℕ) (s : Finset ι) (f : ι → ℕ → ℤ) :
    centeredWindowEnergy H (fun r => ∑ i ∈ s, f i r) =
      ∑ i ∈ s, ∑ j ∈ s, centeredWindowCrossEnergy H (f i) (f j) := by
  classical
  have hcenter :
      centeredWindowPath H (fun r => ∑ i ∈ s, f i r) =
        fun r => ∑ i ∈ s, centeredWindowPath H (f i) r := by
    funext r
    exact centeredWindowPath_sum H s f r
  unfold centeredWindowEnergy centeredWindowCrossEnergy
  rw [hcenter]
  exact windowPathEnergy_sum H s (fun i => centeredWindowPath H (f i))

/-! ## Canonical ancestry generation ledgers -/

/-- The actual signed path of generation `j` in a window beginning at `N`. -/
def signedGenerationWindowPath (B j N : ℕ) : ℕ → ℤ := fun r =>
  (-1 : ℤ) ^ j * generationWindowPrefix B j N r

/-- The actual full source-prefix path in a window beginning at `N`. -/
def sourceWindowPath (B N : ℕ) : ℕ → ℤ := fun r =>
  sourcePrefix B (N + r)

/-- Exact pathwise recombination of all signed successor generations, including
each generation's inherited backlog. -/
theorem sourceWindowPath_eq_signedGeneration_sum
    {B N : ℕ} (hN : 1 ≤ N) :
    sourceWindowPath B N =
      fun r => ∑ j ∈ Finset.range (B + 1), signedGenerationWindowPath B j N r := by
  funext r
  unfold sourceWindowPath signedGenerationWindowPath
  exact sourcePrefix_eq_generationWindow_sum hN

/-- Full raw ancestry Gram ledger on the actual source-prefix path. -/
theorem sourceWindowEnergy_eq_generationGram
    {B N H : ℕ} (hN : 1 ≤ N) :
    windowPathEnergy H (sourceWindowPath B N) =
      ∑ j ∈ Finset.range (B + 1),
        ∑ k ∈ Finset.range (B + 1),
          windowPathCrossEnergy H
            (signedGenerationWindowPath B j N)
            (signedGenerationWindowPath B k N) := by
  rw [sourceWindowPath_eq_signedGeneration_sum hN]
  exact windowPathEnergy_sum H (Finset.range (B + 1))
    (fun j => signedGenerationWindowPath B j N)

/-- Full centered ancestry Gram ledger after exact removal of the coherent endpoint
mode from the actual source path and every signed generation path. -/
theorem sourceWindowCenteredEnergy_eq_generationGram
    {B N H : ℕ} (hN : 1 ≤ N) :
    centeredWindowEnergy H (sourceWindowPath B N) =
      ∑ j ∈ Finset.range (B + 1),
        ∑ k ∈ Finset.range (B + 1),
          centeredWindowCrossEnergy H
            (signedGenerationWindowPath B j N)
            (signedGenerationWindowPath B k N) := by
  rw [sourceWindowPath_eq_signedGeneration_sum hN]
  exact centeredWindowEnergy_sum H (Finset.range (B + 1))
    (fun j => signedGenerationWindowPath B j N)

end CanonicalGapAncestryGram

end RHLean.Proof
