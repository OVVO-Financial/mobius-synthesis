import Mathlib
import RHLean.Analysis.DyadicTransportCompression

/-!
# Dyadically compressed transport packet Gram

The existing dyadic transport theorem proves pointwise that an odd parent
channel `(c,q)` plus its doubled child `(2c,q)` is exactly the short boundary
packet left after cancellation of their common suffix.

This module lifts that coordinate identity to the internal block-time Gram.
It also allows an arbitrary unmatched coordinate to remain explicit and proves
the exact four-term Gram expansion:

* compressed paired Gram;
* unmatched Gram;
* both signed cross interactions.

No absolute-value estimate, orthogonality, or asymptotic cancellation is used.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace RHLean.Proof

/-- Raw paired transport coordinate before dyadic compression. -/
def dyadicRawPairCoordinate
    {ι : Type*} (c q : ι → ℕ) (N t : ℕ) (i : ι) : ℂ :=
  finiteTransportContribution N (c i) (q i) t +
    finiteTransportContribution N (dyadicChildCofactor (c i)) (q i) t

/-- Compressed boundary-packet coordinate. -/
def dyadicCompressedPairCoordinate
    {ι : Type*} (c q : ι → ℕ) (N t : ℕ) (i : ι) : ℂ :=
  dyadicBoundaryContribution N (c i) (q i) t

/-- Pointwise coordinate compression for odd parent cofactors and odd upper
primes. -/
theorem dyadicRawPairCoordinate_eq_compressed
    {ι : Type*} (c q : ι → ℕ) (N t : ℕ) (i : ι)
    (hc : Odd (c i)) (hq : Odd (q i)) :
    dyadicRawPairCoordinate c q N t i =
      dyadicCompressedPairCoordinate c q N t i := by
  exact finiteTransportContribution_add_dyadicChild
    N (c i) (q i) t hc hq

/-- Internal block-time Gram of the uncompressed paired coordinates. -/
def dyadicRawPairBlockGram
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (N s t : ℕ) : ℂ :=
  ∑ i ∈ U,
    conj (dyadicRawPairCoordinate c q N s i) *
      dyadicRawPairCoordinate c q N t i

/-- Internal block-time Gram of the compressed boundary packets. -/
def dyadicCompressedPairBlockGram
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (N s t : ℕ) : ℂ :=
  ∑ i ∈ U,
    conj (dyadicCompressedPairCoordinate c q N s i) *
      dyadicCompressedPairCoordinate c q N t i

/-- Dyadic compression preserves the complete internal paired Gram exactly. -/
theorem dyadicRawPairBlockGram_eq_compressed
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (N s t : ℕ)
    (hc : ∀ i ∈ U, Odd (c i))
    (hq : ∀ i ∈ U, Odd (q i)) :
    dyadicRawPairBlockGram U c q N s t =
      dyadicCompressedPairBlockGram U c q N s t := by
  classical
  unfold dyadicRawPairBlockGram dyadicCompressedPairBlockGram
  apply Finset.sum_congr rfl
  intro i hi
  rw [dyadicRawPairCoordinate_eq_compressed c q N s i (hc i hi) (hq i hi),
    dyadicRawPairCoordinate_eq_compressed c q N t i (hc i hi) (hq i hi)]

/-- Full coordinate retaining an arbitrary unmatched or boundary contribution. -/
def dyadicFullCoordinate
    {ι : Type*} (c q : ι → ℕ) (unmatched : ι → ℕ → ℂ)
    (N t : ℕ) (i : ι) : ℂ :=
  dyadicRawPairCoordinate c q N t i + unmatched i t

/-- The same full coordinate after exact dyadic compression. -/
def dyadicCompressedFullCoordinate
    {ι : Type*} (c q : ι → ℕ) (unmatched : ι → ℕ → ℂ)
    (N t : ℕ) (i : ι) : ℂ :=
  dyadicCompressedPairCoordinate c q N t i + unmatched i t

/-- Pointwise full-coordinate recombination preserves every unmatched term. -/
theorem dyadicFullCoordinate_eq_compressed
    {ι : Type*} (c q : ι → ℕ) (unmatched : ι → ℕ → ℂ)
    (N t : ℕ) (i : ι)
    (hc : Odd (c i)) (hq : Odd (q i)) :
    dyadicFullCoordinate c q unmatched N t i =
      dyadicCompressedFullCoordinate c q unmatched N t i := by
  rw [dyadicFullCoordinate, dyadicCompressedFullCoordinate,
    dyadicRawPairCoordinate_eq_compressed c q N t i hc hq]

/-- Gram contribution of the unmatched coordinates. -/
def dyadicUnmatchedBlockGram
    {ι : Type*} (U : Finset ι) (unmatched : ι → ℕ → ℂ)
    (s t : ℕ) : ℂ :=
  ∑ i ∈ U, conj (unmatched i s) * unmatched i t

/-- Cross interaction with compressed packets in the first coordinate. -/
def dyadicCompressedUnmatchedCrossGram
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (unmatched : ι → ℕ → ℂ) (N s t : ℕ) : ℂ :=
  ∑ i ∈ U,
    conj (dyadicCompressedPairCoordinate c q N s i) * unmatched i t

/-- Cross interaction with unmatched coordinates in the first coordinate. -/
def dyadicUnmatchedCompressedCrossGram
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (unmatched : ι → ℕ → ℂ) (N s t : ℕ) : ℂ :=
  ∑ i ∈ U,
    conj (unmatched i s) * dyadicCompressedPairCoordinate c q N t i

/-- Internal Gram of the complete paired-plus-unmatched coordinate system. -/
def dyadicFullBlockGram
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (unmatched : ι → ℕ → ℂ) (N s t : ℕ) : ℂ :=
  ∑ i ∈ U,
    conj (dyadicFullCoordinate c q unmatched N s i) *
      dyadicFullCoordinate c q unmatched N t i

/-- Exact compressed-packet Gram expansion. No cross interaction is discarded. -/
theorem dyadicFullBlockGram_eq_compressed_add_unmatched_add_cross
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (unmatched : ι → ℕ → ℂ) (N s t : ℕ)
    (hc : ∀ i ∈ U, Odd (c i))
    (hq : ∀ i ∈ U, Odd (q i)) :
    dyadicFullBlockGram U c q unmatched N s t =
      dyadicCompressedPairBlockGram U c q N s t +
        dyadicUnmatchedBlockGram U unmatched s t +
        dyadicCompressedUnmatchedCrossGram U c q unmatched N s t +
        dyadicUnmatchedCompressedCrossGram U c q unmatched N s t := by
  classical
  unfold dyadicFullBlockGram dyadicCompressedPairBlockGram
    dyadicUnmatchedBlockGram dyadicCompressedUnmatchedCrossGram
    dyadicUnmatchedCompressedCrossGram
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dyadicFullCoordinate_eq_compressed c q unmatched N s i
      (hc i hi) (hq i hi),
    dyadicFullCoordinate_eq_compressed c q unmatched N t i
      (hc i hi) (hq i hi)]
  simp only [dyadicCompressedFullCoordinate, map_add]
  ring

/-- Finite-window coherent energy of the complete coordinate system. -/
def dyadicFullWindowGramEnergy
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (unmatched : ι → ℕ → ℂ) (N A H : ℕ) : ℂ :=
  ∑ s ∈ Finset.range H,
    ∑ t ∈ Finset.range H,
      dyadicFullBlockGram U c q unmatched N (A + s) (A + t)

/-- The exact four-term decomposition survives summation over every block pair
in a finite window. -/
theorem dyadicFullWindowGramEnergy_eq_compressed_decomposition
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (unmatched : ι → ℕ → ℂ) (N A H : ℕ)
    (hc : ∀ i ∈ U, Odd (c i))
    (hq : ∀ i ∈ U, Odd (q i)) :
    dyadicFullWindowGramEnergy U c q unmatched N A H =
      ∑ s ∈ Finset.range H,
        ∑ t ∈ Finset.range H,
          (dyadicCompressedPairBlockGram U c q N (A + s) (A + t) +
            dyadicUnmatchedBlockGram U unmatched (A + s) (A + t) +
            dyadicCompressedUnmatchedCrossGram U c q unmatched N (A + s) (A + t) +
            dyadicUnmatchedCompressedCrossGram U c q unmatched N (A + s) (A + t)) := by
  unfold dyadicFullWindowGramEnergy
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  exact dyadicFullBlockGram_eq_compressed_add_unmatched_add_cross
    U c q unmatched N (A + s) (A + t) hc hq

/-- Finite-window coherent energy of the compressed paired packet system. -/
def dyadicCompressedWindowGramEnergy
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ)
    (N A H : ℕ) : ℂ :=
  ∑ s ∈ Finset.range H,
    ∑ t ∈ Finset.range H,
      dyadicCompressedPairBlockGram U c q N (A + s) (A + t)

/-- The exact worst-case vanishing condition suggested by the packet experiments.
After normalization by `H * A^2`, the compressed packet Gram energy tends to
zero uniformly over every translated window contained in the finite horizon.

This is written in epsilon form so the worst-case quantifiers are explicit:
for every positive `ε`, all sufficiently large block scales `A` and every
admissible `N,H` satisfy the normalized bound by `ε`. -/
def DyadicCompressedWorstCaseNormalizedEnergyTendsToZero
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A₀ : ℕ,
      ∀ N A H : ℕ,
        A₀ ≤ A →
        1 ≤ H →
        H ≤ A →
        A + H ≤ N + 1 →
        ‖dyadicCompressedWindowGramEnergy U c q N A H‖ ≤
          ε * (H : ℝ) * (A : ℝ) ^ 2

end RHLean.Proof
