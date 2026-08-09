import Mathlib
import RHLean.Proof.CanonicalGapAncestryProjectedRenewal

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryPrimePackets

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryHighRealization
open CanonicalGapAncestryProjectedRenewal

/-!
# Dyadic scales and packet projectors for canonical ancestry

This module defines exact finite `q` and `(p,q)` packet projectors and proves
their finite recombination and triangular support. No analytic estimate is asserted.
-/

/-! ## Exact dyadic scale coordinates -/

/-- Base-two dyadic scale of the distinguished source prime. -/
def sourcePrimeDyadicScale {B : ℕ} (s : SourceIndex B) : ℕ :=
  Nat.log 2 (sourcePrime s)

/-- Largest prime stripped from the core on a canonical parent edge.  The
harmless repository convention gives value `1` on cores `0` and `1`. -/
def sourceStrippedPrime {B : ℕ} (s : SourceIndex B) : ℕ :=
  canonicalLargestPrimeFactor (sourceCore s)

/-- Base-two dyadic scale of the stripped core prime. -/
def sourceStrippedPrimeDyadicScale {B : ℕ} (s : SourceIndex B) : ℕ :=
  Nat.log 2 (sourceStrippedPrime s)

/-- The largest prime factor of a nontrivial integer is at most that integer. -/
theorem canonicalLargestPrimeFactor_le_self
    {c : ℕ} (hc : 1 < c) :
    canonicalLargestPrimeFactor c ≤ c := by
  have hprod := canonicalCofactor_mul_largestPrimeFactor hc
  have hdvd : canonicalLargestPrimeFactor c ∣ c := by
    refine ⟨canonicalCofactor c, ?_⟩
    simpa [Nat.mul_comm] using hprod.symm
  exact Nat.le_of_dvd (by omega) hdvd

/-- Every distinguished-prime scale fits in the finite source cutoff. -/
theorem sourcePrimeDyadicScale_lt_bound
    {B : ℕ} (s : SourceIndex B) :
    sourcePrimeDyadicScale s < B + 1 := by
  exact lt_of_le_of_lt
    (Nat.log_le_self 2 (sourcePrime s)) s.1.2

/-- Every stripped-prime scale also fits in the finite source cutoff. -/
theorem sourceStrippedPrimeDyadicScale_lt_bound
    {B : ℕ} (s : SourceIndex B) :
    sourceStrippedPrimeDyadicScale s < B + 1 := by
  by_cases hc : 1 < sourceCore s
  · have hp_le : sourceStrippedPrime s ≤ sourceCore s := by
      simpa [sourceStrippedPrime] using
        (canonicalLargestPrimeFactor_le_self hc)
    exact lt_of_le_of_lt
      ((Nat.log_le_self 2 (sourceStrippedPrime s)).trans hp_le) s.2.2
  · simp [sourceStrippedPrimeDyadicScale, sourceStrippedPrime,
      canonicalLargestPrimeFactor, hc]

/-- On a smooth child, the stripped core prime is strictly below the
unchanged distinguished prime. -/
theorem sourceStrippedPrime_lt_sourcePrime_of_smooth
    {B : ℕ} {s : SourceIndex B} (hs : SmoothOriented s) :
    sourceStrippedPrime s < sourcePrime s := by
  rcases hs.1 with ⟨hq, _hcpos, _hsq, _hcop, hdom⟩
  have hcgt : 1 < sourceCore s := lt_trans hq.one_lt hs.2
  have hpPrime : (sourceStrippedPrime s).Prime := by
    simpa [sourceStrippedPrime] using
      (canonicalLargestPrimeFactor_prime hcgt)
  have hpDvd : sourceStrippedPrime s ∣ sourceCore s := by
    have hprod := canonicalCofactor_mul_largestPrimeFactor hcgt
    refine ⟨canonicalCofactor (sourceCore s), ?_⟩
    simpa [sourceStrippedPrime, Nat.mul_comm] using hprod.symm
  exact hdom (sourceStrippedPrime s) hpPrime hpDvd

/-- Consequently the stripped-prime scale is no larger than the
`q`-scale on every smooth child. -/
theorem sourceStrippedPrimeDyadicScale_le_sourcePrimeDyadicScale_of_smooth
    {B : ℕ} {s : SourceIndex B} (hs : SmoothOriented s) :
    sourceStrippedPrimeDyadicScale s ≤ sourcePrimeDyadicScale s := by
  unfold sourceStrippedPrimeDyadicScale sourcePrimeDyadicScale
  exact Nat.log_mono_right
    (Nat.le_of_lt (sourceStrippedPrime_lt_sourcePrime_of_smooth hs))

/-! ## Generic finite packet projectors -/

/-- Restrict a source field to one distinguished-prime dyadic scale. -/
def sourceQPacketField (B k : ℕ) (f : SourceIndex B → ℤ) :
    SourceIndex B → ℤ := fun s =>
  if sourcePrimeDyadicScale s = k then f s else 0

/-- Restrict a source field to one stripped-prime and distinguished-prime
scale pair `(j,k)`. -/
def sourceQPPacketField (B j k : ℕ) (f : SourceIndex B → ℤ) :
    SourceIndex B → ℤ := fun s =>
  if sourcePrimeDyadicScale s = k ∧
      sourceStrippedPrimeDyadicScale s = j then f s else 0

/-- Exact finite recombination of all distinguished-prime packets. -/
theorem sourceField_eq_qPacket_sum
    (B : ℕ) (f : SourceIndex B → ℤ) :
    f = ∑ k ∈ Finset.range (B + 1), sourceQPacketField B k f := by
  classical
  funext s
  simp only [Finset.sum_apply]
  have hk : sourcePrimeDyadicScale s ∈ Finset.range (B + 1) :=
    Finset.mem_range.mpr (sourcePrimeDyadicScale_lt_bound s)
  rw [Finset.sum_eq_single (sourcePrimeDyadicScale s)]
  · simp [sourceQPacketField]
  · intro k _hk hne
    have hne' : sourcePrimeDyadicScale s ≠ k := Ne.symm hne
    simp [sourceQPacketField, hne']
  · intro hnot
    exact (hnot hk).elim

/-- Exact finite recombination of all two-parameter prime packets. -/
theorem sourceField_eq_qpPacket_sum
    (B : ℕ) (f : SourceIndex B → ℤ) :
    f = ∑ k ∈ Finset.range (B + 1),
      ∑ j ∈ Finset.range (B + 1), sourceQPPacketField B j k f := by
  classical
  funext s
  simp only [Finset.sum_apply]
  have hk : sourcePrimeDyadicScale s ∈ Finset.range (B + 1) :=
    Finset.mem_range.mpr (sourcePrimeDyadicScale_lt_bound s)
  have hj : sourceStrippedPrimeDyadicScale s ∈ Finset.range (B + 1) :=
    Finset.mem_range.mpr (sourceStrippedPrimeDyadicScale_lt_bound s)
  rw [Finset.sum_eq_single (sourcePrimeDyadicScale s)]
  · rw [Finset.sum_eq_single (sourceStrippedPrimeDyadicScale s)]
    · simp [sourceQPPacketField]
    · intro j _hj hne
      have hne' : sourceStrippedPrimeDyadicScale s ≠ j := Ne.symm hne
      simp [sourceQPPacketField, hne']
    · intro hnot
      exact (hnot hj).elim
  · intro k _hk hne
    apply Finset.sum_eq_zero
    intro j _hj
    have hne' : sourcePrimeDyadicScale s ≠ k := Ne.symm hne
    simp [sourceQPPacketField, hne']
  · intro hnot
    exact (hnot hk).elim

/-- A field supported on smooth children has no packet strictly above the
triangular region `j ≤ k`. -/
theorem sourceQPPacketField_eq_zero_of_k_lt_j
    {B j k : ℕ} (f : SourceIndex B → ℤ)
    (hvanish : ∀ s, ¬ SmoothOriented s → f s = 0)
    (hjk : k < j) :
    sourceQPPacketField B j k f = 0 := by
  classical
  funext s
  by_cases hs : SmoothOriented s
  · have hscale :=
      sourceStrippedPrimeDyadicScale_le_sourcePrimeDyadicScale_of_smooth hs
    have hnot : ¬(sourcePrimeDyadicScale s = k ∧
        sourceStrippedPrimeDyadicScale s = j) := by
      rintro ⟨hq, hp⟩
      omega
    simp [sourceQPPacketField, hnot]
  · simp [sourceQPPacketField, hvanish s hs]

end CanonicalGapAncestryPrimePackets

end RHLean.Proof
