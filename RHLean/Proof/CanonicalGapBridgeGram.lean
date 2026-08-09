import Mathlib
import RHLean.Proof.CanonicalGapPrefixGram
import RHLean.Proof.CanonicalExtremeHeight

open scoped BigOperators

namespace RHLean.Proof

namespace CanonicalGapBridgeGram

open CanonicalGapPrefixGram

/-!
# Zero-mode-removed prefix Gram identities

For a length-`H` increment sequence `a`, its endpoint total is the final prefix.
The integer-scaled bridge

`H * prefix(r) - (r+1) * endpoint`

is the prefix obtained after removing the constant increment mode, without introducing
fractions. This is the exact object used by the canonical-gap scanner.
-/

/-- The total increment over a length-`H` window. -/
def endpointPrefix (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  prefixSum H a (H - 1)

/-- Integer-scaled prefix bridge after removing the constant increment mode. -/
def bridgePrefix (H : ℕ) (a : ℕ → ℤ) (r : ℕ) : ℤ :=
  (H : ℤ) * prefixSum H a r -
    ((r + 1 : ℕ) : ℤ) * endpointPrefix H a

/-- Bilinear Gram form of the zero-mode-removed prefix bridges. -/
def bridgeCrossEnergy (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  ∑ r ∈ Finset.range H, bridgePrefix H a r * bridgePrefix H b r

/-- Quadratic bridge energy. -/
def bridgeEnergy (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  bridgeCrossEnergy H a a

/-- Endpoint totals are additive. -/
theorem endpointPrefix_add (H : ℕ) (a b : ℕ → ℤ) :
    endpointPrefix H (fun i => a i + b i) =
      endpointPrefix H a + endpointPrefix H b := by
  unfold endpointPrefix
  exact prefixSum_add H a b (H - 1)

/-- Zero-mode-removed bridges are additive. -/
theorem bridgePrefix_add (H : ℕ) (a b : ℕ → ℤ) (r : ℕ) :
    bridgePrefix H (fun i => a i + b i) r =
      bridgePrefix H a r + bridgePrefix H b r := by
  unfold bridgePrefix
  rw [prefixSum_add, endpointPrefix_add]
  ring

/-- The bridge vanishes at the right endpoint of a nonempty window. -/
@[simp] theorem bridgePrefix_last {H : ℕ} (hH : 0 < H) (a : ℕ → ℤ) :
    bridgePrefix H a (H - 1) = 0 := by
  unfold bridgePrefix endpointPrefix
  have hsucc : H - 1 + 1 = H := by omega
  rw [hsucc]
  ring

/-- The bridge Gram form is additive in its first argument. -/
theorem bridgeCrossEnergy_add_left
    (H : ℕ) (a b c : ℕ → ℤ) :
    bridgeCrossEnergy H (fun i => a i + b i) c =
      bridgeCrossEnergy H a c + bridgeCrossEnergy H b c := by
  unfold bridgeCrossEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [bridgePrefix_add]
  ring

/-- The bridge Gram form is additive in its second argument. -/
theorem bridgeCrossEnergy_add_right
    (H : ℕ) (a b c : ℕ → ℤ) :
    bridgeCrossEnergy H a (fun i => b i + c i) =
      bridgeCrossEnergy H a b + bridgeCrossEnergy H a c := by
  unfold bridgeCrossEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [bridgePrefix_add]
  ring

/-- The bridge Gram form is symmetric. -/
theorem bridgeCrossEnergy_comm (H : ℕ) (a b : ℕ → ℤ) :
    bridgeCrossEnergy H a b = bridgeCrossEnergy H b a := by
  unfold bridgeCrossEnergy
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- Exact balanced/extreme energy ledger after removing the constant increment mode. -/
theorem bridgeEnergy_add (H : ℕ) (a b : ℕ → ℤ) :
    bridgeEnergy H (fun i => a i + b i) =
      bridgeEnergy H a + 2 * bridgeCrossEnergy H a b + bridgeEnergy H b := by
  unfold bridgeEnergy
  rw [bridgeCrossEnergy_add_left]
  simp_rw [bridgeCrossEnergy_add_right]
  rw [bridgeCrossEnergy_comm H b a]
  ring

/-- Arithmetic instantiation for the balanced and extreme canonical high-band
increments. -/
theorem balanced_extreme_bridge_energy_ledger
    (H N K : ℕ) :
    bridgeEnergy H
        (fun r =>
          BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K +
          BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) =
      bridgeEnergy H
          (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K) +
      2 * bridgeCrossEnergy H
          (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K)
          (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) +
      bridgeEnergy H
          (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) := by
  exact bridgeEnergy_add H
    (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K)
    (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K)

end CanonicalGapBridgeGram

end RHLean.Proof
