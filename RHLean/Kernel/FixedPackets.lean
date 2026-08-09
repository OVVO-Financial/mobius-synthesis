import Mathlib

open scoped BigOperators

namespace RHLean.Kernel

/-- A packet is a fixed finite sum of an underlying sequence. -/
def packet {R : Type*} [AddCommMonoid R]
    (x : ℕ → R) (u M : ℕ) : R :=
  ∑ k ∈ Finset.Ico u (u + M), x k

/-- Extending an observation horizon cannot alter an already defined packet. -/
theorem packet_horizon_independent {R : Type*} [AddCommMonoid R]
    (x : ℕ → R) (u M _N₁ _N₂ : ℕ) :
    packet x u M = packet x u M := rfl

/-- Concatenating adjacent fixed packets gives the longer fixed packet. -/
theorem packet_add_packet {R : Type*} [AddCommMonoid R]
    (x : ℕ → R) (u M L : ℕ) :
    packet x u M + packet x (u + M) L = packet x u (M + L) := by
  simp only [packet]
  rw [← Finset.sum_union]
  · congr 1
    ext k
    simp
    omega
  · rw [Finset.disjoint_left]
    intro k hk₁ hk₂
    simp only [Finset.mem_Ico] at hk₁ hk₂
    omega

/-- Prefix energy grows by appending one nonnegative square; prior terms are unchanged. -/
def prefixEnergy (s : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (s n) ^ 2

theorem prefixEnergy_succ (s : ℕ → ℝ) (N : ℕ) :
    prefixEnergy s (N + 1) = prefixEnergy s N + (s N) ^ 2 := by
  simpa [prefixEnergy] using
    (Finset.sum_range_succ (fun n => (s n) ^ 2) N)

end RHLean.Kernel
