import Mathlib
import RHLean.Arithmetic.FullPrimeFactorizationState
import RHLean.Analysis.CanonicalLowOccupancy
import RHLean.Proof.DeathShellCofactorParity

/-!
# Phase 2 bridge: canonical transport as a certified full-factorization edge

Phase 1 introduced `FullFactorizationState` and `FullPrimeTransportEdge`, which
carry the complete prime factorization with multiplicity.  This module connects
the repository's existing canonical largest-prime transport
`m = canonicalCofactor m * canonicalLargestPrimeFactor m` to those certified
objects, so the death-shell / cofactor parity is read from full factorization
states rather than from the two displayed factors `c` and `q`.

It is additive: no existing proved theorem is modified.  Downstream modules can
migrate onto `canonicalTransportEdge` incrementally.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- The canonical largest-prime transport `m = c · P⁺(m)` of `m > 1`, realized as
a certified `FullPrimeTransportEdge`.  The parent and child carry their complete
factorization states, and the terminal prime is `P⁺(m)`. -/
def canonicalTransportEdge (m : ℕ) (hm : 1 < m) : FullPrimeTransportEdge where
  parent := canonicalCofactor m
  child := m
  terminal := canonicalLargestPrimeFactor m
  terminal_prime := canonicalLargestPrimeFactor_prime hm
  parentState := FullFactorizationState.canonical (canonicalCofactor m)
  childState := FullFactorizationState.canonical m
  parentState_value := rfl
  childState_value := rfl
  product_eq := canonicalCofactor_mul_largestPrimeFactor hm
  factorization_update := by
    have hprod := canonicalCofactor_mul_largestPrimeFactor hm
    have hq0 : canonicalLargestPrimeFactor m ≠ 0 :=
      (canonicalLargestPrimeFactor_prime hm).ne_zero
    have hc0 : canonicalCofactor m ≠ 0 := by
      intro h; rw [h, zero_mul] at hprod; omega
    simp only [FullFactorizationState.canonical_factorization]
    conv_lhs => rw [← hprod]
    rw [Nat.factorization_mul hc0 hq0,
      (canonicalLargestPrimeFactor_prime hm).factorization]

@[simp] theorem canonicalTransportEdge_parent (m : ℕ) (hm : 1 < m) :
    (canonicalTransportEdge m hm).parent = canonicalCofactor m := rfl

@[simp] theorem canonicalTransportEdge_child (m : ℕ) (hm : 1 < m) :
    (canonicalTransportEdge m hm).child = m := rfl

@[simp] theorem canonicalTransportEdge_terminal (m : ℕ) (hm : 1 < m) :
    (canonicalTransportEdge m hm).terminal = canonicalLargestPrimeFactor m := rfl

/-- The death-shell cofactor `ω` is the certified `omega` of the canonical
cofactor's full-factorization state — not a count of displayed factors. -/
theorem deathShellCofactorOmega_eq_state_omega (m : ℕ) :
    deathShellCofactorOmega m
      = (FullFactorizationState.canonical (canonicalCofactor m)).omega := rfl

/-- Fresh canonical transport flips the Möbius sign, read through the certified
edge: `μ m = -μ(canonicalCofactor m)` when `P⁺(m)` does not divide the cofactor.
This retires the raw two-factor parity read. -/
theorem canonicalTransport_moebius_child (m : ℕ) (hm : 1 < m)
    (hfresh : ¬ canonicalLargestPrimeFactor m ∣ canonicalCofactor m) :
    μ m = - μ (canonicalCofactor m) :=
  (canonicalTransportEdge m hm).moebius_child_eq_neg_parent hfresh

/-- A canonical collision (`P⁺(m) ∣ cofactor`, i.e. `P⁺(m)² ∣ m`) gives Möbius
value zero, read through the certified edge. -/
theorem canonicalTransport_moebius_collision (m : ℕ) (hm : 1 < m)
    (hcollision : canonicalLargestPrimeFactor m ∣ canonicalCofactor m) :
    μ m = 0 :=
  (canonicalTransportEdge m hm).moebius_child_eq_zero_of_collision hcollision

end RHLean.Proof
