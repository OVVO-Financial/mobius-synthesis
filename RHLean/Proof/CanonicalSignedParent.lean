import Mathlib
import RHLean.Proof.FullFactorizationBridge

/-!
# Canonical signed-parent identity

For a squarefree `n > 1` the canonical largest-prime decomposition
`n = c · q`, `q = P⁺(n)`, has `q ∤ c` automatically (squarefreeness), so the
certified `canonicalTransportEdge` is always *fresh*. Reading everything through
the complete factorization states, this gives the canonical signed-parent
identity without compressing the parent depth:

```text
ω(n) = ω(c) + 1,      μ(n) = -μ(c),      c = canonicalCofactor n.
```

Parent `c` and child `n` are distinct full-factorization states throughout.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- For squarefree `n > 1`, the largest prime factor does not divide the
canonical cofactor: the canonical transport is always fresh. -/
theorem canonicalLargestPrimeFactor_not_dvd_cofactor
    {n : ℕ} (hsq : Squarefree n) (hn : 1 < n) :
    ¬ canonicalLargestPrimeFactor n ∣ canonicalCofactor n := by
  have hprod : canonicalCofactor n * canonicalLargestPrimeFactor n = n :=
    canonicalCofactor_mul_largestPrimeFactor hn
  have hprime : (canonicalLargestPrimeFactor n).Prime :=
    canonicalLargestPrimeFactor_prime hn
  have hcop : Nat.Coprime (canonicalCofactor n) (canonicalLargestPrimeFactor n) :=
    coprime_factors_of_squarefree hsq hprod
  exact hprime.coprime_iff_not_dvd.mp hcop.symm

/-- The canonical cofactor of a squarefree number is squarefree. -/
theorem squarefree_canonicalCofactor
    {n : ℕ} (hsq : Squarefree n) (hn : 1 < n) :
    Squarefree (canonicalCofactor n) :=
  hsq.squarefree_of_dvd ⟨_, (canonicalCofactor_mul_largestPrimeFactor hn).symm⟩

/-- **Canonical signed-parent Möbius identity.** For squarefree `n > 1`,
`μ n = -μ(canonicalCofactor n)`, read through the certified transport edge with
freshness discharged from squarefreeness. -/
theorem canonicalSignedParent_moebius
    {n : ℕ} (hsq : Squarefree n) (hn : 1 < n) :
    μ n = - μ (canonicalCofactor n) :=
  canonicalTransport_moebius_child n hn
    (canonicalLargestPrimeFactor_not_dvd_cofactor hsq hn)

/-- **Canonical parent depth increment.** The complete factorization depth of
`n` exceeds that of its canonical cofactor by exactly one. -/
theorem canonicalSignedParent_bigOmega_succ {n : ℕ} (hn : 1 < n) :
    (FullFactorizationState.canonical n).bigOmega
      = (FullFactorizationState.canonical (canonicalCofactor n)).bigOmega + 1 :=
  (canonicalTransportEdge n hn).bigOmega_child_eq_succ

/-- On squarefree `n > 1`, the distinct-prime depth also increments by one:
`ω(n) = ω(canonicalCofactor n) + 1`. -/
theorem canonicalSignedParent_omega_succ
    {n : ℕ} (hsq : Squarefree n) (hn : 1 < n) :
    (FullFactorizationState.canonical n).omega
      = (FullFactorizationState.canonical (canonicalCofactor n)).omega + 1 := by
  have hscf : Squarefree (canonicalCofactor n) := squarefree_canonicalCofactor hsq hn
  rw [← FullFactorizationState.bigOmega_eq_omega_of_squarefree
        (FullFactorizationState.canonical n) hsq,
      ← FullFactorizationState.bigOmega_eq_omega_of_squarefree
        (FullFactorizationState.canonical (canonicalCofactor n)) hscf]
  exact canonicalSignedParent_bigOmega_succ hn

end RHLean.Proof
