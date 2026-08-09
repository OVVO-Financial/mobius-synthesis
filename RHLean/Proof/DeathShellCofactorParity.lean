import Mathlib
import RHLean.Proof.DeathShellDivisorFibers
import RHLean.Proof.NormalizedCofactorExpansion

/-!
# Finite cofactor-parity decomposition of death shells

The final square-prefix object remains the exact theorem-predicted subtraction

```text
squareBlockSmoothPrefix - squareBlockTransportPrefix = squarePrefixMertens.
```

The lifetime/death route is one sufficient route toward controlling that full
residual.  This module refines only the discrete death increment.  It does not
control the separate survivor discrepancy `birth - death`, and it does not turn
shell sparsity into cancellation by itself.

On the nonzero Möbius support of a positive-cutoff death shell, write

```text
m = c * q,
q = P⁺(m),
ω(c) = number of distinct prime factors of c.
```

Squarefreeness gives `q ∤ c`, hence

```text
μ(m) = μ(c) μ(q) = -μ(c) = (-1)^(ω(c)+1).
```

The shell increment is therefore the finite alternating sum of the populations
with each cofactor prime count.  The value `ω(c)=0` is retained: it is the
cofactor-one class, not an omitted exceptional case.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Number of distinct prime factors of the canonical cofactor. -/
def deathShellCofactorOmega (m : ℕ) : ℕ :=
  ArithmeticFunction.cardDistinctFactors (canonicalCofactor m)

/-- Nonzero-Möbius sources in a canonical death shell. -/
noncomputable def deathShellNonzeroSupport (Λ : ℝ) (t : ℕ) : Finset ℕ := by
  classical
  exact (deathHeightShellSet Λ t).filter fun m => μ m ≠ 0

/-- Prime-count values actually represented in a shell's nonzero support. -/
noncomputable def deathShellCofactorOmegaValues (Λ : ℝ) (t : ℕ) : Finset ℕ := by
  classical
  exact (deathShellNonzeroSupport Λ t).image deathShellCofactorOmega

/-- The shell sources whose canonical cofactor has exactly `k` distinct prime
factors. -/
noncomputable def deathShellCofactorOmegaFiber
    (Λ : ℝ) (t k : ℕ) : Finset ℕ := by
  classical
  exact (deathShellNonzeroSupport Λ t).filter fun m =>
    deathShellCofactorOmega m = k

/-- The finite cofactor-prime-count population `N_k(t)`. -/
def deathShellCofactorOmegaCount (Λ : ℝ) (t k : ℕ) : ℕ :=
  (deathShellCofactorOmegaFiber Λ t k).card

@[simp] theorem mem_deathShellNonzeroSupport
    {Λ : ℝ} {t m : ℕ} :
    m ∈ deathShellNonzeroSupport Λ t ↔
      m ∈ deathHeightShellSet Λ t ∧ μ m ≠ 0 := by
  simp [deathShellNonzeroSupport]

@[simp] theorem mem_deathShellCofactorOmegaFiber
    {Λ : ℝ} {t k m : ℕ} :
    m ∈ deathShellCofactorOmegaFiber Λ t k ↔
      m ∈ deathShellNonzeroSupport Λ t ∧ deathShellCofactorOmega m = k := by
  simp [deathShellCofactorOmegaFiber]

@[simp] theorem mem_deathShellCofactorOmegaValues
    {Λ : ℝ} {t k : ℕ} :
    k ∈ deathShellCofactorOmegaValues Λ t ↔
      ∃ m ∈ deathShellNonzeroSupport Λ t, deathShellCofactorOmega m = k := by
  simp [deathShellCofactorOmegaValues]

/-- Every nonzero-Möbius source in a positive-cutoff shell is nontrivial. -/
theorem one_lt_of_mem_deathShellNonzeroSupport
    {Λ : ℝ} (hΛ : 0 < Λ) {t m : ℕ}
    (hm : m ∈ deathShellNonzeroSupport Λ t) :
    1 < m := by
  have hmData := mem_deathShellNonzeroSupport.mp hm
  have hsq : Squarefree m :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmData.2
  have hm0 : m ≠ 0 := hsq.ne_zero
  have hheightPos := deathShellHeightNat_pos_of_mem hΛ hmData.1
  have hm1 : m ≠ 1 := by
    intro hmEq
    subst m
    norm_num [deathShellHeightNat, canonicalAbsoluteGap, canonicalPairLo,
      canonicalPairHi, canonicalCofactor, canonicalLargestPrimeFactor] at hheightPos
  omega

/-- On the shell's nonzero support, the Möbius sign is exactly the alternating
parity of the canonical cofactor's distinct-prime count. -/
theorem moebius_eq_negOnePow_succ_deathShellCofactorOmega
    {Λ : ℝ} (hΛ : 0 < Λ) {t m : ℕ}
    (hm : m ∈ deathShellNonzeroSupport Λ t) :
    μ m = (-1 : ℤ) ^ (deathShellCofactorOmega m + 1) := by
  have hmData := mem_deathShellNonzeroSupport.mp hm
  have hm1 : 1 < m := one_lt_of_mem_deathShellNonzeroSupport hΛ hm
  have hsq : Squarefree m :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmData.2
  have hprod :
      canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm1
  have hcofactorDvd : canonicalCofactor m ∣ m :=
    ⟨canonicalLargestPrimeFactor m, hprod.symm⟩
  have hsqCofactor : Squarefree (canonicalCofactor m) :=
    hsq.squarefree_of_dvd hcofactorDvd
  have hcop :
      Nat.Coprime (canonicalCofactor m) (canonicalLargestPrimeFactor m) :=
    coprime_factors_of_squarefree hsq hprod
  have hprime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hm1
  have homega :
      ArithmeticFunction.cardFactors (canonicalCofactor m) =
        ArithmeticFunction.cardDistinctFactors (canonicalCofactor m) := by
    exact
      ((ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
          hsqCofactor.ne_zero).2 hsqCofactor).symm
  calc
    μ m = μ (canonicalCofactor m * canonicalLargestPrimeFactor m) := by
      rw [hprod]
    _ = μ (canonicalCofactor m) * μ (canonicalLargestPrimeFactor m) :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    _ = (-1 : ℤ) ^ ArithmeticFunction.cardFactors (canonicalCofactor m) * (-1) := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsqCofactor,
        ArithmeticFunction.moebius_apply_prime hprime]
    _ = (-1 : ℤ) ^ (ArithmeticFunction.cardFactors (canonicalCofactor m) + 1) := by
      rw [pow_succ]
    _ = (-1 : ℤ) ^ (deathShellCofactorOmega m + 1) := by
      rw [homega]
      rfl

/-- Complex-valued form of the exact cofactor-parity sign law. -/
theorem canonicalMoebiusWeight_eq_deathShellCofactorParity
    {Λ : ℝ} (hΛ : 0 < Λ) {t m : ℕ}
    (hm : m ∈ deathShellNonzeroSupport Λ t) :
    canonicalMoebiusWeight m =
      (-1 : ℂ) ^ (deathShellCofactorOmega m + 1) := by
  simpa [canonicalMoebiusWeight] using
    congrArg (fun z : ℤ => (z : ℂ))
      (moebius_eq_negOnePow_succ_deathShellCofactorOmega hΛ hm)

/-- Removing zero Möbius weights does not change the shell mass. -/
theorem deathHeightShellMass_eq_nonzeroSupport_sum
    (Λ : ℝ) (t : ℕ) :
    deathHeightShellMass Λ t =
      ∑ m ∈ deathShellNonzeroSupport Λ t, canonicalMoebiusWeight m := by
  classical
  unfold deathHeightShellMass movingCanonicalCrossingMass canonicalMoebiusMass
    deathShellNonzeroSupport deathHeightShellSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hμ : μ m = 0
  · simp [hμ, canonicalMoebiusWeight]
  · simp [hμ]

/-- Pointwise finite parity form of the shell mass. -/
theorem deathHeightShellMass_eq_pointwiseCofactorParity
    {Λ : ℝ} (hΛ : 0 < Λ) (t : ℕ) :
    deathHeightShellMass Λ t =
      ∑ m ∈ deathShellNonzeroSupport Λ t,
        (-1 : ℂ) ^ (deathShellCofactorOmega m + 1) := by
  rw [deathHeightShellMass_eq_nonzeroSupport_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact canonicalMoebiusWeight_eq_deathShellCofactorParity hΛ hm

/-- The finite alternating cofactor-prime-count sum. -/
def deathShellCofactorParityMass (Λ : ℝ) (t : ℕ) : ℂ :=
  ∑ k ∈ deathShellCofactorOmegaValues Λ t,
    (deathShellCofactorOmegaCount Λ t k : ℂ) * (-1 : ℂ) ^ (k + 1)

/-- Regrouping the pointwise parity signs by their finite `ω(c)` fibers gives the
counted alternating sum. -/
theorem deathShellCofactorParityMass_eq_pointwise
    (Λ : ℝ) (t : ℕ) :
    deathShellCofactorParityMass Λ t =
      ∑ m ∈ deathShellNonzeroSupport Λ t,
        (-1 : ℂ) ^ (deathShellCofactorOmega m + 1) := by
  classical
  have hmaps :
      ∀ m ∈ deathShellNonzeroSupport Λ t,
        deathShellCofactorOmega m ∈ deathShellCofactorOmegaValues Λ t := by
    intro m hm
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  unfold deathShellCofactorParityMass deathShellCofactorOmegaCount
    deathShellCofactorOmegaFiber
  calc
    (∑ k ∈ deathShellCofactorOmegaValues Λ t,
        (((deathShellNonzeroSupport Λ t).filter fun m =>
            deathShellCofactorOmega m = k).card : ℂ) *
          (-1 : ℂ) ^ (k + 1)) =
      ∑ k ∈ deathShellCofactorOmegaValues Λ t,
        ∑ _m ∈ deathShellNonzeroSupport Λ t with
            deathShellCofactorOmega _m = k,
          (-1 : ℂ) ^ (k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp
    _ = ∑ m ∈ deathShellNonzeroSupport Λ t,
          (-1 : ℂ) ^ (deathShellCofactorOmega m + 1) := by
      simpa using
        (Finset.sum_fiberwise_of_maps_to'
          (s := deathShellNonzeroSupport Λ t)
          (t := deathShellCofactorOmegaValues Λ t)
          (g := deathShellCofactorOmega)
          hmaps
          (fun k : ℕ => (-1 : ℂ) ^ (k + 1)))

/-- Exact finite cofactor-`ω` decomposition of a canonical death-shell mass. -/
theorem deathHeightShellMass_eq_cofactorParityMass
    {Λ : ℝ} (hΛ : 0 < Λ) (t : ℕ) :
    deathHeightShellMass Λ t = deathShellCofactorParityMass Λ t := by
  rw [deathHeightShellMass_eq_pointwiseCofactorParity hΛ]
  exact (deathShellCofactorParityMass_eq_pointwise Λ t).symm

/-- Exact finite cofactor-`ω` decomposition of the actual discrete death
increment.  This is the shell-cancellation coordinate that later analytic work
must control; it is not by itself a bound for the full smooth-minus-transport
residual or for the endpoint survivor discrepancy. -/
theorem lifetimeDeathIncrement_eq_finiteCofactorOmegaSum
    {Λ : ℝ} (hΛ : 0 < Λ) (t : ℕ) :
    lifetimeDeathIncrement Λ t =
      ∑ k ∈ deathShellCofactorOmegaValues Λ t,
        (deathShellCofactorOmegaCount Λ t k : ℂ) * (-1 : ℂ) ^ (k + 1) := by
  rw [lifetimeDeathIncrement_eq_deathHeightShellMass hΛ.le,
    deathHeightShellMass_eq_cofactorParityMass hΛ]
  rfl

end RHLean.Proof
