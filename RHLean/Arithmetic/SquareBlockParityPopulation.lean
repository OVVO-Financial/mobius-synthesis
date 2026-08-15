import Mathlib
import RHLean.Arithmetic.FullPrimeFactorizationState

/-!
# Square-block parity populations and the exact identity `Δ_m = E_m − O_m`

This is step 1 of the parity-balance ladder in issue #144.  On the square block
`I_m = [m², (m+1)²)`, the block Möbius sum

```text
Δ_m = ∑_{n ∈ I_m} μ n
```

is exactly the even-minus-odd count of squarefree integers, where parity is the
distinct-prime depth read from the **complete certified factorization state**
(`FullFactorizationState`), never from a displayed transport product `c·q`:

```text
E_m = #{n ∈ I_m : Squarefree n ∧ Even (ω n)}
O_m = #{n ∈ I_m : Squarefree n ∧ Odd  (ω n)}
Δ_m = E_m − O_m.
```

Summing over `m ≤ N` gives `M((N+1)² − 1) = ∑_{m ≤ N} Δ_m`, so the governing
open target `Δ_m = o(m)` implies `M(x) = o(x)`.  This module proves only the
exact identity; the quantitative boundary bound is the remaining open theorem.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- The square block `I_m = [m², (m+1)²)`. -/
def squareBlockInterval (m : ℕ) : Finset ℕ := Finset.Ico (m ^ 2) ((m + 1) ^ 2)

/-- The block Möbius sum `Δ_m = ∑_{n ∈ I_m} μ n`. -/
def squareBlockMoebius (m : ℕ) : ℤ := ∑ n ∈ squareBlockInterval m, μ n

/-- Distinct-prime depth `ω(n)` read from the complete certified factorization
state of `n`. -/
def stateOmega (n : ℕ) : ℕ := (FullFactorizationState.canonical n).omega

theorem stateOmega_eq (n : ℕ) : stateOmega n = distinctPrimeFactorDepth n := rfl

/-- On squarefree `n`, `μ n` is the parity sign of the certified distinct-prime
depth. -/
theorem moebius_eq_negOnePow_stateOmega {n : ℕ} (hsq : Squarefree n) :
    μ n = (-1 : ℤ) ^ stateOmega n := by
  rw [stateOmega_eq, ← fullPrimeFactorDepth_eq_distinctPrimeFactorDepth hsq]
  exact moebius_eq_negOnePow_fullPrimeFactorDepth hsq

/-- Even-depth squarefree population of the block. -/
def evenDepthPopulation (m : ℕ) : Finset ℕ :=
  (squareBlockInterval m).filter fun n => Squarefree n ∧ Even (stateOmega n)

/-- Odd-depth squarefree population of the block. -/
def oddDepthPopulation (m : ℕ) : Finset ℕ :=
  (squareBlockInterval m).filter fun n => Squarefree n ∧ Odd (stateOmega n)

/-- `E_m`. -/
def evenDepthCount (m : ℕ) : ℕ := (evenDepthPopulation m).card

/-- `O_m`. -/
def oddDepthCount (m : ℕ) : ℕ := (oddDepthPopulation m).card

theorem disjoint_evenOdd (m : ℕ) :
    Disjoint (evenDepthPopulation m) (oddDepthPopulation m) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  rw [evenDepthPopulation, Finset.mem_filter] at hn
  rw [oddDepthPopulation, Finset.mem_filter] at hn'
  obtain ⟨_, _, he⟩ := hn
  obtain ⟨_, _, ho⟩ := hn'
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff] at ho
  omega

theorem moebius_one_of_mem_evenPopulation {m n : ℕ}
    (hn : n ∈ evenDepthPopulation m) : μ n = 1 := by
  rw [evenDepthPopulation, Finset.mem_filter] at hn
  rw [moebius_eq_negOnePow_stateOmega hn.2.1]
  exact hn.2.2.neg_one_pow

theorem moebius_negOne_of_mem_oddPopulation {m n : ℕ}
    (hn : n ∈ oddDepthPopulation m) : μ n = -1 := by
  rw [oddDepthPopulation, Finset.mem_filter] at hn
  rw [moebius_eq_negOnePow_stateOmega hn.2.1]
  exact hn.2.2.neg_one_pow

/-- **Exact parity-population identity** (issue #144, ladder step 1):
`Δ_m = E_m − O_m`, with parity read from the complete factorization state. -/
theorem squareBlockMoebius_eq_evenMinusOdd (m : ℕ) :
    squareBlockMoebius m = (evenDepthCount m : ℤ) - (oddDepthCount m : ℤ) := by
  classical
  have hunion : ∀ n ∈ squareBlockInterval m, μ n ≠ 0 →
      n ∈ evenDepthPopulation m ∨ n ∈ oddDepthPopulation m := by
    intro n hnI hμ
    have hsq : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ
    rcases Nat.even_or_odd (stateOmega n) with he | ho
    · exact Or.inl (by rw [evenDepthPopulation, Finset.mem_filter]; exact ⟨hnI, hsq, he⟩)
    · exact Or.inr (by rw [oddDepthPopulation, Finset.mem_filter]; exact ⟨hnI, hsq, ho⟩)
  have hstep : squareBlockMoebius m
      = ∑ n ∈ evenDepthPopulation m ∪ oddDepthPopulation m, μ n := by
    unfold squareBlockMoebius
    symm
    apply Finset.sum_subset
    · intro n hn
      rw [Finset.mem_union, evenDepthPopulation, oddDepthPopulation,
        Finset.mem_filter, Finset.mem_filter] at hn
      rcases hn with h | h
      · exact h.1
      · exact h.1
    · intro n hnI hnnot
      by_contra hμ
      rcases hunion n hnI hμ with h | h
      · exact hnnot (Finset.mem_union_left _ h)
      · exact hnnot (Finset.mem_union_right _ h)
  have hEsum : ∑ n ∈ evenDepthPopulation m, μ n = (evenDepthCount m : ℤ) := by
    rw [Finset.sum_congr rfl (fun n hn => moebius_one_of_mem_evenPopulation hn)]
    simp [evenDepthCount]
  have hOsum : ∑ n ∈ oddDepthPopulation m, μ n = -(oddDepthCount m : ℤ) := by
    rw [Finset.sum_congr rfl (fun n hn => moebius_negOne_of_mem_oddPopulation hn)]
    simp [oddDepthCount]
  rw [hstep, Finset.sum_union (disjoint_evenOdd m), hEsum, hOsum]
  ring

end RHLean.Arithmetic
