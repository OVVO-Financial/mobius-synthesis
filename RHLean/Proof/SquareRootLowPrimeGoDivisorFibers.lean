import Mathlib
import RHLean.Proof.DeathShellDivisorFibers

/-!
# Generic canonical height divisor fibers for Go boundary shells

The divisor code used by the death process does not intrinsically depend on a
death-shell predicate.  For every source with positive canonical doubled
height, the pair

`(|q^2-c^2|, |q-c|)`

already determines the unordered canonical factor pair, hence the source
integer itself.  The factor gap divides the height identically.

This module exposes that arithmetic fact without the death-stage wrapper.  A
future Go localization theorem therefore only has to put the surviving
second-difference population into a short finite set of canonical heights; the
existing divisor bound can then be applied directly.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Positive canonical height is enough for the existing `(height,gap)` divisor
code to be injective.  No death-shell membership is needed. -/
theorem deathShellDivisorCode_injOn_positiveHeight :
    Set.InjOn deathShellDivisorCode
      {m : ℕ | 0 < deathShellHeightNat m} := by
  intro m hm n hn hcode
  have hheight : deathShellHeightNat m = deathShellHeightNat n :=
    congrArg Sigma.fst hcode
  have hgap : canonicalAbsoluteGap m = canonicalAbsoluteGap n :=
    congrArg Sigma.snd hcode
  have hgapPos : 0 < canonicalAbsoluteGap m := by
    apply Nat.pos_of_ne_zero
    intro hgapZero
    change 0 < deathShellHeightNat m at hm
    rw [deathShellHeightNat, hgapZero, zero_mul] at hm
    exact (Nat.lt_irrefl 0) hm
  have hsum :
      canonicalPairLo m + canonicalPairHi m =
        canonicalPairLo n + canonicalPairHi n := by
    apply Nat.eq_of_mul_eq_mul_left hgapPos
    simpa [deathShellHeightNat, hgap] using hheight
  have hhi_m := canonicalPairLo_add_absoluteGap m
  have hhi_n := canonicalPairLo_add_absoluteGap n
  have hlo : canonicalPairLo m = canonicalPairLo n := by omega
  have hhi : canonicalPairHi m = canonicalPairHi n := by omega
  calc
    m = canonicalPairLo m * canonicalPairHi m :=
      (canonicalPairLo_mul_pairHi_all m).symm
    _ = canonicalPairLo n * canonicalPairHi n := by rw [hlo, hhi]
    _ = n := canonicalPairLo_mul_pairHi_all n

/-- For every positive-height source, its absolute canonical factor gap is a
literal divisor of its canonical height. -/
theorem canonicalAbsoluteGap_mem_heightDivisors_of_positiveHeight
    {m : ℕ} (hpos : 0 < deathShellHeightNat m) :
    canonicalAbsoluteGap m ∈ (deathShellHeightNat m).divisors := by
  apply Nat.mem_divisors.mpr
  constructor
  · refine ⟨canonicalPairLo m + canonicalPairHi m, ?_⟩
    rfl
  · exact Nat.ne_of_gt hpos

/-- Divisor fibers over an arbitrary finite set of canonical heights. -/
noncomputable def canonicalHeightDivisorFibers (H : Finset ℕ) :
    Finset (Σ _k : ℕ, ℕ) := by
  classical
  exact H.sigma fun k => k.divisors

/-- Every positive-height source whose height lies in `H` maps into the
corresponding divisor-fiber population. -/
theorem deathShellDivisorCode_mem_canonicalHeightDivisorFibers
    {H : Finset ℕ} {m : ℕ}
    (hpos : 0 < deathShellHeightNat m)
    (hheight : deathShellHeightNat m ∈ H) :
    deathShellDivisorCode m ∈ canonicalHeightDivisorFibers H := by
  apply Finset.mem_sigma.mpr
  exact ⟨hheight,
    canonicalAbsoluteGap_mem_heightDivisors_of_positiveHeight hpos⟩

/-- **Generic divisor-fiber cardinality bridge.**  Any finite arithmetic
population with positive canonical height and height image contained in `H` has
cardinality at most the divisor sum over `H`.

Thus the remaining Go estimate can be reduced to proving that its globally
recombined second-difference support occupies only a short set of canonical
height values. -/
theorem card_le_canonicalHeight_divisorSum
    {S H : Finset ℕ}
    (hpos : ∀ m ∈ S, 0 < deathShellHeightNat m)
    (hheight : ∀ m ∈ S, deathShellHeightNat m ∈ H) :
    S.card ≤ ∑ k ∈ H, k.divisors.card := by
  classical
  have hinj :
      Set.InjOn deathShellDivisorCode (↑S : Set ℕ) := by
    intro m hm n hn hcode
    exact deathShellDivisorCode_injOn_positiveHeight
      (hpos m hm) (hpos n hn) hcode
  have hsubset :
      S.image deathShellDivisorCode ⊆ canonicalHeightDivisorFibers H := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨m, hm, rfl⟩
    exact deathShellDivisorCode_mem_canonicalHeightDivisorFibers
      (hpos m hm) (hheight m hm)
  calc
    S.card = (S.image deathShellDivisorCode).card := by
      exact (Finset.card_image_of_injOn hinj).symm
    _ ≤ (canonicalHeightDivisorFibers H).card :=
      Finset.card_le_card hsubset
    _ = ∑ k ∈ H, k.divisors.card := by
      simp [canonicalHeightDivisorFibers, Finset.card_sigma]

end RHLean.Proof
