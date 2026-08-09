import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy
import RHLean.Proof.DeathShellCardinalityAndCentering

/-!
# Exact divisor fibers for canonical death shells

This module gives the elementary finite combinatorial bound that precedes any
asymptotic divisor estimate.  A death-shell source is encoded by

* its positive integer height `|q^2 - c^2|`, and
* the positive absolute factor gap `|q-c|`, which divides that height.

The encoding is injective on each shell.  Consequently the shell cardinality is
bounded by the sum of divisor counts over every integer height in the half-open
shell window.  In particular, the bound is a divisor *sum over the window*;
it is not the unsupported single-endpoint claim `#S_t <= tau(2 * Lambda * (t+1))`.

No subpolynomial divisor estimate, cancellation estimate, or RH implication is
asserted here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- The natural-valued absolute doubled height
`|q^2-c^2| = |q-c| * (min(q,c)+max(q,c))`. -/
def deathShellHeightNat (m : ℕ) : ℕ :=
  canonicalAbsoluteGap m * (canonicalPairLo m + canonicalPairHi m)

/-- The natural shell height casts to the existing real absolute doubled
height. -/
theorem deathShellHeightNat_cast (m : ℕ) :
    (deathShellHeightNat m : ℝ) = |canonicalHeightTwice m| := by
  rw [abs_canonicalHeightTwice_eq_gap_mul_factorSum]
  simp [deathShellHeightNat]

/-- The finite set of integer heights in the half-open shell window. -/
noncomputable def deathShellIntegerWindow (Λ : ℝ) (t : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (Nat.floor (2 * Λ * ((t + 1 : ℕ) : ℝ)) + 1)).filter
      (fun k => 2 * Λ * (t : ℝ) < (k : ℝ))

/-- A canonical source in a positive-cutoff death shell has positive natural
height. -/
theorem deathShellHeightNat_pos_of_mem
    {Λ : ℝ} (hΛ : 0 < Λ) {t m : ℕ}
    (hm : m ∈ deathHeightShellSet Λ t) :
    0 < deathShellHeightNat m := by
  have hshell := mem_deathHeightShellSet_implies_shell Λ t m hm
  have hwindow := (isDeathHeightShell_iff_height_window Λ t m).mp hshell
  have hthreshold : 0 ≤ 2 * Λ * (t : ℝ) := by positivity
  have hheightReal : 0 < (deathShellHeightNat m : ℝ) := by
    rw [deathShellHeightNat_cast]
    exact lt_of_le_of_lt hthreshold hwindow.1
  exact_mod_cast hheightReal

/-- The integer height of every source in a shell belongs to that shell's
finite integer window. -/
theorem deathShellHeightNat_mem_integerWindow
    {Λ : ℝ} {t m : ℕ}
    (hm : m ∈ deathHeightShellSet Λ t) :
    deathShellHeightNat m ∈ deathShellIntegerWindow Λ t := by
  have hshell := mem_deathHeightShellSet_implies_shell Λ t m hm
  have hwindow := (isDeathHeightShell_iff_height_window Λ t m).mp hshell
  have hupper :
      (deathShellHeightNat m : ℝ) ≤ 2 * Λ * ((t + 1 : ℕ) : ℝ) := by
    simpa [deathShellHeightNat_cast] using hwindow.2
  have hfloor :
      deathShellHeightNat m ≤ Nat.floor (2 * Λ * ((t + 1 : ℕ) : ℝ)) :=
    Nat.le_floor hupper
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hfloor)
  · simpa [deathShellHeightNat_cast] using hwindow.1

/-- The product of the unordered canonical pair is the source, including the
harmless endpoints `m=0,1`. -/
theorem canonicalPairLo_mul_pairHi_all (m : ℕ) :
    canonicalPairLo m * canonicalPairHi m = m := by
  by_cases hm : 1 < m
  · exact canonicalPairLo_mul_pairHi hm
  · have hm_cases : m = 0 ∨ m = 1 := by omega
    rcases hm_cases with rfl | rfl <;>
      norm_num [canonicalPairLo, canonicalPairHi, canonicalCofactor,
        canonicalLargestPrimeFactor]

/-- Encode a shell source by its integer height and a divisor of that height,
namely its positive absolute factor gap. -/
def deathShellDivisorCode (m : ℕ) : Σ _k : ℕ, ℕ :=
  ⟨deathShellHeightNat m, canonicalAbsoluteGap m⟩

/-- The divisor-fiber population attached to the full integer shell window. -/
noncomputable def deathShellDivisorFibers (Λ : ℝ) (t : ℕ) :
    Finset (Σ _k : ℕ, ℕ) := by
  classical
  exact (deathShellIntegerWindow Λ t).sigma fun k => k.divisors

/-- Every shell code lies in the corresponding divisor-fiber population. -/
theorem deathShellDivisorCode_mem_fibers
    {Λ : ℝ} (hΛ : 0 < Λ) {t m : ℕ}
    (hm : m ∈ deathHeightShellSet Λ t) :
    deathShellDivisorCode m ∈ deathShellDivisorFibers Λ t := by
  apply Finset.mem_sigma.mpr
  constructor
  · exact deathShellHeightNat_mem_integerWindow hm
  · change canonicalAbsoluteGap m ∈ (deathShellHeightNat m).divisors
    apply Nat.mem_divisors.mpr
    constructor
    · refine ⟨canonicalPairLo m + canonicalPairHi m, ?_⟩
      rfl
    · exact Nat.ne_of_gt (deathShellHeightNat_pos_of_mem hΛ hm)

/-- Height plus positive factor gap determines the canonical source uniquely. -/
theorem deathShellDivisorCode_injOn
    {Λ : ℝ} (hΛ : 0 < Λ) (t : ℕ) :
    Set.InjOn deathShellDivisorCode
      (↑(deathHeightShellSet Λ t) : Set ℕ) := by
  intro m hm n hn hcode
  have hheight : deathShellHeightNat m = deathShellHeightNat n :=
    congrArg Sigma.fst hcode
  have hgap : canonicalAbsoluteGap m = canonicalAbsoluteGap n :=
    congrArg Sigma.snd hcode
  have hheightPos : 0 < deathShellHeightNat m :=
    deathShellHeightNat_pos_of_mem hΛ hm
  have hgapPos : 0 < canonicalAbsoluteGap m := by
    apply Nat.pos_of_ne_zero
    intro hgapZero
    rw [deathShellHeightNat, hgapZero, zero_mul] at hheightPos
    exact (Nat.lt_irrefl 0) hheightPos
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

/-- Exact unconditional shell-cardinality bound by the sum of divisor counts
across all integer heights in the shell window. -/
theorem card_deathHeightShellSet_le_divisorSum
    {Λ : ℝ} (hΛ : 0 < Λ) (t : ℕ) :
    (deathHeightShellSet Λ t).card ≤
      ∑ k ∈ deathShellIntegerWindow Λ t, k.divisors.card := by
  classical
  have hinj := deathShellDivisorCode_injOn hΛ t
  have hsubset :
      (deathHeightShellSet Λ t).image deathShellDivisorCode ⊆
        deathShellDivisorFibers Λ t := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨m, hm, rfl⟩
    exact deathShellDivisorCode_mem_fibers hΛ hm
  calc
    (deathHeightShellSet Λ t).card =
        ((deathHeightShellSet Λ t).image deathShellDivisorCode).card := by
      exact (Finset.card_image_of_injOn hinj).symm
    _ ≤ (deathShellDivisorFibers Λ t).card :=
      Finset.card_le_card hsubset
    _ = ∑ k ∈ deathShellIntegerWindow Λ t, k.divisors.card := by
      simp [deathShellDivisorFibers, Finset.card_sigma]

/-- The real-valued divisor-sum majorant supplied by the exact fiber bound. -/
noncomputable def deathShellDivisorMajorant (Λ : ℝ) (t : ℕ) : ℝ :=
  ((∑ k ∈ deathShellIntegerWindow Λ t, k.divisors.card : ℕ) : ℝ)

/-- Package the exact divisor-fiber estimate as the existing shell-cardinality
control interface. -/
noncomputable def deathShellDivisorCardinalityControl
    (Λ : ℝ) (hΛ : 0 < Λ) : DeathShellCardinalityControl Λ where
  majorant := deathShellDivisorMajorant Λ
  majorant_nonneg := fun _ => by
    unfold deathShellDivisorMajorant
    positivity
  card_le := fun t => by
    change ((deathHeightShellSet Λ t).card : ℝ) ≤
      ((∑ k ∈ deathShellIntegerWindow Λ t, k.divisors.card : ℕ) : ℝ)
    exact_mod_cast card_deathHeightShellSet_le_divisorSum hΛ t

/-- The exact shell identity and divisor-fiber bound control every death
increment by the divisor sum across its full integer window. -/
theorem norm_lifetimeDeathIncrement_le_divisorMajorant
    {Λ : ℝ} (hΛ : 0 < Λ) (t : ℕ) :
    ‖lifetimeDeathIncrement Λ t‖ ≤ deathShellDivisorMajorant Λ t := by
  exact norm_lifetimeDeathIncrement_le_majorant hΛ.le
    (deathShellDivisorCardinalityControl Λ hΛ) t

/-- Summing the exact divisor majorants gives the corresponding unconditional
pointwise bound for the cumulative death process. -/
theorem norm_lifetimeDeathMass_le_initial_add_sum_divisorMajorant
    {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    ‖lifetimeDeathMass Λ n‖ ≤
      ‖lifetimeDeathMass Λ 0‖ +
        ∑ t ∈ Finset.range n, deathShellDivisorMajorant Λ t := by
  exact norm_lifetimeDeathMass_le_initial_add_sum_majorant hΛ.le
    (deathShellDivisorCardinalityControl Λ hΛ) n

end RHLean.Proof
