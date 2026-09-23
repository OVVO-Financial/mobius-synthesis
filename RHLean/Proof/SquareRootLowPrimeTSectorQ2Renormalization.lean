import Mathlib
import RHLean.Analysis.FinitePrimeTMixing
import RHLean.Proof.SquareRootLowPrimeGoSecondContactSources

/-!
# T-sector spectral damping times q^2 scale descent

The old finite-prime T-sector calculation and the new Go second-contact scale
flux are complementary rather than competing mechanisms.

* At the first generic prime `11`, the Mertens-visible weight-one Walsh mode is
  multiplied by `19/23`, so its square-energy factor is `(19/23)^2 < 3/4`.
* Every second-contact owner `q` sends its unresolved daughter to the cutoff
  `X / q^2`.  Summed over all possible prime owners, these daughter scales have
  total reciprocal-square budget strictly below the parent scale.

The second fact is proved here with an elementary finite telescoping estimate;
no PNT or infinite-series evaluation is used.  Combining the two gives a
strictly subcritical energy branching coefficient.  The final theorem packages
the resulting strong-induction engine: any nonnegative energy profile whose
one-step arithmetic recurrence has the exact `11`-sector factor and the `q^2`
daughters is automatically linear in the arithmetic scale.

This module does **not** assert that the physical Mobius endpoint already
satisfies that recurrence.  Its purpose is to make the remaining intertwining
statement exact and quantitatively sufficient: once the physical degree-one
mode is transported through the existing `11`-state law before the Go daughters
are separated, no further analytic estimate is needed to close the energy
induction.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Finite reciprocal-square prefix, including the terms `2,...,N`. -/
def reciprocalSquarePrefix (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N + 1),
    if 2 ≤ n then (1 : ℚ) / (n : ℚ) ^ 2 else 0

/-- The elementary summand comparison behind the reciprocal-square telescope:
`1/n^2 <= 1/(n-1) - 1/n` for `n >= 2`. -/
theorem reciprocalSquareTerm_le_telescope
    {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℚ) / (n : ℚ) ^ 2 ≤
      1 / ((n : ℚ) - 1) - 1 / (n : ℚ) := by
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn0 : (0 : ℚ) < (n : ℚ) := by linarith
  have hnm10 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  rw [show 1 / ((n : ℚ) - 1) - 1 / (n : ℚ) =
      1 / (((n : ℚ) - 1) * (n : ℚ)) by
        field_simp [ne_of_gt hn0, ne_of_gt hnm10]
        ring]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simp only [one_mul]
  exact (inv_le_inv₀ (by positivity : (0 : ℚ) < (n : ℚ) ^ 2)
    (mul_pos hnm10 hn0)).2 (by nlinarith)

/-- The finite reciprocal-square prefix is bounded by the elementary telescoping
majorant `1 - 1/N`. -/
theorem reciprocalSquarePrefix_le_one_sub_inv
    (k : ℕ) :
    reciprocalSquarePrefix (k + 2) ≤
      1 - 1 / ((k + 2 : ℕ) : ℚ) := by
  induction k with
  | zero =>
      norm_num [reciprocalSquarePrefix, Finset.sum_range_succ]
  | succ k ih =>
      have hterm := reciprocalSquareTerm_le_telescope
        (n := k + 3) (by omega)
      have hsplit :
          reciprocalSquarePrefix (k + 3) =
            reciprocalSquarePrefix (k + 2) +
              (1 : ℚ) / ((k + 3 : ℕ) : ℚ) ^ 2 := by
        unfold reciprocalSquarePrefix
        rw [show k + 3 + 1 = (k + 2 + 1) + 1 by omega,
          Finset.sum_range_succ]
        simp only [show 2 ≤ k + 3 by omega, if_true]
      rw [hsplit]
      calc
        reciprocalSquarePrefix (k + 2) +
            (1 : ℚ) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤
          (1 - 1 / ((k + 2 : ℕ) : ℚ)) +
            (1 : ℚ) / ((k + 3 : ℕ) : ℚ) ^ 2 :=
              add_le_add_right ih _
        _ ≤ (1 - 1 / ((k + 2 : ℕ) : ℚ)) +
            (1 / (((k + 3 : ℕ) : ℚ) - 1) -
              1 / ((k + 3 : ℕ) : ℚ)) :=
              add_le_add_left hterm _
        _ = 1 - 1 / ((k + 3 : ℕ) : ℚ) := by
          have hkcast : (((k + 3 : ℕ) : ℚ) - 1) =
              ((k + 2 : ℕ) : ℚ) := by
            push_cast
            ring
          rw [hkcast]
          ring

/-- In particular every finite reciprocal-square prefix from `2` onward has
budget at most one. -/
theorem reciprocalSquarePrefix_le_one (N : ℕ) :
    reciprocalSquarePrefix N ≤ 1 := by
  by_cases hN : N < 2
  · interval_cases N <;>
      norm_num [reciprocalSquarePrefix, Finset.sum_range_succ]
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := by
      exact ⟨N - 2, by omega⟩
    have h := reciprocalSquarePrefix_le_one_sub_inv k
    have hnonneg : (0 : ℚ) ≤ 1 / (((k + 2 : ℕ) : ℚ)) := by positivity
    linarith

/-- Reciprocal-square budget of the prime owners through `N`. -/
def primeOwnerReciprocalSquareBudget (N : ℕ) : ℚ :=
  ∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2

/-- Prime owners consume no more reciprocal-square budget than all integers.
The bound is finite and elementary; no Euler product or zeta value is used. -/
theorem primeOwnerReciprocalSquareBudget_le_one (N : ℕ) :
    primeOwnerReciprocalSquareBudget N ≤ 1 := by
  have hsub : primesUpTo N ⊆ Finset.range (N + 1) := by
    intro q hq
    exact Finset.mem_range.mpr (by
      have hqN := (mem_primesUpTo.mp hq).2
      omega)
  have hsum :
      primeOwnerReciprocalSquareBudget N ≤ reciprocalSquarePrefix N := by
    unfold primeOwnerReciprocalSquareBudget reciprocalSquarePrefix
    calc
      (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) =
          ∑ q ∈ primesUpTo N,
            (if 2 ≤ q then (1 : ℚ) / (q : ℚ) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hq2 := (mem_primesUpTo.mp hq).1.two_le
        simp [hq2]
      _ ≤ ∑ q ∈ Finset.range (N + 1),
            (if 2 ≤ q then (1 : ℚ) / (q : ℚ) ^ 2 else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro q _hqRange hqNot
        split_ifs
        · positivity
        · norm_num
  exact hsum.trans (reciprocalSquarePrefix_le_one N)

/-- The sum of the literal square-dilated daughter cutoffs is at most the parent
scale.  This is the finite `q^2` branching budget in the exact arithmetic units
used by the Go recursion. -/
theorem sum_primeOwner_squareDilatedCutoffs_le_parent
    (N X : ℕ) :
    (∑ q ∈ primesUpTo N, ((X / (q * q) : ℕ) : ℚ)) ≤ (X : ℚ) := by
  have hterm : ∀ q ∈ primesUpTo N,
      ((X / (q * q) : ℕ) : ℚ) ≤
        (X : ℚ) * ((1 : ℚ) / (q : ℚ) ^ 2) := by
    intro q hq
    have hqPrime := (mem_primesUpTo.mp hq).1
    have hqqPosNat : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
    have hmulNat : (X / (q * q)) * (q * q) ≤ X :=
      Nat.div_mul_le_self X (q * q)
    have hmul :
        (((X / (q * q) : ℕ) : ℚ) * ((q * q : ℕ) : ℚ)) ≤ (X : ℚ) := by
      exact_mod_cast hmulNat
    have hqqPos : (0 : ℚ) < ((q * q : ℕ) : ℚ) := by exact_mod_cast hqqPosNat
    have hdiv := (le_div_iff₀ hqqPos).2 hmul
    calc
      ((X / (q * q) : ℕ) : ℚ) ≤
          (X : ℚ) / ((q * q : ℕ) : ℚ) := hdiv
      _ = (X : ℚ) * ((1 : ℚ) / (q : ℚ) ^ 2) := by
        push_cast
        rw [pow_two]
        field_simp
  calc
    (∑ q ∈ primesUpTo N, ((X / (q * q) : ℕ) : ℚ)) ≤
        ∑ q ∈ primesUpTo N,
          (X : ℚ) * ((1 : ℚ) / (q : ℚ) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hterm q hq
    _ = (X : ℚ) * primeOwnerReciprocalSquareBudget N := by
      unfold primeOwnerReciprocalSquareBudget
      rw [Finset.mul_sum]
    _ ≤ (X : ℚ) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (primeOwnerReciprocalSquareBudget_le_one N) (by positivity)
    _ = (X : ℚ) := by ring

/-- Exact energy multiplier of the first generic `T`-sector prime on the
Mertens-visible weight-one Walsh mode. -/
def elevenWeightOneEnergyFactor : ℚ :=
  (onePrimeWalshFactor 11 1) ^ 2

@[simp] theorem elevenWeightOneEnergyFactor_eq :
    elevenWeightOneEnergyFactor = (19 : ℚ) ^ 2 / 23 ^ 2 := by
  rw [elevenWeightOneEnergyFactor, onePrimeWalshFactor_eleven_one]
  ring

/-- One `11`-layer already dissipates more than one quarter of weight-one
energy. -/
theorem elevenWeightOneEnergyFactor_lt_three_quarters :
    elevenWeightOneEnergyFactor < (3 : ℚ) / 4 := by
  rw [elevenWeightOneEnergyFactor_eq]
  norm_num

/-- The spectral factor is nonnegative. -/
theorem elevenWeightOneEnergyFactor_nonneg :
    0 ≤ elevenWeightOneEnergyFactor := by
  unfold elevenWeightOneEnergyFactor
  positivity

/-- The numerical renormalization constant obtained by combining the crude
unit `q^2` daughter budget with the exact `11` weight-one energy factor. -/
def elevenQ2RenormalizationCoefficient : ℚ :=
  elevenWeightOneEnergyFactor

/-- The combined T-sector / `q^2` branching coefficient is strictly
subcritical. -/
theorem elevenQ2RenormalizationCoefficient_lt_one :
    elevenQ2RenormalizationCoefficient < 1 := by
  unfold elevenQ2RenormalizationCoefficient
  exact elevenWeightOneEnergyFactor_lt_three_quarters.trans (by norm_num)

/-- One-step recurrence required of an arithmetic energy profile.  The
coefficient is not a hypothesis: it is the exact compiled `11` weight-one
factor.  The only daughters are the square-dilated cutoffs already present in
the Go recursion. -/
def ElevenQ2EnergyStep (E : ℕ → ℚ) (C : ℚ) : Prop :=
  ∀ X : ℕ,
    E X ≤ C * (X : ℚ) +
      elevenWeightOneEnergyFactor *
        ∑ q ∈ primesUpTo X, E (X / (q * q))

/-- **Fixed-point form of the q-square energy induction.**  The earlier
`3/4` lemma is only one convenient specialization.  If `K` is any nonnegative
linear envelope satisfying `C + lambda*K <= K`, then the same strong induction
closes at `E(X) <= K*X`.  This exposes all of the spectral margin below one. -/
theorem q2EnergyStep_implies_linear_of_fixedPointBudget
    {E : ℕ → ℚ} {C lambda K : ℚ}
    (hK : 0 ≤ K) (hlambda0 : 0 ≤ lambda)
    (hfixed : C + lambda * K ≤ K)
    (hstep : ∀ X : ℕ, E X ≤ C * (X : ℚ) +
      lambda * ∑ q ∈ primesUpTo X, E (X / (q * q))) :
    ∀ X : ℕ, E X ≤ K * (X : ℚ) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      by_cases hX : X = 0
      · subst X
        have hs := hstep 0
        simpa using hs
      · have hXpos : 0 < X := Nat.pos_of_ne_zero hX
        have hchildren :
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              K * (∑ q ∈ primesUpTo X, ((X / (q * q) : ℕ) : ℚ)) := by
          calc
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
                ∑ q ∈ primesUpTo X,
                  K * ((X / (q * q) : ℕ) : ℚ) := by
              apply Finset.sum_le_sum
              intro q hq
              have hqPrime := (mem_primesUpTo.mp hq).1
              have hqq : 1 < q * q := by nlinarith [hqPrime.two_le]
              have hchild : X / (q * q) < X :=
                Nat.div_lt_self hXpos hqq
              exact ih (X / (q * q)) hchild
            _ = K *
                (∑ q ∈ primesUpTo X, ((X / (q * q) : ℕ) : ℚ)) := by
              rw [Finset.mul_sum]
        have hscale := sum_primeOwner_squareDilatedCutoffs_le_parent X X
        have hchildrenParent :
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤ K * (X : ℚ) := by
          exact hchildren.trans (mul_le_mul_of_nonneg_left hscale hK)
        have hweighted :
            lambda * (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              lambda * (K * (X : ℚ)) :=
          mul_le_mul_of_nonneg_left hchildrenParent hlambda0
        calc
          E X ≤ C * (X : ℚ) +
              lambda * ∑ q ∈ primesUpTo X, E (X / (q * q)) := hstep X
          _ ≤ C * (X : ℚ) + lambda * (K * (X : ℚ)) :=
            add_le_add_left hweighted _
          _ = (C + lambda * K) * (X : ℚ) := by ring
          _ ≤ K * (X : ℚ) :=
            mul_le_mul_of_nonneg_right hfixed (by positivity)

/-- The same induction permits any nonnegative coefficient at most `3/4`.
This retains the available margin for a bulk-boundary cross term. -/
theorem q2EnergyStep_implies_linear
    {E : ℕ → ℚ} {C lambda : ℚ}
    (hC : 0 ≤ C) (hlambda0 : 0 ≤ lambda)
    (hlambda : lambda ≤ (3 : ℚ) / 4)
    (hstep : ∀ X : ℕ, E X ≤ C * (X : ℚ) +
      lambda * ∑ q ∈ primesUpTo X, E (X / (q * q))) :
    ∀ X : ℕ, E X ≤ 4 * C * (X : ℚ) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      by_cases hX : X = 0
      · subst X
        have hs := hstep 0
        simpa using hs
      · have hXpos : 0 < X := Nat.pos_of_ne_zero hX
        have hchildren :
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              4 * C *
                (∑ q ∈ primesUpTo X, ((X / (q * q) : ℕ) : ℚ)) := by
          calc
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
                ∑ q ∈ primesUpTo X,
                  4 * C * ((X / (q * q) : ℕ) : ℚ) := by
              apply Finset.sum_le_sum
              intro q hq
              have hqPrime := (mem_primesUpTo.mp hq).1
              have hqq : 1 < q * q := by nlinarith [hqPrime.two_le]
              have hchild : X / (q * q) < X :=
                Nat.div_lt_self hXpos hqq
              exact ih (X / (q * q)) hchild
            _ = 4 * C *
                (∑ q ∈ primesUpTo X, ((X / (q * q) : ℕ) : ℚ)) := by
              rw [Finset.mul_sum]
        have hscale := sum_primeOwner_squareDilatedCutoffs_le_parent X X
        have hchildrenParent :
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              4 * C * (X : ℚ) := by
          exact hchildren.trans
            (mul_le_mul_of_nonneg_left hscale (by positivity))
        have hs := hstep X
        have hweighted :
            lambda *
                (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              ((3 : ℚ) / 4) * (4 * C * (X : ℚ)) := by
          calc
            lambda *
                (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              lambda * (4 * C * (X : ℚ)) := by
                exact mul_le_mul_of_nonneg_left hchildrenParent
                  hlambda0
            _ ≤ ((3 : ℚ) / 4) * (4 * C * (X : ℚ)) := by
                exact mul_le_mul_of_nonneg_right hlambda (by positivity)
        calc
          E X ≤ C * (X : ℚ) +
              lambda *
                ∑ q ∈ primesUpTo X, E (X / (q * q)) := hs
          _ ≤ C * (X : ℚ) +
              ((3 : ℚ) / 4) * (4 * C * (X : ℚ)) :=
                add_le_add_left hweighted _
          _ = 4 * C * (X : ℚ) := by ring

/-- **Subcritical energy induction with the exact prime-11 factor.** -/
theorem elevenQ2EnergyStep_implies_linear
    {E : ℕ → ℚ} {C : ℚ}
    (hC : 0 ≤ C)
    (hstep : ElevenQ2EnergyStep E C) :
    ∀ X : ℕ, E X ≤ 4 * C * (X : ℚ) := by
  exact q2EnergyStep_implies_linear hC
    elevenWeightOneEnergyFactor_nonneg
    (le_of_lt elevenWeightOneEnergyFactor_lt_three_quarters) hstep

/-- Absorb the bulk-boundary cross term while spending only `1/12` of the
bulk coefficient.  No sign of the boundary is assumed. -/
theorem elevenQ2_bulk_boundary_sq_le (u b : ℚ) :
    (u + b) ^ 2 ≤ (13 : ℚ) / 12 * u ^ 2 + 13 * b ^ 2 := by
  nlinarith [sq_nonneg (u - 12 * b)]

/-- The exact prime-11 factor has enough margin for that absorption. -/
theorem elevenQ2_boundary_inflated_factor_le_three_quarters :
    (13 : ℚ) / 12 * elevenWeightOneEnergyFactor ≤ 3 / 4 := by
  rw [elevenWeightOneEnergyFactor_eq]
  norm_num

/-- **Complete bulk-boundary energy induction.**  A square-root-size global
boundary and the desired interior estimate suffice even though squaring their
sum creates a cross term.  The resulting recurrence uses coefficient
`(13/12)*(19/23)^2`, still below `3/4`, and yields `E(X) <= 52*B*X`.
The physical decomposition and interior estimate remain explicit hypotheses. -/
theorem elevenQ2_bulk_boundary_implies_linear
    {E I b : ℕ → ℚ} {B : ℚ}
    (hB : 0 ≤ B)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤ elevenWeightOneEnergyFactor *
      ∑ q ∈ primesUpTo X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X : ℕ, E X ≤ 52 * B * (X : ℚ) := by
  have hstep : ∀ X : ℕ, E X ≤ (13 * B) * (X : ℚ) +
      ((13 : ℚ) / 12 * elevenWeightOneEnergyFactor) *
        ∑ q ∈ primesUpTo X, E (X / (q * q)) := by
    intro X
    have hsplit := elevenQ2_bulk_boundary_sq_le (I X) (b X)
    have hi := hinterior X
    have hb := hboundary X
    have hd := hdecomp X
    nlinarith
  have h := q2EnergyStep_implies_linear
    (by positivity : 0 ≤ 13 * B)
    (mul_nonneg (by norm_num) elevenWeightOneEnergyFactor_nonneg)
    elevenQ2_boundary_inflated_factor_le_three_quarters hstep
  intro X
  simpa only [show (4 : ℚ) * (13 * B) = 52 * B by ring] using h X

/-- Optimized Young absorption for the exact `19/23` daughter amplitude.  This
spends the entire strict subunit margin rather than rounding the recurrence down
to `3/4`. -/
theorem elevenQ2_bulk_boundary_sq_le_optimal (u b : ℚ) :
    (u + b) ^ 2 ≤ (23 : ℚ) / 19 * u ^ 2 + (23 : ℚ) / 4 * b ^ 2 := by
  nlinarith [sq_nonneg (4 * u - 19 * b)]

/-- **Full-margin bulk-boundary induction.**  Under the exact interior estimate,
the optimized Young split leaves daughter coefficient `19/23`.  The fixed-point
linear envelope is therefore `(529/16)*B*X`, improving the coarse `52*B*X`
constant and, more importantly, exposing the whole margin below one. -/
theorem elevenQ2_bulk_boundary_implies_linear_fullMargin
    {E I b : ℕ → ℚ} {B : ℚ}
    (hB : 0 ≤ B)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤ elevenWeightOneEnergyFactor *
      ∑ q ∈ primesUpTo X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X : ℕ, E X ≤ ((529 : ℚ) / 16 * B) * (X : ℚ) := by
  have hfactor :
      (23 : ℚ) / 19 * elevenWeightOneEnergyFactor = (19 : ℚ) / 23 := by
    rw [elevenWeightOneEnergyFactor_eq]
    norm_num
  have hstep : ∀ X : ℕ,
      E X ≤ ((23 : ℚ) / 4 * B) * (X : ℚ) +
        ((19 : ℚ) / 23) * ∑ q ∈ primesUpTo X, E (X / (q * q)) := by
    intro X
    have hsplit := elevenQ2_bulk_boundary_sq_le_optimal (I X) (b X)
    have hiScaled :
        (23 : ℚ) / 19 * (I X) ^ 2 ≤
          (19 : ℚ) / 23 * ∑ q ∈ primesUpTo X, E (X / (q * q)) := by
      calc
        (23 : ℚ) / 19 * (I X) ^ 2 ≤
            (23 : ℚ) / 19 *
              (elevenWeightOneEnergyFactor *
                ∑ q ∈ primesUpTo X, E (X / (q * q))) :=
          mul_le_mul_of_nonneg_left (hinterior X) (by norm_num)
        _ = (19 : ℚ) / 23 *
              ∑ q ∈ primesUpTo X, E (X / (q * q)) := by
          rw [← mul_assoc, hfactor]
    have hbScaled :
        (23 : ℚ) / 4 * (b X) ^ 2 ≤
          (23 : ℚ) / 4 * (B * (X : ℚ)) :=
      mul_le_mul_of_nonneg_left (hboundary X) (by norm_num)
    calc
      E X ≤ (I X + b X) ^ 2 := hdecomp X
      _ ≤ (23 : ℚ) / 19 * (I X) ^ 2 +
          (23 : ℚ) / 4 * (b X) ^ 2 := hsplit
      _ ≤ (19 : ℚ) / 23 *
            (∑ q ∈ primesUpTo X, E (X / (q * q))) +
          (23 : ℚ) / 4 * (B * (X : ℚ)) :=
        add_le_add hiScaled hbScaled
      _ = ((23 : ℚ) / 4 * B) * (X : ℚ) +
          ((19 : ℚ) / 23) *
            ∑ q ∈ primesUpTo X, E (X / (q * q)) := by ring
  have hfixed :
      (23 : ℚ) / 4 * B +
          (19 : ℚ) / 23 * ((529 : ℚ) / 16 * B) ≤
        (529 : ℚ) / 16 * B := by
    ring_nf
    exact le_rfl
  exact q2EnergyStep_implies_linear_of_fixedPointBudget
    (by positivity : 0 ≤ (529 : ℚ) / 16 * B)
    (by norm_num : (0 : ℚ) ≤ 19 / 23)
    hfixed hstep

/-- A deliberately non-sharp Young split leaving room for cross-owner frame
loss. -/
theorem elevenQ2_bulk_boundary_sq_le_fourThirdsFrame (u b : ℚ) :
    (u + b) ^ 2 ≤ (23 : ℚ) / 22 * u ^ 2 + 23 * b ^ 2 := by
  nlinarith [sq_nonneg (u - 22 * b)]

/-- **A `4/3` cross-owner frame bound is already enough.**  Exact orthogonality
of owner daughters is unnecessary.  If the physical interior loses as much as
a factor `4/3` before the prime-11 energy contraction, the resulting daughter
coefficient is still `722/759 < 1`, and the full recurrence remains linear. -/
theorem elevenQ2_bulk_boundary_fourThirdsFrame_implies_linear
    {E I b : ℕ → ℚ} {B : ℚ}
    (hB : 0 ≤ B)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤
      (4 : ℚ) / 3 * elevenWeightOneEnergyFactor *
        ∑ q ∈ primesUpTo X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X : ℕ, E X ≤ ((17457 : ℚ) / 37 * B) * (X : ℚ) := by
  have hfactor :
      (23 : ℚ) / 22 * ((4 : ℚ) / 3 * elevenWeightOneEnergyFactor) =
        (722 : ℚ) / 759 := by
    rw [elevenWeightOneEnergyFactor_eq]
    norm_num
  have hstep : ∀ X : ℕ,
      E X ≤ (23 * B) * (X : ℚ) +
        ((722 : ℚ) / 759) *
          ∑ q ∈ primesUpTo X, E (X / (q * q)) := by
    intro X
    have hsplit := elevenQ2_bulk_boundary_sq_le_fourThirdsFrame (I X) (b X)
    have hiScaled :
        (23 : ℚ) / 22 * (I X) ^ 2 ≤
          (722 : ℚ) / 759 *
            ∑ q ∈ primesUpTo X, E (X / (q * q)) := by
      calc
        (23 : ℚ) / 22 * (I X) ^ 2 ≤
            (23 : ℚ) / 22 *
              (((4 : ℚ) / 3 * elevenWeightOneEnergyFactor) *
                ∑ q ∈ primesUpTo X, E (X / (q * q))) :=
          mul_le_mul_of_nonneg_left (hinterior X) (by norm_num)
        _ = (722 : ℚ) / 759 *
              ∑ q ∈ primesUpTo X, E (X / (q * q)) := by
          rw [← mul_assoc, hfactor]
    have hbScaled : 23 * (b X) ^ 2 ≤ 23 * (B * (X : ℚ)) :=
      mul_le_mul_of_nonneg_left (hboundary X) (by norm_num)
    calc
      E X ≤ (I X + b X) ^ 2 := hdecomp X
      _ ≤ (23 : ℚ) / 22 * (I X) ^ 2 + 23 * (b X) ^ 2 := hsplit
      _ ≤ (722 : ℚ) / 759 *
            (∑ q ∈ primesUpTo X, E (X / (q * q))) +
          23 * (B * (X : ℚ)) := add_le_add hiScaled hbScaled
      _ = (23 * B) * (X : ℚ) +
          (722 : ℚ) / 759 *
            ∑ q ∈ primesUpTo X, E (X / (q * q)) := by ring
  have hfixed :
      23 * B + (722 : ℚ) / 759 * ((17457 : ℚ) / 37 * B) ≤
        (17457 : ℚ) / 37 * B := by
    ring_nf
    exact le_rfl
  exact q2EnergyStep_implies_linear_of_fixedPointBudget
    (by positivity : 0 ≤ (17457 : ℚ) / 37 * B)
    (by norm_num : (0 : ℚ) ≤ 722 / 759)
    hfixed hstep

end RHLean.Proof