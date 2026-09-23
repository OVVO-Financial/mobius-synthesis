import Mathlib
import RHLean.Proof.SquareRootLowPrimeTSectorQ2Renormalization
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux

/-!
# Sharper finite daughter budgets and admissible frame losses

The previous unit daughter budget is deliberately coarse. A finite odd-number
telescope gives budget `1/2` for all prime owners and `1/4` when owner `2` is
absent. Consequently frame loss `2` on all primes, or `4` on odd primes, still
closes the same linear-energy induction, including a global boundary term.

These are conditional induction theorems. They do not prove the physical frame
estimate or identify the reduced residual with the full degree-one packet.
The final packing lemmas below do prove that the actual saturated second-contact
old-owner fibres exclude `2` once the reassembled child owner is prime.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Proof
open RHLean.Arithmetic RHLean.Analysis
attribute [local instance] Classical.propDecidable

/-- Elementary odd-number telescope; the denominator comparison has slack one. -/
theorem oddReciprocalSquareTerm_le_telescope (k : ℕ) :
    (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2 ≤
      1 / (4 * ((k : ℚ) + 1)) - 1 / (4 * ((k : ℚ) + 2)) := by
  have h1 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) < (k : ℚ) + 2 := by positivity
  rw [show (1 : ℚ) / (4 * ((k : ℚ) + 1)) -
      1 / (4 * ((k : ℚ) + 2)) =
      1 / (4 * ((k : ℚ) + 1) * ((k : ℚ) + 2)) by
    field_simp
    ring]
  apply (div_le_div_iff₀ (by positivity)
    (by positivity : (0 : ℚ) < 4 * ((k : ℚ) + 1) * ((k : ℚ) + 2))).2
  push_cast
  nlinarith

/-- A finite telescope, with its endpoint retained. -/
theorem sum_oddReciprocalSquares_le_quarter_sub (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2) ≤
      1 / 4 - 1 / (4 * ((N : ℚ) + 1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (1 / 4 - 1 / (4 * ((N : ℚ) + 1))) +
          (1 / (4 * ((N : ℚ) + 1)) - 1 / (4 * ((N : ℚ) + 2))) :=
        add_le_add ih (oddReciprocalSquareTerm_le_telescope N)
      _ = 1 / 4 - 1 / (4 * ((((N + 1 : ℕ) : ℚ)) + 1)) := by
        push_cast
        ring

private theorem oddPrimes_subset_oddImage (N : ℕ) :
    (primesUpTo N).erase 2 ⊆
      (Finset.range N).image (fun k : ℕ => (2 * k + 3 : ℕ)) := by
  intro q hq
  have hdata := mem_primesUpTo.mp (Finset.mem_erase.mp hq).2
  have hqN := hdata.2
  have hq2 := hdata.1.two_le
  have hne := (Finset.mem_erase.mp hq).1
  obtain ⟨k, hk⟩ := hdata.1.odd_of_ne_two hne
  have hk1 : 1 ≤ k := by omega
  refine Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
  omega

/-- The actual odd-prime schedule costs at most a quarter of its parent scale. -/
theorem oddPrimeOwnerReciprocalSquareBudget_le_quarter (N : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2, (1 : ℚ) / (q : ℚ) ^ 2) ≤ 1 / 4 := by
  have hsum :
      (∑ q ∈ (primesUpTo N).erase 2, (1 : ℚ) / (q : ℚ) ^ 2) ≤
        ∑ q ∈ (Finset.range N).image (fun k : ℕ => (2 * k + 3 : ℕ)),
          (1 : ℚ) / (q : ℚ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (oddPrimes_subset_oddImage N) ?_
    intro q _hqImage _hqOld
    positivity
  rw [Finset.sum_image] at hsum
  · have h := sum_oddReciprocalSquares_le_quarter_sub N
    have hp : (0 : ℚ) ≤ 1 / (4 * ((N : ℚ) + 1)) := by positivity
    linarith
  · intro a _ha b _hb hab
    have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
    omega

/-- Prime `2` costs one quarter; all odd primes together cost at most another. -/
theorem primeOwnerReciprocalSquareBudget_le_half (N : ℕ) :
    primeOwnerReciprocalSquareBudget N ≤ 1 / 2 := by
  have h := oddPrimeOwnerReciprocalSquareBudget_le_quarter N
  unfold primeOwnerReciprocalSquareBudget
  by_cases htwo : 2 ∈ primesUpTo N
  · have hs := Finset.sum_erase_add (s := primesUpTo N)
      (f := fun q => (1 : ℚ) / (q : ℚ) ^ 2) htwo
    have hs' :
        (∑ q ∈ (primesUpTo N).erase 2, (1 : ℚ) / (q : ℚ) ^ 2) + 1 / 4 =
          ∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2 := by
      norm_num at hs ⊢
      exact hs
    calc
      (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) =
          (∑ q ∈ (primesUpTo N).erase 2, (1 : ℚ) / (q : ℚ) ^ 2) + 1 / 4 := hs'.symm
      _ ≤ 1 / 4 + 1 / 4 := add_le_add_right h _
      _ = 1 / 2 := by norm_num
  · have heq : (primesUpTo N).erase 2 = primesUpTo N :=
      Finset.erase_eq_of_notMem htwo
    calc
      (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) =
          ∑ q ∈ (primesUpTo N).erase 2, (1 : ℚ) / (q : ℚ) ^ 2 := by rw [heq]
      _ ≤ 1 / 4 := h
      _ ≤ 1 / 2 := by norm_num

/-- The daughter estimate with the reciprocal-square budget kept explicit. -/
theorem sum_squareDilatedCutoffs_le_scale_mul_budget
    (S : Finset ℕ) (X : ℕ) (hS : ∀ q ∈ S, q.Prime) :
    (∑ q ∈ S, ((X / (q * q) : ℕ) : ℚ)) ≤
      (X : ℚ) * ∑ q ∈ S, (1 : ℚ) / (q : ℚ) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hp := hS q hq
  have hmul : (((X / (q * q) : ℕ) : ℚ) * ((q * q : ℕ) : ℚ)) ≤ (X : ℚ) := by
    exact_mod_cast Nat.div_mul_le_self X (q * q)
  have hpos : (0 : ℚ) < ((q * q : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos hp.pos hp.pos
  have hdiv := (le_div_iff₀ hpos).2 hmul
  simpa [Nat.cast_mul, pow_two, div_eq_mul_inv] using hdiv

/-- A half-parent budget on the literal integer daughter cutoffs. -/
theorem sum_primeOwner_squareDilatedCutoffs_le_half_parent (N X : ℕ) :
    (∑ q ∈ primesUpTo N, ((X / (q * q) : ℕ) : ℚ)) ≤ (X : ℚ) / 2 := by
  have h := sum_squareDilatedCutoffs_le_scale_mul_budget (primesUpTo N) X
    (fun q hq => (mem_primesUpTo.mp hq).1)
  have hb := mul_le_mul_of_nonneg_left
    (primeOwnerReciprocalSquareBudget_le_half N) (by positivity : (0 : ℚ) ≤ X)
  change (X : ℚ) * (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) ≤ _ at hb
  nlinarith

/-- A quarter-parent budget when the owner schedule excludes `2`. -/
theorem sum_oddPrimeOwner_squareDilatedCutoffs_le_quarter_parent (N X : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2, ((X / (q * q) : ℕ) : ℚ)) ≤ (X : ℚ) / 4 := by
  have h := sum_squareDilatedCutoffs_le_scale_mul_budget ((primesUpTo N).erase 2) X
    (fun q hq => (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1)
  have hb := mul_le_mul_of_nonneg_left
    (oddPrimeOwnerReciprocalSquareBudget_le_quarter N)
    (by positivity : (0 : ℚ) ≤ X)
  nlinarith

/-- In the actual reassembly an old owner is strictly above the prime child
owner. Hence prime `2` is absent from every genuine old-owner collision fibre. -/
theorem lowWheelFrozenSecondContactOldOwnerFiber_subset_oddPrimeOwners
    {R r d : ℕ} (hr : r.Prime) :
    lowWheelFrozenSecondContactOldOwnerFiber R r d ⊆
      (primesUpTo (R - 1)).erase 2 := by
  intro q hq
  have hdata := Finset.mem_filter.mp hq
  have hrq : r < q := hdata.2.1
  apply Finset.mem_erase.mpr
  refine ⟨?_, hdata.1⟩
  intro hq2
  subst q
  have hr2 := hr.two_le
  omega

/-- The intrinsic `q^-2` mass of every genuine fixed-child-owner collision fibre
is at most `1/4`, not merely the coarse unit bound. -/
theorem lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass_le_quarter
    {R r d : ℕ} (hr : r.Prime) :
    lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass R r d ≤ 1 / 4 := by
  unfold lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass
  have hsum :
      (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
          (1 : ℚ) / (q : ℚ) ^ 2) ≤
        ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          (1 : ℚ) / (q : ℚ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (lowWheelFrozenSecondContactOldOwnerFiber_subset_oddPrimeOwners hr) ?_
    intro q _hqNew _hqOld
    positivity
  exact hsum.trans (oddPrimeOwnerReciprocalSquareBudget_le_quarter (R - 1))

/-- The same quarter budget in the literal daughter-cutoff units used by the
q-square renormalization engine. -/
theorem sum_oldOwnerFiber_squareDilatedCutoffs_le_quarter_parent
    {R r d X : ℕ} (hr : r.Prime) :
    (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
      ((X / (q * q) : ℕ) : ℚ)) ≤ (X : ℚ) / 4 := by
  calc
    (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
        ((X / (q * q) : ℕ) : ℚ)) ≤
      ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        ((X / (q * q) : ℕ) : ℚ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (lowWheelFrozenSecondContactOldOwnerFiber_subset_oddPrimeOwners hr) ?_
          intro q _hqNew _hqOld
          positivity
    _ ≤ (X : ℚ) / 4 :=
      sum_oddPrimeOwner_squareDilatedCutoffs_le_quarter_parent (R - 1) X

/-- The induction depends on `lambda * rho`, not on `lambda` alone. -/
theorem q2EnergyStep_implies_linear_of_ownerScaleBudget
    {E : ℕ → ℚ} {owners : ℕ → Finset ℕ} {C lambda rho K : ℚ}
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hK : 0 ≤ K) (hlambda : 0 ≤ lambda)
    (hscale : ∀ X, (∑ q ∈ owners X, ((X / (q * q) : ℕ) : ℚ)) ≤ rho * (X : ℚ))
    (hfixed : C + lambda * rho * K ≤ K)
    (hstep : ∀ X, E X ≤ C * (X : ℚ) + lambda * ∑ q ∈ owners X, E (X / (q * q))) :
    ∀ X, E X ≤ K * (X : ℚ) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hX : X = 0
    · subst X
      have hempty : owners 0 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        have hp := mem_primesUpTo.mp (howners 0 hq)
        have := hp.1.two_le
        omega
      simpa [hempty] using hstep 0
    · have hchildren : (∑ q ∈ owners X, E (X / (q * q))) ≤
          K * (∑ q ∈ owners X, ((X / (q * q) : ℕ) : ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro q hq
        have hp := (mem_primesUpTo.mp (howners X hq)).1
        exact ih (X / (q * q))
          (Nat.div_lt_self (Nat.pos_of_ne_zero hX) (by nlinarith [hp.two_le]))
      have hchildren' := hchildren.trans (mul_le_mul_of_nonneg_left (hscale X) hK)
      have hweighted := mul_le_mul_of_nonneg_left hchildren' hlambda
      have hfixed' := mul_le_mul_of_nonneg_right hfixed (by positivity : (0 : ℚ) ≤ X)
      have hs := hstep X
      nlinarith

/-- A factor-two frame loss is sufficient on the complete prime schedule. -/
theorem elevenQ2_bulk_boundary_twoFrame_implies_linear
    {E I b : ℕ → ℚ} {B : ℚ}
    (hB : 0 ≤ B)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤
      2 * elevenWeightOneEnergyFactor * ∑ q ∈ primesUpTo X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ (48 * B) * (X : ℚ) := by
  apply q2EnergyStep_implies_linear_of_ownerScaleBudget
    (owners := primesUpTo) (C := 4 * B)
    (lambda := (8 : ℚ) / 3 * elevenWeightOneEnergyFactor) (rho := 1 / 2)
    (fun _ => Finset.Subset.refl _) (by nlinarith [hB])
      (mul_nonneg (by norm_num) elevenWeightOneEnergyFactor_nonneg)
  · intro X
    simpa [div_eq_mul_inv, mul_comm] using
      sum_primeOwner_squareDilatedCutoffs_le_half_parent X X
  · rw [elevenWeightOneEnergyFactor_eq]
    nlinarith
  · intro X
    have hi := hinterior X
    have hb := hboundary X
    have he := hdecomp X
    have hy : (I X + b X) ^ 2 ≤ (4 : ℚ) / 3 * (I X) ^ 2 + 4 * (b X) ^ 2 := by
      nlinarith [sq_nonneg (I X - 3 * b X)]
    nlinarith

/-- A factor-four frame loss is sufficient if the physical schedule has no
owner `2`. -/
theorem elevenQ2_bulk_boundary_fourFrame_oddOwners_implies_linear
    {E I b : ℕ → ℚ} {B : ℚ}
    (hB : 0 ≤ B)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤
      4 * elevenWeightOneEnergyFactor *
        ∑ q ∈ (primesUpTo X).erase 2, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ (48 * B) * (X : ℚ) := by
  apply q2EnergyStep_implies_linear_of_ownerScaleBudget
    (owners := fun X => (primesUpTo X).erase 2) (C := 4 * B)
    (lambda := (16 : ℚ) / 3 * elevenWeightOneEnergyFactor) (rho := 1 / 4)
    (fun _ => Finset.erase_subset _ _) (by nlinarith [hB])
      (mul_nonneg (by norm_num) elevenWeightOneEnergyFactor_nonneg)
  · intro X
    simpa [div_eq_mul_inv, mul_comm] using
      sum_oddPrimeOwner_squareDilatedCutoffs_le_quarter_parent X X
  · rw [elevenWeightOneEnergyFactor_eq]
    nlinarith
  · intro X
    have hi := hinterior X
    have hb := hboundary X
    have he := hdecomp X
    have hy : (I X + b X) ^ 2 ≤ (4 : ℚ) / 3 * (I X) ^ 2 + 4 * (b X) ^ 2 := by
      nlinarith [sq_nonneg (I X - 3 * b X)]
    nlinarith

/-! ## A one-term sharpening admits a six-frame interior

The `1/4` odd-owner budget above spends the telescoping majorant already at the
first odd integer.  Keeping the exact `1/3^2 = 1/9` term and telescoping only
from `5` onward saves exactly `1/72`, giving the elementary finite bound
`17/72`.  This small improvement is enough to admit a frame loss of `6` after
the exact `(19/23)^2` prime-11 factor.
-/

/-- Exact first-term refinement of the odd reciprocal-square telescope. -/
theorem sum_oddReciprocalSquares_le_seventeen_over_seventy_two_sub (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2) ≤
        17 / 72 - 1 / (4 * ((N : ℚ) + 2)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (17 / 72 - 1 / (4 * ((N : ℚ) + 2))) +
          (1 / (4 * ((((N + 1 : ℕ) : ℚ)) + 1)) -
            1 / (4 * ((((N + 1 : ℕ) : ℚ)) + 2))) :=
        add_le_add ih (oddReciprocalSquareTerm_le_telescope (N + 1))
      _ = 17 / 72 - 1 / (4 * ((((N + 1 : ℕ) : ℚ)) + 2)) := by
        push_cast
        ring

/-- Every finite odd-integer reciprocal-square prefix from `3` onward is at
most `17/72`; no infinite series evaluation is used. -/
theorem sum_oddReciprocalSquares_le_seventeen_over_seventy_two (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2) ≤ 17 / 72 := by
  cases N with
  | zero => norm_num
  | succ N =>
      have h := sum_oddReciprocalSquares_le_seventeen_over_seventy_two_sub N
      have hp : (0 : ℚ) ≤ 1 / (4 * ((N : ℚ) + 2)) := by positivity
      nlinarith

/-- Sharpened finite odd-prime owner budget. -/
theorem oddPrimeOwnerReciprocalSquareBudget_le_seventeen_over_seventy_two
    (N : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2, (1 : ℚ) / (q : ℚ) ^ 2) ≤ 17 / 72 := by
  have hsum :
      (∑ q ∈ (primesUpTo N).erase 2, (1 : ℚ) / (q : ℚ) ^ 2) ≤
        ∑ q ∈ (Finset.range N).image (fun k : ℕ => (2 * k + 3 : ℕ)),
          (1 : ℚ) / (q : ℚ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (oddPrimes_subset_oddImage N) ?_
    intro q _hqImage _hqOld
    positivity
  rw [Finset.sum_image] at hsum
  · exact hsum.trans (sum_oddReciprocalSquares_le_seventeen_over_seventy_two N)
  · intro a _ha b _hb hab
    have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
    omega

/-- The literal odd-prime daughter cutoffs consume at most `17/72` of the
parent scale. -/
theorem sum_oddPrimeOwner_squareDilatedCutoffs_le_seventeen_over_seventy_two_parent
    (N X : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2, ((X / (q * q) : ℕ) : ℚ)) ≤
      (17 / 72 : ℚ) * (X : ℚ) := by
  have h := sum_squareDilatedCutoffs_le_scale_mul_budget ((primesUpTo N).erase 2) X
    (fun q hq => (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1)
  have hb := mul_le_mul_of_nonneg_left
    (oddPrimeOwnerReciprocalSquareBudget_le_seventeen_over_seventy_two N)
    (by positivity : (0 : ℚ) ≤ X)
  nlinarith

/-- **Frame six is sufficient on the odd-owner schedule.**  The stronger
`17/72` scale budget leaves enough margin after the exact prime-11 factor even
when the globally compensated signed interior loses a factor `6`.  A `60/59`
Young split keeps the boundary inside the recurrence, and `3600 * B * X` is an
explicit (deliberately non-sharp) linear envelope.

This remains a conditional induction theorem: it does not assert the missing
physical frame-six inequality. -/
theorem elevenQ2_bulk_boundary_sixFrame_oddOwners_implies_linear
    {E I b : ℕ → ℚ} {B : ℚ}
    (hB : 0 ≤ B)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤
      6 * elevenWeightOneEnergyFactor *
        ∑ q ∈ (primesUpTo X).erase 2, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ (3600 * B) * (X : ℚ) := by
  apply q2EnergyStep_implies_linear_of_ownerScaleBudget
    (owners := fun X => (primesUpTo X).erase 2)
    (C := 60 * B)
    (lambda := (360 : ℚ) / 59 * elevenWeightOneEnergyFactor)
    (rho := 17 / 72)
    (K := 3600 * B)
    (fun _ => Finset.erase_subset _ _)
    (by nlinarith [hB])
    (mul_nonneg (by norm_num) elevenWeightOneEnergyFactor_nonneg)
  · intro X
    exact sum_oddPrimeOwner_squareDilatedCutoffs_le_seventeen_over_seventy_two_parent X X
  · rw [elevenWeightOneEnergyFactor_eq]
    nlinarith [hB]
  · intro X
    have hi := hinterior X
    have hb := hboundary X
    have he := hdecomp X
    have hy :
        (I X + b X) ^ 2 ≤
          (60 : ℚ) / 59 * (I X) ^ 2 + 60 * (b X) ^ 2 := by
      nlinarith [sq_nonneg (I X - 59 * b X)]
    nlinarith

end RHLean.Proof