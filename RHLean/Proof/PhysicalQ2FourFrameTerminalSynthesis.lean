import RHLean.Proof.PhysicalQ2TerminalSynthesis

/-!
# Factor-four terminal synthesis without the selected-11 transfer

The exact signed q^2 daughter dictionary is already compiled in
`PhysicalQ2BookkeepingSynthesis`: only after all least-owner overlaps have been
reassembled, a whole physical daughter is literally the lower-scale Mertens
packet.

This file sharpens the terminal induction so that a factor-four parent
recurrence no longer needs the selected-prime `11` contraction.  The key is to
use the already-compiled sharp odd-owner scale budget

  sum_{q odd prime} 1/q^2 <= 17/72.

At raw daughter cutoffs, the endpoint transfer

  |M(Y) - M(4 floor(Y/4))| <= 3

is absorbed with the `36/35` Young split rather than the older `5/4` split.
Consequently a physical factor-four recurrence has effective recursive
coefficient

  4 * (36/35) * (17/72) = 34/35 < 1.

Thus a genuine factor-four recurrence on the fully signed, fully reassembled
physical daughters is by itself sufficient for linear Mertens energy and RH.
No selected-prime observable, tensor substitution, frame mask, or additional
Mertens hypothesis is used here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem mertensSummatoryInt_eq_moebiusPrefix_fourFrameLocal (Y : ℕ) :
    mertensSummatoryInt Y = moebiusPrefix Y := by
  rw [mertensSummatoryInt_eq_Icc]
  change moebiusPositivePrefix Y = moebiusPrefix Y
  exact moebiusPositivePrefix_eq_moebiusPrefix Y

/-- A sharper endpoint transfer adapted to the `17/72` owner budget. -/
theorem mertensEnergy_le_thirtySix_thirtyFive_completeCell_add_threeTwentyFour
    (Y : ℕ) :
    mertensEnergy Y <=
      (36 : ℚ) / 35 * mertensEnergy (4 * (Y / 4)) + 324 := by
  have hz := abs_moebiusPrefix_sub_fourCell_le Y
  obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
  have hzloQ : (-3 : ℚ) <=
      ((moebiusPrefix Y - moebiusPrefix (4 * (Y / 4)) : ℤ) : ℚ) := by
    exact_mod_cast hzlo
  have hzhiQ :
      ((moebiusPrefix Y - moebiusPrefix (4 * (Y / 4)) : ℤ) : ℚ) <= 3 := by
    exact_mod_cast hzhi
  let a : ℚ := (mertensSummatoryInt (4 * (Y / 4)) : ℚ)
  let b : ℚ :=
    ((mertensSummatoryInt Y -
      mertensSummatoryInt (4 * (Y / 4)) : ℤ) : ℚ)
  have hb_lo : (-3 : ℚ) <= b := by
    dsimp [b]
    rw [mertensSummatoryInt_eq_moebiusPrefix_fourFrameLocal,
      mertensSummatoryInt_eq_moebiusPrefix_fourFrameLocal]
    exact hzloQ
  have hb_hi : b <= (3 : ℚ) := by
    dsimp [b]
    rw [mertensSummatoryInt_eq_moebiusPrefix_fourFrameLocal,
      mertensSummatoryInt_eq_moebiusPrefix_fourFrameLocal]
    exact hzhiQ
  have hb : b ^ 2 <= 9 := by
    have hprod : 0 <= (3 - b) * (b + 3) :=
      mul_nonneg (sub_nonneg.mpr hb_hi) (by linarith)
    nlinarith
  have hsplit : (mertensSummatoryInt Y : ℚ) = a + b := by
    dsimp [a, b]
    push_cast
    ring
  have hyoung :
      (a + b) ^ 2 <= (36 : ℚ) / 35 * a ^ 2 + 36 * b ^ 2 := by
    nlinarith [sq_nonneg (a - 35 * b)]
  unfold mertensEnergy
  rw [hsplit]
  dsimp [a]
  nlinarith

private theorem natCast_div_four_le_fourFrame (Y : ℕ) :
    ((Y / 4 : ℕ) : ℚ) <= (Y : ℚ) / 4 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).2
  exact_mod_cast Nat.div_mul_le_self Y 4

/-- With the sharp odd-prime reciprocal-square budget, complete-cell daughter
indices consume at most `17/72` of the parent complete-cell index. -/
theorem sum_rawDaughter_completeCellIndices_le_seventeen_over_seventy_two
    (K : ℕ) :
    (∑ q ∈ (primesUpTo (4 * K)).erase 2,
      (((4 * K) / (q * q)) / 4 : ℕ) : ℚ) <=
        (17 : ℚ) / 72 * (K : ℚ) := by
  let S := (primesUpTo (4 * K)).erase 2
  have hterm :
      (∑ q ∈ S, ((((4 * K) / (q * q)) / 4 : ℕ) : ℚ)) <=
        (1 : ℚ) / 4 *
          ∑ q ∈ S, (((4 * K) / (q * q) : ℕ) : ℚ) := by
    calc
      (∑ q ∈ S, ((((4 * K) / (q * q)) / 4 : ℕ) : ℚ)) <=
          ∑ q ∈ S, ((((4 * K) / (q * q) : ℕ) : ℚ) / 4) := by
            apply Finset.sum_le_sum
            intro q hq
            exact natCast_div_four_le_fourFrame ((4 * K) / (q * q))
      _ = (1 : ℚ) / 4 *
          ∑ q ∈ S, (((4 * K) / (q * q) : ℕ) : ℚ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            ring
  have hscale :=
    sum_oddPrimeOwner_squareDilatedCutoffs_le_seventeen_over_seventy_two_parent
      (4 * K) (4 * K)
  change (∑ q ∈ S, (((4 * K) / (q * q) : ℕ) : ℚ)) <=
      (17 : ℚ) / 72 * ((4 * K : ℕ) : ℚ) at hscale
  have hscaled :
      (1 : ℚ) / 4 *
          (∑ q ∈ S, (((4 * K) / (q * q) : ℕ) : ℚ)) <=
        (17 : ℚ) / 72 * (K : ℚ) := by
    have hm := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℚ) <= 1 / 4)
    push_cast at hm
    nlinarith
  exact hterm.trans hscaled

private theorem oddPrimeOwner_card_le_five_mul_fourFrame
    {K : ℕ} (hK : 0 < K) :
    ((primesUpTo (4 * K)).erase 2).card <= 5 * K := by
  have hsub : (primesUpTo (4 * K)).erase 2 ⊆ Finset.range (4 * K + 1) := by
    intro q hq
    have hqK := (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).2
    exact Finset.mem_range.mpr (by omega)
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_range] at hc
  omega

/-- **Factor four closes without prime 11.**  Once the physical parent has been
reassembled into whole signed q^2 daughters and obeys a factor-four recurrence,
the sharp `17/72` odd-owner budget makes the recursion strictly subcritical. -/
theorem physicalCompleteCell_fourFrameStep_implies_linear
    {C : ℚ} (hC : 0 <= C)
    (hstep : PhysicalCompleteCellOddQ2EnergyStep C 4) :
    ∀ K : ℕ,
      mertensEnergy (4 * K) <=
        (35 * (C + 6480)) * (K : ℚ) := by
  let A : ℚ := 35 * (C + 6480)
  have hA : 0 <= A := by
    dsimp [A]
    nlinarith
  have hfixed : C + 6480 + (34 : ℚ) / 35 * A <= A := by
    dsimp [A]
    nlinarith
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
      by_cases hK0 : K = 0
      · subst K
        simp [mertensEnergy, mertensSummatoryInt]
      · have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
        let S : Finset ℕ := (primesUpTo (4 * K)).erase 2
        have hchild : ∀ q ∈ S,
            mertensEnergy ((4 * K) / (q * q)) <=
              (36 : ℚ) / 35 * A *
                (((4 * K) / (q * q)) / 4 : ℕ) + 324 := by
          intro q hq
          have hqPrime := (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1
          let Y : ℕ := (4 * K) / (q * q)
          let J : ℕ := Y / 4
          have hden : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
          have hq3 : 3 <= q := by
            have hqNe2 := (Finset.mem_erase.mp hq).1
            have hq2 := hqPrime.two_le
            omega
          have hqSq : 4 < q * q := by
            nlinarith
          have hYlt : Y < K := by
            dsimp [Y]
            apply (Nat.div_lt_iff_lt_mul hden).2
            have hmul : 4 * K < (q * q) * K :=
              Nat.mul_lt_mul_of_pos_right hqSq hKpos
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
          have hJlt : J < K :=
            (Nat.div_le_self Y 4).trans_lt hYlt
          have hcomplete := ih J hJlt
          have hend :=
            mertensEnergy_le_thirtySix_thirtyFive_completeCell_add_threeTwentyFour Y
          change mertensEnergy Y <= (36 : ℚ) / 35 * A * (J : ℚ) + 324
          calc
            mertensEnergy Y <=
                (36 : ℚ) / 35 * mertensEnergy (4 * J) + 324 := by
                  simpa [J] using hend
            _ <= (36 : ℚ) / 35 * (A * (J : ℚ)) + 324 := by
                  gcongr
            _ = (36 : ℚ) / 35 * A * (J : ℚ) + 324 := by ring
        have hchildren :
            (∑ q ∈ S, mertensEnergy ((4 * K) / (q * q))) <=
              ((17 : ℚ) / 70 * A + 1620) * (K : ℚ) := by
          calc
            (∑ q ∈ S, mertensEnergy ((4 * K) / (q * q))) <=
                ∑ q ∈ S,
                  ((36 : ℚ) / 35 * A *
                    ((((4 * K) / (q * q)) / 4 : ℕ) : ℚ) + 324) := by
                      apply Finset.sum_le_sum
                      intro q hq
                      exact hchild q hq
            _ = (36 : ℚ) / 35 * A *
                  (∑ q ∈ S,
                    ((((4 * K) / (q * q)) / 4 : ℕ) : ℚ)) +
                  324 * (S.card : ℚ) := by
                    rw [Finset.sum_add_distrib]
                    simp only [Finset.sum_const, nsmul_eq_mul]
                    rw [Finset.mul_sum]
                    ring
            _ <= (36 : ℚ) / 35 * A *
                    ((17 : ℚ) / 72 * (K : ℚ)) +
                  324 * (5 * (K : ℚ)) := by
                    have hscale :=
                      sum_rawDaughter_completeCellIndices_le_seventeen_over_seventy_two K
                    have hcardNat := oddPrimeOwner_card_le_five_mul_fourFrame hKpos
                    have hcard : (S.card : ℚ) <= 5 * (K : ℚ) := by
                      exact_mod_cast hcardNat
                    have hcoef : 0 <= (36 : ℚ) / 35 * A := by positivity
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left hscale hcoef)
                      (mul_le_mul_of_nonneg_left hcard (by norm_num))
            _ = ((17 : ℚ) / 70 * A + 1620) * (K : ℚ) := by ring
        have hs := hstep K
        change mertensEnergy (4 * K) <= C * (K : ℚ) +
          4 * ∑ q ∈ S, mertensEnergy ((4 * K) / (q * q)) at hs
        have hweighted :=
          mul_le_mul_of_nonneg_left hchildren (by norm_num : (0 : ℚ) <= 4)
        calc
          mertensEnergy (4 * K) <=
              C * (K : ℚ) +
                4 * ∑ q ∈ S, mertensEnergy ((4 * K) / (q * q)) := hs
          _ <= C * (K : ℚ) +
                4 * (((17 : ℚ) / 70 * A + 1620) * (K : ℚ)) :=
                  add_le_add_left hweighted _
          _ = (C + 6480 + (34 : ℚ) / 35 * A) * (K : ℚ) := by ring
          _ <= A * (K : ℚ) :=
                mul_le_mul_of_nonneg_right hfixed (by positivity)

/-- Terminal RH theorem with no selected-prime contraction hypothesis. -/
theorem riemannHypothesis_of_physicalCompleteCell_fourFrameStep
    {C : ℚ} (hC : 0 <= C)
    (hstep : PhysicalCompleteCellOddQ2EnergyStep C 4) :
    RiemannHypothesis := by
  let A : ℚ := 35 * (C + 6480)
  have hA : 0 <= A := by
    dsimp [A]
    nlinarith [hC]
  have hlinear : ∀ K : ℕ, mertensEnergy (4 * K) <= A * (K : ℚ) := by
    simpa [A] using physicalCompleteCell_fourFrameStep_implies_linear hC hstep
  exact riemannHypothesis_of_threeSlotDegreeOneEnergy
    (threeSlotDegreeOneEnergy_of_completeCellMertensLinear hA hlinear)

end RHLean.Proof
