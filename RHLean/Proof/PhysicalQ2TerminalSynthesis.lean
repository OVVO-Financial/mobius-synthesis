import RHLean.Proof.PhysicalQ2BookkeepingSynthesis
import RHLean.Proof.SquareRootLowPrimeSharpFrameBudget
import RHLean.Analysis.ThreeSlotDegreeOneCriterion

/-!
# Terminal synthesis for the physical q^2 route

After the signed daughter bookkeeping is complete, the remaining physical input
should be one parent recurrence.  This file packages every step *after* that
recurrence, including the fact that the exact daughter cutoff `4*K/q^2` need
not itself be divisible by four.

The only nontrivial endpoint loss is the already-compiled bound

`|M(Y) - M(4*floor(Y/4))| <= 3`.

A weighted square inequality turns this into

`E(Y) <= (5/4) E(4*floor(Y/4)) + 45`.

The odd-prime `q^-2` budget is at most `1/4`.  Hence a factor-four physical
synthesis loss followed by the exact prime-11 energy factor `(19/23)^2` still
has effective recursive coefficient

`(5/4) * 4 * (19/23)^2 * (1/4) = 1805/2116 < 1`.

Thus any complete-cell parent recurrence with precisely that coefficient gives
a linear complete-cell Mertens energy bound.  The existing three-slot endpoint
bridge then yields `RiemannHypothesis`.

Nothing in this file proves the parent recurrence.  Its purpose is to make the
remaining hypothesis irreducible: after this module, no q=2 convention,
least-owner transfer, daughter normalization, floor endpoint, reciprocal-square
budget, strong induction, or terminal RH wiring remains outside the theorem.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## 1. Endpoint transfer for the exact raw q^2 child -/

private theorem mertensSummatoryInt_eq_moebiusPrefix_local (Y : ℕ) :
    mertensSummatoryInt Y = moebiusPrefix Y := by
  rw [mertensSummatoryInt_eq_Icc]
  change moebiusPositivePrefix Y = moebiusPrefix Y
  exact moebiusPositivePrefix_eq_moebiusPrefix Y

/-- The raw daughter energy is controlled by the nearest complete four-cell
energy with a fixed additive loss.  This is just a sharpened Young absorption
of the repository's endpoint error `3`. -/
theorem mertensEnergy_le_five_fourths_completeCell_add_fortyFive (Y : ℕ) :
    mertensEnergy Y ≤
      (5 : ℚ) / 4 * mertensEnergy (4 * (Y / 4)) + 45 := by
  have hz := abs_moebiusPrefix_sub_fourCell_le Y
  obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
  have hzloQ : (-3 : ℚ) ≤
      ((moebiusPrefix Y - moebiusPrefix (4 * (Y / 4)) : ℤ) : ℚ) := by
    exact_mod_cast hzlo
  have hzhiQ :
      ((moebiusPrefix Y - moebiusPrefix (4 * (Y / 4)) : ℤ) : ℚ) ≤ 3 := by
    exact_mod_cast hzhi
  let a : ℚ := (mertensSummatoryInt (4 * (Y / 4)) : ℚ)
  let b : ℚ :=
    ((mertensSummatoryInt Y -
      mertensSummatoryInt (4 * (Y / 4)) : ℤ) : ℚ)
  have hb_lo : (-3 : ℚ) ≤ b := by
    dsimp [b]
    rw [mertensSummatoryInt_eq_moebiusPrefix_local,
      mertensSummatoryInt_eq_moebiusPrefix_local]
    exact hzloQ
  have hb_hi : b ≤ (3 : ℚ) := by
    dsimp [b]
    rw [mertensSummatoryInt_eq_moebiusPrefix_local,
      mertensSummatoryInt_eq_moebiusPrefix_local]
    exact hzhiQ
  have hb : b ^ 2 ≤ 9 := by
    have hprod : 0 ≤ (3 - b) * (b + 3) :=
      mul_nonneg (sub_nonneg.mpr hb_hi) (by linarith)
    nlinarith
  have hsplit : (mertensSummatoryInt Y : ℚ) = a + b := by
    dsimp [a, b]
    push_cast
    ring
  have hyoung : (a + b) ^ 2 ≤ (5 : ℚ) / 4 * a ^ 2 + 5 * b ^ 2 := by
    nlinarith [sq_nonneg (a - 4 * b)]
  unfold mertensEnergy
  rw [hsplit]
  dsimp [a]
  nlinarith

/-! ## 2. The one recurrence that remains to be supplied physically -/

/-- Complete-cell parent recurrence with the exact raw signed Mertens daughters
certified by an earlier layer.  The owner schedule is explicitly odd-prime; q=2 is
base mod-four geometry and is not a physical square-contact owner. -/
def PhysicalCompleteCellOddQ2EnergyStep (C lambda : ℚ) : Prop :=
  ∀ K : ℕ,
    mertensEnergy (4 * K) ≤ C * (K : ℚ) +
      lambda *
        ∑ q ∈ (primesUpTo (4 * K)).erase 2,
          mertensEnergy ((4 * K) / (q * q))

/-- Casted division by four never exceeds exact division in `ℚ`. -/
private theorem natCast_div_four_le (Y : ℕ) :
    ((Y / 4 : ℕ) : ℚ) ≤ (Y : ℚ) / 4 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).2
  exact_mod_cast Nat.div_mul_le_self Y 4

/-- The complete-cell indices underneath all raw odd-prime daughters consume at
most one sixteenth of the parent *physical* scale, equivalently one quarter of
the complete-cell index `K`. -/
private theorem sum_rawDaughter_completeCellIndices_le_quarter
    (K : ℕ) :
    (∑ q ∈ (primesUpTo (4 * K)).erase 2,
      (((4 * K) / (q * q)) / 4 : ℕ) : ℚ) ≤ (K : ℚ) / 4 := by
  let S := (primesUpTo (4 * K)).erase 2
  have hterm :
      (∑ q ∈ S, ((((4 * K) / (q * q)) / 4 : ℕ) : ℚ)) ≤
        (1 : ℚ) / 4 *
          ∑ q ∈ S, (((4 * K) / (q * q) : ℕ) : ℚ) := by
    calc
      (∑ q ∈ S, ((((4 * K) / (q * q)) / 4 : ℕ) : ℚ)) ≤
          ∑ q ∈ S, ((((4 * K) / (q * q) : ℕ) : ℚ) / 4) := by
            apply Finset.sum_le_sum
            intro q hq
            exact natCast_div_four_le ((4 * K) / (q * q))
      _ = (1 : ℚ) / 4 *
          ∑ q ∈ S, (((4 * K) / (q * q) : ℕ) : ℚ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            ring
  have hscale :=
    sum_oddPrimeOwner_squareDilatedCutoffs_le_quarter_parent (4 * K) (4 * K)
  change (∑ q ∈ S, (((4 * K) / (q * q) : ℕ) : ℚ)) ≤
      ((4 * K : ℕ) : ℚ) / 4 at hscale
  have hscale' :
      (∑ q ∈ S, (((4 * K) / (q * q) : ℕ) : ℚ)) ≤ (K : ℚ) := by
    push_cast at hscale
    norm_num at hscale ⊢
    exact hscale
  exact hterm.trans (by nlinarith)

/-- Crude but sufficient owner-count bound.  At positive complete-cell index K,
there are at most `5*K` odd-prime owners in `primesUpTo (4*K)`. -/
private theorem oddPrimeOwner_card_le_five_mul
    {K : ℕ} (hK : 0 < K) :
    ((primesUpTo (4 * K)).erase 2).card ≤ 5 * K := by
  have hsub : (primesUpTo (4 * K)).erase 2 ⊆ Finset.range (4 * K + 1) := by
    intro q hq
    have hqK := (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).2
    exact Finset.mem_range.mpr (by omega)
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_range] at hc
  omega

/-! ## 3. Strong induction: the factor-four / prime-11 recurrence is subcritical -/

/-- **Terminal quantitative engine.**  A factor-four physical parent recurrence
on the exact whole signed daughters implies a linear complete-cell Mertens
energy bound.  The constant is deliberately simple rather than optimized. -/
theorem physicalCompleteCell_fourFrame_elevenStep_implies_linear
    {C : ℚ} (hC : 0 ≤ C)
    (hstep : PhysicalCompleteCellOddQ2EnergyStep C
      (4 * elevenWeightOneEnergyFactor)) :
    ∀ K : ℕ,
      mertensEnergy (4 * K) ≤
        (7 * (C + 225 * (4 * elevenWeightOneEnergyFactor))) * (K : ℚ) := by
  let lambda : ℚ := 4 * elevenWeightOneEnergyFactor
  let A : ℚ := 7 * (C + 225 * lambda)
  have hlambda : 0 ≤ lambda := by
    dsimp [lambda]
    exact mul_nonneg (by norm_num) elevenWeightOneEnergyFactor_nonneg
  have hA : 0 ≤ A := by
    dsimp [A]
    nlinarith [hC, hlambda]
  have hfixed : C + 225 * lambda + ((5 : ℚ) / 16) * lambda * A ≤ A := by
    dsimp [lambda, A]
    rw [elevenWeightOneEnergyFactor_eq]
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
            mertensEnergy ((4 * K) / (q * q)) ≤
              (5 : ℚ) / 4 * A *
                (((4 * K) / (q * q)) / 4 : ℕ) + 45 := by
          intro q hq
          have hqPrime := (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1
          have hqNe2 := (Finset.mem_erase.mp hq).1
          have hq3 : 3 ≤ q := by
            have := hqPrime.two_le
            omega
          let Y : ℕ := (4 * K) / (q * q)
          let J : ℕ := Y / 4
          have hden : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
          have hden4 : 4 < q * q := by nlinarith
          have hYlt : Y < K := by
            dsimp [Y]
            apply (Nat.div_lt_iff_lt_mul hden).2
            nlinarith
          have hJlt : J < K :=
            (Nat.div_le_self Y 4).trans_lt hYlt
          have hcomplete := ih J hJlt
          have hend := mertensEnergy_le_five_fourths_completeCell_add_fortyFive Y
          change mertensEnergy Y ≤ (5 : ℚ) / 4 * A * (J : ℚ) + 45
          calc
            mertensEnergy Y ≤
                (5 : ℚ) / 4 * mertensEnergy (4 * J) + 45 := by
                  simpa [J] using hend
            _ ≤ (5 : ℚ) / 4 * (A * (J : ℚ)) + 45 := by
                  gcongr
            _ = (5 : ℚ) / 4 * A * (J : ℚ) + 45 := by ring
        have hchildren :
            (∑ q ∈ S, mertensEnergy ((4 * K) / (q * q))) ≤
              ((5 : ℚ) / 16 * A + 225) * (K : ℚ) := by
          calc
            (∑ q ∈ S, mertensEnergy ((4 * K) / (q * q))) ≤
                ∑ q ∈ S,
                  ((5 : ℚ) / 4 * A *
                    ((((4 * K) / (q * q)) / 4 : ℕ) : ℚ) + 45) := by
                      apply Finset.sum_le_sum
                      intro q hq
                      exact hchild q hq
            _ = (5 : ℚ) / 4 * A *
                  (∑ q ∈ S,
                    ((((4 * K) / (q * q)) / 4 : ℕ) : ℚ)) +
                  45 * (S.card : ℚ) := by
                    rw [Finset.sum_add_distrib]
                    simp only [Finset.sum_const, nsmul_eq_mul]
                    rw [Finset.mul_sum]
                    ring
            _ ≤ (5 : ℚ) / 4 * A * ((K : ℚ) / 4) +
                  45 * (5 * (K : ℚ)) := by
                    have hscale := sum_rawDaughter_completeCellIndices_le_quarter K
                    have hcardNat := oddPrimeOwner_card_le_five_mul hKpos
                    have hcard : (S.card : ℚ) ≤ 5 * (K : ℚ) := by
                      exact_mod_cast hcardNat
                    have hcoef : 0 ≤ (5 : ℚ) / 4 * A := by positivity
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left hscale hcoef)
                      (mul_le_mul_of_nonneg_left hcard (by norm_num))
            _ = ((5 : ℚ) / 16 * A + 225) * (K : ℚ) := by ring
        have hs := hstep K
        change mertensEnergy (4 * K) ≤ C * (K : ℚ) +
          lambda * ∑ q ∈ S, mertensEnergy ((4 * K) / (q * q)) at hs
        have hweighted := mul_le_mul_of_nonneg_left hchildren hlambda
        calc
          mertensEnergy (4 * K) ≤
              C * (K : ℚ) +
                lambda * ∑ q ∈ S, mertensEnergy ((4 * K) / (q * q)) := hs
          _ ≤ C * (K : ℚ) +
                lambda * (((5 : ℚ) / 16 * A + 225) * (K : ℚ)) :=
                  add_le_add_left hweighted _
          _ = (C + 225 * lambda + (5 : ℚ) / 16 * lambda * A) * (K : ℚ) := by
                ring
          _ ≤ A * (K : ℚ) :=
                mul_le_mul_of_nonneg_right hfixed (by positivity)

/-! ## 4. Linear complete-cell energy is already enough for the protected RH chain -/

private theorem norm_intCast_complex_sq_eq_intCast (z : ℤ) :
    ‖((z : ℤ) : ℂ)‖ ^ 2 = ((z * z : ℤ) : ℝ) := by
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply]

/-- A linear bound on `mertensEnergy (4*K)` implies the exact three-slot energy
criterion, with arbitrarily much exponent slack. -/
theorem threeSlotDegreeOneEnergy_of_completeCellMertensLinear
    {A : ℚ} (hA : 0 ≤ A)
    (hlinear : ∀ K : ℕ, mertensEnergy (4 * K) ≤ A * (K : ℚ)) :
    ThreeSlotDegreeOneEnergyBoundedStatement := by
  intro ε hε
  refine ⟨(A : ℝ), by exact_mod_cast hA, ?_⟩
  intro K
  have hlin := hlinear K
  have hnorm :
      ‖mertensSummatory (4 * K)‖ ^ 2 ≤ (A : ℝ) * (K : ℝ) := by
    rw [mertensSummatory_eq_moebiusPrefix_cast,
      norm_intCast_complex_sq_eq_intCast]
    unfold mertensEnergy at hlin
    rw [mertensSummatoryInt_eq_moebiusPrefix_local] at hlin
    rw [pow_two] at hlin
    exact_mod_cast hlin
  have hscale :
      (K : ℝ) ≤ Real.rpow ((K + 1 : ℕ) : ℝ) (1 + ε) := by
    have hbase : (1 : ℝ) ≤ (((K + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
    have hmono :
        (((K + 1 : ℕ) : ℝ)) ≤
          Real.rpow ((K + 1 : ℕ) : ℝ) (1 + ε) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hbase
          (by linarith : (1 : ℝ) ≤ 1 + ε)
    have hKle : (K : ℝ) ≤ (((K + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.le_succ K
    exact hKle.trans hmono
  rw [← mertensSummatory_four_mul_eq_degreeOne]
  exact hnorm.trans (mul_le_mul_of_nonneg_left hscale (by exact_mod_cast hA))

/-- **Single-hypothesis terminal theorem.**  Once the compensated physical
parent supplies the factor-four / prime-11 complete-cell recurrence on the
whole signed daughters, every remaining step to RH is already formalized. -/
theorem riemannHypothesis_of_physicalCompleteCell_fourFrame_elevenStep
    {C : ℚ} (hC : 0 ≤ C)
    (hstep : PhysicalCompleteCellOddQ2EnergyStep C
      (4 * elevenWeightOneEnergyFactor)) :
    RiemannHypothesis := by
  let A : ℚ := 7 * (C + 225 * (4 * elevenWeightOneEnergyFactor))
  have hA : 0 ≤ A := by
    dsimp [A]
    nlinarith [hC, elevenWeightOneEnergyFactor_nonneg]
  have hlinear : ∀ K : ℕ, mertensEnergy (4 * K) ≤ A * (K : ℚ) := by
    simpa [A] using
      physicalCompleteCell_fourFrame_elevenStep_implies_linear hC hstep
  exact riemannHypothesis_of_threeSlotDegreeOneEnergy
    (threeSlotDegreeOneEnergy_of_completeCellMertensLinear hA hlinear)

end RHLean.Proof
