import RHLean.Proof.PostRootCovarianceUnconditionalDecayScratch
import RHLean.Analysis.RoughWheelFiniteCounting

/-!
# Explicit 210-wheel continuation

The generic finite-wheel transport is already proved in
`PostRootCovarianceUnconditionalDecayScratch`.  This file pushes the concrete
staircase one prime farther: adjoining `7` to the compiled `30`-wheel refines
each surviving band by the same multiplicative finite difference.  No estimate
or restart occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **The wheel keeps iterating.**  Adjoining `7` to the explicit `30`-wheel
four-band representation gives the corresponding eight-band `210`-rough
staircase.  Every old band survives as a parent term and gains exactly one
`1/7` child with the opposite sign. -/
theorem roughMertens_one_eq_twoTenWheel_eightBands (B : ℕ) :
    roughMertens 1 B =
      roughInterval 210 (B / 2) B -
        roughInterval 210 (B / 14) (B / 7) -
        roughInterval 210 (B / 10) (B / 5) +
        roughInterval 210 (B / 70) (B / 35) -
        roughInterval 210 (B / 6) (B / 3) +
        roughInterval 210 (B / 42) (B / 21) +
        roughInterval 210 (B / 30) (B / 15) -
        roughInterval 210 (B / 210) (B / 105) := by
  have hsq6 : Squarefree 6 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).2
        ⟨Nat.prime_two.squarefree, (show Nat.Prime 3 by norm_num).squarefree⟩
  have hsq30 : Squarefree 30 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 5 6)).2
        ⟨(show Nat.Prime 5 by norm_num).squarefree, hsq6⟩
  have hsq210 : Squarefree 210 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 7 30)).2
        ⟨(show Nat.Prime 7 by norm_num).squarefree, hsq30⟩
  have htop :=
    roughInterval_wheel_recursion
      (W := 210) (p := 7) (by norm_num) (by norm_num) hsq210 (B / 2) B
  have hten :=
    roughInterval_wheel_recursion
      (W := 210) (p := 7) (by norm_num) (by norm_num) hsq210 (B / 10) (B / 5)
  have hsix :=
    roughInterval_wheel_recursion
      (W := 210) (p := 7) (by norm_num) (by norm_num) hsq210 (B / 6) (B / 3)
  have hthirty :=
    roughInterval_wheel_recursion
      (W := 210) (p := 7) (by norm_num) (by norm_num) hsq210 (B / 30) (B / 15)
  norm_num at htop hten hsix hthirty
  have htop' :
      roughInterval 30 (B / 2) B =
        roughInterval 210 (B / 2) B -
          roughInterval 210 (B / 14) (B / 7) := by
    simpa [Nat.div_div_eq_div_mul] using htop
  have hten' :
      roughInterval 30 (B / 10) (B / 5) =
        roughInterval 210 (B / 10) (B / 5) -
          roughInterval 210 (B / 70) (B / 35) := by
    simpa [Nat.div_div_eq_div_mul] using hten
  have hsix' :
      roughInterval 30 (B / 6) (B / 3) =
        roughInterval 210 (B / 6) (B / 3) -
          roughInterval 210 (B / 42) (B / 21) := by
    simpa [Nat.div_div_eq_div_mul] using hsix
  have hthirty' :
      roughInterval 30 (B / 30) (B / 15) =
        roughInterval 210 (B / 30) (B / 15) -
          roughInterval 210 (B / 210) (B / 105) := by
    simpa [Nat.div_div_eq_div_mul] using hthirty
  rw [roughMertens_one_eq_thirtyWheel_fourBands B,
    htop', hten', hsix', hthirty']
  ring

/-! ## A second exact overlap already present after adjoining 11

The first 2310 cancellation uses the overlap of the negative 11-band with the
positive 15-band.  There is another opposite-sign overlap: the positive
`(B/154,B/77]` band and the negative `(B/210,B/105]` band share
`(B/154,B/105]`.  Cancelling it before any absolute value is purely algebraic
and removes another `1/165` of normalized band length.
-/

/-- The second 2310 opposite-band overlap cancels exactly, independently of any
ordering or estimate: it is just additivity of the same rough prefix. -/
theorem roughInterval_2310_secondOppositeOverlap (B : ℕ) :
    roughInterval 2310 (B / 154) (B / 77) -
        roughInterval 2310 (B / 210) (B / 105) =
      roughInterval 2310 (B / 105) (B / 77) -
        roughInterval 2310 (B / 210) (B / 154) := by
  unfold roughInterval
  ring

/-- At the continuum-width level the second exact cancellation removes exactly
`1/165` from the unsigned band-length majorant. -/
theorem roughInterval_2310_secondOppositeOverlap_widthGain :
    (((1 / 77 : ℝ) - 1 / 154) + ((1 / 105 : ℝ) - 1 / 210)) =
      (((1 / 77 : ℝ) - 1 / 105) + ((1 / 154 : ℝ) - 1 / 210)) + 1 / 165 := by
  norm_num

/-! ## Full two-overlap 2310 estimate

The earlier quantitative proof spent most of its elaboration time on one large
natural-number `omega` goal containing every quotient endpoint.  The only fact
needed there is the one-dimensional floor estimate below.  Applying it once per
band preserves the exact continuum coefficient and makes the arithmetic layer
linear.
-/

set_option maxRecDepth 10000 in
private theorem roughWheelResidues_card_2310_refined :
    (roughWheelResidues 2310).card = 480 := by
  decide

/-- Two quotient endpoints cost at most one unit beyond their continuum width. -/
private theorem natDivIntervalWidth_le
    (B a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((B / b : ℕ) : ℝ) - ((B / a : ℕ) : ℝ) ≤
      (B : ℝ) / b - (B : ℝ) / a + 1 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hub : ((B / b : ℕ) : ℝ) ≤ (B : ℝ) / b := by
    apply (le_div_iff₀ hbR).2
    exact_mod_cast Nat.div_mul_le_self B b
  have hlowNat : B < B / a * a + a := by
    nlinarith [Nat.mod_add_div B a, Nat.mod_lt B ha]
  have hlowCast :
      (B : ℝ) < ((B / a : ℕ) : ℝ) * (a : ℝ) + (a : ℝ) := by
    exact_mod_cast hlowNat
  have hlow : (B : ℝ) / a < ((B / a : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ haR).2
    nlinarith
  linarith

/-- The covariance prefix and wheel-one prefix have the same physical endpoint. -/
theorem realMertensLength_succ_eq_roughMertens_one_refined (B : ℕ) :
    realMertensLength (B + 1) = (roughMertens 1 B : ℝ) := by
  simp [realMertensLength, realMoebiusStep, roughMertens, roughMoebius]

/-- Adjoining `11` to the exact `210` wheel and cancelling both opposite-sign
overlaps gives the fully reduced sixteen-piece `2310` staircase. -/
theorem roughMertens_one_eq_2310Wheel_twoOverlapsCancelled (B : ℕ) :
    roughMertens 1 B =
      roughInterval 2310 (B / 2) B
      - roughInterval 2310 (B / 15) (B / 11)
      - roughInterval 2310 (B / 14) (B / 7)
      + roughInterval 2310 (B / 105) (B / 77)
      - roughInterval 2310 (B / 10) (B / 5)
      + roughInterval 2310 (B / 110) (B / 55)
      + roughInterval 2310 (B / 70) (B / 35)
      - roughInterval 2310 (B / 770) (B / 385)
      - roughInterval 2310 (B / 6) (B / 3)
      + roughInterval 2310 (B / 66) (B / 33)
      + roughInterval 2310 (B / 42) (B / 21)
      - roughInterval 2310 (B / 462) (B / 231)
      + roughInterval 2310 (B / 30) (B / 22)
      - roughInterval 2310 (B / 330) (B / 165)
      - roughInterval 2310 (B / 210) (B / 154)
      + roughInterval 2310 (B / 2310) (B / 1155) := by
  have hs6 : Squarefree 6 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).2
      ⟨Nat.prime_two.squarefree, (show Nat.Prime 3 by norm_num).squarefree⟩
  have hs30 : Squarefree 30 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 5 6)).2
      ⟨(show Nat.Prime 5 by norm_num).squarefree, hs6⟩
  have hs210 : Squarefree 210 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 7 30)).2
      ⟨(show Nat.Prime 7 by norm_num).squarefree, hs30⟩
  have hs2310 : Squarefree 2310 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 11 210)).2
      ⟨(show Nat.Prime 11 by norm_num).squarefree, hs210⟩
  have hr0 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 2) B
  have hr1 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 14) (B / 7)
  have hr2 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 10) (B / 5)
  have hr3 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 70) (B / 35)
  have hr4 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 6) (B / 3)
  have hr5 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 42) (B / 21)
  have hr6 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 30) (B / 15)
  have hr7 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 210) (B / 105)
  norm_num at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have h0 : roughInterval 210 (B / 2) B =
      roughInterval 2310 (B / 2) B -
        roughInterval 2310 (B / 22) (B / 11) := by
    simpa [Nat.div_div_eq_div_mul] using hr0
  have h1 : roughInterval 210 (B / 14) (B / 7) =
      roughInterval 2310 (B / 14) (B / 7) -
        roughInterval 2310 (B / 154) (B / 77) := by
    simpa [Nat.div_div_eq_div_mul] using hr1
  have h2 : roughInterval 210 (B / 10) (B / 5) =
      roughInterval 2310 (B / 10) (B / 5) -
        roughInterval 2310 (B / 110) (B / 55) := by
    simpa [Nat.div_div_eq_div_mul] using hr2
  have h3 : roughInterval 210 (B / 70) (B / 35) =
      roughInterval 2310 (B / 70) (B / 35) -
        roughInterval 2310 (B / 770) (B / 385) := by
    simpa [Nat.div_div_eq_div_mul] using hr3
  have h4 : roughInterval 210 (B / 6) (B / 3) =
      roughInterval 2310 (B / 6) (B / 3) -
        roughInterval 2310 (B / 66) (B / 33) := by
    simpa [Nat.div_div_eq_div_mul] using hr4
  have h5 : roughInterval 210 (B / 42) (B / 21) =
      roughInterval 2310 (B / 42) (B / 21) -
        roughInterval 2310 (B / 462) (B / 231) := by
    simpa [Nat.div_div_eq_div_mul] using hr5
  have h6 : roughInterval 210 (B / 30) (B / 15) =
      roughInterval 2310 (B / 30) (B / 15) -
        roughInterval 2310 (B / 330) (B / 165) := by
    simpa [Nat.div_div_eq_div_mul] using hr6
  have h7 : roughInterval 210 (B / 210) (B / 105) =
      roughInterval 2310 (B / 210) (B / 105) -
        roughInterval 2310 (B / 2310) (B / 1155) := by
    simpa [Nat.div_div_eq_div_mul] using hr7
  rw [roughMertens_one_eq_twoTenWheel_eightBands, h0, h1, h2, h3, h4, h5, h6, h7]
  unfold roughInterval
  ring

/-- The sixteen quotient widths after both overlap cancellations have their
exact continuum coefficient `1096/1155`, with at most one floor unit per band. -/
private theorem twoOverlap2310_totalWidth_le (B : ℕ) :
    ((B : ℝ) - ((B / 2 : ℕ) : ℝ)) +
      (((B / 11 : ℕ) : ℝ) - ((B / 15 : ℕ) : ℝ)) +
      (((B / 7 : ℕ) : ℝ) - ((B / 14 : ℕ) : ℝ)) +
      (((B / 77 : ℕ) : ℝ) - ((B / 105 : ℕ) : ℝ)) +
      (((B / 5 : ℕ) : ℝ) - ((B / 10 : ℕ) : ℝ)) +
      (((B / 55 : ℕ) : ℝ) - ((B / 110 : ℕ) : ℝ)) +
      (((B / 35 : ℕ) : ℝ) - ((B / 70 : ℕ) : ℝ)) +
      (((B / 385 : ℕ) : ℝ) - ((B / 770 : ℕ) : ℝ)) +
      (((B / 3 : ℕ) : ℝ) - ((B / 6 : ℕ) : ℝ)) +
      (((B / 33 : ℕ) : ℝ) - ((B / 66 : ℕ) : ℝ)) +
      (((B / 21 : ℕ) : ℝ) - ((B / 42 : ℕ) : ℝ)) +
      (((B / 231 : ℕ) : ℝ) - ((B / 462 : ℕ) : ℝ)) +
      (((B / 22 : ℕ) : ℝ) - ((B / 30 : ℕ) : ℝ)) +
      (((B / 165 : ℕ) : ℝ) - ((B / 330 : ℕ) : ℝ)) +
      (((B / 154 : ℕ) : ℝ) - ((B / 210 : ℕ) : ℝ)) +
      (((B / 1155 : ℕ) : ℝ) - ((B / 2310 : ℕ) : ℝ)) ≤
        (1096 / 1155 : ℝ) * B + 16 := by
  have h0 := natDivIntervalWidth_le B 2 1 (by norm_num) (by norm_num)
  have h1 := natDivIntervalWidth_le B 15 11 (by norm_num) (by norm_num)
  have h2 := natDivIntervalWidth_le B 14 7 (by norm_num) (by norm_num)
  have h3 := natDivIntervalWidth_le B 105 77 (by norm_num) (by norm_num)
  have h4 := natDivIntervalWidth_le B 10 5 (by norm_num) (by norm_num)
  have h5 := natDivIntervalWidth_le B 110 55 (by norm_num) (by norm_num)
  have h6 := natDivIntervalWidth_le B 70 35 (by norm_num) (by norm_num)
  have h7 := natDivIntervalWidth_le B 770 385 (by norm_num) (by norm_num)
  have h8 := natDivIntervalWidth_le B 6 3 (by norm_num) (by norm_num)
  have h9 := natDivIntervalWidth_le B 66 33 (by norm_num) (by norm_num)
  have h10 := natDivIntervalWidth_le B 42 21 (by norm_num) (by norm_num)
  have h11 := natDivIntervalWidth_le B 462 231 (by norm_num) (by norm_num)
  have h12 := natDivIntervalWidth_le B 30 22 (by norm_num) (by norm_num)
  have h13 := natDivIntervalWidth_le B 330 165 (by norm_num) (by norm_num)
  have h14 := natDivIntervalWidth_le B 210 154 (by norm_num) (by norm_num)
  have h15 := natDivIntervalWidth_le B 2310 1155 (by norm_num) (by norm_num)
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  linarith

/-- Counting only after both exact opposite-sign overlaps are removed improves
the 2310 leading coefficient from `17648/88935` to `17536/88935`. -/
theorem abs_realMertensLength_succ_le_2310Wheel_twoOverlaps (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (17536 / 88935 : ℝ) * B + 15364 := by
  have h0 := abs_roughInterval_le_density (W := 2310)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  have h1 := abs_roughInterval_le_density (W := 2310)
    (a := B / 15) (b := B / 11) (by norm_num) (by omega)
  have h2 := abs_roughInterval_le_density (W := 2310)
    (a := B / 14) (b := B / 7) (by norm_num) (by omega)
  have h3 := abs_roughInterval_le_density (W := 2310)
    (a := B / 105) (b := B / 77) (by norm_num) (by omega)
  have h4 := abs_roughInterval_le_density (W := 2310)
    (a := B / 10) (b := B / 5) (by norm_num) (by omega)
  have h5 := abs_roughInterval_le_density (W := 2310)
    (a := B / 110) (b := B / 55) (by norm_num) (by omega)
  have h6 := abs_roughInterval_le_density (W := 2310)
    (a := B / 70) (b := B / 35) (by norm_num) (by omega)
  have h7 := abs_roughInterval_le_density (W := 2310)
    (a := B / 770) (b := B / 385) (by norm_num) (by omega)
  have h8 := abs_roughInterval_le_density (W := 2310)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  have h9 := abs_roughInterval_le_density (W := 2310)
    (a := B / 66) (b := B / 33) (by norm_num) (by omega)
  have h10 := abs_roughInterval_le_density (W := 2310)
    (a := B / 42) (b := B / 21) (by norm_num) (by omega)
  have h11 := abs_roughInterval_le_density (W := 2310)
    (a := B / 462) (b := B / 231) (by norm_num) (by omega)
  have h12 := abs_roughInterval_le_density (W := 2310)
    (a := B / 30) (b := B / 22) (by norm_num) (by omega)
  have h13 := abs_roughInterval_le_density (W := 2310)
    (a := B / 330) (b := B / 165) (by norm_num) (by omega)
  have h14 := abs_roughInterval_le_density (W := 2310)
    (a := B / 210) (b := B / 154) (by norm_num) (by omega)
  have h15 := abs_roughInterval_le_density (W := 2310)
    (a := B / 2310) (b := B / 1155) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_refined] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  obtain ⟨h3lo, h3hi⟩ := abs_le.mp h3
  obtain ⟨h4lo, h4hi⟩ := abs_le.mp h4
  obtain ⟨h5lo, h5hi⟩ := abs_le.mp h5
  obtain ⟨h6lo, h6hi⟩ := abs_le.mp h6
  obtain ⟨h7lo, h7hi⟩ := abs_le.mp h7
  obtain ⟨h8lo, h8hi⟩ := abs_le.mp h8
  obtain ⟨h9lo, h9hi⟩ := abs_le.mp h9
  obtain ⟨h10lo, h10hi⟩ := abs_le.mp h10
  obtain ⟨h11lo, h11hi⟩ := abs_le.mp h11
  obtain ⟨h12lo, h12hi⟩ := abs_le.mp h12
  obtain ⟨h13lo, h13hi⟩ := abs_le.mp h13
  obtain ⟨h14lo, h14hi⟩ := abs_le.mp h14
  obtain ⟨h15lo, h15hi⟩ := abs_le.mp h15
  have hwidth := twoOverlap2310_totalWidth_le B
  rw [realMertensLength_succ_eq_roughMertens_one_refined,
    roughMertens_one_eq_2310Wheel_twoOverlapsCancelled]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The second-overlap gain transfers unchanged to the exact post-root Bessel
remainder majorant. -/
theorem postRootCovarianceRemainder_le_2310Wheel_twoOverlapsSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((17536 / 88935 : ℝ) * W + 15364) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_2310Wheel_twoOverlaps W)

end RHLean.Proof
