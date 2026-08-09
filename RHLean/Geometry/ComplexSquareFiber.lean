import RHLean.Geometry.ComplexSquareRecovery

namespace RHLean.Geometry

/-- Equality of complex squares determines the original points up to sign. -/
theorem complex_sq_eq_sq_iff_eq_or_eq_neg
    (z w : ℂ) :
    z ^ 2 = w ^ 2 ↔ z = w ∨ z = -w := by
  constructor
  · intro h
    have hfac : (z - w) * (z + w) = 0 := by
      calc
        (z - w) * (z + w) = z ^ 2 - w ^ 2 := by ring
        _ = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp hfac with hsub | hadd
    · left
      linear_combination hsub
    · right
      linear_combination hadd
  · intro h
    rcases h with rfl | hneg
    · rfl
    · rw [hneg]
      ring

/-- The complex squaring map has exactly the sign symmetry. -/
theorem complex_sq_eq_of_eq_or_eq_neg
    {z w : ℂ}
    (h : z = w ∨ z = -w) :
    z ^ 2 = w ^ 2 :=
  (complex_sq_eq_sq_iff_eq_or_eq_neg z w).mpr h

/-- On the positive-real branch, equality of squares implies equality. -/
theorem complex_sq_injective_of_re_pos
    {z w : ℂ}
    (hsq : z ^ 2 = w ^ 2)
    (hz : 0 < z.re)
    (hw : 0 < w.re) :
    z = w := by
  rcases (complex_sq_eq_sq_iff_eq_or_eq_neg z w).mp hsq with h | hneg
  · exact h
  · have hre : z.re = -w.re := by
      simpa using congrArg Complex.re hneg
    linarith

/-- Equality of Fermat points recovers both factor coordinates. -/
theorem fermatPoint_injective
    {c q c' q' : ℝ}
    (h : fermatPoint c q = fermatPoint c' q') :
    c = c' ∧ q = q' := by
  have ha : fermatA c q = fermatA c' q' := by
    simpa [fermatPoint] using congrArg Complex.re h
  have hb : fermatB c q = fermatB c' q' := by
    simpa [fermatPoint] using congrArg Complex.im h
  constructor
  · calc
      c = fermatA c q - fermatB c q := (fermatA_sub_fermatB c q).symm
      _ = fermatA c' q' - fermatB c' q' := by rw [ha, hb]
      _ = c' := fermatA_sub_fermatB c' q'
  · calc
      q = fermatA c q + fermatB c q := (fermatA_add_fermatB c q).symm
      _ = fermatA c' q' + fermatB c' q' := by rw [ha, hb]
      _ = q' := fermatA_add_fermatB c' q'

/-- Positive midpoint branches remove the sign ambiguity of the squared Fermat map. -/
theorem fermatPoint_sq_injective_of_sum_pos
    {c q c' q' : ℝ}
    (hsq : (fermatPoint c q) ^ 2 = (fermatPoint c' q') ^ 2)
    (hpos : 0 < c + q)
    (hpos' : 0 < c' + q') :
    c = c' ∧ q = q' := by
  have hre : 0 < (fermatPoint c q).re := by
    simp only [fermatPoint]
    unfold fermatA
    linarith
  have hre' : 0 < (fermatPoint c' q').re := by
    simp only [fermatPoint]
    unfold fermatA
    linarith
  exact fermatPoint_injective
    (complex_sq_injective_of_re_pos hsq hre hre')

end RHLean.Geometry
