import Mathlib
import RHLean.Proof.NormalizedCofactorTripling

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

/-- The normalized ordered-factor weight is symmetric in its two coordinates. -/
theorem normalizedCofactorWeightRat_comm (c q : ℕ) :
    normalizedCofactorWeightRat c q = normalizedCofactorWeightRat q c := by
  unfold normalizedCofactorWeightRat
  rw [Nat.mul_comm c q]
  ring

/-- Moving the fresh factor `3` to the upper coordinate gives the same `-1/2`
scaling as moving it to the lower coordinate. -/
theorem normalized_tripling_scaling_right_rat
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeightRat c (3 * q) =
      -(1 / 2 : ℚ) * normalizedCofactorWeightRat c q := by
  calc
    normalizedCofactorWeightRat c (3 * q) =
        normalizedCofactorWeightRat (3 * q) c :=
      normalizedCofactorWeightRat_comm c (3 * q)
    _ = -(1 / 2 : ℚ) * normalizedCofactorWeightRat q c := by
      apply normalized_tripling_scaling_rat q c
      simpa [Nat.mul_comm] using h3
    _ = -(1 / 2 : ℚ) * normalizedCofactorWeightRat c q := by
      rw [normalizedCofactorWeightRat_comm q c]

/-- Complex-valued upper-coordinate form of the normalized tripling law. -/
theorem normalized_tripling_scaling_right
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeight c (3 * q) =
      -(1 / 2 : ℂ) * normalizedCofactorWeight c q := by
  simpa [normalizedCofactorWeight] using
    congrArg (fun x : ℚ => (x : ℂ))
      (normalized_tripling_scaling_right_rat c q h3)

/-- Exact two-child normalized cancellation.  A parent ordered factor pair has two
fresh-`3` descendants, according to whether `3` is allocated to the lower or the
upper coordinate.  Each child has weight `-1/2` times the parent. -/
theorem normalized_two_child_tripling_cancellation_rat
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeightRat c q +
        normalizedCofactorWeightRat (3 * c) q +
        normalizedCofactorWeightRat c (3 * q) = 0 := by
  rw [normalized_tripling_scaling_rat c q h3]
  rw [normalized_tripling_scaling_right_rat c q h3]
  ring

/-- Complex-valued exact two-child cancellation. -/
theorem normalized_two_child_tripling_cancellation
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeight c q +
        normalizedCofactorWeight (3 * c) q +
        normalizedCofactorWeight c (3 * q) = 0 := by
  simpa [normalizedCofactorWeight] using
    congrArg (fun x : ℚ => (x : ℂ))
      (normalized_two_child_tripling_cancellation_rat c q h3)

/-- Symmetric multiplicative second difference on the logarithmic factor-ratio
axis.  The two descendants lie at shifts `u-a` and `u+a`. -/
def symmetricMultiplicativeDifference
    (F : ℝ → ℝ) (a u : ℝ) : ℝ :=
  F u - (F (u - a) + F (u + a)) / 2

/-- The symmetric prime-extension difference annihilates constants exactly. -/
@[simp] theorem symmetricMultiplicativeDifference_const
    (b a u : ℝ) :
    symmetricMultiplicativeDifference (fun _ => b) a u = 0 := by
  simp [symmetricMultiplicativeDifference]

/-- The symmetric prime-extension difference annihilates every affine function
of the logarithmic factor-ratio coordinate. -/
@[simp] theorem symmetricMultiplicativeDifference_affine
    (s b a u : ℝ) :
    symmetricMultiplicativeDifference (fun x => s * x + b) a u = 0 := by
  unfold symmetricMultiplicativeDifference
  ring

/-- Weighted two-child packet identity.  The arithmetic scaling converts the
parent and its two descendants into a symmetric second difference of an arbitrary
real packet profile. -/
theorem normalized_tripling_packet_eq_symmetric_difference
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q)
    (F : ℝ → ℝ) (a u : ℝ) :
    (normalizedCofactorWeightRat c q : ℝ) * F u +
        (normalizedCofactorWeightRat (3 * c) q : ℝ) * F (u - a) +
        (normalizedCofactorWeightRat c (3 * q) : ℝ) * F (u + a) =
      (normalizedCofactorWeightRat c q : ℝ) *
        symmetricMultiplicativeDifference F a u := by
  rw [normalized_tripling_scaling_rat c q h3]
  rw [normalized_tripling_scaling_right_rat c q h3]
  unfold symmetricMultiplicativeDifference
  push_cast
  ring

/-- Consequently, every complete fresh-`3` parent/two-child cell annihilates an
affine coherent profile on the log-factor axis. -/
theorem normalized_tripling_packet_affine_eq_zero
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q)
    (s b a u : ℝ) :
    (normalizedCofactorWeightRat c q : ℝ) * (s * u + b) +
        (normalizedCofactorWeightRat (3 * c) q : ℝ) *
          (s * (u - a) + b) +
        (normalizedCofactorWeightRat c (3 * q) : ℝ) *
          (s * (u + a) + b) = 0 := by
  rw [normalized_tripling_packet_eq_symmetric_difference c q h3
    (fun x => s * x + b) a u]
  simp

end RHLean.Proof
