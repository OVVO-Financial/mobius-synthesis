import RHLean.Proof.SquareRootLegalAncestryGramReduction

/-!
# Square-root Mertens endpoint amplification

This module removes the ancestry coordinates from the statement of the open
endpoint estimate.  The resulting proposition is exactly the quantity measured
in the empirical `A_R` scan:

`(M(R^2 - 1) - 1)^2 <= A * R^2 * K`,

for every lower critical envelope `K` below the square-root scale `R`.

The theorem below proves that this scalar endpoint statement is equivalent to
the complete legal root-successor Gram statement, and therefore also equivalent
to the prime-root versus smooth-mass anti-alignment statement.  No estimate is
proved here.
-/

noncomputable section

namespace RHLean.Proof

/-- Scalar endpoint form of the square-root amplification theorem. -/
def SquareRootMertensEndpointAmplificationStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
        A * (R : ℝ) ^ 2 * K

/-- The empirical endpoint amplification statement is exactly the complete legal
ancestry Gram amplification statement. -/
theorem squareRootMertensEndpointAmplification_iff_legalAncestryGram :
    SquareRootMertensEndpointAmplificationStatement ↔
      SquareRootLegalAncestryGramAmplificationStatement := by
  constructor
  · rintro ⟨A, hA, hendpoint⟩
    refine ⟨A, hA, ?_⟩
    intro R K B hR hK hB
    rw [squareRootLegalAncestryGramDefect_eq_mertensNumerator hR hB]
    exact hendpoint R K hR hK
  · rintro ⟨A, hA, hgram⟩
    refine ⟨A, hA, ?_⟩
    intro R K hR hK
    let B := squareRootEndpoint R
    have hB : squareRootEndpoint R ≤ B := by simp [B]
    have h := hgram R K B hR hK hB
    rw [squareRootLegalAncestryGramDefect_eq_mertensNumerator hR hB] at h
    exact h

/-- Final exact reduction: the measured scalar endpoint theorem is equivalent to
the direct prime-root versus smooth-mass anti-alignment theorem. -/
theorem squareRootMertensEndpointAmplification_iff_primeSmoothAntiAlignment :
    SquareRootMertensEndpointAmplificationStatement ↔
      SquareRootPrimeSmoothAntiAlignmentStatement := by
  calc
    SquareRootMertensEndpointAmplificationStatement ↔
        SquareRootLegalAncestryGramAmplificationStatement :=
      squareRootMertensEndpointAmplification_iff_legalAncestryGram
    _ ↔ SquareRootPrimeSmoothAntiAlignmentStatement :=
      squareRootLegalAncestryGramAmplification_iff_primeSmoothAntiAlignment

end RHLean.Proof
