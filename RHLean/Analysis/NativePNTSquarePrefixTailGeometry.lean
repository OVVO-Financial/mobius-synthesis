import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailMass

noncomputable section

namespace RHLean.Analysis

/-- The finite small-quotient fibres are exactly the upper reciprocal interval
`N / M < n <= N`. -/
theorem nativePNTSquarePrefixSmallQuotientFiberSet_eq_Icc
    (N M : ℕ) (hM : 1 ≤ M) :
    nativePNTSquarePrefixSmallQuotientFiberSet N M =
      Finset.Icc (N / M + 1) N := by
  classical
  ext n
  simp only [nativePNTSquarePrefixSmallQuotientFiberSet,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hquot⟩
    have hnpos : 0 < n := by omega
    have hMpos : 0 < M := by omega
    have hNlt : N < M * n :=
      (Nat.div_lt_iff_lt_mul hnpos).1 hquot
    have hNMlt : N / M < n := by
      apply (Nat.div_lt_iff_lt_mul hMpos).2
      simpa [Nat.mul_comm] using hNlt
    exact ⟨by omega, hnN⟩
  · rintro ⟨hNM, hnN⟩
    have hn1 : 1 ≤ n :=
      (Nat.succ_le_succ (Nat.zero_le (N / M))).trans hNM
    have hnpos : 0 < n := by omega
    have hMpos : 0 < M := by omega
    have hNMlt : N / M < n := Nat.lt_of_succ_le hNM
    have hNlt : N < n * M :=
      (Nat.div_lt_iff_lt_mul hMpos).1 hNMlt
    have hquot : N / n < M := by
      apply (Nat.div_lt_iff_lt_mul hnpos).2
      simpa [Nat.mul_comm] using hNlt
    exact ⟨⟨hn1, hnN⟩, hquot⟩

/-- The finite-prefix carry is literally an existing reciprocal LambdaTwo
interval mass. -/
theorem nativeLambdaTwoSmallQuotientRecipMass_eq_interval
    (N M : ℕ) (hM : 1 ≤ M) :
    nativeLambdaTwoSmallQuotientRecipMass N M =
      nativeLambdaTwoRecipIntervalMass (N / M) N := by
  unfold nativeLambdaTwoSmallQuotientRecipMass
    nativeLambdaTwoRecipIntervalMass
  rw [nativePNTSquarePrefixSmallQuotientFiberSet_eq_Icc N M hM]

end RHLean.Analysis