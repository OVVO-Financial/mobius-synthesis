import Mathlib
import RHLean.Proof.SquareRootBornPostTailLowPrimeCollapse

/-!
# Cofactor monotonicity of the high response

The post-root high response is an honest reciprocal prime prefix.  Increasing
the cofactor can only decrease that prefix.  The shallow plateau in
`squareRootBornPostTailHighResponse` preserves the same monotonicity: below `K`
the response is constant, and across the transition from `a <= K` to `K < b`
the shallow value contains the complete prefix at `K+1`, which dominates the
prefix at `b`.

This is the arithmetic downward-closure fact needed by the descending-pivot
argument.  On a channel-tagged high-seat carrier, any admitted high seat over a
larger cofactor is also admitted over every smaller positive cofactor.  Hence
the reverse four-corner defect cannot occur in the high channel.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The post-root reciprocal prime prefix is antitone in its positive cofactor
argument. -/
theorem squareRootPostRootPrimePrefixCard_antitone
    {R a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    squareRootPostRootPrimePrefixCard R b ≤
      squareRootPostRootPrimePrefixCard R a := by
  classical
  unfold squareRootPostRootPrimePrefixCard
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hRq, hqTop⟩
  have hdiv : squareRootEndpoint R / b ≤ squareRootEndpoint R / a :=
    Nat.div_le_div_left hab ha
  have hmax :
      max R (squareRootEndpoint R / b) ≤
        max R (squareRootEndpoint R / a) :=
    max_le_max_left R hdiv
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hRq, hqTop.trans hmax⟩, hqPrime⟩

/-- **The complete high response is antitone in the cofactor.** -/
theorem squareRootBornPostTailHighResponse_antitone
    {R K j a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    squareRootBornPostTailHighResponse R K j b ≤
      squareRootBornPostTailHighResponse R K j a := by
  unfold squareRootBornPostTailHighResponse
  by_cases hbK : b ≤ K
  · have haK : a ≤ K := hab.trans hbK
    simp [hbK, haK]
  · have hKb : K < b := Nat.lt_of_not_ge hbK
    by_cases haK : a ≤ K
    · have hK1b : K + 1 ≤ b := by omega
      rw [if_neg hbK, if_pos haK]
      have hprefix :
          squareRootPostRootPrimePrefixCard R b ≤
            squareRootPostRootPrimePrefixCard R (K + 1) :=
        squareRootPostRootPrimePrefixCard_antitone
          (Nat.succ_pos K) hK1b
      exact hprefix.trans (Nat.le_add_left _ _)
    · have hKa : K < a := Nat.lt_of_not_ge haK
      rw [if_neg hbK, if_neg haK]
      exact squareRootPostRootPrimePrefixCard_antitone ha hab

/-- Multiplying by a positive factor can only decrease the high response. -/
theorem squareRootBornPostTailHighResponse_mul_le
    (R K j p c : ℕ) (hp : 0 < p) (hc : 0 < c) :
    squareRootBornPostTailHighResponse R K j (p * c) ≤
      squareRootBornPostTailHighResponse R K j c := by
  apply squareRootBornPostTailHighResponse_antitone hc
  exact Nat.le_mul_of_pos_left c hp

end RHLean.Proof
