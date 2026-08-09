import Mathlib
import RHLean.Analysis.TwoABPrimeDilation
import RHLean.Proof.SurvivorZeroMode

/-!
# Large-prime survivor root boundary

For the concrete cutoff `Lambda = 16`, the large-prime part of the survivor
agrees with the raw product-cutoff prime-dilation fibre away from a fixed-width
neighborhood of the square root.

Write `R=t+1` and `X_t=R^2-1`.  If `t>=55`, `q>=t+9=R+8`, and
`c*q<=X_t`, then the product cutoff forces `c<=t-7=R-8`.  Hence

```text
q^2-c^2 >= (R+8)^2-(R-8)^2 = 32R > 32t.
```

Thus the height test for `Lambda=16` is automatic.  This is an exact finite
root-boundary theorem: only the first seven integer offsets above `R` can differ
from the raw prime-dilation fibre.  No prime-density estimate or cancellation
bound is used.
-/

noncomputable section

namespace RHLean.Proof

/-- The product cutoff forces a cofactor at least eight steps below the square
root once the distinguished prime is eight steps above it. -/
theorem survivor_largePrime_cofactor_le_t_sub_seven
    (t c q : ℕ) (ht : 55 ≤ t) (hq : t + 9 ≤ q)
    (hprod : c * q ≤ RHLean.Analysis.squarePrefixEndpoint t) :
    c ≤ t - 7 := by
  by_contra hnot
  have hc : t - 6 ≤ c := by omega
  have hlower : (t - 6) * (t + 9) ≤ c * q :=
    Nat.mul_le_mul hc hq
  have hsub6 : t - 6 + 6 = t := by omega
  have hendPositive : 0 < (t + 1) ^ 2 := by positivity
  have hendPos : 1 ≤ (t + 1) ^ 2 := by omega
  have hend : RHLean.Analysis.squarePrefixEndpoint t + 1 = (t + 1) ^ 2 := by
    unfold RHLean.Analysis.squarePrefixEndpoint
    exact Nat.sub_add_cancel hendPos
  have hpoly :
      RHLean.Analysis.squarePrefixEndpoint t < (t - 6) * (t + 9) := by
    nlinarith [hsub6, hend]
  exact (not_lt_of_ge hprod) (hpoly.trans_le hlower)

/-- For `Lambda=16`, the high-height inequality is automatic outside the first
seven integer offsets above the square root. -/
theorem survivor_sixteen_height_automatic_of_far_largePrime
    (t c q : ℕ) (ht : 55 ≤ t) (hq : t + 9 ≤ q)
    (hprod : c * q ≤ RHLean.Analysis.squarePrefixEndpoint t) :
    2 * (16 : ℝ) * (t : ℝ) <
      |(q : ℝ) ^ 2 - (c : ℝ) ^ 2| := by
  have hcNat : c ≤ t - 7 :=
    survivor_largePrime_cofactor_le_t_sub_seven t c q ht hq hprod
  have hsub7 : t - 7 + 7 = t := by omega
  have hcReal : (c : ℝ) ≤ (t - 7 : ℕ) := by exact_mod_cast hcNat
  have hsub7Real : ((t - 7 : ℕ) : ℝ) + 7 = (t : ℝ) := by
    exact_mod_cast hsub7
  have hqReal : (t : ℝ) + 9 ≤ (q : ℝ) := by exact_mod_cast hq
  have hqNonneg : 0 ≤ (q : ℝ) := by positivity
  have hcNonneg : 0 ≤ (c : ℝ) := by positivity
  have ht9Nonneg : 0 ≤ (t : ℝ) + 9 := by positivity
  have ht7Nonneg : 0 ≤ ((t - 7 : ℕ) : ℝ) := by positivity
  have hqSq : ((t : ℝ) + 9) ^ 2 ≤ (q : ℝ) ^ 2 := by
    have hmul :
        0 ≤ ((q : ℝ) - ((t : ℝ) + 9)) * ((q : ℝ) + ((t : ℝ) + 9)) :=
      mul_nonneg (sub_nonneg.mpr hqReal) (add_nonneg hqNonneg ht9Nonneg)
    nlinarith
  have hcSq : (c : ℝ) ^ 2 ≤ ((t - 7 : ℕ) : ℝ) ^ 2 := by
    have hmul :
        0 ≤ (((t - 7 : ℕ) : ℝ) - (c : ℝ)) *
          (((t - 7 : ℕ) : ℝ) + (c : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hcReal) (add_nonneg ht7Nonneg hcNonneg)
    nlinarith
  have hgap :
      32 * (t : ℝ) < (q : ℝ) ^ 2 - (c : ℝ) ^ 2 := by
    nlinarith
  have hbaseNonneg : 0 ≤ 32 * (t : ℝ) := by positivity
  have hgapNonneg : 0 ≤ (q : ℝ) ^ 2 - (c : ℝ) ^ 2 :=
    hbaseNonneg.trans (le_of_lt hgap)
  rw [abs_of_nonneg hgapNonneg]
  norm_num at hgap ⊢
  exact hgap

/-- Outside the fixed root neighborhood, the `Lambda=16` survivor predicate is
exactly canonical source data plus the product cutoff; the height condition
contributes no further restriction. -/
theorem isSurvivorZeroModePair_sixteen_iff_source_and_product_of_far_largePrime
    (t c q : ℕ) (ht : 55 ≤ t) (hq : t + 9 ≤ q) :
    IsSurvivorZeroModePair 16 t c q ↔
      CanonicalGapAncestryBridge.CanonicalSourceData q c ∧
        c * q ≤ RHLean.Analysis.squarePrefixEndpoint t := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hsource, hprod⟩
    exact ⟨hsource, hprod,
      survivor_sixteen_height_automatic_of_far_largePrime t c q ht hq hprod⟩

end RHLean.Proof
