import Mathlib
import RHLean.Arithmetic.PrimesUpToFrontier
import RHLean.Proof.SurvivorDyadicStaticCancellation

/-!
# Survivor prime-face frontier cancellation

This module lifts the static parent/child cancellation to the complete finite
prime-face cube below a fixed distinguished prime `q`.

For a face `u` of primes below `q`, put `c = prod u`.  The square-prefix product
cutoff is downward closed in `u`.  The transport-side high condition

```text
2 Lambda n < q^2 - c^2
```

is also downward closed, as is the complementary below-smooth condition

```text
c^2 - q^2 <= 2 Lambda n.
```

For nonnegative `Lambda`, the full high selector satisfies the exact indicator
identity

```text
1_high = 1_transport + 1_product - 1_belowSmooth.
```

Consequently its alternating Boolean-cube mass is a signed combination of
three downward-closed alternating masses.  Applying the repository's exact
truncated-cube cancellation theorem to each term collapses the entire interior
cube to three first-failure frontiers at any selected prime coordinate.

This is exact sign cancellation.  No frontier cardinality estimate, random-sign
model, or analytic power saving is used.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Prime coordinates available to a canonical cofactor below distinguished
prime `q`. -/
def survivorPrimeFaceAmbient (q : ℕ) : Finset ℕ :=
  primesUpTo (q - 1)

/-- Square-prefix product cutoff on a prime face. -/
def survivorPrimeFaceProductPrefix
    (n q : ℕ) (u : Finset ℕ) : Prop :=
  u ⊆ survivorPrimeFaceAmbient q ∧
    primeFaceProduct u * q ≤ RHLean.Analysis.squarePrefixEndpoint n

/-- Transport-side high support. -/
def survivorPrimeFaceTransportPrefix
    (Λ : ℝ) (n q : ℕ) (u : Finset ℕ) : Prop :=
  survivorPrimeFaceProductPrefix n q u ∧
    2 * Λ * (n : ℝ) <
      (q : ℝ) ^ 2 - (primeFaceProduct u : ℝ) ^ 2

/-- Product-prefix points that have not yet entered the smooth-side high tail. -/
def survivorPrimeFaceBelowSmoothPrefix
    (Λ : ℝ) (n q : ℕ) (u : Finset ℕ) : Prop :=
  survivorPrimeFaceProductPrefix n q u ∧
    (primeFaceProduct u : ℝ) ^ 2 - (q : ℝ) ^ 2 ≤
      2 * Λ * (n : ℝ)

/-- Full absolute-height selector on the product prefix. -/
def survivorPrimeFaceHigh
    (Λ : ℝ) (n q : ℕ) (u : Finset ℕ) : Prop :=
  survivorPrimeFaceProductPrefix n q u ∧
    2 * Λ * (n : ℝ) <
      |(q : ℝ) ^ 2 - (primeFaceProduct u : ℝ) ^ 2|

/-- Integer-valued proposition indicator.  Keeping the classical decision
inside this noncomputable definition avoids placing a `Decidable` obligation in
public theorem signatures. -/
noncomputable def survivorPrimeFaceIndicator (P : Prop) : ℤ := by
  classical
  exact if P then 1 else 0

private theorem survivorPrimeFaceProduct_mono
    {q : ℕ} {u v : Finset ℕ}
    (huv : u ⊆ v) (hv : v ⊆ survivorPrimeFaceAmbient q) :
    primeFaceProduct u ≤ primeFaceProduct v := by
  exact Finset.prod_le_prod_of_subset_of_one_le' huv (by
    intro p hpv _hpu
    have hpAmbient : p ∈ primesUpTo (q - 1) := hv hpv
    exact (prime_of_mem_primesUpTo hpAmbient).one_le)

/-- The complete product prefix is downward closed. -/
theorem survivorPrimeFaceProductPrefix_downward
    (n q : ℕ) :
    CubeDownwardClosed (survivorPrimeFaceProductPrefix n q) := by
  intro u v huv hv
  refine ⟨huv.trans hv.1, ?_⟩
  have hprod := survivorPrimeFaceProduct_mono huv hv.1
  exact (Nat.mul_le_mul_right q hprod).trans hv.2

/-- The transport-side high prefix is downward closed. -/
theorem survivorPrimeFaceTransportPrefix_downward
    (Λ : ℝ) (n q : ℕ) :
    CubeDownwardClosed (survivorPrimeFaceTransportPrefix Λ n q) := by
  intro u v huv hv
  have huPrefix : survivorPrimeFaceProductPrefix n q u :=
    survivorPrimeFaceProductPrefix_downward n q u v huv hv.1
  have hprodNat := survivorPrimeFaceProduct_mono huv hv.1.1
  have hprod :
      (primeFaceProduct u : ℝ) ≤ (primeFaceProduct v : ℝ) := by
    exact_mod_cast hprodNat
  have huNonneg : 0 ≤ (primeFaceProduct u : ℝ) := by positivity
  have hvNonneg : 0 ≤ (primeFaceProduct v : ℝ) := by positivity
  refine ⟨huPrefix, ?_⟩
  nlinarith [hv.2]

/-- The below-smooth prefix is downward closed. -/
theorem survivorPrimeFaceBelowSmoothPrefix_downward
    (Λ : ℝ) (n q : ℕ) :
    CubeDownwardClosed (survivorPrimeFaceBelowSmoothPrefix Λ n q) := by
  intro u v huv hv
  have huPrefix : survivorPrimeFaceProductPrefix n q u :=
    survivorPrimeFaceProductPrefix_downward n q u v huv hv.1
  have hprodNat := survivorPrimeFaceProduct_mono huv hv.1.1
  have hprod :
      (primeFaceProduct u : ℝ) ≤ (primeFaceProduct v : ℝ) := by
    exact_mod_cast hprodNat
  have huNonneg : 0 ≤ (primeFaceProduct u : ℝ) := by positivity
  have hvNonneg : 0 ≤ (primeFaceProduct v : ℝ) := by positivity
  refine ⟨huPrefix, ?_⟩
  nlinarith [hv.2]

/-- Exact pointwise decomposition of the V-shaped survivor height selector into
three monotone predicates. -/
theorem survivorPrimeFaceHigh_indicator_decomposition
    (Λ : ℝ) (n q : ℕ) (u : Finset ℕ) (hΛ : 0 ≤ Λ) :
    survivorPrimeFaceIndicator (survivorPrimeFaceHigh Λ n q u) =
      survivorPrimeFaceIndicator (survivorPrimeFaceTransportPrefix Λ n q u) +
        survivorPrimeFaceIndicator (survivorPrimeFaceProductPrefix n q u) -
          survivorPrimeFaceIndicator (survivorPrimeFaceBelowSmoothPrefix Λ n q u) := by
  classical
  unfold survivorPrimeFaceIndicator
  let H : ℝ := 2 * Λ * (n : ℝ)
  let c : ℝ := (primeFaceProduct u : ℝ)
  have hH : 0 ≤ H := by
    dsimp [H]
    positivity
  by_cases hp : survivorPrimeFaceProductPrefix n q u
  · by_cases ht : H < (q : ℝ) ^ 2 - c ^ 2
    · have hx : 0 ≤ (q : ℝ) ^ 2 - c ^ 2 := by linarith
      have ha : survivorPrimeFaceHigh Λ n q u := by
        refine ⟨hp, ?_⟩
        dsimp [H, c] at ht ⊢
        rw [abs_of_nonneg hx]
        exact ht
      have htransport : survivorPrimeFaceTransportPrefix Λ n q u := by
        exact ⟨hp, by simpa [H, c] using ht⟩
      have hbelow : survivorPrimeFaceBelowSmoothPrefix Λ n q u := by
        refine ⟨hp, ?_⟩
        dsimp [H, c] at ht hH ⊢
        nlinarith
      rw [if_pos ha, if_pos htransport, if_pos hp, if_pos hbelow]
      norm_num
    · by_cases hs : H < c ^ 2 - (q : ℝ) ^ 2
      · have hx : (q : ℝ) ^ 2 - c ^ 2 ≤ 0 := by linarith
        have ha : survivorPrimeFaceHigh Λ n q u := by
          refine ⟨hp, ?_⟩
          dsimp [H, c] at hs ⊢
          rw [abs_of_nonpos hx]
          nlinarith
        have htransport : ¬ survivorPrimeFaceTransportPrefix Λ n q u := by
          intro h
          exact ht (by simpa [H, c] using h.2)
        have hbelow : ¬ survivorPrimeFaceBelowSmoothPrefix Λ n q u := by
          intro h
          have hb := h.2
          dsimp [H, c] at hs hb
          linarith
        rw [if_pos ha, if_neg htransport, if_pos hp, if_neg hbelow]
        norm_num
      · have hsle : c ^ 2 - (q : ℝ) ^ 2 ≤ H := le_of_not_gt hs
        have hqside : (q : ℝ) ^ 2 - c ^ 2 ≤ H := le_of_not_gt ht
        have habs : |(q : ℝ) ^ 2 - c ^ 2| ≤ H := by
          apply abs_le.mpr
          constructor <;> linarith
        have habsOriginal :
            |(q : ℝ) ^ 2 - (primeFaceProduct u : ℝ) ^ 2| ≤
              2 * Λ * (n : ℝ) := by
          simpa [H, c] using habs
        have ha : ¬ survivorPrimeFaceHigh Λ n q u := by
          intro h
          exact (not_lt_of_ge habsOriginal) h.2
        have htransport : ¬ survivorPrimeFaceTransportPrefix Λ n q u := by
          intro h
          exact ht (by simpa [H, c] using h.2)
        have hbelow : survivorPrimeFaceBelowSmoothPrefix Λ n q u := by
          exact ⟨hp, by simpa [H, c] using hsle⟩
        rw [if_neg ha, if_neg htransport, if_pos hp, if_pos hbelow]
        norm_num
  · have ha : ¬ survivorPrimeFaceHigh Λ n q u := fun h => hp h.1
    have ht : ¬ survivorPrimeFaceTransportPrefix Λ n q u := fun h => hp h.1
    have hb : ¬ survivorPrimeFaceBelowSmoothPrefix Λ n q u := fun h => hp h.1
    rw [if_neg ha, if_neg ht, if_neg hp, if_neg hb]
    norm_num

/-- The alternating mass of the full high selector is exactly the signed
combination of three downward-closed cube masses. -/
theorem survivorPrimeFaceHigh_alternatingMass_decomposition
    (Λ : ℝ) (n q : ℕ) (hΛ : 0 ≤ Λ) :
    truncatedCubeAlternatingSum (survivorPrimeFaceAmbient q)
        (survivorPrimeFaceHigh Λ n q) =
      truncatedCubeAlternatingSum (survivorPrimeFaceAmbient q)
          (survivorPrimeFaceTransportPrefix Λ n q) +
        truncatedCubeAlternatingSum (survivorPrimeFaceAmbient q)
          (survivorPrimeFaceProductPrefix n q) -
        truncatedCubeAlternatingSum (survivorPrimeFaceAmbient q)
          (survivorPrimeFaceBelowSmoothPrefix Λ n q) := by
  classical
  unfold truncatedCubeAlternatingSum
  calc
    (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceHigh Λ n q u then booleanCubeSign u else 0) =
      ∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        ((if survivorPrimeFaceTransportPrefix Λ n q u then booleanCubeSign u else 0) +
          (if survivorPrimeFaceProductPrefix n q u then booleanCubeSign u else 0) -
          (if survivorPrimeFaceBelowSmoothPrefix Λ n q u then booleanCubeSign u else 0)) := by
      apply Finset.sum_congr rfl
      intro u _hu
      have hind := survivorPrimeFaceHigh_indicator_decomposition Λ n q u hΛ
      unfold survivorPrimeFaceIndicator at hind
      have hscaled := congrArg (fun z : ℤ => z * booleanCubeSign u) hind
      simpa [add_mul, sub_mul] using hscaled
    _ =
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceTransportPrefix Λ n q u then booleanCubeSign u else 0) +
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceProductPrefix n q u then booleanCubeSign u else 0) -
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceBelowSmoothPrefix Λ n q u then booleanCubeSign u else 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Complete interior cancellation: at any prime coordinate `ell < q`, the full
high alternating mass is carried by three explicit first-failure frontiers. -/
theorem survivorPrimeFaceHigh_alternatingMass_eq_threeFrontiers
    (Λ : ℝ) (n q ell : ℕ) (hΛ : 0 ≤ Λ)
    (hell : ell ∈ survivorPrimeFaceAmbient q) :
    truncatedCubeAlternatingSum (survivorPrimeFaceAmbient q)
        (survivorPrimeFaceHigh Λ n q) =
      firstFailureBoundaryAlternatingSum (survivorPrimeFaceAmbient q) ell
          (survivorPrimeFaceTransportPrefix Λ n q) +
        firstFailureBoundaryAlternatingSum (survivorPrimeFaceAmbient q) ell
          (survivorPrimeFaceProductPrefix n q) -
        firstFailureBoundaryAlternatingSum (survivorPrimeFaceAmbient q) ell
          (survivorPrimeFaceBelowSmoothPrefix Λ n q) := by
  rw [survivorPrimeFaceHigh_alternatingMass_decomposition Λ n q hΛ]
  rw [truncatedCubeAlternatingSum_eq_firstFailureBoundary hell
      (survivorPrimeFaceTransportPrefix_downward Λ n q),
    truncatedCubeAlternatingSum_eq_firstFailureBoundary hell
      (survivorPrimeFaceProductPrefix_downward n q),
    truncatedCubeAlternatingSum_eq_firstFailureBoundary hell
      (survivorPrimeFaceBelowSmoothPrefix_downward Λ n q)]

end RHLean.Proof
