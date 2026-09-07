import Mathlib
import RHLean.Proof.CanonicalRoughBoundaryProfileAbelReturn
import RHLean.Proof.CanonicalRoughTruncatedWheelManyPrimeTelescope

/-!
# Canonical unweighted columns land on the Abel primitive

The unweighted-column law turns each `mu(c)/c`-shaped column into `q` times a
discrete drop of the canonical reciprocal boundary profile, and the finite Abel
return closes the resulting prime-weighted variation.  This file composes the
two, identifying the column aggregate with the signed primitive

```text
A_X(K) = sum_{n < K} B_n(X) - K * B_K(X),
```

both over a full prime prefix and over a half-open prime band.  Nothing here is
normed: routing through the primitive is what keeps the nonlocal signed
cancellation available downstream.

## These columns are canonical, not yet physical

The summands below are

```text
primorialTruncatedSignedReciprocalCube (primesUpTo (q-1)) (X / q)
  - primorialSignedContractionFactor (primesUpTo (q-1)),
```

which is a *canonical* truncated-wheel column indexed by the full prime prefix
`primesUpTo (q-1)`.  It is **not** yet a sum of the literal physical face masses
`squareRootCanonicalRoughCompleteWheelTopEscapePartnerFaceMass` or
`...BirthPartnerFaceMass`.  The physical identification of those masses carries
hypotheses `p < q`, `q < R` and `SquareRootCanonicalRoughCompleteWheelBelowRoot
R p`, and the many-prime transported ledger is generic in an arbitrary prime
list `ps`, landing on the boundary indexed by `ps.toFinset`.

Nothing available here proves that the legal physical `p`-schedule satisfies

```text
ps.toFinset = primesUpTo (q - 1),
```

and it need not: the complete-wheel hypothesis only survives while
`prod_{r <= p} r < R`, so the physical schedule may stop strictly earlier than
every prime below `q`.  Until that carrier/schedule theorem is compiled, the
names here stay `canonical...`; calling them physical would smuggle in exactly
that unproved step.  Either the schedule really is the full prefix, in which
case these theorems fire immediately, or the physical column equals the
canonical column minus an explicit missing-`p` tail, and that tail is what has
to rotate into the existing root/external machinery.

## The two orientations

The profile is parameterized by the truncation, so one band theorem covers both.
A post-root escape column runs over `R < q <= X_R` against the square endpoint.
A birth owner column runs against the lower global cutoff `R - 1`, and its band
is pinned by the birth hypotheses themselves: `q` prime with `p < q` for a prime
`p` forces `q > 2`, while `c * q < R` with `c >= 1` forces `q < R`.  So the
birth band is exactly `2 < q < R`, and since the boundary profile vanishes while
the complete wheel still fits inside the truncation, the birth orientation
collapses to the single primitive value `A_{R-1}(R-1)`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## Canonical column aggregates -/

/-- **The canonical unweighted column aggregate is the Abel primitive.** -/
theorem canonicalUnweightedColumn_eq_abelPrimitive (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive X K := by
  rw [primorialTruncatedBoundary_unweightedUpperColumn_eq_primeWeightedDrops X K]
  exact primorialTruncatedBoundary_primeWeightedDrops_eq_abelPrimitive X K

/-- **Interval form.**  Over a half-open prime band the aggregate returns the
difference of the primitives at the band endpoints. -/
theorem canonicalUnweightedColumn_primeBand_eq_abelPrimitive_sub
    (X : ℕ) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive X K₁ -
        primorialTruncatedWheelAbelPrimitive X K₀ := by
  have hcongr :
      (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) =
        ∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
          (q : ℝ) *
            (primorialTruncatedWheelBoundaryProfile X (q - 1) -
              primorialTruncatedWheelBoundaryProfile X q) := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    exact primorialTruncatedBoundary_unweightedColumn_eq_prime_mul_boundaryDrop
      X (mem_primesUpTo_sdiff.mp hq).1
  rw [hcongr]
  exact primorialTruncatedBoundary_primeBand_eq_abelPrimitive_sub X hK

/-! ## Vanishing of the profile below the first incomplete wheel -/

/-- While the complete wheel still fits inside the truncation, the truncated
profile has already stabilized on its Euler contraction, so the boundary
vanishes. -/
theorem primorialTruncatedWheelBoundaryProfile_eq_zero_of_complete
    {X n : ℕ} (hX : primorialWheelProduct (primesUpTo n) ≤ X) :
    primorialTruncatedWheelBoundaryProfile X n = 0 := by
  unfold primorialTruncatedWheelBoundaryProfile
  rw [primorialTruncatedSignedReciprocalCube_eq_factor (primesUpTo n) X
    (fun _p hp => prime_of_mem_primesUpTo hp) hX]
  exact sub_self _

theorem primesUpTo_eq_empty_of_le_one {n : ℕ} (hn : n ≤ 1) : primesUpTo n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rcases mem_primesUpTo.mp hq with ⟨hqPrime, hqle⟩
  have h2 := hqPrime.two_le
  omega

theorem primesUpTo_two : primesUpTo 2 = {2} := by
  ext q
  rw [mem_primesUpTo, Finset.mem_singleton]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    have h2 := hqPrime.two_le
    omega
  · rintro rfl
    exact ⟨Nat.prime_two, le_rfl⟩

theorem primorialWheelProduct_primesUpTo_of_le_one {n : ℕ} (hn : n ≤ 1) :
    primorialWheelProduct (primesUpTo n) = 1 := by
  rw [primesUpTo_eq_empty_of_le_one hn]
  simp [primorialWheelProduct]

theorem primorialWheelProduct_primesUpTo_two :
    primorialWheelProduct (primesUpTo 2) = 2 := by
  rw [primesUpTo_two]
  simp [primorialWheelProduct]

/-- **The Abel primitive vanishes at the initial cutoff.**  Through the prime
`2` the complete wheel already fits inside any truncation of size at least two,
so every profile value involved is zero. -/
theorem primorialTruncatedWheelAbelPrimitive_two_eq_zero {X : ℕ} (hX : 2 ≤ X) :
    primorialTruncatedWheelAbelPrimitive X 2 = 0 := by
  have h0 : primorialTruncatedWheelBoundaryProfile X 0 = 0 :=
    primorialTruncatedWheelBoundaryProfile_eq_zero_of_complete
      (by rw [primorialWheelProduct_primesUpTo_of_le_one (by omega : (0:ℕ) ≤ 1)]; omega)
  have h1 : primorialTruncatedWheelBoundaryProfile X 1 = 0 :=
    primorialTruncatedWheelBoundaryProfile_eq_zero_of_complete
      (by rw [primorialWheelProduct_primesUpTo_of_le_one (by omega : (1:ℕ) ≤ 1)]; omega)
  have h2 : primorialTruncatedWheelBoundaryProfile X 2 = 0 :=
    primorialTruncatedWheelBoundaryProfile_eq_zero_of_complete
      (by rw [primorialWheelProduct_primesUpTo_two]; omega)
  unfold primorialTruncatedWheelAbelPrimitive boundaryProfileAbelPrimitive
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2]
  norm_num

/-! ## The post-root orientation -/

theorem le_squareRootEndpoint_self {R : ℕ} (hR : 2 ≤ R) :
    R ≤ squareRootEndpoint R := by
  unfold squareRootEndpoint
  have h : R * 2 ≤ R * R := Nat.mul_le_mul (le_refl R) hR
  rw [pow_two]
  omega

/-- Canonical column aggregate over the complete external band `R < q <= X_R`,
against the square endpoint. -/
theorem canonicalPostRootBandColumn_eq_abelPrimitive_sub {R : ℕ} (hR : 2 ≤ R) :
    (∑ q ∈ primesUpTo (squareRootEndpoint R) \ primesUpTo R,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R)
          (squareRootEndpoint R) -
        primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R) R :=
  canonicalUnweightedColumn_primeBand_eq_abelPrimitive_sub
    (squareRootEndpoint R) (le_squareRootEndpoint_self hR)

/-! ## The birth orientation -/

/-- Canonical column aggregate against the lower global cutoff `R - 1`. -/
theorem canonicalBirthColumn_eq_abelPrimitive_sub
    (R : ℕ) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
          ((R - 1) / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive (R - 1) K₁ -
        primorialTruncatedWheelAbelPrimitive (R - 1) K₀ :=
  canonicalUnweightedColumn_primeBand_eq_abelPrimitive_sub (R - 1) hK

/-- **Birth owner band.**  The birth hypotheses pin the band exactly: a prime
`p < q` forces `q > 2`, and `c * q < R` with `c >= 1` forces `q < R`.  Over that
band the aggregate collapses to a single primitive value, because the lower
endpoint `A_{R-1}(2)` vanishes. -/
theorem canonicalBirthOwnerBandColumn_eq_abelPrimitive {R : ℕ} (hR : 3 ≤ R) :
    (∑ q ∈ primesUpTo (R - 1) \ primesUpTo 2,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
          ((R - 1) / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive (R - 1) (R - 1) := by
  rw [canonicalBirthColumn_eq_abelPrimitive_sub R (by omega : (2:ℕ) ≤ R - 1),
    primorialTruncatedWheelAbelPrimitive_two_eq_zero (by omega : (2:ℕ) ≤ R - 1)]
  ring

/-- **Three nontrivial primitive values.**  Combining the two orientations, the
signed post-root minus birth aggregate is carried by exactly three primitive
values rather than four: the birth lower endpoint is zero. -/
theorem canonicalPostRoot_sub_canonicalBirth_eq_threePrimitiveValues
    {R : ℕ} (hR : 3 ≤ R) :
    ((∑ q ∈ primesUpTo (squareRootEndpoint R) \ primesUpTo R,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
            (squareRootEndpoint R / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) -
      (∑ q ∈ primesUpTo (R - 1) \ primesUpTo 2,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
            ((R - 1) / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1))))) =
      primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R)
          (squareRootEndpoint R) -
        primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R) R -
        primorialTruncatedWheelAbelPrimitive (R - 1) (R - 1) := by
  rw [canonicalPostRootBandColumn_eq_abelPrimitive_sub (by omega : (2:ℕ) ≤ R),
    canonicalBirthOwnerBandColumn_eq_abelPrimitive hR]

end RHLean.Proof
