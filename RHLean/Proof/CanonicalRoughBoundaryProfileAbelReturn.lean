import Mathlib
import RHLean.Arithmetic.PrimorialTruncatedWheelBoundary
import RHLean.Arithmetic.PrimesUpToFrontier

/-!
# Finite Abel return in the prime coordinate

The truncated reciprocal Euler recurrence supplies a native `1/q` on the moving
`X/q` column, so the reciprocal-weighted upper column telescopes to a single
final boundary.  The literal physical fixed-`q` columns carry `mu(c)/c` and no
`1/q`, and for them the recurrence gives instead the exact unweighted law

```text
T_{q-}(X/q) - E_{q-} = q * (B_{q-}(X) - B_q(X)),
```

where `B_n(X) = T_{primesUpTo n}(X) - E_{primesUpTo n}` is the canonical
reciprocal boundary profile.  Summing over primes therefore produces a
*prime-weighted discrete variation* of the boundary, not one terminal boundary.

This file supplies the step that turns that variation back into a closed form.
The boundary profile is constant across composite cutoffs, because `primesUpTo`
does not move there, so the prime-indexed sum is really a sum over every cutoff,
and ordinary finite summation by parts gives

```text
sum_{q <= K, q prime} q * (B_{q-} - B_q) = sum_{n < K} B_n - K * B_K.
```

The architecture is therefore

```text
physical defects -> fixed-q shells -> transport telescope in p
  -> boundary profile in q -> finite Abel return in q.
```

The quantitative consequence is the point of the file.  A bound on the endpoint
`B_K(X)` alone does **not** control the physical aggregate: the Abel return also
carries the integrated profile `sum_{n < K} B_n(X)`, and the final estimate
below keeps both terms explicitly.  So the RH-critical object attached to the
physical columns is not `|T_{<=K}(X) - E_{<=K}|` on its own but the Abel
combination `sum_{n < K} B_n(X) - K * B_K(X)`.

The Abel step is proved first for an arbitrary profile that is stationary off
the primes, so it applies verbatim to any boundary family with that shape, and
is then specialized to the truncated wheel profile.  Nothing here is asymptotic.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## Abel summation against a profile that only moves at primes -/

/-- **Finite Abel transform of a discrete variation.**  For an arbitrary real
profile `B`, weighting each backward difference by its index and summing over an
initial segment returns the integrated profile minus the scaled endpoint.  No
primality is involved; this is pure summation by parts. -/
theorem sum_Icc_natCast_mul_boundaryDrop_eq_abel (B : ℕ → ℝ) (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) * (B (n - 1) - B n)) =
      (∑ n ∈ Finset.range K, B n) - (K : ℝ) * B K := by
  induction K with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0)]
      simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ K + 1), ih,
        Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- Primes below a cutoff sit inside the corresponding index segment. -/
theorem primesUpTo_subset_Icc_one (K : ℕ) : primesUpTo K ⊆ Finset.Icc 1 K := by
  intro q hq
  rcases mem_primesUpTo.mp hq with ⟨hqPrime, hqle⟩
  exact Finset.mem_Icc.mpr ⟨hqPrime.one_lt.le, hqle⟩

/-- A profile that does not move at composite cutoffs contributes nothing there,
so its prime-indexed variation is the full indexed variation. -/
theorem sum_primesUpTo_natCast_mul_boundaryDrop_eq_sum_Icc
    (B : ℕ → ℝ) (K : ℕ) (hstat : ∀ n, ¬ n.Prime → B n = B (n - 1)) :
    (∑ q ∈ primesUpTo K, (q : ℝ) * (B (q - 1) - B q)) =
      ∑ n ∈ Finset.Icc 1 K, (n : ℝ) * (B (n - 1) - B n) := by
  refine Finset.sum_subset (primesUpTo_subset_Icc_one K) ?_
  intro n hn hnot
  have hnle : n ≤ K := (Finset.mem_Icc.mp hn).2
  have hnp : ¬ n.Prime := by
    intro hp
    exact hnot (mem_primesUpTo.mpr ⟨hp, hnle⟩)
  rw [hstat n hnp]
  ring

/-- **Finite Abel return in the prime coordinate.**  For any profile stationary
off the primes, the prime-weighted discrete variation equals the integrated
profile minus the scaled endpoint. -/
theorem sum_primesUpTo_natCast_mul_boundaryDrop_eq_abel
    (B : ℕ → ℝ) (K : ℕ) (hstat : ∀ n, ¬ n.Prime → B n = B (n - 1)) :
    (∑ q ∈ primesUpTo K, (q : ℝ) * (B (q - 1) - B q)) =
      (∑ n ∈ Finset.range K, B n) - (K : ℝ) * B K := by
  rw [sum_primesUpTo_natCast_mul_boundaryDrop_eq_sum_Icc B K hstat,
    sum_Icc_natCast_mul_boundaryDrop_eq_abel B K]

/-! ## The canonical reciprocal boundary profile -/

/-- Canonical reciprocal boundary profile: the truncated signed reciprocal cube
on the prime prefix, measured against its own complete Euler contraction. -/
def primorialTruncatedWheelBoundaryProfile (X n : ℕ) : ℝ :=
  primorialTruncatedSignedReciprocalCube (primesUpTo n) X -
    primorialSignedContractionFactor (primesUpTo n)

theorem primorialTruncatedWheelBoundaryProfile_eq (X n : ℕ) :
    primorialTruncatedWheelBoundaryProfile X n =
      primorialTruncatedSignedReciprocalCube (primesUpTo n) X -
        primorialSignedContractionFactor (primesUpTo n) := rfl

/-- A composite cutoff adjoins no prime coordinate. -/
theorem primesUpTo_eq_pred_of_not_prime {n : ℕ} (hn : ¬ n.Prime) :
    primesUpTo n = primesUpTo (n - 1) := by
  ext q
  simp only [mem_primesUpTo]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    refine ⟨hqPrime, ?_⟩
    have hqne : q ≠ n := by
      rintro rfl
      exact hn hqPrime
    omega
  · rintro ⟨hqPrime, hqle⟩
    exact ⟨hqPrime, by omega⟩

/-- Hence the boundary profile is stationary off the primes. -/
theorem primorialTruncatedWheelBoundaryProfile_eq_of_not_prime
    (X : ℕ) {n : ℕ} (hn : ¬ n.Prime) :
    primorialTruncatedWheelBoundaryProfile X n =
      primorialTruncatedWheelBoundaryProfile X (n - 1) := by
  unfold primorialTruncatedWheelBoundaryProfile
  rw [primesUpTo_eq_pred_of_not_prime hn]

/-! ## The physical column aggregate in closed form -/

/-- **Abel return for the truncated wheel boundary.**  The prime-weighted
boundary drops produced by the literal unweighted physical columns sum to the
integrated boundary profile minus its scaled endpoint. -/
theorem primorialTruncatedBoundary_primeWeightedDrops_eq_abelReturn (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (q : ℝ) *
        (primorialTruncatedWheelBoundaryProfile X (q - 1) -
          primorialTruncatedWheelBoundaryProfile X q)) =
      (∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
        (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K :=
  sum_primesUpTo_natCast_mul_boundaryDrop_eq_abel
    (primorialTruncatedWheelBoundaryProfile X) K
    (fun _n hn => primorialTruncatedWheelBoundaryProfile_eq_of_not_prime X hn)

/-- The same statement with the profile written out, matching the shape in which
the unweighted-column law is stated on the truncated wheel telescope. -/
theorem primorialTruncatedBoundary_primeWeightedDrops_eq_abelReturn_unfolded
    (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (q : ℝ) *
        ((primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) X -
            primorialSignedContractionFactor (primesUpTo (q - 1))) -
          (primorialTruncatedSignedReciprocalCube (primesUpTo q) X -
            primorialSignedContractionFactor (primesUpTo q)))) =
      (∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
        (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K :=
  primorialTruncatedBoundary_primeWeightedDrops_eq_abelReturn X K

/-- **Diagnostic only.**  The Abel return carries two terms, so an endpoint
bound on `B_K` alone does not control the physical aggregate: the integrated
profile appears with full weight.

This is deliberately *not* a closure route.  Its right-hand side norms the
boundary profile termwise, which discards exactly the nonlocal signed
cancellation the Euler telescope exists to preserve, so proving a bound on
`sum_{n < K} |B_n|` would be a magnitude-first detour.  The statement is here to
certify that endpoint control is insufficient, and nothing downstream should
route through it. -/
theorem abs_primorialTruncatedBoundaryAbelReturn_le (X K : ℕ) :
    |(∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
        (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K| ≤
      (∑ n ∈ Finset.range K, |primorialTruncatedWheelBoundaryProfile X n|) +
        (K : ℝ) * |primorialTruncatedWheelBoundaryProfile X K| := by
  have hsplit :
      |(∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
          (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K| ≤
        |∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n| +
          |(K : ℝ) * primorialTruncatedWheelBoundaryProfile X K| :=
    abs_sub _ _
  have hsum :
      |∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n| ≤
        ∑ n ∈ Finset.range K, |primorialTruncatedWheelBoundaryProfile X n| :=
    Finset.abs_sum_le_sum_abs _ _
  have hmul :
      |(K : ℝ) * primorialTruncatedWheelBoundaryProfile X K| =
        (K : ℝ) * |primorialTruncatedWheelBoundaryProfile X K| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg K)]
  rw [hmul] at hsplit
  linarith

/-! ## The Abel primitive and its interval form

The prime-weighted boundary variation returns a single signed object, so it is
worth naming: `boundaryProfileAbelPrimitive B K` is the integrated profile minus
the scaled endpoint.  Restricted to a half-open prime band the return becomes a
difference of two primitives, which is the shape a physical column sum over a
restricted prime range lands on.

The two physical orientations are the same construction at different truncation
arguments.  A post-root escape column runs against the square endpoint, so its
profile is `primorialTruncatedWheelBoundaryProfile X_R` and its band is the
external range above the root.  A birth column runs against the lower global
cutoff `(R-1)/q`, so its profile is `primorialTruncatedWheelBoundaryProfile
(R-1)` and its band is the root range.  Nothing below is normed: both endpoints
of every interval return keep their sign. -/

/-- **Abel primitive of a boundary profile**: integrated profile minus scaled
endpoint.  This is the object the prime-weighted variation actually returns. -/
def boundaryProfileAbelPrimitive (B : ℕ → ℝ) (K : ℕ) : ℝ :=
  (∑ n ∈ Finset.range K, B n) - (K : ℝ) * B K

/-- The Abel return, restated on the primitive. -/
theorem sum_primesUpTo_natCast_mul_boundaryDrop_eq_abelPrimitive
    (B : ℕ → ℝ) (K : ℕ) (hstat : ∀ n, ¬ n.Prime → B n = B (n - 1)) :
    (∑ q ∈ primesUpTo K, (q : ℝ) * (B (q - 1) - B q)) =
      boundaryProfileAbelPrimitive B K :=
  sum_primesUpTo_natCast_mul_boundaryDrop_eq_abel B K hstat

/-- Prime prefixes are monotone in the cutoff. -/
theorem primesUpTo_subset_primesUpTo {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    primesUpTo K₀ ⊆ primesUpTo K₁ := by
  intro q hq
  rcases mem_primesUpTo.mp hq with ⟨hqPrime, hqle⟩
  exact mem_primesUpTo.mpr ⟨hqPrime, hqle.trans hK⟩

/-- The index set of an interval return is exactly a half-open prime band. -/
theorem mem_primesUpTo_sdiff {K₀ K₁ q : ℕ} :
    q ∈ primesUpTo K₁ \ primesUpTo K₀ ↔ q.Prime ∧ K₀ < q ∧ q ≤ K₁ := by
  rw [Finset.mem_sdiff, mem_primesUpTo, mem_primesUpTo]
  constructor
  · rintro ⟨⟨hqPrime, hq1⟩, hq0⟩
    refine ⟨hqPrime, ?_, hq1⟩
    by_contra hle
    exact hq0 ⟨hqPrime, by omega⟩
  · rintro ⟨hqPrime, hq0, hq1⟩
    refine ⟨⟨hqPrime, hq1⟩, ?_⟩
    rintro ⟨_, hle⟩
    omega

/-- **Interval Abel return.**  The prime-weighted boundary variation restricted
to a half-open prime band is the difference of the two Abel primitives. -/
theorem sum_primesUpTo_sdiff_natCast_mul_boundaryDrop_eq_abelPrimitive_sub
    (B : ℕ → ℝ) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁)
    (hstat : ∀ n, ¬ n.Prime → B n = B (n - 1)) :
    (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀, (q : ℝ) * (B (q - 1) - B q)) =
      boundaryProfileAbelPrimitive B K₁ - boundaryProfileAbelPrimitive B K₀ := by
  have hsplit :=
    Finset.sum_sdiff (primesUpTo_subset_primesUpTo hK)
      (f := fun q : ℕ => (q : ℝ) * (B (q - 1) - B q))
  rw [sum_primesUpTo_natCast_mul_boundaryDrop_eq_abelPrimitive B K₀ hstat,
    sum_primesUpTo_natCast_mul_boundaryDrop_eq_abelPrimitive B K₁ hstat] at hsplit
  linarith

/-! ## The physical orientations -/

/-- Abel primitive of the canonical reciprocal boundary profile at truncation
`X`.  The post-root orientation takes `X = X_R`; the birth orientation takes the
lower global cutoff. -/
def primorialTruncatedWheelAbelPrimitive (X K : ℕ) : ℝ :=
  boundaryProfileAbelPrimitive (primorialTruncatedWheelBoundaryProfile X) K

theorem primorialTruncatedWheelAbelPrimitive_eq (X K : ℕ) :
    primorialTruncatedWheelAbelPrimitive X K =
      (∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
        (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K := rfl

/-- The full prime-weighted drop sum, on the primitive. -/
theorem primorialTruncatedBoundary_primeWeightedDrops_eq_abelPrimitive (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (q : ℝ) *
        (primorialTruncatedWheelBoundaryProfile X (q - 1) -
          primorialTruncatedWheelBoundaryProfile X q)) =
      primorialTruncatedWheelAbelPrimitive X K :=
  primorialTruncatedBoundary_primeWeightedDrops_eq_abelReturn X K

/-- **Interval Abel return for the truncated wheel boundary.**  A physical
column sum restricted to the prime band `K_0 < q <= K_1` returns exactly the
difference of the two signed primitives.  With `X = X_R` and the band above the
root this is the post-root orientation; with the lower global cutoff and the
root band it is the birth orientation. -/
theorem primorialTruncatedBoundary_primeBand_eq_abelPrimitive_sub
    (X : ℕ) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
      (q : ℝ) *
        (primorialTruncatedWheelBoundaryProfile X (q - 1) -
          primorialTruncatedWheelBoundaryProfile X q)) =
      primorialTruncatedWheelAbelPrimitive X K₁ -
        primorialTruncatedWheelAbelPrimitive X K₀ :=
  sum_primesUpTo_sdiff_natCast_mul_boundaryDrop_eq_abelPrimitive_sub
    (primorialTruncatedWheelBoundaryProfile X) hK
    (fun _n hn => primorialTruncatedWheelBoundaryProfile_eq_of_not_prime X hn)

end RHLean.Proof
