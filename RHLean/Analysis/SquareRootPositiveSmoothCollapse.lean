import Mathlib
import RHLean.Analysis.SquareRootTransportRealization
import RHLean.Analysis.PrimeSievePNTCentering

/-!
# Positive-orientation smooth mass as a prime-indexed Mertens transform

The square-root smooth/transport decomposition splits the smooth population into

* the positive orientation `c < q = P+(m)`, and
* the born-smooth orientation `q <= c`.

This module closes the exact algebra on the positive side.  For `R >= 1`, every
positive-orientation source below `R^2` has a unique canonical factorization

`m = c*q`,  `1 <= c < q <= R`,  `q` prime,

and the product cutoff is automatic.  Along that factorization
`mu(c*q) = -mu(c)`.  Reindexing first by `q` therefore gives

```text
squareRootPositiveSmoothMass R
  = - sum_{q <= R, q prime} M(q-1).
```

Combining this with the already-realized square-prefix identity gives

```text
M(R^2-1)
  = - sum_{q <= R, q prime} M(q-1)
    + squareRootMatchedBornSmoothTransport R.
```

The final theorem pushes this exact square-side collapse through the existing
prime-wheel zero-mode centering identity.  It is an exact synthesis theorem,
not an asymptotic estimate: no power saving, lower bound, PNT error estimate,
or RH implication is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Positive-orientation canonical source integers in the complete square prefix. -/
def squareRootPositiveSmoothSourceSet (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun m =>
    canonicalLargestPrimeFactor m ≤ R ∧
      canonicalCofactor m < canonicalLargestPrimeFactor m

/-- Prime-first canonical coordinates for the same positive-orientation family. -/
def squareRootPositiveSmoothPairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 R).product (Finset.Ico 1 R)).filter fun qc =>
    qc.1.Prime ∧ qc.2 < qc.1

/-- Native source mass on the positive-orientation population. -/
def squareRootPositiveSmoothSourceMass (R : ℕ) : ℂ :=
  ∑ m ∈ squareRootPositiveSmoothSourceSet R, canonicalMoebiusWeight m

/-- The same source mass reindexed by prime/cofactor coordinates. -/
def squareRootPositiveSmoothPairSourceMass (R : ℕ) : ℂ :=
  ∑ qc ∈ squareRootPositiveSmoothPairSet R,
    canonicalMoebiusWeight (qc.2 * qc.1)

/-- The prime-indexed lower-scale Mertens transform exposed by the positive
orientation. -/
def squareRootPositiveSmoothPrimeMertensTransform (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 2 R,
    if q.Prime then RHLean.Analysis.mertensSummatory (q - 1) else 0

private theorem one_lt_of_mem_squareRootPositiveSmoothSourceSet
    {R m : ℕ} (hm : m ∈ squareRootPositiveSmoothSourceSet R) :
    1 < m := by
  rcases Finset.mem_filter.mp hm with ⟨hmRange, hdata⟩
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmRange).1
  have hcq : canonicalCofactor m < canonicalLargestPrimeFactor m := hdata.2
  by_contra hnot
  have hmEq : m = 1 := by omega
  subst m
  simp [canonicalLargestPrimeFactor, canonicalCofactor] at hcq

/-- Removing the zero source, whose Möbius weight is zero, identifies the
existing `if`-sum definition with the positive source set. -/
theorem squareRootPositiveSmoothMass_eq_sourceMass
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootPositiveSmoothMass R = squareRootPositiveSmoothSourceMass R := by
  unfold squareRootPositiveSmoothMass squareRootPositiveSmoothSourceMass
    squareRootPositiveSmoothSourceSet
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  have hset :
      cumulativeSquarePrefixSet (R - 1) =
        insert 0 (Finset.Icc 1 (squareRootEndpoint R)) := by
    ext m
    simp [cumulativeSquarePrefixSet, squareRootEndpoint, hpred]
    omega
  rw [hset, Finset.sum_filter]
  simp [canonicalMoebiusWeight]

private theorem positiveSmoothSource_to_pair_mem
    {R m : ℕ} (hm : m ∈ squareRootPositiveSmoothSourceSet R) :
    (canonicalLargestPrimeFactor m, canonicalCofactor m) ∈
      squareRootPositiveSmoothPairSet R := by
  rcases Finset.mem_filter.mp hm with ⟨hmRange, hdata⟩
  rcases hdata with ⟨hqR, hcq⟩
  have hmgt : 1 < m := one_lt_of_mem_squareRootPositiveSmoothSourceSet hm
  have hqPrime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hmgt
  have hprod :
      canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hmgt
  have hcPos : 0 < canonicalCofactor m := by
    by_contra hnot
    have hc0 : canonicalCofactor m = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hc0, zero_mul] at hprod
    omega
  have hcR : canonicalCofactor m < R := lt_of_lt_of_le hcq hqR
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqR⟩,
        Finset.mem_Ico.mpr ⟨Nat.succ_le_iff.mpr hcPos, hcR⟩⟩
  · exact ⟨hqPrime, hcq⟩

private theorem positiveSmoothSource_pair_injective
    {R m n : ℕ}
    (hm : m ∈ squareRootPositiveSmoothSourceSet R)
    (hn : n ∈ squareRootPositiveSmoothSourceSet R)
    (hpair :
      (canonicalLargestPrimeFactor m, canonicalCofactor m) =
        (canonicalLargestPrimeFactor n, canonicalCofactor n)) :
    m = n := by
  have hmgt : 1 < m := one_lt_of_mem_squareRootPositiveSmoothSourceSet hm
  have hngt : 1 < n := one_lt_of_mem_squareRootPositiveSmoothSourceSet hn
  have hmprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  have hnprod := canonicalCofactor_mul_largestPrimeFactor hngt
  have hq : canonicalLargestPrimeFactor m = canonicalLargestPrimeFactor n :=
    congrArg Prod.fst hpair
  have hc : canonicalCofactor m = canonicalCofactor n :=
    congrArg Prod.snd hpair
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hmprod.symm
    _ = canonicalCofactor n * canonicalLargestPrimeFactor n := by rw [hc, hq]
    _ = n := hnprod

private theorem positiveSmoothPair_surjective
    {R : ℕ} (qc : ℕ × ℕ) (hqc : qc ∈ squareRootPositiveSmoothPairSet R) :
    ∃ m ∈ squareRootPositiveSmoothSourceSet R,
      (canonicalLargestPrimeFactor m, canonicalCofactor m) = qc := by
  rcases Finset.mem_filter.mp hqc with ⟨hbase, hdata⟩
  rcases Finset.mem_product.mp hbase with ⟨hqMem, hcMem⟩
  rcases Finset.mem_Icc.mp hqMem with ⟨hq2, hqR⟩
  rcases Finset.mem_Ico.mp hcMem with ⟨hc1, hcR⟩
  rcases hdata with ⟨hqPrime, hcq⟩
  have hcPos : 0 < qc.2 := by omega
  have hlargest : canonicalLargestPrimeFactor (qc.2 * qc.1) = qc.1 :=
    canonicalLargestPrimeFactor_mul_prime_eq hcPos hcq hqPrime
  have hcofactor : canonicalCofactor (qc.2 * qc.1) = qc.2 :=
    canonicalCofactor_mul_prime_eq hcPos hcq hqPrime
  have hmulLt : qc.2 * qc.1 < R ^ 2 := by
    have h1 : qc.2 * qc.1 < R * qc.1 :=
      Nat.mul_lt_mul_of_pos_right hcR hqPrime.pos
    have h2 : R * qc.1 ≤ R * R := Nat.mul_le_mul_left R hqR
    simpa [pow_two] using lt_of_lt_of_le h1 h2
  have hmulX : qc.2 * qc.1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hm1 : 1 ≤ qc.2 * qc.1 := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt hcPos) hqPrime.ne_zero)
  refine ⟨qc.2 * qc.1, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨hm1, hmulX⟩
    · simpa only [hlargest, hcofactor] using And.intro hqR hcq
  · apply Prod.ext
    · exact hlargest
    · exact hcofactor

/-- Reindex the positive-orientation source population by its unique prime-first
canonical coordinates. -/
theorem squareRootPositiveSmoothSourceMass_eq_pairSourceMass (R : ℕ) :
    squareRootPositiveSmoothSourceMass R = squareRootPositiveSmoothPairSourceMass R := by
  classical
  unfold squareRootPositiveSmoothSourceMass squareRootPositiveSmoothPairSourceMass
  refine Finset.sum_bij
    (fun m _hm => (canonicalLargestPrimeFactor m, canonicalCofactor m))
    (fun m hm => positiveSmoothSource_to_pair_mem hm)
    (fun m hm n hn hmn => positiveSmoothSource_pair_injective hm hn hmn)
    (fun qc hcq => by simpa using positiveSmoothPair_surjective qc hcq)
    ?_
  intro m hm
  have hmgt : 1 < m := one_lt_of_mem_squareRootPositiveSmoothSourceSet hm
  rw [canonicalCofactor_mul_largestPrimeFactor hmgt]

/-- Each fixed prime fibre is the negative complete Mertens prefix through
`q-1`, so the full pair mass is the negative prime-indexed Mertens transform. -/
theorem squareRootPositiveSmoothPairSourceMass_eq_neg_primeMertensTransform
    (R : ℕ) :
    squareRootPositiveSmoothPairSourceMass R =
      -squareRootPositiveSmoothPrimeMertensTransform R := by
  classical
  unfold squareRootPositiveSmoothPairSourceMass squareRootPositiveSmoothPairSet
    squareRootPositiveSmoothPrimeMertensTransform
  rw [Finset.sum_filter]
  calc
    (∑ qc ∈ (Finset.Icc 2 R).product (Finset.Ico 1 R),
        if qc.1.Prime ∧ qc.2 < qc.1 then
          canonicalMoebiusWeight (qc.2 * qc.1)
        else 0) =
      ∑ q ∈ Finset.Icc 2 R,
        ∑ c ∈ Finset.Ico 1 R,
          if q.Prime ∧ c < q then canonicalMoebiusWeight (c * q) else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Icc 2 R)
          (t := Finset.Ico 1 R)
          (f := fun qc : ℕ × ℕ =>
            if qc.1.Prime ∧ qc.2 < qc.1 then
              canonicalMoebiusWeight (qc.2 * qc.1)
            else 0))
    _ = ∑ q ∈ Finset.Icc 2 R,
          if q.Prime then -RHLean.Analysis.mertensSummatory (q - 1) else 0 := by
      apply Finset.sum_congr rfl
      intro q hqMem
      by_cases hqPrime : q.Prime
      · simp only [hqPrime, true_and, if_true]
        have hqR : q ≤ R := (Finset.mem_Icc.mp hqMem).2
        have hset :
            (Finset.Ico 1 R).filter (fun c => c < q) =
              Finset.Icc 1 (q - 1) := by
          ext c
          simp
          omega
        rw [← Finset.sum_filter, hset]
        calc
          (∑ c ∈ Finset.Icc 1 (q - 1), canonicalMoebiusWeight (c * q)) =
              ∑ c ∈ Finset.Icc 1 (q - 1), -canonicalMoebiusWeight c := by
            apply Finset.sum_congr rfl
            intro c hc
            rcases Finset.mem_Icc.mp hc with ⟨hc1, hcq1⟩
            have hcq : c < q := by omega
            exact canonicalMoebiusWeight_mul_prime_eq_neg (by omega) hcq hqPrime
          _ = -∑ c ∈ Finset.Icc 1 (q - 1), canonicalMoebiusWeight c := by simp
          _ = -cofactorMobiusPrefixMass (q - 1) := by rfl
          _ = -RHLean.Analysis.mertensSummatory (q - 1) := by
            rw [cofactorMobiusPrefixMass_eq_mertensSummatory]
      · simp [hqPrime]
    _ = -∑ q ∈ Finset.Icc 2 R,
          if q.Prime then RHLean.Analysis.mertensSummatory (q - 1) else 0 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q hqMem
      by_cases hqPrime : q.Prime <;> simp [hqPrime]

/-- **Positive-smooth collapse.**  The entire positive orientation is the
negative sum of Mertens values immediately below each prime up to `R`. -/
theorem squareRootPositiveSmoothMass_eq_neg_primeMertensTransform
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootPositiveSmoothMass R =
      -squareRootPositiveSmoothPrimeMertensTransform R := by
  rw [squareRootPositiveSmoothMass_eq_sourceMass R hR,
    squareRootPositiveSmoothSourceMass_eq_pairSourceMass,
    squareRootPositiveSmoothPairSourceMass_eq_neg_primeMertensTransform]

/-- The complete square-prefix Mertens value is exactly the collapsed positive
prime transform plus the matched born-smooth/transport term. -/
theorem squarePrefixMertens_eq_neg_positivePrimeTransform_add_matched
    (R : ℕ) (hR : 1 ≤ R) :
    RHLean.Analysis.squarePrefixMertens (R - 1) =
      -squareRootPositiveSmoothPrimeMertensTransform R +
        squareRootMatchedBornSmoothTransport R := by
  rw [squarePrefixMertens_eq_positiveSmooth_add_matched R hR,
    squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R hR]

/-- **Cross-track synthesis form.**  At a synchronized prime-wheel sample whose
square index is `R-1`, substitute the exact positive-smooth collapse into the
sample Mertens term before applying the unchanged wheel zero-mode centering.
This is only a coordinate identity; it asserts no bound on either signed term. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_positiveSmoothCollapsedCenter
    (k R : ℕ) (hR : 1 ≤ R)
    (hlower : primorialBlockLower k < RHLean.Analysis.squarePrefixEndpoint (R - 1))
    (hupper : RHLean.Analysis.squarePrefixEndpoint (R - 1) ≤ primorialBlockUpper k) :
    RHLean.Analysis.squareWheelNonzeroSampleResponse
        (primorialMinimalWheelSystem k) (R - 1) =
      ((-squareRootPositiveSmoothPrimeMertensTransform R +
          squareRootMatchedBornSmoothTransport R) -
        RHLean.Analysis.mertensSummatory (primorialBlockLower k)) -
      RHLean.Analysis.squareWheelSampleRatio
          (primorialMinimalWheelSystem k) (R - 1) *
        (RHLean.Analysis.mertensSummatory (primorialBlockUpper k) -
          RHLean.Analysis.mertensSummatory (primorialBlockLower k)) := by
  rw [RHLean.Analysis.primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter
    k (R - 1) hlower hupper]
  have hsquare := squarePrefixMertens_eq_positiveSmooth_add_matched R hR
  rw [squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R hR] at hsquare
  unfold RHLean.Analysis.squarePrefixMertens at hsquare
  unfold RHLean.Analysis.primorialSquareZeroModeCenter
  rw [hsquare]

end RHLean.Proof
