import Mathlib
import RHLean.Proof.PrimeSievePostSqrtGap
import RHLean.Analysis.PrimeDilateTransportCompression
import RHLean.Analysis.SquareRootTransportRealization

/-!
# Elementary prime-sieve realization of square-root transport

The generic post-square-root sieve theorem in `PrimeSievePostSqrtGap` states
that, after all primes through `y > sqrt x` have acted in the all-plus comb, the
remaining discrepancy from `M(x)` is exactly twice the lower-scale Mertens tail
carried by primes above `y`.

The arbitrary-prime cofactor compression theorem now rewrites each lower-scale
Mertens value in that tail as the exact `p`-free reciprocal shell

```text
floor(x/q) / p < c <= floor(x/q),   p ∤ c.
```

Thus, for any fixed prime `p`, the generic post-square-root gap is exactly a sum
of the same prime-dilate boundary shells identified geometrically in
`PrimeDilateTransportCompression`.  When `p <= y < q`, the acting prime `p` and
unprocessed prime `q` are automatically distinct, so this is literally the
parent/child mechanism of the prime-dilate transport theorem.

The second half of the module specializes that elementary process to the
complete square endpoint

```text
x = R^2 - 1,   y = R,
```

and identifies the resulting pre-large-prime state with the original
square-block smooth/transport variables:

```text
before the remaining large-prime flips:  A_R + T_R
after all prime flips:                  A_R - T_R = M(R^2-1).
```

Thus the transport term is literally half the gap between those two finite
prime-sieve states, while the smooth term is half their sum.  No analytic
estimate is used or claimed.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## Arbitrary-prefix prime-dilate shell form -/

/-- The post-square-root prime tail after replacing every lower-scale Mertens
value by its exact `p`-free reciprocal boundary shell. -/
def primeSievePrimeDilateShellTail (p y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    if q.Prime then
      ∑ c ∈ primeDilatePrefixReciprocalShell p x q,
        canonicalMoebiusWeight c
    else
      0

/-- Every lower-scale Mertens value in a `q`-fiber is exactly the mass of the
arbitrary-prefix `1/p` shell from `PrimeDilateTransportCompression`. -/
theorem mertensSummatory_primeDilatePrefixCutoff_eq_shellMass
    (p x q : ℕ) (hp : p.Prime) :
    RHLean.Analysis.mertensSummatory (primeDilatePrefixCutoff x q) =
      ∑ c ∈ primeDilatePrefixReciprocalShell p x q,
        canonicalMoebiusWeight c := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory
    (primeDilatePrefixCutoff x q)]
  rw [cofactorMobiusPrefixMass_eq_primeCofactorBoundaryMass
    p (primeDilatePrefixCutoff x q) hp]
  unfold primeCofactorBoundaryMass
  rw [primeCofactorBoundary_eq_primeDilatePrefixReciprocalShell]

/-- The Mertens prime tail is exactly the sum of the moving `1/p` boundary
shells in all unresolved prime fibers. -/
theorem primeSieveMertensPrimeTail_eq_primeDilateShellTail
    (p y x : ℕ) (hp : p.Prime) :
    primeSieveMertensPrimeTail y x =
      primeSievePrimeDilateShellTail p y x := by
  unfold primeSieveMertensPrimeTail primeSievePrimeDilateShellTail
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hprime : q.Prime
  · simp only [hprime, if_true]
    simpa only [primeDilatePrefixCutoff] using
      (mertensSummatory_primeDilatePrefixCutoff_eq_shellMass p x q hp)
  · simp [hprime]

/-- **Arbitrary-prefix shell gap identity.**  For every `x`, once the sieve
cutoff lies strictly above `sqrt x`, the remaining discrepancy is exactly twice
the total `p`-free prime-dilate boundary mass, for any fixed prime `p`. -/
theorem allPlusPrimeCombPrefixMass_sub_mertens_eq_two_primeDilateShellTail
    (p y x : ℕ) (hp : p.Prime) (hroot : Nat.sqrt x < y) :
    allPlusPrimeCombPrefixMass y x - RHLean.Analysis.mertensSummatory x =
      2 * primeSievePrimeDilateShellTail p y x := by
  rw [allPlusPrimeCombPrefixMass_sub_mertens_eq_two_mertensPrimeTail y x hroot,
    primeSieveMertensPrimeTail_eq_primeDilateShellTail p y x hp]

/-- A prime already processed by the cutoff is distinct from every unresolved
prime in the post-square-root tail. -/
theorem processedPrime_ne_unprocessedPrime
    {p y x q : ℕ} (hpy : p ≤ y) (hq : q ∈ Finset.Ioc y x) :
    p ≠ q := by
  have hyq := (Finset.mem_Ioc.mp hq).1
  omega

/-! ## Complete square specialization -/

/-- Sum of the all-plus prime-comb state over a complete square prefix after all
primes at most `R` have acted. -/
def allPlusSquareRootPrimeCombMass (R : ℕ) : ℂ :=
  ∑ m ∈ cumulativeSquarePrefixSet (R - 1),
    (((allPlusPrimeCombSite (primesUpTo R) m : ℤ) : ℂ))

private theorem squareRootEndpoint_sqrt_lt
    {R : ℕ} (hR : 1 ≤ R) :
    Nat.sqrt (squareRootEndpoint R) < R := by
  apply (Nat.sqrt_lt').2
  unfold squareRootEndpoint
  have hpos : 0 < R ^ 2 := by positivity
  omega

/-- Before the primes above `R` have acted, the complete square-prefix all-plus
state is exactly `smooth + transport`.  This is the elementary counterpart of
the already-proved final identity `M = smooth - transport`. -/
theorem allPlusSquareRootPrimeCombMass_eq_smooth_add_transport
    (R : ℕ) (hR : 2 ≤ R) :
    allPlusSquareRootPrimeCombMass R =
      squareRootSmoothMass (R - 1) + squareRootTransportMass (R - 1) := by
  classical
  have hR1 : 1 ≤ R := by omega
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR1
  have hsqrt : Nat.sqrt (squareRootEndpoint R) ≤ R :=
    (squareRootEndpoint_sqrt_lt hR1).le
  have hcover : PrimeWheelSqrtCoverage (primesUpTo R) (squareRootEndpoint R) :=
    primesUpTo_sqrtCoverage hsqrt
  have hprime : ∀ p ∈ primesUpTo R, Nat.Prime p := by
    intro p hp
    exact prime_of_mem_primesUpTo hp
  unfold allPlusSquareRootPrimeCombMass squareRootSmoothMass squareRootTransportMass
  rw [hpred]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    simp [allPlusPrimeCombSite, canonicalMoebiusWeight]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmLt : m < R ^ 2 := by
      simpa [cumulativeSquarePrefixSet, hpred] using hm
    have hmUpper : m ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      omega
    by_cases hsq : Squarefree m
    · have hsmoothIff :=
        isPrimeWheelSmooth_primesUpTo_iff_largestPrime_le hR1 hmpos hsq
      by_cases hq : canonicalLargestPrimeFactor m ≤ R
      · have hsmooth : IsPrimeWheelSmooth (primesUpTo R) m := hsmoothIff.mpr hq
        have hsite := allPlusPrimeCombSite_eq_moebius_of_smooth
          (primesUpTo R) hprime hmpos hsmooth
        rw [hsite]
        simp [hq, canonicalMoebiusWeight]
      · have hsmooth : ¬ IsPrimeWheelSmooth (primesUpTo R) m := by
          intro hs
          exact hq (hsmoothIff.mp hs)
        have hqgt : R < canonicalLargestPrimeFactor m := Nat.lt_of_not_ge hq
        have hsite := allPlusPrimeCombSite_eq_neg_moebius_of_not_smooth
          (primesUpTo R) hprime hcover hsq hmUpper hsmooth
        rw [hsite]
        simp [hq, hqgt, canonicalMoebiusWeight]
    · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      have hsite := allPlusPrimeCombSite_eq_zero_of_not_squarefree
        (primesUpTo R) hcover hmpos hmUpper hsq
      rw [hsite]
      simp [hmu, canonicalMoebiusWeight]

/-- Exact elementary gap identity at a complete square endpoint: the difference
between the state before and after the remaining large-prime flips is twice the
original square-root transport mass. -/
theorem allPlusSquareRootPrimeCombMass_sub_mertens_eq_two_transport
    (R : ℕ) (hR : 2 ≤ R) :
    allPlusSquareRootPrimeCombMass R -
        RHLean.Analysis.squarePrefixMertens (R - 1) =
      2 * squareRootTransportMass (R - 1) := by
  rw [allPlusSquareRootPrimeCombMass_eq_smooth_add_transport R hR]
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport]
  ring

/-- The complementary half-sum is exactly the original smooth contribution.
This names the identification `A_R = (before + after)/2` without introducing
any division into the formal statement. -/
theorem allPlusSquareRootPrimeCombMass_add_mertens_eq_two_smooth
    (R : ℕ) (hR : 2 ≤ R) :
    allPlusSquareRootPrimeCombMass R +
        RHLean.Analysis.squarePrefixMertens (R - 1) =
      2 * squareRootSmoothMass (R - 1) := by
  rw [allPlusSquareRootPrimeCombMass_eq_smooth_add_transport R hR]
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport]
  ring

/-- Prime-first form of the same square-endpoint gap.  The transport is
literally the batch sum of lower-scale Mertens values carried by the as-yet
unprocessed primes `q > R`. -/
theorem allPlusSquareRootPrimeCombMass_sub_mertens_eq_mertensPrimeTail
    (R : ℕ) (hR : 2 ≤ R) :
    allPlusSquareRootPrimeCombMass R -
        RHLean.Analysis.squarePrefixMertens (R - 1) =
      2 *
        (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime then
            RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
          else
            0) := by
  rw [allPlusSquareRootPrimeCombMass_sub_mertens_eq_two_transport R hR]
  rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]
  rw [squareRootTransportCofactorFirst_eq_primeFirst]
  rw [squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)]

/-- The square-endpoint prime tail is the specialization of the generic
post-square-root transport batch. -/
theorem primeSieveMertensPrimeTail_squareRootEndpoint
    (R : ℕ) :
    primeSieveMertensPrimeTail R (squareRootEndpoint R) =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if q.Prime then
          RHLean.Analysis.mertensSummatory (squareRootEndpoint R / q)
        else
          0 := by
  rfl

end RHLean.Proof
