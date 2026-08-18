import Mathlib
import RHLean.Analysis.SquareRootMatchedTransport
import RHLean.Proof.CanonicalGapAncestryBridge

/-!
# Realize the original square-root transport term

An earlier layer exposed the prime-dilated transport expression and the matched
born-smooth minus transport object.  This module closes the remaining exact
interface to the original dynamic identity

`S = A - T`.

For `R >= 1`, the dynamic transport population at stage `R - 1` consists
exactly of canonical sources whose largest prime `q` lies above `R`.  Since the
whole source lies below `R^2`, its canonical cofactor `c` is automatically
strictly below `R`, hence `c < q`.  The canonical factorization therefore gives
a bijection

`m < R^2, R < P+(m)  <->  1 <= c < R < q, q prime, c*q <= R^2 - 1`.

Along that bijection `mu(c*q) = -mu(c)`, so the sign-reversed dynamic transport
mass is exactly the cofactor-first transport term already used by the `2ab`
prime-dilation layer.

No analytic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Canonical source integers in the square prefix whose largest prime lies
strictly above the square-root cutoff. -/
def squareRootHighTransportSourceSet (R : ℕ) : Finset ℕ :=
  (cumulativeSquarePrefixSet (R - 1)).filter fun m =>
    R < canonicalLargestPrimeFactor m

/-- Canonical cofactor/prime pairs for the same high transport population. -/
def squareRootTransportPairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 R).product (Finset.Ioc R (squareRootEndpoint R))).filter
    fun cq => cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R

/-- The high transport population with its native source sign reversed, written
on canonical cofactor/prime pairs. -/
def squareRootTransportPairSourceMass (R : ℕ) : ℂ :=
  ∑ cq ∈ squareRootTransportPairSet R,
    -canonicalMoebiusWeight (cq.1 * cq.2)

private theorem one_lt_of_mem_squareRootHighTransportSourceSet
    {R m : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R) :
    1 < m := by
  have hhigh := (Finset.mem_filter.mp hm).2
  by_contra hnot
  have hP : canonicalLargestPrimeFactor m = 1 := by
    unfold canonicalLargestPrimeFactor
    rw [dif_neg hnot]
  omega

private theorem highTransportSource_to_pair_mem
    {R m : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R) :
    (canonicalCofactor m, canonicalLargestPrimeFactor m) ∈
      squareRootTransportPairSet R := by
  rcases Finset.mem_filter.mp hm with ⟨hmPrefix, hhigh⟩
  have hmgt : 1 < m :=
    one_lt_of_mem_squareRootHighTransportSourceSet hR hm
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  have hmLt : m < R ^ 2 := by
    simpa [cumulativeSquarePrefixSet, hpred] using hmPrefix
  have hprod :
      canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hmgt
  have hqPrime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hmgt
  have hcPos : 0 < canonicalCofactor m := by
    by_contra hnot
    have hc0 : canonicalCofactor m = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hc0, zero_mul] at hprod
    omega
  have hcR : canonicalCofactor m < R := by
    by_contra hnot
    have hRc : R ≤ canonicalCofactor m := Nat.le_of_not_gt hnot
    have hleft : R * R ≤ canonicalCofactor m * R :=
      Nat.mul_le_mul_right R hRc
    have hright :
        canonicalCofactor m * R <
          canonicalCofactor m * canonicalLargestPrimeFactor m :=
      Nat.mul_lt_mul_of_pos_left hhigh hcPos
    have hRRm : R ^ 2 < m := by
      rw [pow_two]
      calc
        R * R ≤ canonicalCofactor m * R := hleft
        _ < canonicalCofactor m * canonicalLargestPrimeFactor m := hright
        _ = m := hprod
    omega
  have hmX : m ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hqDvd : canonicalLargestPrimeFactor m ∣ m :=
    canonicalLargestPrimeFactor_dvd hmgt
  have hqLe : canonicalLargestPrimeFactor m ≤ m :=
    Nat.le_of_dvd (by omega) hqDvd
  have hqX : canonicalLargestPrimeFactor m ≤ squareRootEndpoint R :=
    hqLe.trans hmX
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨Nat.succ_le_iff.mpr hcPos, hcR⟩,
        Finset.mem_Ioc.mpr ⟨hhigh, hqX⟩⟩
  · exact ⟨hqPrime, by simpa [hprod] using hmX⟩

private theorem highTransportSource_pair_injective
    {R m n : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R)
    (hn : n ∈ squareRootHighTransportSourceSet R)
    (hpair :
      (canonicalCofactor m, canonicalLargestPrimeFactor m) =
        (canonicalCofactor n, canonicalLargestPrimeFactor n)) :
    m = n := by
  have hmgt : 1 < m :=
    one_lt_of_mem_squareRootHighTransportSourceSet hR hm
  have hngt : 1 < n :=
    one_lt_of_mem_squareRootHighTransportSourceSet hR hn
  have hmprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  have hnprod := canonicalCofactor_mul_largestPrimeFactor hngt
  have hc : canonicalCofactor m = canonicalCofactor n :=
    congrArg Prod.fst hpair
  have hq : canonicalLargestPrimeFactor m = canonicalLargestPrimeFactor n :=
    congrArg Prod.snd hpair
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hmprod.symm
    _ = canonicalCofactor n * canonicalLargestPrimeFactor n := by rw [hc, hq]
    _ = n := hnprod

private theorem transportPair_surjective
    {R : ℕ} (hR : 1 ≤ R)
    (cq : ℕ × ℕ) (hcq : cq ∈ squareRootTransportPairSet R) :
    ∃ m ∈ squareRootHighTransportSourceSet R,
      (canonicalCofactor m, canonicalLargestPrimeFactor m) = cq := by
  rcases Finset.mem_filter.mp hcq with ⟨hbase, hdata⟩
  rcases Finset.mem_product.mp hbase with ⟨hcMem, hqMem⟩
  rcases Finset.mem_Ico.mp hcMem with ⟨hc1, hcR⟩
  rcases Finset.mem_Ioc.mp hqMem with ⟨hRq, hqX⟩
  rcases hdata with ⟨hqPrime, hmulX⟩
  have hcPos : 0 < cq.1 := Nat.zero_lt_of_lt hc1
  have hcqLt : cq.1 < cq.2 := lt_trans hcR hRq
  have hlargest :
      canonicalLargestPrimeFactor (cq.1 * cq.2) = cq.2 :=
    canonicalLargestPrimeFactor_mul_prime_eq hcPos hcqLt hqPrime
  have hcofactor : canonicalCofactor (cq.1 * cq.2) = cq.1 :=
    canonicalCofactor_mul_prime_eq hcPos hcqLt hqPrime
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  have hRsqOne : 1 ≤ R ^ 2 := by
    have hp := Nat.pow_le_pow_left hR 2
    norm_num at hp ⊢
    exact hp
  have hsubadd : R ^ 2 - 1 + 1 = R ^ 2 :=
    Nat.sub_add_cancel hRsqOne
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    omega
  have hmPrefix : cq.1 * cq.2 ∈ cumulativeSquarePrefixSet (R - 1) := by
    simp only [cumulativeSquarePrefixSet, Finset.mem_range, hpred]
    exact lt_of_le_of_lt hmulX hXlt
  have hmHigh : R < canonicalLargestPrimeFactor (cq.1 * cq.2) := by
    simpa only [hlargest] using hRq
  refine ⟨cq.1 * cq.2, Finset.mem_filter.mpr ⟨hmPrefix, hmHigh⟩, ?_⟩
  apply Prod.ext
  · exact hcofactor
  · exact hlargest

/-- Reindex the dynamic high-source population by its canonical cofactor and
largest-prime coordinates. -/
theorem sum_squareRootHighTransportSourceSet_eq_pairProducts
    (R : ℕ) (hR : 1 ≤ R) :
    (∑ m ∈ squareRootHighTransportSourceSet R, canonicalMoebiusWeight m) =
      ∑ cq ∈ squareRootTransportPairSet R,
        canonicalMoebiusWeight (cq.1 * cq.2) := by
  classical
  refine Finset.sum_bij
    (fun m _hm => (canonicalCofactor m, canonicalLargestPrimeFactor m))
    (fun m hm => highTransportSource_to_pair_mem hR hm)
    (fun m hm n hn hmn => highTransportSource_pair_injective hR hm hn hmn)
    (fun cq hcq => by
      simpa using (transportPair_surjective hR cq hcq))
    ?_
  intro m hm
  have hmgt : 1 < m :=
    one_lt_of_mem_squareRootHighTransportSourceSet hR hm
  rw [canonicalCofactor_mul_largestPrimeFactor hmgt]

/-- The original dynamic transport definition is the negative source mass on
the high-largest-prime population. -/
theorem squareRootTransportMass_eq_neg_highSourceMass
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootTransportMass (R - 1) =
      -∑ m ∈ squareRootHighTransportSourceSet R, canonicalMoebiusWeight m := by
  unfold squareRootTransportMass squareRootHighTransportSourceSet
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  rw [hpred]
  rw [Finset.sum_filter]

/-- The pair-source mass is exactly the cofactor-first `T_R`: on every retained
pair `c < R < q`, the prime `q` is coprime to `c` and flips the Möbius sign. -/
theorem squareRootTransportPairSourceMass_eq_cofactorFirst
    (R : ℕ) :
    squareRootTransportPairSourceMass R =
      squareRootTransportCofactorFirst R := by
  classical
  unfold squareRootTransportPairSourceMass squareRootTransportPairSet
    squareRootTransportCofactorFirst
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈ (Finset.Ico 1 R).product (Finset.Ioc R (squareRootEndpoint R)),
        if cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R then
          -canonicalMoebiusWeight (cq.1 * cq.2)
        else 0) =
      ∑ c ∈ Finset.Ico 1 R,
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime ∧ c * q ≤ squareRootEndpoint R then
            -canonicalMoebiusWeight (c * q)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Ico 1 R)
          (t := Finset.Ioc R (squareRootEndpoint R))
          (f := fun cq : ℕ × ℕ =>
            if cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R then
              -canonicalMoebiusWeight (cq.1 * cq.2)
            else 0))
    _ = ∑ c ∈ Finset.Ico 1 R,
          ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
            if q.Prime ∧ c * q ≤ squareRootEndpoint R then
              canonicalMoebiusWeight c
            else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hprime : q.Prime
      · by_cases hmul : c * q ≤ squareRootEndpoint R
        · have hcData := Finset.mem_Ico.mp hc
          have hqData := Finset.mem_Ioc.mp hq
          have hcPos : 0 < c := Nat.zero_lt_of_lt hcData.1
          have hcq : c < q := lt_trans hcData.2 hqData.1
          have hweight := canonicalMoebiusWeight_mul_prime_eq_neg hcPos hcq hprime
          simp [hprime, hmul, hweight]
        · simp [hprime, hmul]
      · simp [hprime]

/-- The prime-dilated `T_R` is exactly the original dynamic transport
term appearing in `squarePrefixMertens = smooth - transport`. -/
theorem squareRootTransportMass_pred_eq_cofactorFirst
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootTransportMass (R - 1) =
      squareRootTransportCofactorFirst R := by
  calc
    squareRootTransportMass (R - 1) =
        -∑ m ∈ squareRootHighTransportSourceSet R,
          canonicalMoebiusWeight m :=
      squareRootTransportMass_eq_neg_highSourceMass R hR
    _ = squareRootTransportPairSourceMass R := by
      have hsum :=
        sum_squareRootHighTransportSourceSet_eq_pairProducts R hR
      have hneg := congrArg Neg.neg hsum
      simpa [squareRootTransportPairSourceMass] using hneg
    _ = squareRootTransportCofactorFirst R :=
      squareRootTransportPairSourceMass_eq_cofactorFirst R

/-- Consequently the matched decomposition is now literally the
original square-prefix Mertens identity. -/
theorem squarePrefixMertens_eq_positiveSmooth_add_matched
    (R : ℕ) (hR : 1 ≤ R) :
    RHLean.Analysis.squarePrefixMertens (R - 1) =
      squareRootPositiveSmoothMass R +
        squareRootMatchedBornSmoothTransport R := by
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport]
  rw [squareRootTransportMass_pred_eq_cofactorFirst R hR]
  rw [squareRootTransportCofactorFirst_eq_primeFirst]
  exact squareRootSmooth_sub_transport_eq_positive_add_matched R hR

/-- Subtraction form of the same terminal bridge. -/
theorem squareRootMatchedBornSmoothTransport_eq_mertens_sub_positiveSmooth
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootMatchedBornSmoothTransport R =
      RHLean.Analysis.squarePrefixMertens (R - 1) -
        squareRootPositiveSmoothMass R := by
  rw [squarePrefixMertens_eq_positiveSmooth_add_matched R hR]
  ring

end RHLean.Proof
