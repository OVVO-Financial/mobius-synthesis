import RHLean.Analysis.DyadicTransportCompression
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux
import RHLean.Proof.PostRootPartnerLogAlignment
import RHLean.Proof.SquareRootLowPrimeGoAncestryClock
import RHLean.Proof.SquareWheelSurvivorProcessedResponseBridge
import RHLean.Proof.SurvivorDyadicActivityMismatch

/-!
# Rough dyadic compression of q^2 daughters

The ordinary dyadic Mobius compression pairs an odd cofactor `d` with `2*d`.
For a q^2 daughter the cofactor is not an unrestricted Mertens prefix: it is
restricted to the predecessor wheel `P+(d) < q`.

For every odd prime owner `q > 2`, adjoining the prime coordinate 2 preserves
that predecessor-wheel condition on every nonzero Mobius atom.  Hence the same
exact cancellation works *inside the q-rough carrier* before any norm is taken.

The owner `q = 2` is intentionally excluded.  It is the distinguished
prime-two coordinate itself and remains the explicit owner-two term already
kept signed by the FAR synthesis.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The q-rough part of the ordinary odd dyadic boundary. -/
def roughDyadicCofactorBoundary (q B : ℕ) : Finset ℕ :=
  (dyadicCofactorBoundary B).filter fun d =>
    canonicalLargestPrimeFactor d < q

/-- Signed Mobius mass of the q-rough odd dyadic boundary. -/
def roughDyadicCofactorBoundaryMass (q B : ℕ) : ℂ :=
  ∑ d ∈ roughDyadicCofactorBoundary q B, canonicalMoebiusWeight d

@[simp] theorem mem_roughDyadicCofactorBoundary {q B d : ℕ} :
    d ∈ roughDyadicCofactorBoundary q B ↔
      d ∈ dyadicCofactorBoundary B ∧ canonicalLargestPrimeFactor d < q := by
  simp [roughDyadicCofactorBoundary]

private def roughDyadicWeight (q d : ℕ) : ℂ :=
  if canonicalLargestPrimeFactor d < q then canonicalMoebiusWeight d else 0

/-- On a squarefree odd parent, the predecessor-wheel condition is invariant
under adjoining the coordinate 2. -/
private theorem rough_two_mul_iff_of_odd_squarefree
    {q d : ℕ} (hq : q.Prime) (hqgt : 2 < q)
    (hd : Odd d) (hd1 : 1 ≤ d) (hsq : Squarefree d) :
    canonicalLargestPrimeFactor (2 * d) < q ↔
      canonicalLargestPrimeFactor d < q := by
  have h2copd : Nat.Coprime 2 d := hd.coprime_two_left
  have hsq2 : Squarefree (2 * d) :=
    (Nat.squarefree_mul h2copd).2 ⟨Nat.squarefree_two, hsq⟩
  constructor
  · intro hrough2
    have hdata2 : CanonicalSourceData q (2 * d) :=
      squareRootLowPrimeGo_canonicalSourceData_of_rough
        hq (by omega) hsq2 hrough2
    have hdata : CanonicalSourceData q d :=
      (canonicalSourceData_two_mul_iff_of_odd hd hqgt).mp hdata2
    exact canonicalLargestPrimeFactor_lt_of_sourceData hdata
  · intro hrough
    have hdata : CanonicalSourceData q d :=
      squareRootLowPrimeGo_canonicalSourceData_of_rough
        hq hd1 hsq hrough
    have hdata2 : CanonicalSourceData q (2 * d) :=
      (canonicalSourceData_two_mul_iff_of_odd hd hqgt).mpr hdata
    exact canonicalLargestPrimeFactor_lt_of_sourceData hdata2

/-- Exact masked doubling law.  The q-rough mask commutes with the prime-two
Mobius cancellation for every odd owner q.  Nonsquarefree parents vanish on
both sides, so no hidden support assumption is introduced. -/
private theorem roughDyadicWeight_two_mul
    (q d : ℕ) (hq : q.Prime) (hqgt : 2 < q) :
    roughDyadicWeight q (2 * d) =
      if Odd d then -roughDyadicWeight q d else 0 := by
  by_cases hd : Odd d
  · rw [if_pos hd]
    by_cases hsq : Squarefree d
    · have hd1 : 1 ≤ d := by
        rcases hd with ⟨k, hk⟩
        omega
      have hroughIff :=
        rough_two_mul_iff_of_odd_squarefree hq hqgt hd hd1 hsq
      by_cases hrough : canonicalLargestPrimeFactor d < q
      · have hrough2 : canonicalLargestPrimeFactor (2 * d) < q :=
          hroughIff.mpr hrough
        unfold roughDyadicWeight
        rw [if_pos hrough, if_pos hrough2,
          canonicalMoebiusWeight_two_mul, if_pos hd]
      · have hrough2 : ¬ canonicalLargestPrimeFactor (2 * d) < q := by
          intro h
          exact hrough (hroughIff.mp h)
        unfold roughDyadicWeight
        rw [if_neg hrough, if_neg hrough2]
        ring
    · have hmuZ : μ d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      have hmu : canonicalMoebiusWeight d = 0 := by
        simp [canonicalMoebiusWeight, hmuZ]
      have hmu2 : canonicalMoebiusWeight (2 * d) = 0 := by
        rw [canonicalMoebiusWeight_two_mul, if_pos hd, hmu, neg_zero]
      unfold roughDyadicWeight
      split_ifs <;> simp [hmu, hmu2]
  · rw [if_neg hd]
    have hmu2 : canonicalMoebiusWeight (2 * d) = 0 := by
      rw [canonicalMoebiusWeight_two_mul, if_neg hd]
    unfold roughDyadicWeight
    split_ifs <;> simp [hmu2]

private theorem rough_sum_Icc_eq_odd_add_even
    (q B : ℕ) :
    (∑ d ∈ Finset.Icc 1 B, roughDyadicWeight q d) =
      (∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d) +
        ∑ d ∈ evenCofactorPrefix B, roughDyadicWeight q d := by
  calc
    (∑ d ∈ Finset.Icc 1 B, roughDyadicWeight q d) =
        ∑ d ∈ Finset.Icc 1 B,
          ((if Odd d then roughDyadicWeight q d else 0) +
            (if Even d then roughDyadicWeight q d else 0)) := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hodd : Odd d
      · have hnotEven : ¬ Even d := Nat.not_even_iff_odd.mpr hodd
        simp [hodd, hnotEven]
      · have heven : Even d := Nat.not_odd_iff_even.mp hodd
        simp [hodd, heven]
    _ =
        (∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d) +
          ∑ d ∈ evenCofactorPrefix B, roughDyadicWeight q d := by
      rw [Finset.sum_add_distrib]
      unfold oddCofactorPrefix evenCofactorPrefix
      rw [Finset.sum_filter, Finset.sum_filter]

private theorem rough_sum_even_eq_sum_double
    (q B : ℕ) :
    (∑ d ∈ evenCofactorPrefix B, roughDyadicWeight q d) =
      ∑ e ∈ Finset.Icc 1 (B / 2), roughDyadicWeight q (2 * e) := by
  classical
  symm
  refine Finset.sum_bij (fun e _ => 2 * e) ?_ ?_ ?_ ?_
  · intro e he
    rcases Finset.mem_Icc.mp he with ⟨he1, heB⟩
    have h2eB : 2 * e ≤ B := by
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 heB
      simpa [Nat.mul_comm] using hmul
    have hePos : 0 < e := by omega
    have h2ePos : 0 < 2 * e := Nat.mul_pos (by norm_num) hePos
    exact mem_evenCofactorPrefix.mpr
      ⟨h2ePos, h2eB, even_two_mul e⟩
  · intro e1 _he1 e2 _he2 h
    change 2 * e1 = 2 * e2 at h
    omega
  · intro d hd
    rcases mem_evenCofactorPrefix.mp hd with ⟨hd1, hdB, hdeven⟩
    have hdouble : 2 * (d / 2) = d := Nat.two_mul_div_two_of_even hdeven
    refine ⟨d / 2, ?_, hdouble⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have hdne : d ≠ 0 := by omega
      have hdgt : 1 < d := Nat.one_lt_of_ne_zero_of_even hdne hdeven
      omega
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      have hmul : d / 2 * 2 = d := by
        simpa [Nat.mul_comm] using hdouble
      rw [hmul]
      exact hdB
  · intro e _he
    rfl

/-- The masked even sector is exactly the negative masked odd half-prefix. -/
private theorem rough_sum_even_eq_neg_odd_half
    (q B : ℕ) (hq : q.Prime) (hqgt : 2 < q) :
    (∑ d ∈ evenCofactorPrefix B, roughDyadicWeight q d) =
      -∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d := by
  rw [rough_sum_even_eq_sum_double]
  calc
    (∑ d ∈ Finset.Icc 1 (B / 2), roughDyadicWeight q (2 * d)) =
        ∑ d ∈ Finset.Icc 1 (B / 2),
          if Odd d then -roughDyadicWeight q d else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact roughDyadicWeight_two_mul q d hq hqgt
    _ = ∑ d ∈ oddCofactorPrefix (B / 2), -roughDyadicWeight q d := by
      unfold oddCofactorPrefix
      rw [Finset.sum_filter]
    _ = -∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d := by
      simp

/-- **Wheel-truncated dyadic survivor invariant.**  For every odd prime owner,
the q-rough predecessor prefix compresses exactly to its q-rough odd dyadic
boundary.  This is an equality of signed amplitudes before any norm. -/
theorem roughCofactorMobiusPrefixMass_eq_roughDyadicBoundaryMass
    {q B : ℕ} (hq : q.Prime) (hqgt : 2 < q) :
    roughCofactorMobiusPrefixMass q B =
      roughDyadicCofactorBoundaryMass q B := by
  unfold roughCofactorMobiusPrefixMass roughDyadicCofactorBoundaryMass
  change
    (∑ d ∈ Finset.Icc 1 B, roughDyadicWeight q d) =
      ∑ d ∈ roughDyadicCofactorBoundary q B, canonicalMoebiusWeight d
  rw [rough_sum_Icc_eq_odd_add_even q B,
    rough_sum_even_eq_neg_odd_half q B hq hqgt]
  have hsubset := oddCofactorPrefix_half_subset B
  have hpartition :
      (∑ d ∈ oddCofactorPrefix B \ oddCofactorPrefix (B / 2),
          roughDyadicWeight q d) +
        ∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d =
          ∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d := by
    exact Finset.sum_sdiff hsubset
  calc
    (∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d) +
          -∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d =
        (∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d) -
          ∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d := by ring
    _ = ∑ d ∈ oddCofactorPrefix B \ oddCofactorPrefix (B / 2),
          roughDyadicWeight q d := by
      exact (eq_sub_of_add_eq hpartition).symm
    _ = ∑ d ∈ dyadicCofactorBoundary B, roughDyadicWeight q d := by
      rfl
    _ = ∑ d ∈ roughDyadicCofactorBoundary q B,
          canonicalMoebiusWeight d := by
      unfold roughDyadicCofactorBoundary roughDyadicWeight
      rw [Finset.sum_filter]


/-! ## Weighted q-rough dyadic compression -/

private def roughDyadicWeightedWeight
    (q : ℕ) (a : ℕ → ℂ) (d : ℕ) : ℂ :=
  a d * roughDyadicWeight q d

private theorem roughDyadicWeightedWeight_two_mul
    (q d : ℕ) (a : ℕ → ℂ) (hq : q.Prime) (hqgt : 2 < q) :
    roughDyadicWeightedWeight q a (2 * d) =
      if Odd d then -(a (2 * d) * roughDyadicWeight q d) else 0 := by
  unfold roughDyadicWeightedWeight
  rw [roughDyadicWeight_two_mul q d hq hqgt]
  by_cases hd : Odd d <;> simp [hd]

private theorem rough_weighted_sum_Icc_eq_odd_add_even
    (q B : ℕ) (a : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 B, roughDyadicWeightedWeight q a d) =
      (∑ d ∈ oddCofactorPrefix B, roughDyadicWeightedWeight q a d) +
        ∑ d ∈ evenCofactorPrefix B, roughDyadicWeightedWeight q a d := by
  calc
    (∑ d ∈ Finset.Icc 1 B, roughDyadicWeightedWeight q a d) =
        ∑ d ∈ Finset.Icc 1 B,
          ((if Odd d then roughDyadicWeightedWeight q a d else 0) +
            (if Even d then roughDyadicWeightedWeight q a d else 0)) := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hodd : Odd d
      · have hnotEven : ¬ Even d := Nat.not_even_iff_odd.mpr hodd
        simp [hodd, hnotEven]
      · have heven : Even d := Nat.not_odd_iff_even.mp hodd
        simp [hodd, heven]
    _ =
        (∑ d ∈ oddCofactorPrefix B, roughDyadicWeightedWeight q a d) +
          ∑ d ∈ evenCofactorPrefix B, roughDyadicWeightedWeight q a d := by
      rw [Finset.sum_add_distrib]
      unfold oddCofactorPrefix evenCofactorPrefix
      rw [Finset.sum_filter, Finset.sum_filter]

private theorem rough_weighted_sum_even_eq_sum_double
    (q B : ℕ) (a : ℕ → ℂ) :
    (∑ d ∈ evenCofactorPrefix B, roughDyadicWeightedWeight q a d) =
      ∑ e ∈ Finset.Icc 1 (B / 2),
        roughDyadicWeightedWeight q a (2 * e) := by
  classical
  symm
  refine Finset.sum_bij (fun e _ => 2 * e) ?_ ?_ ?_ ?_
  · intro e he
    rcases Finset.mem_Icc.mp he with ⟨he1, heB⟩
    have h2eB : 2 * e ≤ B := by
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 heB
      simpa [Nat.mul_comm] using hmul
    have hePos : 0 < e := by omega
    have h2ePos : 0 < 2 * e :=
      Nat.mul_pos (by norm_num) hePos
    exact mem_evenCofactorPrefix.mpr
      ⟨Nat.succ_le_iff.mpr h2ePos, h2eB, even_two_mul e⟩
  · intro e1 _he1 e2 _he2 h
    change 2 * e1 = 2 * e2 at h
    omega
  · intro d hd
    rcases mem_evenCofactorPrefix.mp hd with ⟨hd1, hdB, hdeven⟩
    have hdouble : 2 * (d / 2) = d := Nat.two_mul_div_two_of_even hdeven
    refine ⟨d / 2, ?_, hdouble⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have hdne : d ≠ 0 := by omega
      have hdgt : 1 < d := Nat.one_lt_of_ne_zero_of_even hdne hdeven
      omega
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      have hmul : d / 2 * 2 = d := by
        simpa [Nat.mul_comm] using hdouble
      rw [hmul]
      exact hdB
  · intro e _he
    rfl

private theorem smooth_weighted_eq_masked
    (q B : ℕ) (a : ℕ → ℂ) :
    (∑ d ∈ squareRootLowPrimeGoSmoothCofactors q B,
        a d * canonicalMoebiusWeight d) =
      ∑ d ∈ Finset.Icc 1 B, roughDyadicWeightedWeight q a d := by
  unfold squareRootLowPrimeGoSmoothCofactors
    roughDyadicWeightedWeight roughDyadicWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hsq : Squarefree d
  · by_cases hrough : canonicalLargestPrimeFactor d < q
    · simp [hsq, hrough]
    · simp [hrough]
  · have hmuZ : μ d = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have hmu : canonicalMoebiusWeight d = 0 := by
      simp [canonicalMoebiusWeight, hmuZ]
    simp [hsq, hmu]

/-- **Weighted predecessor-wheel dyadic compression.**

For every odd prime owner, an arbitrary coefficient field on the q-rough
squarefree prefix can be paired before any norm.  Interior odd/even pairs retain
only the coefficient difference `a(d)-a(2d)`; the sole unpaired population is
the explicit q-rough top dyadic boundary. -/
theorem squareRootLowPrimeGoSmoothCofactorWeightedMass_eq_dyadicPairs_add_boundary
    {q B : ℕ} (hq : q.Prime) (hqgt : 2 < q) (a : ℕ → ℂ) :
    (∑ d ∈ squareRootLowPrimeGoSmoothCofactors q B,
        a d * canonicalMoebiusWeight d) =
      (∑ d ∈ oddCofactorPrefix (B / 2),
        if canonicalLargestPrimeFactor d < q then
          (a d - a (2 * d)) * canonicalMoebiusWeight d else 0) +
      ∑ d ∈ roughDyadicCofactorBoundary q B,
        a d * canonicalMoebiusWeight d := by
  rw [smooth_weighted_eq_masked q B a,
    rough_weighted_sum_Icc_eq_odd_add_even q B a,
    rough_weighted_sum_even_eq_sum_double q B a]
  have heven :
      (∑ d ∈ Finset.Icc 1 (B / 2),
          roughDyadicWeightedWeight q a (2 * d)) =
        ∑ d ∈ oddCofactorPrefix (B / 2),
          -(a (2 * d) * roughDyadicWeight q d) := by
    calc
      (∑ d ∈ Finset.Icc 1 (B / 2),
          roughDyadicWeightedWeight q a (2 * d)) =
        ∑ d ∈ Finset.Icc 1 (B / 2),
          if Odd d then -(a (2 * d) * roughDyadicWeight q d) else 0 := by
            apply Finset.sum_congr rfl
            intro d _hd
            exact roughDyadicWeightedWeight_two_mul q d a hq hqgt
      _ = ∑ d ∈ oddCofactorPrefix (B / 2),
          -(a (2 * d) * roughDyadicWeight q d) := by
            unfold oddCofactorPrefix
            rw [Finset.sum_filter]
  rw [heven]
  have hsubset := oddCofactorPrefix_half_subset B
  have hoddSplit :
      (∑ d ∈ oddCofactorPrefix B, roughDyadicWeightedWeight q a d) =
        (∑ d ∈ dyadicCofactorBoundary B,
          roughDyadicWeightedWeight q a d) +
        ∑ d ∈ oddCofactorPrefix (B / 2),
          roughDyadicWeightedWeight q a d := by
    unfold dyadicCofactorBoundary
    exact (Finset.sum_sdiff hsubset).symm
  rw [hoddSplit]
  have hpair :
      (∑ d ∈ oddCofactorPrefix (B / 2),
          roughDyadicWeightedWeight q a d) +
        (∑ d ∈ oddCofactorPrefix (B / 2),
          -(a (2 * d) * roughDyadicWeight q d)) =
        ∑ d ∈ oddCofactorPrefix (B / 2),
          if canonicalLargestPrimeFactor d < q then
            (a d - a (2 * d)) * canonicalMoebiusWeight d else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    unfold roughDyadicWeightedWeight roughDyadicWeight
    by_cases hrough : canonicalLargestPrimeFactor d < q
    · simp [hrough]
      ring
    · simp [hrough]
  have hboundary :
      (∑ d ∈ dyadicCofactorBoundary B,
          roughDyadicWeightedWeight q a d) =
        ∑ d ∈ roughDyadicCofactorBoundary q B,
          a d * canonicalMoebiusWeight d := by
    unfold roughDyadicCofactorBoundary roughDyadicWeightedWeight
      roughDyadicWeight
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _hd
    by_cases hrough : canonicalLargestPrimeFactor d < q <;> simp [hrough]
  rw [add_assoc, hpair, hboundary]
  ring

/-- The frozen q-predecessor cube is exactly the q-rough Mobius prefix in
complex currency.  This generic form lets the dyadic compression be applied at
every reciprocal cutoff `Y/p` in ChildFar, not only at the whole q^2 daughter
cutoff. -/
theorem frozenPrimeUniverseMass_cast_eq_roughCofactorMobiusPrefixMass
    {q B : ℕ} (hq : q.Prime) :
    ((frozenPrimeUniverseMass (primesUpTo (q - 1)) B : ℤ) : ℂ) =
      roughCofactorMobiusPrefixMass q B := by
  rw [frozenPrimeUniverseMass_eq_goSmoothCofactorSum hq]
  push_cast
  unfold squareRootLowPrimeGoSmoothCofactors
    roughCofactorMobiusPrefixMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hrough : canonicalLargestPrimeFactor d < q
  · rw [if_pos hrough]
    by_cases hsq : Squarefree d
    · simp [hsq, hrough, canonicalMoebiusWeight]
    · have hmu : μ d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hsq, hrough, canonicalMoebiusWeight, hmu]
  · simp [hrough]

/-- The literal Go q^2 daughter therefore lives on the q-rough dyadic boundary
for every odd owner q. -/
theorem squareRootLowPrimeGoWallSquareResidual_cast_eq_roughDyadicBoundaryMass
    {q X : ℕ} (hq : q.Prime) (hqgt : 2 < q) :
    (((squareRootLowPrimeGoWallSquareResidual q X : ℤ) : ℂ)) =
      roughDyadicCofactorBoundaryMass q (X / (q * q)) := by
  rw [squareRootLowPrimeGoWallSquareResidual_cast_eq_roughCofactorMobiusPrefixMass hq,
    roughCofactorMobiusPrefixMass_eq_roughDyadicBoundaryMass hq hqgt]

/-- Far-prime ChildFar column after exact q-rough dyadic compression in each
reciprocal p-fibre. -/
def q2DaughterFarRoughDyadicColumn (R q : ℕ) : ℂ :=
  let Y := squareRootEndpoint R / (q * q)
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
    roughDyadicCofactorBoundaryMass q (Y / p)

/-- The common q-predecessor far column compresses fibrewise to the q-rough
dyadic wall for every odd owner. -/
theorem q2DaughterFarBaseColumn_cast_eq_roughDyadicColumn
    {R q : ℕ} (hq : q.Prime) (hqgt : 2 < q) :
    ((q2DaughterFarBaseColumn R q : ℤ) : ℂ) =
      q2DaughterFarRoughDyadicColumn R q := by
  let Y := squareRootEndpoint R / (q * q)
  unfold q2DaughterFarBaseColumn q2DaughterFarRoughDyadicColumn
  push_cast
  apply Finset.sum_congr rfl
  intro p _hp
  rw [frozenPrimeUniverseMass_cast_eq_roughCofactorMobiusPrefixMass hq,
    roughCofactorMobiusPrefixMass_eq_roughDyadicBoundaryMass hq hqgt]

/-- **ChildFar compression.**  For every odd q^2 owner, the literal physical
ChildFar mass is exactly a sum of q-rough odd dyadic walls, one at each
reciprocal cutoff `Y_q/p`.  This is still a signed identity before norms. -/
theorem lowWheelFarPrimeQ2ChildFarSlice_mass_eq_roughDyadicColumn
    {R q : ℕ} (hq : q.Prime) (hqgt : 2 < q) :
    (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) =
      q2DaughterFarRoughDyadicColumn R q := by
  calc
    (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) =
      ((q2DaughterFarBaseColumn R q : ℤ) : ℂ) :=
        (q2DaughterFarBaseColumn_cast_eq_childFarSliceMass hq).symm
    _ = q2DaughterFarRoughDyadicColumn R q :=
      q2DaughterFarBaseColumn_cast_eq_roughDyadicColumn hq hqgt

/-- Every compressed q^2 ChildFar atom lifts to the *single global* top
odd dyadic wall.  Although the compression occurs at the reciprocal scale
`(X_R/q^2)/p`, multiplying back by `q^2 p` sends its strict half-window
exactly to `X_R/2 < q^2*d*p <= X_R`. -/
theorem roughDyadicQ2FarAtom_mem_topBoundary
    {R q p d : ℕ} (hq : q.Prime) (hqgt : 2 < q)
    (hp : p.Prime) (hpgt : 2 < p)
    (hd : d ∈ roughDyadicCofactorBoundary q
      ((squareRootEndpoint R / (q * q)) / p)) :
    q * q * d * p ∈ dyadicCofactorBoundary (squareRootEndpoint R) := by
  have hdWall := (mem_roughDyadicCofactorBoundary.mp hd).1
  rcases mem_dyadicCofactorBoundary.mp hdWall with
    ⟨hd1, hdCut, hdOdd, hhalf⟩
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hdp :
      d * p ≤ squareRootEndpoint R / (q * q) :=
    (Nat.le_div_iff_mul_le hp.pos).1 hdCut
  have hupper0 :
      (d * p) * (q * q) ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hq2Pos).1 hdp
  have hupper :
      q * q * d * p ≤ squareRootEndpoint R := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hupper0
  have hchildHalf :
      squareRootEndpoint R / (q * q) < (2 * d) * p :=
    (Nat.div_lt_iff_lt_mul hp.pos).1 hhalf
  have hlower0 :
      squareRootEndpoint R < ((2 * d) * p) * (q * q) :=
    (Nat.div_lt_iff_lt_mul hq2Pos).1 hchildHalf
  have hlower :
      squareRootEndpoint R < 2 * (q * q * d * p) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlower0
  have hqOdd : Odd q := hq.odd_of_ne_two (by omega)
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hnOdd : Odd (q * q * d * p) :=
    ((hqOdd.mul hqOdd).mul hdOdd).mul hpOdd
  have hdPos : 0 < d := by omega
  have hnPos : 0 < q * q * d * p := by positivity
  exact mem_dyadicCofactorBoundary.mpr
    ⟨by omega, hupper, hnOdd, hlower⟩

/-- The far-prime schedule used by ChildFar supplies the oddness hypothesis
automatically, so every atom of every compressed odd-owner p-fibre lands on the
same global top wall. -/
theorem roughDyadicQ2FarAtom_mem_topBoundary_of_highPrime
    {R q p d : ℕ} (hq : q.Prime) (hqgt : 2 < q)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet (R + 7)
      (squareRootEndpoint R / (q * q)))
    (hd : d ∈ roughDyadicCofactorBoundary q
      ((squareRootEndpoint R / (q * q)) / p)) :
    q * q * d * p ∈ dyadicCofactorBoundary (squareRootEndpoint R) := by
  rcases mem_frozenPrimeUniverseHighPrimeSet.mp hp with
    ⟨hpPrime, hpLo, _hpHi⟩
  exact roughDyadicQ2FarAtom_mem_topBoundary
    hq hqgt hpPrime (by omega) hd

private theorem largePrime_not_dvd_roughCofactor
    {r q d : ℕ} (hr : r.Prime) (hqr : q < r)
    (hd1 : 1 ≤ d) (hrough : canonicalLargestPrimeFactor d < q) :
    ¬ r ∣ d := by
  intro hrd
  by_cases hdOne : d = 1
  · subst d
    exact hr.not_dvd_one hrd
  · have hdgt : 1 < d := by omega
    have hrLe :=
      prime_dvd_le_canonicalLargestPrimeFactor hdgt hr hrd
    omega

/-- **Global multiplicity-free lift.**  An odd q^2 owner, its q-rough
cofactor and a post-root far prime are uniquely recoverable from the lifted
physical site `q^2*d*p`.  Thus distinct ChildFar atoms cannot pile up on the
same point of the global top dyadic wall. -/
theorem roughDyadicQ2FarLift_unique
    {R q q' d d' p p' : ℕ}
    (hq : q.Prime) (hqR : q < R)
    (hq' : q'.Prime) (hq'R : q' < R)
    (hd1 : 1 ≤ d) (hdrough : canonicalLargestPrimeFactor d < q)
    (hd1' : 1 ≤ d') (hdrough' : canonicalLargestPrimeFactor d' < q')
    (hp : p.Prime) (hpR : R < p)
    (hp' : p'.Prime) (hp'R : R < p')
    (heq : q * q * d * p = q' * q' * d' * p') :
    q = q' ∧ d = d' ∧ p = p' := by
  have hpLe : p ≤ p' := by
    have hpDiv : p ∣ q' * q' * d' * p' := by
      rw [← heq]
      simp
    rcases hp.dvd_mul.mp hpDiv with hbase | hpp'
    · rcases hp.dvd_mul.mp hbase with hqq' | hpd'
      · rcases hp.dvd_mul.mp hqq' with hpq' | hpq'
        · have hle := Nat.le_of_dvd hq'.pos hpq'
          omega
        · have hle := Nat.le_of_dvd hq'.pos hpq'
          omega
      · exact (largePrime_not_dvd_roughCofactor
          hp (by omega : q' < p) hd1' hdrough' hpd').elim
    · exact Nat.le_of_dvd hp'.pos hpp'
  have hp'Le : p' ≤ p := by
    have hp'Div : p' ∣ q * q * d * p := by
      rw [heq]
      simp
    rcases hp'.dvd_mul.mp hp'Div with hbase | hp'p
    · rcases hp'.dvd_mul.mp hbase with hqq | hp'd
      · rcases hp'.dvd_mul.mp hqq with hp'q | hp'q
        · have hle := Nat.le_of_dvd hq.pos hp'q
          omega
        · have hle := Nat.le_of_dvd hq.pos hp'q
          omega
      · exact (largePrime_not_dvd_roughCofactor
          hp' (by omega : q < p') hd1 hdrough hp'd).elim
    · exact Nat.le_of_dvd hp.pos hp'p
  have hpp : p = p' := Nat.le_antisymm hpLe hp'Le
  subst p'
  have hcore : q * q * d = q' * q' * d' :=
    Nat.mul_right_cancel hp.pos heq
  have hqLe : q ≤ q' := by
    have hqDiv : q ∣ q' * q' * d' := by
      rw [← hcore]
      exact ⟨q * d, by ring⟩
    rcases hq.dvd_mul.mp hqDiv with hqq' | hqd'
    · rcases hq.dvd_mul.mp hqq' with hqq' | hqq'
      · exact Nat.le_of_dvd hq'.pos hqq'
      · exact Nat.le_of_dvd hq'.pos hqq'
    · by_cases hdOne : d' = 1
      · subst d'
        exact (hq.not_dvd_one hqd').elim
      · have hdgt : 1 < d' := by omega
        have hle :=
          prime_dvd_le_canonicalLargestPrimeFactor hdgt hq hqd'
        omega
  have hq'Le : q' ≤ q := by
    have hq'Div : q' ∣ q * q * d := by
      rw [hcore]
      exact ⟨q' * d', by ring⟩
    rcases hq'.dvd_mul.mp hq'Div with hqq | hq'd
    · rcases hq'.dvd_mul.mp hqq with hq'q | hq'q
      · exact Nat.le_of_dvd hq.pos hq'q
      · exact Nat.le_of_dvd hq.pos hq'q
    · by_cases hdOne : d = 1
      · subst d
        exact (hq'.not_dvd_one hq'd).elim
      · have hdgt : 1 < d := by omega
        have hle :=
          prime_dvd_le_canonicalLargestPrimeFactor hdgt hq' hq'd
        omega
  have hqq : q = q' := Nat.le_antisymm hqLe hq'Le
  subst q'
  have hdd : d = d' := by
    exact Nat.mul_left_cancel (Nat.mul_pos hq.pos hq.pos) hcore
  exact ⟨rfl, hdd, rfl⟩

/-- On the actual rough dyadic ChildFar support, positivity and roughness are
automatic; only the owner/root and far-prime clock inequalities need to be
supplied to recover the full atom uniquely. -/
theorem roughDyadicQ2FarLift_unique_of_mem
    {R q q' d d' p p' : ℕ}
    (hq : q.Prime) (hqR : q < R)
    (hq' : q'.Prime) (hq'R : q' < R)
    (hp : p.Prime) (hpR : R < p)
    (hp' : p'.Prime) (hp'R : R < p')
    (hd : d ∈ roughDyadicCofactorBoundary q
      ((squareRootEndpoint R / (q * q)) / p))
    (hd' : d' ∈ roughDyadicCofactorBoundary q'
      ((squareRootEndpoint R / (q' * q')) / p'))
    (heq : q * q * d * p = q' * q' * d' * p') :
    q = q' ∧ d = d' ∧ p = p' := by
  have hdData := mem_roughDyadicCofactorBoundary.mp hd
  have hdData' := mem_roughDyadicCofactorBoundary.mp hd'
  have hdWall := mem_dyadicCofactorBoundary.mp hdData.1
  have hdWall' := mem_dyadicCofactorBoundary.mp hdData'.1
  exact roughDyadicQ2FarLift_unique
    hq hqR hq' hq'R
    hdWall.1 hdData.2 hdWall'.1 hdData'.2
    hp hpR hp' hp'R heq

/-- Aggregate odd-owner ChildFar mass after the same exact compression. -/
def squareEndpointQ2OddChildFarRoughDyadicColumn (R : ℕ) : ℂ :=
  ∑ q ∈ (primesUpTo (R - 1)).erase 2,
    q2DaughterFarRoughDyadicColumn R q

/-- The whole odd-owner ChildFar column is carried by the wheel-truncated
dyadic walls.  Owner two is deliberately absent from both sides. -/
theorem squareEndpointQ2OddChildFarSlice_eq_roughDyadicColumn
    (R : ℕ) :
    (∑ q ∈ (primesUpTo (R - 1)).erase 2,
      ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) =
      squareEndpointQ2OddChildFarRoughDyadicColumn R := by
  unfold squareEndpointQ2OddChildFarRoughDyadicColumn
  apply Finset.sum_congr rfl
  intro q hq
  rcases Finset.mem_erase.mp hq with ⟨hqne, hqmem⟩
  have hqPrime : q.Prime := (mem_primesUpTo.mp hqmem).1
  have hqgt : 2 < q := by
    have hq2 := hqPrime.two_le
    omega
  exact lowWheelFarPrimeQ2ChildFarSlice_mass_eq_roughDyadicColumn hqPrime hqgt

end RHLean.Proof
