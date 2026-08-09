import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm
import RHLean.Analysis.SquareRootTransportRealization
import RHLean.Proof.CanonicalGapAncestryEnergyBridge

/-!
# Square-root triangular form of the canonical ancestry root

The canonical ancestry flow and the square-root transport decomposition are two
exact descriptions of the same largest-prime geometry.  This file identifies
the root term of the ancestry renewal directly, without splitting it at the
artificial seam `q = R`.

At the square endpoint `X = R^2 - 1`, a root has canonical coordinates
`m = c*q` with `q = P+(m)` and `c < q`.  Necessarily `c < R`, so the complete
root population is the single square-root-inversion interval

`1 <= c < R,  c < q,  c*q <= X,  q prime`.

Since `mu(c*q) = -mu(c)`, this gives a cofactor-first root transform.  Fubini
then gives the prime-first form

`- sum_{q <= X, q prime} M(min(q-1, floor(X/q)))`.

Every Mertens argument in this formula is strictly below `R`.  Thus the ancestry
root is genuinely lower-triangular at the square-root scale.  No norm estimate
or RH-scale bound is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

/-- Integer Mertens prefix, convenient for the integer-valued ancestry flow. -/
def mertensSummatoryInt (x : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (x + 1), μ n

@[simp] theorem mertensSummatoryInt_cast (x : ℕ) :
    (mertensSummatoryInt x : ℂ) = RHLean.Analysis.mertensSummatory x := by
  unfold mertensSummatoryInt RHLean.Analysis.mertensSummatory
  push_cast
  rfl

/-- Omitting the zero term turns the integer Mertens prefix into the positive
cofactor prefix. -/
theorem mertensSummatoryInt_eq_Icc (x : ℕ) :
    mertensSummatoryInt x = ∑ c ∈ Finset.Icc 1 x, μ c := by
  unfold mertensSummatoryInt
  have hset :
      Finset.range (x + 1) = insert 0 (Finset.Icc 1 x) := by
    ext n
    simp
    omega
  rw [hset]
  simp

/-- Square-prefix and square-root endpoints agree after the native predecessor
clock. -/
theorem squarePrefixEndpoint_pred_eq_squareRootEndpoint
    (R : ℕ) (hR : 1 ≤ R) :
    RHLean.Analysis.squarePrefixEndpoint (R - 1) = squareRootEndpoint R := by
  unfold RHLean.Analysis.squarePrefixEndpoint squareRootEndpoint
  rw [Nat.sub_add_cancel hR]

/-- Clock-pushed root term of the bounded canonical ancestry flow. -/
def sourceRootPrefix (B x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x (boundedSourceFlow B).rootField

/-- Active transport-oriented roots under a square-prefix clock. -/
def activeRootSourceSet (B x : ℕ) : Finset (SourceIndex B) := by
  classical
  exact Finset.univ.filter fun s =>
    SourceAdmissible s ∧ sourceClock B s ≤ x ∧ TransportOriented s

/-- The abstract root-field pushforward is exactly the sum over active
transport-oriented canonical sources. -/
theorem sourceRootPrefix_eq_activeRoot_sum (B x : ℕ) :
    sourceRootPrefix B x =
      ∑ s ∈ activeRootSourceSet B x, sourceWeight s := by
  classical
  unfold sourceRootPrefix activeRootSourceSet clockPushforward
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hclock : sourceClock B s ≤ x
  · by_cases hadm : SourceAdmissible s
    · by_cases htrans : TransportOriented s
      · have hnone : sourceParent s = none :=
          (sourceParent_eq_none_iff_transport s hadm).2 htrans
        simp [boundedSourceFlow, ParentFlow.rootField, hclock, hadm, htrans,
          hnone]
      · have hnotnone : sourceParent s ≠ none := by
          intro hnone
          exact htrans ((sourceParent_eq_none_iff_transport s hadm).1 hnone)
        cases hparent : sourceParent s with
        | none => exact False.elim (hnotnone hparent)
        | some p =>
            simp [boundedSourceFlow, ParentFlow.rootField, hclock, hadm, htrans,
              hparent]
    · cases hparent : sourceParent s <;>
        simp [boundedSourceFlow, ParentFlow.rootField, sourceWeight, hclock,
          hadm, hparent]
  · simp [hclock]

/-- Canonical cofactor/prime pairs for all active ancestry roots at square-root
cutoff `R`.  The squarefree condition makes this set exactly bijective with the
native source universe; it will disappear after the Möbius sign rewrite. -/
def squareRootAncestryRootPairSet (R : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((Finset.Ico 1 R).product (Finset.Icc 2 (squareRootEndpoint R))).filter
      fun cq =>
        cq.2.Prime ∧ Squarefree cq.1 ∧ cq.1 < cq.2 ∧
          cq.1 * cq.2 ≤ squareRootEndpoint R

/-- Native signed root mass on canonical cofactor/prime pairs. -/
def squareRootAncestryRootPairMass (R : ℕ) : ℤ :=
  ∑ cq ∈ squareRootAncestryRootPairSet R, μ (cq.1 * cq.2)

/-- The same root with the largest prime removed from the Möbius weight. -/
def squareRootAncestryRootCofactorMass (R : ℕ) : ℤ :=
  -∑ c ∈ Finset.Ico 1 R,
    ∑ q ∈ Finset.Icc 2 (squareRootEndpoint R),
      if q.Prime ∧ c < q ∧ c * q ≤ squareRootEndpoint R then μ c else 0

/-- Prime-first lower-scale form of the ancestry root. -/
def squareRootAncestryRootPrimeMass (R : ℕ) : ℤ :=
  -∑ q ∈ Finset.Icc 2 (squareRootEndpoint R),
    if q.Prime then
      mertensSummatoryInt
        (min (q - 1) (squareRootEndpoint R / q))
    else 0

/-- A retained root pair has exactly the native canonical coordinates. -/
private theorem rootPair_canonicalData
    {R c q : ℕ}
    (h : (c, q) ∈ squareRootAncestryRootPairSet R) :
    CanonicalSourceData q c := by
  rcases Finset.mem_filter.mp h with ⟨hbase, hdata⟩
  rcases Finset.mem_product.mp hbase with ⟨hcMem, _hqMem⟩
  rcases Finset.mem_Ico.mp hcMem with ⟨hc1, _hcR⟩
  rcases hdata with ⟨hqPrime, hsq, hcq, _hprod⟩
  have hcpos : 0 < c := Nat.zero_lt_of_lt hc1
  have hcop : Nat.Coprime q c :=
    Nat.coprime_of_lt_prime (Nat.ne_of_gt hcpos) hcq hqPrime
  refine ⟨hqPrime, hc1, hsq, hcop, ?_⟩
  intro p hp hpc
  have hp_le_c : p ≤ c := Nat.le_of_dvd hcpos hpc
  exact lt_of_le_of_lt hp_le_c hcq

/-- Reindex the clock-pushed ancestry root by its canonical `(c,q)` coordinates. -/
theorem sourceRootPrefix_eq_pairMass
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    sourceRootPrefix B (R - 1) = squareRootAncestryRootPairMass R := by
  classical
  rw [sourceRootPrefix_eq_activeRoot_sum]
  unfold squareRootAncestryRootPairMass
  refine Finset.sum_bij
    (fun s _hs => (sourceCore s, sourcePrime s)) ?_ ?_ ?_ ?_
  · intro s hs
    have hsdata :
        SourceAdmissible s ∧ sourceClock B s ≤ R - 1 ∧ TransportOriented s := by
      simpa [activeRootSourceSet] using hs
    rcases hsdata.1 with ⟨hqPrime, hc1, hsq, _hcop, hdom⟩
    have hprod : sourceProduct s ≤ squareRootEndpoint R := by
      have hclock :=
        (CanonicalGapAncestryEnergyBridge.sourceClock_le_iff_sourceProduct_le_endpoint
          (x := R - 1) s).1 hsdata.2.1
      simpa [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)] using hclock
    have hcq : sourceCore s < sourcePrime s := by
      have hle := hsdata.2.2.2
      by_contra hnot
      have heq : sourceCore s = sourcePrime s :=
        Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
      have hqdiv : sourcePrime s ∣ sourceCore s := by rw [heq]
      exact (lt_irrefl (sourcePrime s))
        (hdom (sourcePrime s) hqPrime hqdiv)
    have hcR : sourceCore s < R := by
      by_contra hnot
      have hRc : R ≤ sourceCore s := Nat.le_of_not_gt hnot
      have hRq : R ≤ sourcePrime s := hRc.trans hsdata.2.2.2
      have hRR : R ^ 2 ≤ sourceCore s * sourcePrime s := by
        simpa [pow_two] using Nat.mul_le_mul hRc hRq
      have hRsqpos : 0 < R ^ 2 := by positivity
      have hXlt : squareRootEndpoint R < R ^ 2 := by
        unfold squareRootEndpoint
        omega
      have hmul : sourceCore s * sourcePrime s ≤ squareRootEndpoint R := by
        simpa [sourceProduct, Nat.mul_comm] using hprod
      exact (not_le_of_gt (lt_of_lt_of_le hXlt hRR)) hmul
    have hqX : sourcePrime s ≤ squareRootEndpoint R := by
      have hqleprod : sourcePrime s ≤ sourceCore s * sourcePrime s := by
        simpa using Nat.mul_le_mul_right (sourcePrime s) hc1
      exact hqleprod.trans (by simpa [sourceProduct, Nat.mul_comm] using hprod)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_Ico.mpr ⟨hc1, hcR⟩,
        Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqX⟩⟩
    · exact ⟨hqPrime, hsq, hcq, by simpa [sourceProduct, Nat.mul_comm] using hprod⟩
  · intro s₁ hs₁ s₂ hs₂ heq
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.snd heq
    · apply Fin.ext
      exact congrArg Prod.fst heq
  · intro cq hcq
    rcases cq with ⟨c, q⟩
    have hdata := rootPair_canonicalData hcq
    rcases Finset.mem_filter.mp hcq with ⟨hbase, hpair⟩
    rcases Finset.mem_product.mp hbase with ⟨hcMem, hqMem⟩
    have hqX := (Finset.mem_Icc.mp hqMem).2
    have hprod := hpair.2.2.2
    have hcB : c ≤ B := by
      have hcX : c ≤ squareRootEndpoint R := by
        have hqpos : 0 < q := hpair.1.pos
        have hcle : c ≤ c * q := by
          simpa using Nat.mul_le_mul_left c hqpos
        exact hcle.trans hprod
      exact hcX.trans hB
    have hqB : q ≤ B := hqX.trans hB
    let s : SourceIndex B :=
      (⟨q, by omega⟩, ⟨c, by omega⟩)
    have hadm : SourceAdmissible s := by
      simpa [s, sourcePrime, sourceCore] using hdata
    have htrans : TransportOriented s := by
      refine ⟨hadm, ?_⟩
      simpa [s, sourcePrime, sourceCore] using hpair.2.2.1.le
    have hclock : sourceClock B s ≤ R - 1 := by
      apply (CanonicalGapAncestryEnergyBridge.sourceClock_le_iff_sourceProduct_le_endpoint
        (x := R - 1) s).2
      rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)]
      simpa [s, sourceProduct, sourcePrime, sourceCore, Nat.mul_comm] using hprod
    refine ⟨s, ?_, ?_⟩
    · simp [activeRootSourceSet, hadm, hclock, htrans]
    · rfl
  · intro s hs
    have hsdata :
        SourceAdmissible s ∧ sourceClock B s ≤ R - 1 ∧ TransportOriented s := by
      simpa [activeRootSourceSet] using hs
    simpa [sourceProduct, Nat.mul_comm] using
      (sourceWeight_of_admissible s hsdata.1)

/-- Removing the distinguished prime flips every squarefree cofactor weight;
non-squarefree cofactors contribute zero on both sides. -/
theorem squareRootAncestryRootPairMass_eq_cofactorMass (R : ℕ) :
    squareRootAncestryRootPairMass R =
      squareRootAncestryRootCofactorMass R := by
  classical
  unfold squareRootAncestryRootPairMass squareRootAncestryRootPairSet
    squareRootAncestryRootCofactorMass
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈ (Finset.Ico 1 R).product
          (Finset.Icc 2 (squareRootEndpoint R)),
        if cq.2.Prime ∧ Squarefree cq.1 ∧ cq.1 < cq.2 ∧
            cq.1 * cq.2 ≤ squareRootEndpoint R then
          μ (cq.1 * cq.2)
        else 0) =
      ∑ c ∈ Finset.Ico 1 R,
        ∑ q ∈ Finset.Icc 2 (squareRootEndpoint R),
          if q.Prime ∧ Squarefree c ∧ c < q ∧
              c * q ≤ squareRootEndpoint R then
            μ (c * q)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Ico 1 R)
          (t := Finset.Icc 2 (squareRootEndpoint R))
          (f := fun cq : ℕ × ℕ =>
            if cq.2.Prime ∧ Squarefree cq.1 ∧ cq.1 < cq.2 ∧
                cq.1 * cq.2 ≤ squareRootEndpoint R then
              μ (cq.1 * cq.2)
            else 0))
    _ = -∑ c ∈ Finset.Ico 1 R,
        ∑ q ∈ Finset.Icc 2 (squareRootEndpoint R),
          if q.Prime ∧ c < q ∧ c * q ≤ squareRootEndpoint R then μ c else 0 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hprime : q.Prime
      · by_cases hsq : Squarefree c
        · by_cases hcq : c < q
          · by_cases hprod : c * q ≤ squareRootEndpoint R
            · have hcpos : 0 < c := by
                have := (Finset.mem_Ico.mp hc).1
                omega
              have hcop : Nat.Coprime c q :=
                (Nat.coprime_of_lt_prime (Nat.ne_of_gt hcpos) hcq hprime).symm
              have hmu :=
                ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
              rw [hmu, ArithmeticFunction.moebius_apply_prime hprime]
              simp [hprime, hsq, hcq, hprod]
            · simp [hprime, hsq, hcq, hprod]
          · simp [hprime, hsq, hcq]
        · have hzero : μ c = 0 :=
            ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
          simp [hprime, hsq, hzero]
      · simp [hprime]

/-- Every prime-first root fiber is exactly one Mertens value at a scale
strictly below the square-root cutoff. -/
theorem squareRootAncestryRootCofactorMass_eq_primeMass
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootAncestryRootCofactorMass R =
      squareRootAncestryRootPrimeMass R := by
  classical
  unfold squareRootAncestryRootCofactorMass squareRootAncestryRootPrimeMass
  rw [Finset.sum_comm]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro q hqmem
  by_cases hprime : q.Prime
  · simp only [hprime, true_and, if_true]
    let K := min (q - 1) (squareRootEndpoint R / q)
    have hqpos : 0 < q := hprime.pos
    have hKlt : K < R := by
      by_cases hqR : q ≤ R
      · have hK : K ≤ q - 1 := min_le_left _ _
        omega
      · have hRq : R < q := Nat.lt_of_not_ge hqR
        have hdiv : squareRootEndpoint R / q < R :=
          squareRootEndpoint_div_lt (by omega) hRq hqpos
        exact lt_of_le_of_lt (min_le_right _ _) hdiv
    have hset :
        (Finset.Ico 1 R).filter
            (fun c => c < q ∧ c * q ≤ squareRootEndpoint R) =
          Finset.Icc 1 K := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hc1, hcR⟩, hcq, hprod⟩
        refine ⟨hc1, ?_⟩
        apply le_min
        · omega
        · exact (Nat.le_div_iff_mul_le hqpos).2 hprod
      · rintro ⟨hc1, hcK⟩
        have hcR : c < R := lt_of_le_of_lt hcK hKlt
        have hcq : c < q := by
          have hcqm1 : c ≤ q - 1 := hcK.trans (min_le_left _ _)
          omega
        have hcdiv : c ≤ squareRootEndpoint R / q :=
          hcK.trans (min_le_right _ _)
        have hprod : c * q ≤ squareRootEndpoint R :=
          (Nat.le_div_iff_mul_le hqpos).1 hcdiv
        exact ⟨⟨hc1, hcR⟩, hcq, hprod⟩
    calc
      (∑ c ∈ Finset.Ico 1 R,
          if c < q ∧ c * q ≤ squareRootEndpoint R then μ c else 0) =
        ∑ c ∈ (Finset.Ico 1 R).filter
            (fun c => c < q ∧ c * q ≤ squareRootEndpoint R), μ c := by
          rw [Finset.sum_filter]
      _ = ∑ c ∈ Finset.Icc 1 K, μ c := by rw [hset]
      _ = mertensSummatoryInt K := (mertensSummatoryInt_eq_Icc K).symm
      _ = mertensSummatoryInt
          (min (q - 1) (squareRootEndpoint R / q)) := by rfl
  · simp [hprime]

/-- Final square-root triangularization of the ancestry root. -/
theorem sourceRootPrefix_eq_lowerMertensPrimeTransform
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    sourceRootPrefix B (R - 1) =
      squareRootAncestryRootPrimeMass R := by
  rw [sourceRootPrefix_eq_pairMass hR hB,
    squareRootAncestryRootPairMass_eq_cofactorMass,
    squareRootAncestryRootCofactorMass_eq_primeMass R hR]

/-- The lower-triangular cutoff in every retained prime fiber is strictly below
`R`; this is the induction lever exposed by the exact transform. -/
theorem squareRootAncestryRootPrime_cutoff_lt
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ Finset.Icc 2 (squareRootEndpoint R)) :
    min (q - 1) (squareRootEndpoint R / q) < R := by
  have hqge : 2 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqpos : 0 < q := by omega
  by_cases hqR : q ≤ R
  · exact lt_of_le_of_lt (min_le_left _ _) (by omega)
  · exact lt_of_le_of_lt (min_le_right _ _)
      (squareRootEndpoint_div_lt (by omega) (Nat.lt_of_not_ge hqR) hqpos)

end RHLean.Proof
