import RHLean.Proof.CanonicalGapAncestryPrimePacketFibre
import RHLean.Analysis.CanonicalLowOccupancy

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryPrimePackets

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge
open CanonicalGapAncestryHighRealization
open CanonicalGapAncestryProjectedRenewal

/-!
# The exact top-fibre prime boundary

The top distinguished-prime dyadic scale below a square-prefix endpoint contains
only sources with core `1`. Consequently every projected successor packet in that
fibre vanishes, while at `Λ = 0` the fibre is exactly the negative cardinality of
the corresponding prime band.

These are exact finite identities. No prime-number estimate is used.
-/

/-- The top distinguished-prime dyadic scale below the square-prefix endpoint. -/
def sourceTopQScale (x : ℕ) : ℕ :=
  Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x)

/-- The prime band represented by the top distinguished-prime scale. -/
noncomputable def sourceTopPrimeBand (x : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ sourceTopQScale x)
    (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter Nat.Prime

/-- At cutoff `Λ = 0`, every admissible source lies in the high sector, while
nonadmissible source weights already vanish. -/
theorem sourceHighField_zero_eq_weight (B : ℕ) :
    sourceHighField 0 B = (boundedSourceFlow B).weight := by
  classical
  funext s
  by_cases hadm : SourceAdmissible s
  · have hm1 : 1 < sourceProduct s :=
      one_lt_sourceProduct_of_admissible hadm
    have hsq : Squarefree (sourceProduct s) :=
      sourceProduct_squarefree_of_admissible hadm
    have hμ : μ (sourceProduct s) ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
    have hgap : 0 < canonicalAbsoluteGap (sourceProduct s) :=
      canonicalAbsoluteGap_pos_of_moebius_ne_zero hm1 hμ
    have hhi : 0 < canonicalPairHi (sourceProduct s) := by
      have hp := canonicalLargestPrimeFactor_prime hm1
      unfold canonicalPairHi
      exact lt_of_lt_of_le hp.pos (le_max_right _ _)
    have hheight : 0 < abs (canonicalHeightTwice (sourceProduct s)) := by
      rw [abs_canonicalHeightTwice_eq_gap_mul_factorSum]
      have hgapR : 0 < (canonicalAbsoluteGap (sourceProduct s) : ℝ) := by
        exact_mod_cast hgap
      have hhiR : 0 < (canonicalPairHi (sourceProduct s) : ℝ) := by
        exact_mod_cast hhi
      exact mul_pos hgapR (add_pos_of_nonneg_of_pos (by positivity) hhiR)
    have hhigh :
        IsCanonicalHighHeight 0 (sourceClock B s) (sourceProduct s) := by
      simpa [IsCanonicalHighHeight, IsCanonicalLowHeight] using
        (not_le_of_gt hheight)
    simp [sourceHighField, sourceHighProjector, boundedSourceFlow, hhigh]
  · simp [sourceHighField, sourceHighProjector, boundedSourceFlow,
      sourceWeight, hadm]

/-- Active sources in the top `q`-scale have core exactly `1`. -/
theorem sourceCore_eq_one_of_active_topQScale
    {B x : ℕ} (s : SourceIndex B)
    (hadm : SourceAdmissible s)
    (hclock : sourceClock B s ≤ x)
    (hscale : sourcePrimeDyadicScale s = sourceTopQScale x) :
    sourceCore s = 1 := by
  have hcore1 : 1 ≤ sourceCore s := hadm.2.1
  by_contra hne
  have hcore2 : 2 ≤ sourceCore s := by omega
  have hqpow0 : 2 ^ sourcePrimeDyadicScale s ≤ sourcePrime s := by
    change 2 ^ Nat.log 2 (sourcePrime s) ≤ sourcePrime s
    exact Nat.pow_log_le_self 2 hadm.1.ne_zero
  have hqpow : 2 ^ sourceTopQScale x ≤ sourcePrime s := by
    simpa [hscale] using hqpow0
  have hXlt :
      RHLean.Analysis.squarePrefixEndpoint x <
        2 ^ (sourceTopQScale x + 1) := by
    simpa [sourceTopQScale, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ))
        (RHLean.Analysis.squarePrefixEndpoint x))
  have hprodle :
      sourceProduct s ≤ RHLean.Analysis.squarePrefixEndpoint x :=
    (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).1 hclock
  have hpowle : 2 ^ (sourceTopQScale x + 1) ≤ sourceProduct s := by
    change 2 ^ (sourceTopQScale x + 1) ≤ sourcePrime s * sourceCore s
    simpa [pow_succ] using Nat.mul_le_mul hqpow hcore2
  omega

/-- Active admissible sources in the top distinguished-prime scale. -/
noncomputable def activeSourceTopQSet (B x : ℕ) : Finset (SourceIndex B) := by
  classical
  exact Finset.univ.filter fun s =>
    SourceAdmissible s ∧ sourceClock B s ≤ x ∧
      sourcePrimeDyadicScale s = sourceTopQScale x

/-- The top `q`-packet prefix at `Λ = 0` is the sum of the weights of active
admissible top-scale sources. -/
theorem sourceHighTopQPacketPrefix_zero_eq_activeSource_sum
    (B x : ℕ) :
    sourceHighQPacketPrefix 0 B (sourceTopQScale x) x =
      ∑ s ∈ activeSourceTopQSet B x, sourceWeight s := by
  classical
  unfold sourceHighQPacketPrefix sourceHighQPacketField
  rw [sourceHighField_zero_eq_weight]
  change
    (∑ s : SourceIndex B,
      if sourceClock B s ≤ x then
        sourceQPacketField B (sourceTopQScale x)
          (boundedSourceFlow B).weight s
      else 0) = _
  unfold activeSourceTopQSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hadm : SourceAdmissible s <;>
  by_cases hclock : sourceClock B s ≤ x <;>
  by_cases hscale : sourcePrimeDyadicScale s = sourceTopQScale x <;>
    simp [sourceQPacketField, boundedSourceFlow, sourceWeight,
      hadm, hclock, hscale]

/-- Every projected successor packet vanishes on the active top `q`-scale.
This statement is independent of `Λ`. -/
theorem sourceProjectedSuccessorPQPacketPrefix_topQScale_eq_zero
    (Λ : ℝ) (B j x : ℕ) :
    sourceProjectedSuccessorPQPacketPrefix Λ B j (sourceTopQScale x) x = 0 := by
  classical
  unfold sourceProjectedSuccessorPQPacketPrefix
  change
    (∑ s : SourceIndex B,
      if sourceClock B s ≤ x then
        sourceProjectedSuccessorPQPacketField Λ B j (sourceTopQScale x) s
      else 0) = 0
  apply Finset.sum_eq_zero
  intro s _hs
  by_cases hclock : sourceClock B s ≤ x
  · by_cases hscale : sourcePrimeDyadicScale s = sourceTopQScale x
    · have hnotSmooth : ¬ SmoothOriented s := by
        intro hsmooth
        have hcore := sourceCore_eq_one_of_active_topQScale
          s hsmooth.1 hclock hscale
        have hq2 := hsmooth.1.1.two_le
        have hq_lt_core := hsmooth.2
        omega
      have hzero :=
        sourceProjectedSuccessorField_eq_zero_of_not_smooth Λ B s hnotSmooth
      simp [sourceProjectedSuccessorPQPacketField, sourceQPPacketField,
        hclock, hscale, hzero]
    · simp [sourceProjectedSuccessorPQPacketField, sourceQPPacketField,
        hclock, hscale]
  · simp [hclock]

/-- The top `q`-packet at `Λ = 0` is exactly minus the number of primes in the
top dyadic band. -/
theorem sourceHighTopQPacketPrefix_zero_eq_neg_sourceTopPrimeBandCard
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourceHighQPacketPrefix 0 B (sourceTopQScale x) x =
      -((sourceTopPrimeBand x).card : ℤ) := by
  classical
  rw [sourceHighTopQPacketPrefix_zero_eq_activeSource_sum]
  calc
    (∑ s ∈ activeSourceTopQSet B x, sourceWeight s) =
        ∑ p ∈ sourceTopPrimeBand x, (-1 : ℤ) := by
      refine Finset.sum_bij (fun s _hs => sourceProduct s) ?_ ?_ ?_ ?_
      · intro s hs
        have hsdata :
            SourceAdmissible s ∧ sourceClock B s ≤ x ∧
              sourcePrimeDyadicScale s = sourceTopQScale x := by
          simpa [activeSourceTopQSet] using hs
        have hcore := sourceCore_eq_one_of_active_topQScale
          s hsdata.1 hsdata.2.1 hsdata.2.2
        have hprod : sourceProduct s = sourcePrime s := by
          simp [sourceProduct, hcore]
        have hp : (sourceProduct s).Prime := by
          simpa [hprod] using hsdata.1.1
        have hupper :
            sourceProduct s ≤ RHLean.Analysis.squarePrefixEndpoint x :=
          (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).1
            hsdata.2.1
        have hlower0 :
            2 ^ sourcePrimeDyadicScale s ≤ sourcePrime s := by
          change 2 ^ Nat.log 2 (sourcePrime s) ≤ sourcePrime s
          exact Nat.pow_log_le_self 2 hsdata.1.1.ne_zero
        have hlower : 2 ^ sourceTopQScale x ≤ sourceProduct s := by
          rw [hsdata.2.2] at hlower0
          simpa [hprod] using hlower0
        simp only [sourceTopPrimeBand, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨hlower, Nat.lt_succ_of_le hupper⟩, hp⟩
      · intro s₁ hs₁ s₂ hs₂ heq
        have hs₁data : SourceAdmissible s₁ := by
          have h :
              SourceAdmissible s₁ ∧ sourceClock B s₁ ≤ x ∧
                sourcePrimeDyadicScale s₁ = sourceTopQScale x := by
            simpa [activeSourceTopQSet] using hs₁
          exact h.1
        have hs₂data : SourceAdmissible s₂ := by
          have h :
              SourceAdmissible s₂ ∧ sourceClock B s₂ ≤ x ∧
                sourcePrimeDyadicScale s₂ = sourceTopQScale x := by
            simpa [activeSourceTopQSet] using hs₂
          exact h.1
        exact sourceProduct_injective_on_admissible hs₁data hs₂data heq
      · intro p hp
        have hpdata :
            (2 ^ sourceTopQScale x ≤ p ∧
              p < RHLean.Analysis.squarePrefixEndpoint x + 1) ∧ p.Prime := by
          simpa [sourceTopPrimeBand, Finset.mem_Ico] using hp
        have hpUpper : p ≤ RHLean.Analysis.squarePrefixEndpoint x :=
          Nat.lt_succ_iff.mp hpdata.1.2
        have hpB : p ≤ B := hpUpper.trans hB
        have hB1 : 1 ≤ B := by
          have hp2 := hpdata.2.two_le
          omega
        let s : SourceIndex B :=
          (⟨p, Nat.lt_succ_of_le hpB⟩,
            ⟨1, Nat.lt_succ_of_le hB1⟩)
        have hadm : SourceAdmissible s := by
          change CanonicalSourceData p 1
          refine ⟨hpdata.2, by norm_num, by simp, by simp, ?_⟩
          intro r hr hdiv
          have hr1 : r = 1 := Nat.dvd_one.mp hdiv
          subst r
          norm_num at hr
        have hclock : sourceClock B s ≤ x := by
          apply (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).2
          simpa [s, sourceProduct, sourcePrime, sourceCore] using hpUpper
        have hXlt :
            RHLean.Analysis.squarePrefixEndpoint x <
              2 ^ (sourceTopQScale x + 1) := by
          simpa [sourceTopQScale, Nat.succ_eq_add_one] using
            (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ))
              (RHLean.Analysis.squarePrefixEndpoint x))
        have hlog : Nat.log 2 p = sourceTopQScale x :=
          Nat.log_eq_of_pow_le_of_lt_pow hpdata.1.1
            (lt_of_le_of_lt hpUpper hXlt)
        have hscale : sourcePrimeDyadicScale s = sourceTopQScale x := by
          simpa [sourcePrimeDyadicScale, sourcePrime, s] using hlog
        refine ⟨s, ?_, ?_⟩
        · simpa [activeSourceTopQSet] using
            (show SourceAdmissible s ∧ sourceClock B s ≤ x ∧
              sourcePrimeDyadicScale s = sourceTopQScale x from
              ⟨hadm, hclock, hscale⟩)
        · simp [s, sourceProduct, sourcePrime, sourceCore]
      · intro s hs
        have hsdata :
            SourceAdmissible s ∧ sourceClock B s ≤ x ∧
              sourcePrimeDyadicScale s = sourceTopQScale x := by
          simpa [activeSourceTopQSet] using hs
        have hcore := sourceCore_eq_one_of_active_topQScale
          s hsdata.1 hsdata.2.1 hsdata.2.2
        have hprod : sourceProduct s = sourcePrime s := by
          simp [sourceProduct, hcore]
        have hp : (sourceProduct s).Prime := by
          simpa [hprod] using hsdata.1.1
        rw [sourceWeight_of_admissible s hsdata.1]
        simpa using ArithmeticFunction.moebius_apply_prime hp
    _ = -((sourceTopPrimeBand x).card : ℤ) := by simp

/-- Expanded prime-band form of the top-fibre gatekeeper identity. -/
theorem sourceHighTopQPacketPrefix_zero_eq_neg_primeBandCard
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourceHighQPacketPrefix 0 B
      (Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x)) x =
      -(((Finset.Ico
          (2 ^ Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x))
          (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
        Nat.Prime).card : ℤ) := by
  simpa [sourceTopQScale, sourceTopPrimeBand] using
    (sourceHighTopQPacketPrefix_zero_eq_neg_sourceTopPrimeBandCard
      (B := B) (x := x) hB)

/-- The root packet equals the same prime boundary because every successor packet
in the top fibre vanishes. -/
theorem sourceHighRootTopQPacketPrefix_zero_eq_neg_primeBandCard
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourceHighRootQPacketPrefix 0 B
      (Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x)) x =
      -(((Finset.Ico
          (2 ^ Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x))
          (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
        Nat.Prime).card : ℤ) := by
  have hrenew := sourceHighQPacketPrefix_eq_root_sub_successorPackets
    0 B (sourceTopQScale x) x
  have hsum :
      (∑ j ∈ Finset.range (B + 1),
        sourceProjectedSuccessorPQPacketPrefix 0 B j
          (sourceTopQScale x) x) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    exact sourceProjectedSuccessorPQPacketPrefix_topQScale_eq_zero 0 B j x
  rw [hsum, sub_zero] at hrenew
  calc
    sourceHighRootQPacketPrefix 0 B
        (Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x)) x =
        sourceHighQPacketPrefix 0 B
          (Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x)) x := by
      simpa [sourceTopQScale] using hrenew.symm
    _ = -(((Finset.Ico
          (2 ^ Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x))
          (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
        Nat.Prime).card : ℤ) :=
      sourceHighTopQPacketPrefix_zero_eq_neg_primeBandCard hB

/-- Consolidated gatekeeper: the top fibre and root packet are the same negative
prime-band cardinality, and every successor packet vanishes. -/
theorem sourceHighTopQPacketPrefix_zero_gatekeeper
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourceHighQPacketPrefix 0 B
        (Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x)) x =
        -(((Finset.Ico
            (2 ^ Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x))
            (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
          Nat.Prime).card : ℤ) ∧
      sourceHighRootQPacketPrefix 0 B
        (Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x)) x =
        -(((Finset.Ico
            (2 ^ Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x))
            (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
          Nat.Prime).card : ℤ) ∧
      ∀ j,
        sourceProjectedSuccessorPQPacketPrefix 0 B j
          (Nat.log 2 (RHLean.Analysis.squarePrefixEndpoint x)) x = 0 := by
  refine ⟨sourceHighTopQPacketPrefix_zero_eq_neg_primeBandCard hB,
    sourceHighRootTopQPacketPrefix_zero_eq_neg_primeBandCard hB, ?_⟩
  intro j
  simpa [sourceTopQScale] using
    (sourceProjectedSuccessorPQPacketPrefix_topQScale_eq_zero 0 B j x)

end CanonicalGapAncestryPrimePackets

end RHLean.Proof