import RHLean.Proof.ComplexVerticalFiberSpacing
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalCutoff
import RHLean.Proof.LowWheelFrozenSecondContactWindowDescent
import RHLean.Proof.StableFarWallOwnedCensus

/-!
# Stable-far owned terminal products are the smooth square shell

An ordered Euler cut with high cofactor one and pivot still inside the inclusive
low wheel cannot be a unique-parent occurrence at the square endpoint: an
explicit second pivot gives another downcross with the same root-side parent.
This saturates the internal terminal source before identifying the owned-product
image with the complete squarefree `R`-smooth shell.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

private theorem terminal_altPivot_mem_taggedDowncross
    {R q : ℕ} {t : Finset ℕ}
    (hR : 2 ≤ R)
    (ht : t ∈ (primesUpTo R).powerset)
    (hmR : primeFaceProduct t ≤ R)
    (hq : q.Prime)
    (hroot : R < q * primeFaceProduct t)
    (htop : q * primeFaceProduct t ≤ squareRootEndpoint R) :
    (t, (1, q)) ∈ lowWheelCanonicalTaggedDowncrossCarrier R := by
  have hmpos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hqX : q ≤ squareRootEndpoint R := by
    have hqle : q ≤ q * primeFaceProduct t := by
      simpa using Nat.mul_le_mul_left q (Nat.succ_le_iff.mpr hmpos)
    exact hqle.trans htop
  have hphysical :
      (1, q) ∈ lowWheelCanonicalPhysicalStateSet R t := by
    apply mem_lowWheelCanonicalPhysicalStateSet.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by norm_num, by omega⟩,
      Finset.mem_Icc.mpr ⟨hq.one_le, hqX⟩, squarefree_one, ?_⟩
    unfold LowWheelTransportPairCarrier
    refine ⟨by norm_num, by omega, ?_, ?_⟩
    · simpa [Nat.mul_comm] using hroot
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htop
  have hpivot : lowWheelCanonicalCofactorQuotientPivot (1, q) = q := by
    simp [lowWheelCanonicalCofactorQuotientPivot, hq.minFac_eq]
  have hnot : ¬ lowWheelCanonicalCofactorQuotientPivot (1, q) ∣ 1 := by
    rw [hpivot]
    exact hq.not_dvd_one
  have hdown :
      primeFaceProduct t *
          (q / lowWheelCanonicalCofactorQuotientPivot (1, q)) ≤ R := by
    rw [hpivot, Nat.div_self hq.pos, Nat.mul_one]
    exact hmR
  apply mem_lowWheelCanonicalTaggedDowncrossCarrier.mpr
  exact ⟨ht, mem_lowWheelCanonicalDowncrossPart.mpr
    ⟨hphysical, hnot, hdown⟩⟩

/-- **Internal terminal saturation.**  At the square endpoint, every ordered
cut with cofactor one whose fresh pivot is still at most `R` lies in a repeated
parent fibre. -/
theorem orderedEulerCut_mem_repeatedTerminalInternal_of_cofactor_one
    {R p : ℕ} {t : Finset ℕ}
    (hR : 56 ≤ R)
    (hy : (t, (1, p)) ∈ orderedEulerCutCarrier R)
    (hpR : p ≤ R) :
    (t, (1, p)) ∈ lowWheelCanonicalRepeatedTerminalInternalPart R := by
  have hR2 : 2 ≤ R := by omega
  have hshape := orderedEulerCutShape_of_mem_carrier hy
  have hocc := mem_orderedEulerCutCarrier.mp hy
  have hp : p.Prime := hshape.1
  have ht := hocc.1
  have hmpos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hmR0 := orderedEulerCutOccursAt_lowProduct_le hshape hocc
  have hmR : primeFaceProduct t ≤ R := by
    simpa [orderedEulerCutLowProduct] using hmR0
  have hlife := (mem_orderedEulerCutCarrier_iff_shape_lifetime.mp hy).2
  have hroot : R < p * primeFaceProduct t := by
    simpa [orderedEulerCutDeathRoot, orderedEulerCutPivot,
      orderedEulerCutLowProduct] using hlife.2
  have hchildTop : p * primeFaceProduct t ≤ squareRootEndpoint R := by
    have hb := hlife.1
    change max (primeFaceProduct t)
      (max (1 + 1)
        (Nat.sqrt (1 * (p * primeFaceProduct t)) + 1)) ≤ R at hb
    have hsqrtSucc := (Nat.max_le.mp (Nat.max_le.mp hb).2).2
    have hsqrt : Nat.sqrt (p * primeFaceProduct t) < R := by
      simpa using Nat.lt_of_succ_le hsqrtSucc
    have h := (orderedEulerCutChild_le_endpoint_iff (R := R) hshape).2
      (by simpa [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct] using hsqrt)
    simpa [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
      orderedEulerCutPivot, orderedEulerCutLowProduct] using h
  have htag : (t, (1, p)) ∈ lowWheelCanonicalTaggedDowncrossCarrier R := by
    exact mem_lowWheelCanonicalTaggedDowncrossCarrier.mpr
      ⟨ht, (LowWheelCanonicalDowncrossOwnership.mem_lowWheelCanonicalDowncrossOrientedPart.mp
        hocc.2).1⟩
  have hpivot : lowWheelCanonicalCofactorQuotientPivot (1, p) = p := by
    exact orderedEulerCutShape_canonicalPivot hshape
  have hrep : (t, (1, p)) ∈ lowWheelCanonicalDowncrossRepeatedParentPart R := by
    apply Finset.mem_filter.mpr
    refine ⟨htag, ?_⟩
    intro hunique
    by_cases hlarge : R < 2 * primeFaceProduct t
    · by_cases hp2 : p = 2
      · have h3root : R < 3 * primeFaceProduct t := by omega
        have h3top : 3 * primeFaceProduct t ≤ squareRootEndpoint R := by
          have h3R : 3 * R ≤ squareRootEndpoint R := by
            unfold squareRootEndpoint
            have hs : 3 * R + 1 ≤ R ^ 2 := by nlinarith
            exact Nat.le_sub_of_add_le hs
          exact (Nat.mul_le_mul_left 3 hmR).trans h3R
        have hz := terminal_altPivot_mem_taggedDowncross
          (R := R) (q := 3) hR2 ht hmR (by norm_num) h3root h3top
        have hzPivot : lowWheelCanonicalCofactorQuotientPivot (1, 3) = 3 := by
          norm_num [lowWheelCanonicalCofactorQuotientPivot]
        have hparent :
            lowWheelCanonicalDowncrossParent (t, (1, 3)) =
              lowWheelCanonicalDowncrossParent (t, (1, p)) := by
          rw [lowWheelCanonicalDowncrossParent, lowWheelCanonicalDowncrossParent,
            hzPivot, hpivot, Nat.div_self (by norm_num : 0 < (3 : ℕ)),
            Nat.div_self hp.pos]
        have heq := hunique (t, (1, 3)) hz hparent
        have hqp := congrArg (fun z : LowWheelTaggedDowncrossState => z.2.2) heq
        simp [hp2] at hqp
      · have hp3 : 3 ≤ p := by
          have hp2le := hp.two_le
          omega
        have h2root : R < 2 * primeFaceProduct t := hlarge
        have h2top : 2 * primeFaceProduct t ≤ squareRootEndpoint R := by
          have hle : 2 * primeFaceProduct t ≤ p * primeFaceProduct t :=
            Nat.mul_le_mul_right (primeFaceProduct t) hp.two_le
          exact hle.trans hchildTop
        have hz := terminal_altPivot_mem_taggedDowncross
          (R := R) (q := 2) hR2 ht hmR (by norm_num) h2root h2top
        have hzPivot : lowWheelCanonicalCofactorQuotientPivot (1, 2) = 2 := by
          norm_num [lowWheelCanonicalCofactorQuotientPivot]
        have hparent :
            lowWheelCanonicalDowncrossParent (t, (1, 2)) =
              lowWheelCanonicalDowncrossParent (t, (1, p)) := by
          rw [lowWheelCanonicalDowncrossParent, lowWheelCanonicalDowncrossParent,
            hzPivot, hpivot, Nat.div_self (by norm_num : 0 < (2 : ℕ)),
            Nat.div_self hp.pos]
        have heq := hunique (t, (1, 2)) hz hparent
        have hqp := congrArg (fun z : LowWheelTaggedDowncrossState => z.2.2) heq
        simp at hqp
        exact hp2 hqp.symm
    · have hsmall : 2 * primeFaceProduct t ≤ R := Nat.le_of_not_gt hlarge
      rcases Nat.bertrand p hp.ne_zero with ⟨q, hqPrime, hpq, hq2p⟩
      have hqroot : R < q * primeFaceProduct t := by
        have hpmul : p * primeFaceProduct t < q * primeFaceProduct t :=
          Nat.mul_lt_mul_of_pos_right hpq hmpos
        exact hroot.trans hpmul
      have hqne : q ≠ 2 * p := by
        intro heq
        have h2dvd : 2 ∣ q := by
          rw [heq]
          exact dvd_mul_right 2 p
        have h2q : 2 = q :=
          (Nat.prime_dvd_prime_iff_eq Nat.prime_two hqPrime).mp h2dvd
        have hp1 : p = 1 := by omega
        exact hp.ne_one hp1
      have hq2pLt : q < 2 * p := by omega
      have hqtop : q * primeFaceProduct t ≤ squareRootEndpoint R := by
        have hqmul : q * primeFaceProduct t <
            (2 * p) * primeFaceProduct t :=
          Nat.mul_lt_mul_of_pos_right hq2pLt hmpos
        have h2pmul : (2 * p) * primeFaceProduct t ≤ R ^ 2 := by
          calc
            (2 * p) * primeFaceProduct t = p * (2 * primeFaceProduct t) := by ring
            _ ≤ p * R := Nat.mul_le_mul_left p hsmall
            _ ≤ R * R := Nat.mul_le_mul_right R hpR
            _ = R ^ 2 := by ring
        have hlt : q * primeFaceProduct t < R ^ 2 := hqmul.trans_le h2pmul
        unfold squareRootEndpoint
        exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlt)
      have hz := terminal_altPivot_mem_taggedDowncross
        (R := R) (q := q) hR2 ht hmR hqPrime hqroot hqtop
      have hzPivot : lowWheelCanonicalCofactorQuotientPivot (1, q) = q := by
        simp [lowWheelCanonicalCofactorQuotientPivot, hqPrime.minFac_eq]
      have hparent :
          lowWheelCanonicalDowncrossParent (t, (1, q)) =
            lowWheelCanonicalDowncrossParent (t, (1, p)) := by
        rw [lowWheelCanonicalDowncrossParent, lowWheelCanonicalDowncrossParent,
          hzPivot, hpivot, Nat.div_self hqPrime.pos, Nat.div_self hp.pos]
      have heq := hunique (t, (1, q)) hz hparent
      have hqp' := congrArg (fun z : LowWheelTaggedDowncrossState => z.2.2) heq
      exact (Nat.ne_of_gt hpq) hqp'
  have hfrozenShape : LowWheelDowncrossFrozenShape (t, (1, p)) := by
    refine ⟨hpivot.symm, ?_⟩
    intro q hqt
    simpa [lowWheelTaggedDowncrossPivot, hpivot] using (hshape.2.2.2.2.1 q hqt).2
  have hfrozen :
      (t, (1, p)) ∈ lowWheelCanonicalRepeatedFrozenPart R :=
    Finset.mem_filter.mpr ⟨hrep, hfrozenShape⟩
  have hterminal :
      (t, (1, p)) ∈ lowWheelCanonicalRepeatedTerminalBoundary R :=
    Finset.mem_filter.mpr ⟨hfrozen, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨hterminal, ?_⟩
  simpa [lowWheelTaggedDowncrossPivot, hpivot] using hpR

end RHLean.Proof
