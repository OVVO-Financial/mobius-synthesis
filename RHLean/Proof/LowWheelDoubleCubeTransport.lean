import Mathlib
import RHLean.Arithmetic.AdmissibleFaceSquarefreeImage
import RHLean.Proof.LowWheelTransportTripleCarrier

/-!
# Full two-cube realization of square-root transport

The prime-count-free transport still has one integer cofactor coordinate `c`
and one Boolean survivor-face coordinate `t`.  This module reindexes the
cofactor through its unique squarefree prime face and then uses the physical
square-root geometry to remove the cofactor-face truncation entirely.

At `X_R = R^2 - 1`, any active physical state satisfies

`R < P(t) * k`,
`P(u) * P(t) * k <= X_R`.

Those two inequalities force `P(u) < R`.  Hence every face `u` with product at
least `R` contributes zero automatically.  The complete transport can therefore
be written on two copies of the *same full low-prime Boolean cube*:

`u,t ⊆ {p prime | p <= R}`.

The signed atom is `(-1)^|u| (-1)^|t|`, and the only remaining restrictions are
the two physical inequalities above.  This is the symmetric carrier on which a
prime can be toggled sequentially in either cube coordinate.

No norm, PNT estimate, Strong Mertens input, or asymptotic argument appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Common physical `k`-carrier for one integer cofactor and one low-prime face. -/
def lowWheelTransportPhysicalKSet
    (R c : ℕ) (t : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (squareRootEndpoint R)).filter fun k =>
    R < primeFaceProduct t * k ∧
      (c * primeFaceProduct t) * k ≤ squareRootEndpoint R

/-- The quotient interval from the triple carrier is exactly the common
physical `k`-carrier. -/
theorem lowWheelTransportPhysicalKSet_eq_quotientInterval
    {R c : ℕ} {t : Finset ℕ}
    (hc : 1 ≤ c) (ht : t ∈ (primesUpTo R).powerset) :
    lowWheelTransportPhysicalKSet R c t =
      Finset.Ioc
        (R / primeFaceProduct t)
        (squareRootEndpoint R / (c * primeFaceProduct t)) := by
  classical
  have hdpos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hcdpos : 0 < c * primeFaceProduct t :=
    Nat.mul_pos (by omega) hdpos
  ext k
  simp only [lowWheelTransportPhysicalKSet, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_hk1, _hkX⟩, hlow, hup⟩
    constructor
    · apply (Nat.div_lt_iff_lt_mul hdpos).2
      simpa [Nat.mul_comm] using hlow
    · apply (Nat.le_div_iff_mul_le hcdpos).2
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hup
  · rintro ⟨hlow, hup⟩
    have hlow' : R < primeFaceProduct t * k := by
      have h := (Nat.div_lt_iff_lt_mul hdpos).1 hlow
      simpa [Nat.mul_comm] using h
    have hup' : (c * primeFaceProduct t) * k ≤ squareRootEndpoint R := by
      have h := (Nat.le_div_iff_mul_le hcdpos).1 hup
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    have hkpos : 0 < k := by
      by_contra hk0
      have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      simp at hlow'
    have hcd1 : 1 ≤ c * primeFaceProduct t := hcdpos
    have hkX : k ≤ squareRootEndpoint R := by
      calc
        k = 1 * k := by simp
        _ ≤ (c * primeFaceProduct t) * k := Nat.mul_le_mul_right k hcd1
        _ ≤ squareRootEndpoint R := hup'
    exact ⟨⟨by omega, hkX⟩, hlow', hup'⟩

/-- Integer-cofactor transport rewritten on the common physical `k` carrier. -/
def lowWheelTransportPhysicalLedger (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    ∑ t ∈ (primesUpTo R).powerset,
      ∑ _k ∈ lowWheelTransportPhysicalKSet R c t,
        canonicalMoebiusWeight c * (booleanCubeSign t : ℂ)

/-- The quotient-interval triple ledger and the common physical carrier are
identical. -/
theorem lowWheelTransportTripleLedger_eq_physicalLedger
    (R : ℕ) :
    lowWheelTransportTripleLedger R = lowWheelTransportPhysicalLedger R := by
  classical
  unfold lowWheelTransportTripleLedger lowWheelTransportPhysicalLedger
  apply Finset.sum_congr rfl
  intro c hc
  have hc1 : 1 ≤ c := (Finset.mem_Ico.mp hc).1
  apply Finset.sum_congr rfl
  intro t ht
  rw [lowWheelTransportPhysicalKSet_eq_quotientInterval hc1 ht]

/-- Weighted squarefree cofactor prefixes can be reindexed by their unique
admissible prime faces. -/
theorem canonicalMoebiusWeighted_Ico_eq_admissibleFaceSum
    (R : ℕ) (_hR : 1 ≤ R) (F : ℕ → ℂ) :
    (∑ c ∈ Finset.Ico 1 R, canonicalMoebiusWeight c * F c) =
      ∑ u ∈ admissiblePrimeFaces (R - 1),
        (booleanCubeSign u : ℂ) * F (primeFaceProduct u) := by
  classical
  let sqIco := (Finset.Ico 1 R).filter Squarefree
  have hfilter :
      (∑ c ∈ Finset.Ico 1 R, canonicalMoebiusWeight c * F c) =
        ∑ c ∈ sqIco, canonicalMoebiusWeight c * F c := by
    unfold sqIco
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hsq : Squarefree c
    · simp [hsq]
    · have hmu : μ c = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hsq, canonicalMoebiusWeight, hmu]
  rw [hfilter]
  symm
  refine Finset.sum_bij (fun u _hu => primeFaceProduct u) ?_ ?_ ?_ ?_
  · intro u hu
    have huAdm :
        primeProductAdmissible (primesUpTo (R - 1)) (R - 1) u :=
      mem_admissiblePrimeFaces.mp hu
    have hmu := moebius_admissiblePrimeFace_eq_booleanCubeSign huAdm
    have hmuNe : μ (primeFaceProduct u) ≠ 0 := by
      rw [hmu]
      simp [booleanCubeSign]
    have hsq : Squarefree (primeFaceProduct u) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    have hpos : 1 ≤ primeFaceProduct u :=
      Nat.one_le_iff_ne_zero.mpr hsq.ne_zero
    have hlt : primeFaceProduct u < R := by
      have hle : primeFaceProduct u ≤ R - 1 := huAdm.2
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hpos, hlt⟩, hsq⟩
  · intro u hu v hv huv
    exact primeFaceProduct_injective_on_admissible_primesUpTo
      (mem_admissiblePrimeFaces.mp hu)
      (mem_admissiblePrimeFaces.mp hv) huv
  · intro c hc
    rcases Finset.mem_filter.mp hc with ⟨hcI, hsq⟩
    let u := squarefreePrimeFace c
    have hcLe : c ≤ R - 1 := by
      have hlt := (Finset.mem_Ico.mp hcI).2
      omega
    have huAdm :
        primeProductAdmissible (primesUpTo (R - 1)) (R - 1) u :=
      squarefreePrimeFace_admissible hsq hcLe
    refine ⟨u, mem_admissiblePrimeFaces.mpr huAdm, ?_⟩
    exact primeFaceProduct_squarefreePrimeFace hsq
  · intro u hu
    have huAdm := mem_admissiblePrimeFaces.mp hu
    have hmu := moebius_admissiblePrimeFace_eq_booleanCubeSign huAdm
    unfold canonicalMoebiusWeight
    rw [hmu]

/-- The admissible cofactor faces below `R` are exactly the full low-prime cube
faces whose product is strictly below `R`. -/
theorem admissiblePrimeFaces_pred_eq_lowCube_filter_product_lt
    (R : ℕ) (_hR : 1 ≤ R) :
    admissiblePrimeFaces (R - 1) =
      (primesUpTo R).powerset.filter fun u => primeFaceProduct u < R := by
  classical
  ext u
  constructor
  · intro hu
    have huAdm := mem_admissiblePrimeFaces.mp hu
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro p hp
      have hpPred := mem_primesUpTo.mp (huAdm.1 hp)
      exact mem_primesUpTo.mpr ⟨hpPred.1, hpPred.2.trans (Nat.sub_le R 1)⟩
    · have hpred : R - 1 < R := by omega
      exact huAdm.2.trans_lt hpred
  · intro hu
    rcases Finset.mem_filter.mp hu with ⟨huPow, hprodR⟩
    have huSubR := Finset.mem_powerset.mp huPow
    have hprodPos : 0 < primeFaceProduct u := by
      unfold primeFaceProduct
      exact Finset.prod_pos fun p hp =>
        (prime_of_mem_primesUpTo (huSubR hp)).pos
    have huSubPred : u ⊆ primesUpTo (R - 1) := by
      intro p hp
      have hpR := mem_primesUpTo.mp (huSubR hp)
      have hpdiv : p ∣ primeFaceProduct u := by
        unfold primeFaceProduct
        exact Finset.dvd_prod_of_mem id hp
      have hpLeProd : p ≤ primeFaceProduct u :=
        Nat.le_of_dvd hprodPos hpdiv
      exact mem_primesUpTo.mpr ⟨hpR.1, by omega⟩
    apply mem_admissiblePrimeFaces.mpr
    exact ⟨huSubPred, by omega⟩

/-- **Square-root geometric cutoff.**  The two physical inequalities force the
cofactor-face product below the root.  This is the key reason the explicit
cofactor truncation can later be removed. -/
theorem lowWheelPhysical_imp_cofactorFace_lt_root
    {R k : ℕ} {u t : Finset ℕ} (hR : 1 ≤ R)
    (hlow : R < primeFaceProduct t * k)
    (hup : (primeFaceProduct u * primeFaceProduct t) * k ≤
      squareRootEndpoint R) :
    primeFaceProduct u < R := by
  by_contra hnot
  have huR : R ≤ primeFaceProduct u := Nat.le_of_not_gt hnot
  have hy : R + 1 ≤ primeFaceProduct t * k := by omega
  have hlower : R * (R + 1) ≤
      primeFaceProduct u * (primeFaceProduct t * k) :=
    Nat.mul_le_mul huR hy
  have hupper :
      primeFaceProduct u * (primeFaceProduct t * k) ≤ squareRootEndpoint R := by
    simpa [Nat.mul_assoc] using hup
  have hsqLt : R ^ 2 < R * (R + 1) := by
    rw [pow_two]
    nlinarith
  have hbad : R ^ 2 < squareRootEndpoint R :=
    hsqLt.trans_le (hlower.trans hupper)
  unfold squareRootEndpoint at hbad
  have hsqpos : 0 < R ^ 2 := by positivity
  omega

/-- Symmetric physical atom on two low-prime faces and one quotient coordinate. -/
def lowWheelDoubleCubeAtom
    (R : ℕ) (u t : Finset ℕ) (k : ℕ) : ℂ :=
  if R < primeFaceProduct t * k ∧
      (primeFaceProduct u * primeFaceProduct t) * k ≤ squareRootEndpoint R then
    (booleanCubeSign u : ℂ) * (booleanCubeSign t : ℂ)
  else
    0

/-- Full symmetric two-cube transport ledger. -/
def lowWheelDoubleCubeTransportLedger (R : ℕ) : ℂ :=
  ∑ u ∈ (primesUpTo R).powerset,
    ∑ t ∈ (primesUpTo R).powerset,
      ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowWheelDoubleCubeAtom R u t k

/-- Physical integer-cofactor ledger reindexed through admissible cofactor
faces. -/
theorem lowWheelTransportPhysicalLedger_eq_admissibleDoubleFace
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelTransportPhysicalLedger R =
      ∑ u ∈ admissiblePrimeFaces (R - 1),
        ∑ t ∈ (primesUpTo R).powerset,
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
            lowWheelDoubleCubeAtom R u t k := by
  classical
  unfold lowWheelTransportPhysicalLedger
  let F : ℕ → ℂ := fun c =>
    ∑ t ∈ (primesUpTo R).powerset,
      ∑ _k ∈ lowWheelTransportPhysicalKSet R c t,
        (booleanCubeSign t : ℂ)
  have hreindex := canonicalMoebiusWeighted_Ico_eq_admissibleFaceSum
    R (by omega) F
  calc
    (∑ c ∈ Finset.Ico 1 R,
        ∑ t ∈ (primesUpTo R).powerset,
          ∑ _k ∈ lowWheelTransportPhysicalKSet R c t,
            canonicalMoebiusWeight c * (booleanCubeSign t : ℂ)) =
      ∑ c ∈ Finset.Ico 1 R, canonicalMoebiusWeight c * F c := by
        apply Finset.sum_congr rfl
        intro c _hc
        dsimp [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _ht
        rw [Finset.mul_sum]
    _ = ∑ u ∈ admissiblePrimeFaces (R - 1),
        (booleanCubeSign u : ℂ) * F (primeFaceProduct u) := hreindex
    _ = ∑ u ∈ admissiblePrimeFaces (R - 1),
        ∑ t ∈ (primesUpTo R).powerset,
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
            lowWheelDoubleCubeAtom R u t k := by
      apply Finset.sum_congr rfl
      intro u _hu
      dsimp [F]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]
      unfold lowWheelTransportPhysicalKSet
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _hk
      unfold lowWheelDoubleCubeAtom
      by_cases hphys : R < primeFaceProduct t * k ∧
          (primeFaceProduct u * primeFaceProduct t) * k ≤ squareRootEndpoint R
      · simp [hphys]
      · simp [hphys]

/-- Faces with product at least `R` have zero physical contribution, uniformly
in the other face and quotient coordinate. -/
theorem lowWheelDoubleCubeAtom_eq_zero_of_root_le_face
    {R k : ℕ} {u t : Finset ℕ} (hR : 1 ≤ R)
    (hu : R ≤ primeFaceProduct u) :
    lowWheelDoubleCubeAtom R u t k = 0 := by
  unfold lowWheelDoubleCubeAtom
  by_cases hphys : R < primeFaceProduct t * k ∧
      (primeFaceProduct u * primeFaceProduct t) * k ≤ squareRootEndpoint R
  · have hlt := lowWheelPhysical_imp_cofactorFace_lt_root hR hphys.1 hphys.2
    exact (Nat.not_lt_of_ge hu hlt).elim
  · simp [hphys]

/-- **Remove the cofactor-face cutoff by geometry.**  The admissible face sum is
identical to the full first low-prime cube because all newly added faces have
zero physical atoms. -/
theorem admissibleDoubleFace_eq_fullDoubleCube
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ u ∈ admissiblePrimeFaces (R - 1),
        ∑ t ∈ (primesUpTo R).powerset,
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R),
            lowWheelDoubleCubeAtom R u t k) =
      lowWheelDoubleCubeTransportLedger R := by
  classical
  rw [admissiblePrimeFaces_pred_eq_lowCube_filter_product_lt R (by omega)]
  unfold lowWheelDoubleCubeTransportLedger
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases hlt : primeFaceProduct u < R
  · simp [hlt]
  · have hge : R ≤ primeFaceProduct u := Nat.le_of_not_gt hlt
    simp only [hlt, if_false]
    symm
    apply Finset.sum_eq_zero
    intro t _ht
    apply Finset.sum_eq_zero
    intro k _hk
    exact lowWheelDoubleCubeAtom_eq_zero_of_root_le_face (by omega) hge

/-- **Full two-cube transport identity.**  The original upper-prime transport is
exactly the symmetric signed ledger on two full copies of the low-prime cube.
The only restrictions left are the physical lower-root and square-endpoint
inequalities. -/
theorem squareRootTransportCofactorFirst_eq_lowWheelDoubleCube
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      lowWheelDoubleCubeTransportLedger R := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelTransportTripleLedger R hR,
    lowWheelTransportTripleLedger_eq_physicalLedger,
    lowWheelTransportPhysicalLedger_eq_admissibleDoubleFace R hR,
    admissibleDoubleFace_eq_fullDoubleCube R hR]

end RHLean.Proof
