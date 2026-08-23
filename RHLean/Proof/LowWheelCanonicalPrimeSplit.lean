import Mathlib
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Proof.LowWheelDoubleCubeTransport

/-!
# Canonical downcross split at the square-root prime boundary

The canonical defect is already an explicit adjacent least-prime downcross.
This module performs the next exact split before any norm or analytic estimate
is introduced.

For a downcross state `(c,k)` let

`p = minFac(c*k)`.

There are two disjoint regimes.

* `p <= R`: the pivot is an already-available low-prime coordinate.  This
  contribution is the low-pivot ledger.
* `R < p`: least-prime minimality and the square-root geometry force the state
  itself to be `(1,p)`.  The remaining low-wheel face is exactly the completed
  parent fibre read by the post-root fresh-prime recurrence.

Consequently the post-root part is exactly the original upper-prime Mertens
transform, while the complementary low-pivot part telescopes algebraically to
minus the canonical fixed ledger.  Since the fixed carrier consists only of
`(1,1)` states, this is a strictly fresh-prime-free remainder.

Everything here is finite and exact.  No absolute value, PNT estimate,
asymptotic, density model, or RH input appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Downcross states whose canonical least-prime pivot has already been
processed by the root cutoff. -/
def lowWheelCanonicalLowPivotDowncrossPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalDowncrossPart R t).filter fun x =>
    lowWheelCanonicalCofactorQuotientPivot x ≤ R

/-- Downcross states whose canonical least-prime pivot lies strictly beyond the
root cutoff. -/
def lowWheelCanonicalPostRootDowncrossPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalDowncrossPart R t).filter fun x =>
    R < lowWheelCanonicalCofactorQuotientPivot x

@[simp] theorem mem_lowWheelCanonicalLowPivotDowncrossPart
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelCanonicalLowPivotDowncrossPart R t ↔
      x ∈ lowWheelCanonicalDowncrossPart R t ∧
        lowWheelCanonicalCofactorQuotientPivot x ≤ R := by
  simp [lowWheelCanonicalLowPivotDowncrossPart]

@[simp] theorem mem_lowWheelCanonicalPostRootDowncrossPart
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelCanonicalPostRootDowncrossPart R t ↔
      x ∈ lowWheelCanonicalDowncrossPart R t ∧
        R < lowWheelCanonicalCofactorQuotientPivot x := by
  simp [lowWheelCanonicalPostRootDowncrossPart]

/-- The low-pivot and post-root pieces are an exact partition of the surviving
downcross carrier. -/
theorem lowWheelCanonicalDowncrossPart_eq_lowPivot_union_postRoot
    (R : ℕ) (t : Finset ℕ) :
    lowWheelCanonicalLowPivotDowncrossPart R t ∪
        lowWheelCanonicalPostRootDowncrossPart R t =
      lowWheelCanonicalDowncrossPart R t := by
  classical
  ext x
  simp only [Finset.mem_union,
    mem_lowWheelCanonicalLowPivotDowncrossPart,
    mem_lowWheelCanonicalPostRootDowncrossPart]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    by_cases hp : lowWheelCanonicalCofactorQuotientPivot x ≤ R
    · exact Or.inl ⟨hx, hp⟩
    · exact Or.inr ⟨hx, Nat.lt_of_not_ge hp⟩

/-- The two pivot regimes are disjoint. -/
theorem lowWheelCanonicalLowPivot_disjoint_postRoot
    (R : ℕ) (t : Finset ℕ) :
    Disjoint (lowWheelCanonicalLowPivotDowncrossPart R t)
      (lowWheelCanonicalPostRootDowncrossPart R t) := by
  classical
  rw [Finset.disjoint_left]
  intro x hlow hhigh
  have hpLow := (mem_lowWheelCanonicalLowPivotDowncrossPart.mp hlow).2
  have hpHigh := (mem_lowWheelCanonicalPostRootDowncrossPart.mp hhigh).2
  omega

/-- Signed low-pivot part of the explicit canonical downcross ledger. -/
def lowWheelCanonicalLowPivotDowncrossLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelCanonicalLowPivotDowncrossPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- Signed post-root-pivot part of the explicit canonical downcross ledger. -/
def lowWheelCanonicalPostRootDowncrossLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelCanonicalPostRootDowncrossPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- **Exact `p <= R` / `p > R` split.** -/
theorem lowWheelCanonicalDowncrossLedger_eq_lowPivot_add_postRoot
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      lowWheelCanonicalLowPivotDowncrossLedger R +
        lowWheelCanonicalPostRootDowncrossLedger R := by
  classical
  unfold lowWheelCanonicalDowncrossLedger
    lowWheelCanonicalLowPivotDowncrossLedger
    lowWheelCanonicalPostRootDowncrossLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [← Finset.sum_union (lowWheelCanonicalLowPivot_disjoint_postRoot R t),
    lowWheelCanonicalDowncrossPart_eq_lowPivot_union_postRoot R t]

/-- **Post-root rigidity.**  If a surviving downcross has least-prime pivot
`p > R`, then no nontrivial factor can remain in the cofactor or below `p` in
the quotient.  Hence the state itself is exactly `(1,p)`. -/
theorem lowWheelCanonicalPostRootDowncross_rigid
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossPart R t)
    (hRp : R < lowWheelCanonicalCofactorQuotientPivot (c, k)) :
    c = 1 ∧ k = lowWheelCanonicalCofactorQuotientPivot (c, k) := by
  let p := lowWheelCanonicalCofactorQuotientPivot (c, k)
  rcases lowWheelCanonicalDowncrossPart_adjacent_shell hx with
    ⟨hp0, _hpc0, hpk0, hdown0, _hhigh0⟩
  have hp : p.Prime := by simpa [p] using hp0
  have hpk : p ∣ k := by simpa [p] using hpk0
  have hdown : primeFaceProduct t * (k / p) ≤ R := by
    simpa [p] using hdown0
  have hRp' : R < p := by simpa [p] using hRp
  have hxPhys := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hmem := mem_lowWheelCanonicalPhysicalStateSet.mp hxPhys
  have hcI := Finset.mem_Ico.mp hmem.1
  have hkI := Finset.mem_Icc.mp hmem.2.1
  have hcpos : 0 < c := by omega
  have hkpos : 0 < k := by omega
  have hcEq : c = 1 := by
    by_contra hcne
    have hcgt : 1 < c := by omega
    let q := Nat.minFac c
    have hqPrime : q.Prime := by
      simpa [q] using Nat.minFac_prime (by omega : c ≠ 1)
    have hqDvdC : q ∣ c := by
      simpa [q] using Nat.minFac_dvd c
    have hqDvdProd : q ∣ c * k := dvd_mul_of_dvd_left hqDvdC k
    have hpLeQ : p ≤ q := by
      have h := Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
      simpa [p, lowWheelCanonicalCofactorQuotientPivot] using h
    have hqLeC : q ≤ c := Nat.le_of_dvd hcpos hqDvdC
    omega
  let j := k / p
  have hfacePos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hjLeProd : j ≤ primeFaceProduct t * j :=
    Nat.le_mul_of_pos_left j hfacePos
  have hjLeR : j ≤ R := hjLeProd.trans hdown
  have hpLeK : p ≤ k := Nat.le_of_dvd hkpos hpk
  have hjOne : 1 ≤ j := by
    unfold j
    exact (Nat.one_le_div_iff hp.pos).2 hpLeK
  have hkCancel : p * j = k := by
    simpa [j] using Nat.mul_div_cancel' hpk
  have hjEq : j = 1 := by
    by_contra hjne
    have hjgt : 1 < j := by omega
    let q := Nat.minFac j
    have hqPrime : q.Prime := by
      simpa [q] using Nat.minFac_prime (by omega : j ≠ 1)
    have hqDvdJ : q ∣ j := by
      simpa [q] using Nat.minFac_dvd j
    have hqDvdK : q ∣ k := by
      rw [← hkCancel]
      exact dvd_mul_of_dvd_right hqDvdJ p
    have hqDvdProd : q ∣ c * k := dvd_mul_of_dvd_right hqDvdK c
    have hpLeQ : p ≤ q := by
      have h := Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
      simpa [p, lowWheelCanonicalCofactorQuotientPivot] using h
    have hqLeJ : q ≤ j := Nat.le_of_dvd (by omega) hqDvdJ
    omega
  have hkEq : k = p := by
    rw [← hkCancel, hjEq]
    simp
  exact ⟨hcEq, by simpa [p] using hkEq⟩

/-- Prime candidates in the exact post-root fibre attached to one low-wheel
face. -/
def lowWheelCanonicalPostRootPrimeSet
    (R : ℕ) (t : Finset ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun q =>
    q.Prime ∧ primeFaceProduct t * q ≤ squareRootEndpoint R

/-- On a prime input, the canonical least-prime pivot of `(1,q)` is `q`. -/
theorem lowWheelCanonicalPivot_one_prime
    {q : ℕ} (hq : q.Prime) :
    lowWheelCanonicalCofactorQuotientPivot (1, q) = q := by
  have hminPrime : (Nat.minFac q).Prime := Nat.minFac_prime hq.ne_one
  have hminDvd : Nat.minFac q ∣ q := Nat.minFac_dvd q
  have hminEq : Nat.minFac q = q :=
    (Nat.prime_dvd_prime_iff_eq hminPrime hq).mp hminDvd
  simp [lowWheelCanonicalCofactorQuotientPivot, hminEq]

/-- Exact membership description of the post-root piece: after rigidity, the
only state coordinate is the post-root prime itself. -/
theorem mem_lowWheelCanonicalPostRootDowncrossPart_iff
    {R c k : ℕ} {t : Finset ℕ} (hR : 2 ≤ R)
    (ht : t ∈ (primesUpTo R).powerset) :
    (c, k) ∈ lowWheelCanonicalPostRootDowncrossPart R t ↔
      c = 1 ∧ k ∈ lowWheelCanonicalPostRootPrimeSet R t := by
  constructor
  · intro hx
    rcases mem_lowWheelCanonicalPostRootDowncrossPart.mp hx with
      ⟨hdown, hRp⟩
    rcases lowWheelCanonicalPostRootDowncross_rigid ht hdown hRp with
      ⟨hcEq, hkPivot⟩
    have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hdown
    have hkPrime : k.Prime := by
      rw [hkPivot]
      exact hshell.1
    have hxPhys := (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
    have hmem := mem_lowWheelCanonicalPhysicalStateSet.mp hxPhys
    have hkRange := Finset.mem_Icc.mp hmem.2.1
    have hcarrier := hmem.2.2.2
    apply And.intro hcEq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, hkRange.2⟩, hkPrime, ?_⟩
    · rw [hkPivot]
      exact hRp
    · simpa [hcEq, Nat.one_mul] using hcarrier.2.2.2
  · rintro ⟨rfl, hk⟩
    rcases Finset.mem_filter.mp hk with ⟨hkI, hkPrime, htop⟩
    rcases Finset.mem_Ioc.mp hkI with ⟨hRk, hkX⟩
    have hfacePos : 0 < primeFaceProduct t :=
      primeFaceProduct_pos_of_mem_powerset ht
    have hkLe : k ≤ primeFaceProduct t * k :=
      Nat.le_mul_of_pos_left k hfacePos
    have hhigh : R < primeFaceProduct t * k := hRk.trans_le hkLe
    have hfaceLt : primeFaceProduct t < R := by
      have h := lowWheelPhysical_imp_cofactorFace_lt_root
        (R := R) (k := k) (u := t) (t := ∅) (by omega)
        (by simpa [primeFaceProduct] using hRk)
        (by simpa [primeFaceProduct] using htop)
      exact h
    have hpivot : lowWheelCanonicalCofactorQuotientPivot (1, k) = k :=
      lowWheelCanonicalPivot_one_prime hkPrime
    have hxPhys : (1, k) ∈ lowWheelCanonicalPhysicalStateSet R t := by
      apply mem_lowWheelCanonicalPhysicalStateSet.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨by norm_num, by omega⟩,
        Finset.mem_Icc.mpr ⟨hkPrime.one_le, hkX⟩, by simp, ?_⟩
      exact ⟨by norm_num, by omega, hhigh, by simpa using htop⟩
    have hnot : ¬ lowWheelCanonicalCofactorQuotientPivot (1, k) ∣ 1 := by
      rw [hpivot]
      intro hd
      have hle : k ≤ 1 := Nat.le_of_dvd (by norm_num) hd
      omega
    have hdown : primeFaceProduct t *
        (k / lowWheelCanonicalCofactorQuotientPivot (1, k)) ≤ R := by
      rw [hpivot, Nat.div_self hkPrime.pos]
      simpa only [Nat.mul_one] using hfaceLt.le
    apply mem_lowWheelCanonicalPostRootDowncrossPart.mpr
    refine ⟨mem_lowWheelCanonicalDowncrossPart.mpr ⟨hxPhys, hnot, hdown⟩, ?_⟩
    rw [hpivot]
    exact hRk

/-- The signed post-root state fibre for one face is simply one copy of the
Boolean sign for each admissible post-root prime. -/
theorem sum_lowWheelCanonicalPostRootDowncrossPart_eq_primeSet
    (R : ℕ) (hR : 2 ≤ R) {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    (∑ x ∈ lowWheelCanonicalPostRootDowncrossPart R t,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ _q ∈ lowWheelCanonicalPostRootPrimeSet R t,
        (booleanCubeSign t : ℂ) := by
  classical
  symm
  refine Finset.sum_bij (fun q _hq => (1, q)) ?_ ?_ ?_ ?_
  · intro q hq
    exact (mem_lowWheelCanonicalPostRootDowncrossPart_iff hR ht).2 ⟨rfl, hq⟩
  · intro q1 _hq1 q2 _hq2 heq
    exact congrArg Prod.snd heq
  · intro x hx
    rcases x with ⟨c, k⟩
    have hmem := (mem_lowWheelCanonicalPostRootDowncrossPart_iff hR ht).1 hx
    refine ⟨k, hmem.2, ?_⟩
    exact Prod.ext hmem.1.symm rfl
  · intro _q _hq
    simp [canonicalMoebiusWeight]

/-- Completed low-wheel parent mass attached to one post-root prime. -/
def lowWheelCanonicalPostRootParentMass (R q : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    if primeFaceProduct t * q ≤ squareRootEndpoint R then
      (booleanCubeSign t : ℂ)
    else 0

/-- A post-root prime sees an already-completed parent cutoff strictly below
`R`, so its low-wheel face mass is the ordinary lower-scale Mertens value. -/
theorem lowWheelCanonicalPostRootParentMass_eq_mertens
    {R q : ℕ} (hR : 1 ≤ R) (hq : q.Prime) (hRq : R < q) :
    lowWheelCanonicalPostRootParentMass R q =
      mertensSummatory (squareRootEndpoint R / q) := by
  have hcut := squareRootEndpoint_div_lt_root_of_postRoot hR hRq
  calc
    lowWheelCanonicalPostRootParentMass R q =
        ((frozenPrimeUniverseMass (primesUpTo R)
          (squareRootEndpoint R / q) : ℤ) : ℂ) := by
      unfold lowWheelCanonicalPostRootParentMass
      rw [frozenPrimeUniverseMass_eq_cutoffSum]
      push_cast
      apply Finset.sum_congr rfl
      intro t _ht
      have hiff :
          primeFaceProduct t * q ≤ squareRootEndpoint R ↔
            primeFaceProduct t ≤ squareRootEndpoint R / q :=
        (Nat.le_div_iff_mul_le hq.pos).symm
      by_cases htop : primeFaceProduct t * q ≤ squareRootEndpoint R
      · have hsmall : primeFaceProduct t ≤ squareRootEndpoint R / q := hiff.mp htop
        simp [htop, hsmall]
      · have hsmall : ¬ primeFaceProduct t ≤ squareRootEndpoint R / q := by
          intro hs
          exact htop (hiff.mpr hs)
        simp [htop, hsmall]
    _ = mertensSummatory (squareRootEndpoint R / q) :=
      frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens (Nat.le_of_lt hcut)

/-- The rigid post-root downcross ledger is exactly the chronological post-root
reciprocal-fibre Mertens transform. -/
theorem lowWheelCanonicalPostRootDowncrossLedger_eq_mertensTransform
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelCanonicalPostRootDowncrossLedger R =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if q.Prime then mertensSummatory (squareRootEndpoint R / q) else 0 := by
  classical
  unfold lowWheelCanonicalPostRootDowncrossLedger
  calc
    (∑ t ∈ (primesUpTo R).powerset,
        ∑ x ∈ lowWheelCanonicalPostRootDowncrossPart R t,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ t ∈ (primesUpTo R).powerset,
        ∑ _q ∈ lowWheelCanonicalPostRootPrimeSet R t,
          (booleanCubeSign t : ℂ) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact sum_lowWheelCanonicalPostRootDowncrossPart_eq_primeSet R hR ht
    _ = ∑ t ∈ (primesUpTo R).powerset,
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime ∧ primeFaceProduct t * q ≤ squareRootEndpoint R then
            (booleanCubeSign t : ℂ)
          else 0 := by
            apply Finset.sum_congr rfl
            intro t _ht
            unfold lowWheelCanonicalPostRootPrimeSet
            rw [Finset.sum_filter]
    _ = ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        ∑ t ∈ (primesUpTo R).powerset,
          if q.Prime ∧ primeFaceProduct t * q ≤ squareRootEndpoint R then
            (booleanCubeSign t : ℂ)
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if q.Prime then mertensSummatory (squareRootEndpoint R / q) else 0 := by
      apply Finset.sum_congr rfl
      intro q hqI
      by_cases hq : q.Prime
      · simp only [hq, true_and, if_true]
        have hRq := (Finset.mem_Ioc.mp hqI).1
        calc
          (∑ t ∈ (primesUpTo R).powerset,
              if primeFaceProduct t * q ≤ squareRootEndpoint R then
                (booleanCubeSign t : ℂ)
              else 0) = lowWheelCanonicalPostRootParentMass R q := by
                rfl
          _ = mertensSummatory (squareRootEndpoint R / q) :=
            lowWheelCanonicalPostRootParentMass_eq_mertens (by omega) hq hRq
      · simp [hq]

/-- Therefore the entire `p > R` sector is not a new error term: it is exactly
the original post-root upper-prime transport. -/
theorem lowWheelCanonicalPostRootDowncrossLedger_eq_transport
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelCanonicalPostRootDowncrossLedger R =
      squareRootTransportCofactorFirst R := by
  rw [lowWheelCanonicalPostRootDowncrossLedger_eq_mertensTransform R hR,
    ← squareRootTransportPrimeFirst_eq_mertensTransform R (by omega),
    ← squareRootTransportCofactorFirst_eq_primeFirst]

/-- Fresh-prime-free remainder left after the low-pivot telescope.  The fixed
carrier consists only of `(1,1)` states, so no active least-prime pivot remains. -/
def lowWheelCanonicalFreshPrimeFreeLedger (R : ℕ) : ℂ :=
  -lowWheelCanonicalFixedLedger R

/-- **Low-pivot telescope.**  Once the rigid post-root sector is recombined into
its complete reciprocal fibres, the entire `p <= R` contribution collapses to
the fresh-prime-free fixed ledger.  This is exact algebra on the finite
partition; no magnitude has been taken. -/
theorem lowWheelCanonicalLowPivotDowncrossLedger_eq_freshPrimeFree
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelCanonicalLowPivotDowncrossLedger R =
      lowWheelCanonicalFreshPrimeFreeLedger R := by
  have hsplit := lowWheelCanonicalDowncrossLedger_eq_lowPivot_add_postRoot R
  have hdef : lowWheelCanonicalDefectLedger R =
      lowWheelCanonicalDowncrossLedger R :=
    lowWheelCanonicalDefectLedger_eq_downcrossLedger R
  have hdefPhys : lowWheelCanonicalDefectLedger R =
      lowWheelCanonicalPhysicalLedger R - lowWheelCanonicalFixedLedger R := by
    rw [lowWheelCanonicalPhysicalLedger_eq_fixed_add_defect R]
    ring
  have hphys : lowWheelCanonicalPhysicalLedger R =
      squareRootTransportCofactorFirst R :=
    (squareRootTransportCofactorFirst_eq_canonicalPhysicalLedger R hR).symm
  have hhigh := lowWheelCanonicalPostRootDowncrossLedger_eq_transport R hR
  unfold lowWheelCanonicalFreshPrimeFreeLedger
  calc
    lowWheelCanonicalLowPivotDowncrossLedger R =
        lowWheelCanonicalDowncrossLedger R -
          lowWheelCanonicalPostRootDowncrossLedger R := by
      rw [hsplit]
      ring
    _ = lowWheelCanonicalDefectLedger R -
          lowWheelCanonicalPostRootDowncrossLedger R := by rw [← hdef]
    _ = (lowWheelCanonicalPhysicalLedger R - lowWheelCanonicalFixedLedger R) -
          lowWheelCanonicalPostRootDowncrossLedger R := by rw [hdefPhys]
    _ = (squareRootTransportCofactorFirst R - lowWheelCanonicalFixedLedger R) -
          lowWheelCanonicalPostRootDowncrossLedger R := by rw [hphys]
    _ = -lowWheelCanonicalFixedLedger R := by rw [hhigh]; ring

/-- In ordinary endpoint coordinates the low-pivot telescope is exactly the
lower Mertens state minus the already-smooth frozen root state. -/
theorem lowWheelCanonicalLowPivotDowncrossLedger_eq_mertens_sub_smooth
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalLowPivotDowncrossLedger R =
      mertensSummatory R - squareRootSmoothMass (R - 1) := by
  rw [lowWheelCanonicalLowPivotDowncrossLedger_eq_freshPrimeFree R (by omega)]
  unfold lowWheelCanonicalFreshPrimeFreeLedger
  rw [lowWheelCanonicalFixedLedger_eq_smooth_sub_mertens R hR]
  ring

end RHLean.Proof