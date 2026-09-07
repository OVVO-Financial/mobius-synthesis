import Mathlib
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Proof.LowWheelSurvivorFloorExpansion
import RHLean.Analysis.CanonicalLowOccupancy

/-!
# Boundary multiplicity of the canonical root-downcross ledger

The final seam records one quantitative proposition,

`||D_R|| <= C * R`,

for `D_R = lowWheelCanonicalDowncrossLedger R`, and proves that it implies the
repository's native formal Riemann hypothesis theorem.  Nothing in the tree had
so far proved *any* inequality about `D_R`.  This file proves several, all
unconditional, all from finite geometry, and none of them assuming the seam.

## What is proved

* `card_lowWheelCanonicalDowncrossChargingFaces_le` -- **boundary multiplicity.**
  Fix a boundary state `(c,k)`, let `p = minFac (c*k)` be its canonical pivot and
  `j = k / p` its root-side parent cofactor.  The Boolean faces that charge that
  one state are carried injectively by `primeFaceProduct` into the single integer
  window `Ioc (R / k) (R / j)`, so the state is charged at most
  `R / j - R / k` times.  A boundary state therefore cannot be charged
  independently once per prime coordinate: its whole ownership set is one
  interval fixed by the state alone.

* `card_lowWheelCanonicalDowncrossContributingFaces_le` -- **face collapse.**
  Of the `2 ^ pi(R)` faces of the low-prime Boolean cube, at most `R` carry any
  downcross mass at all.  Every nonempty face has `primeFaceProduct t <= R`,
  because the downcross geometry reads `primeFaceProduct t * j <= R` with
  `j >= 1`, and prime-face products are injective.

* `card_lowWheelCanonicalDowncrossPart_le` -- **per-face window.**  A single face
  `t` retains only states inside `Ico 1 R` times `Ioc (R / P) (W / P)`, where
  `P = primeFaceProduct t` and `W = R ^ 2 - 1`.

* `norm_lowWheelCanonicalDowncrossLedger_le_quartic` -- an actual unconditional
  `<=` on the ledger norm: `||D_R|| <= R ^ 4`, obtained from the two counts
  above with no analytic input.

## What is *not* proved, and why the counting route cannot prove it

The quartic bound is honest but weak: it is worse than the trivial
`||D_R|| <= ||M(R)|| + ||M(R^2-1)||`, which is `O(R^2)`.  That is not an artifact
of a lossy step.  `card_primes_le_lowWheelCanonicalDowncrossUnsignedMass` proves
that the unsigned mass of the ledger -- the quantity every triangle-inequality
argument bounds -- already dominates `pi(R^2-1) - pi(R)` at the empty face alone:
the map `k |-> (1,k)` embeds every integer of `(R, R^2-1]` whose least-prime
quotient is still at or below the root, in particular every prime of that range,
into `lowWheelCanonicalDowncrossPart R empty`, each with Moebius weight `+1` and
face sign `+1`.

Consequently no bound of the shape `||D_R|| <= C * R` can be reached by
discarding signs: the unsigned mass is superlinear.  Every remaining route to
the seam must cancel signs across the ownership intervals produced here, not
estimate them termwise.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Ownership of a single boundary state -/

/-- The faces of the low-prime Boolean cube that charge one fixed boundary
state. -/
def lowWheelCanonicalDowncrossChargingFaces
    (R : ℕ) (x : LowWheelCofactorQuotientState) : Finset (Finset ℕ) :=
  (primesUpTo R).powerset.filter fun t =>
    x ∈ lowWheelCanonicalDowncrossPart R t

theorem mem_lowWheelCanonicalDowncrossChargingFaces
    {R : ℕ} {x : LowWheelCofactorQuotientState} {t : Finset ℕ} :
    t ∈ lowWheelCanonicalDowncrossChargingFaces R x ↔
      t ∈ (primesUpTo R).powerset ∧
        x ∈ lowWheelCanonicalDowncrossPart R t := by
  unfold lowWheelCanonicalDowncrossChargingFaces
  exact Finset.mem_filter

/-- **Ownership window.**  Every face charging the boundary state `(c,k)` has its
prime-face product inside one integer window determined by the state alone: it
is above `R / k` because the state is still on the high side of the root, and at
most `R / (k / p)` because deleting the canonical pivot crosses back. -/
theorem primeFaceProduct_mem_Ioc_of_mem_chargingFaces
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k)) :
    primeFaceProduct t ∈
      Finset.Ioc (R / k)
        (R / (k / lowWheelCanonicalCofactorQuotientPivot (c, k))) := by
  obtain ⟨_htPow, hx⟩ := mem_lowWheelCanonicalDowncrossChargingFaces.mp ht
  obtain ⟨hp, _hpc, hpk, hdown, _hup⟩ :=
    lowWheelCanonicalDowncrossPart_adjacent_shell hx
  have hmem := mem_lowWheelCanonicalDowncrossPart.mp hx
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp hmem.1
  have hkpos : 0 < k := (Finset.mem_Icc.mp hphys.2.1).1
  have hjpos : 0 < k / lowWheelCanonicalCofactorQuotientPivot (c, k) :=
    Nat.div_pos (Nat.le_of_dvd hkpos hpk) hp.pos
  obtain ⟨_hc1, _hcR, hhigh, _htop⟩ := hphys.2.2.2
  have hhigh' : R < primeFaceProduct t * k := hhigh
  refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hkpos).mpr hhigh'
  · exact (Nat.le_div_iff_mul_le hjpos).mpr hdown

/-- Prime-face products separate the faces charging one boundary state. -/
theorem primeFaceProduct_injOn_chargingFaces
    (R : ℕ) (x : LowWheelCofactorQuotientState) :
    Set.InjOn primeFaceProduct
      (↑(lowWheelCanonicalDowncrossChargingFaces R x)) := by
  intro u hu v hv hprod
  have hu' := mem_lowWheelCanonicalDowncrossChargingFaces.mp
    (Finset.mem_coe.mp hu)
  have hv' := mem_lowWheelCanonicalDowncrossChargingFaces.mp
    (Finset.mem_coe.mp hv)
  have huSub := Finset.mem_powerset.mp hu'.1
  have hvSub := Finset.mem_powerset.mp hv'.1
  exact (primeFaceProduct_eq_iff
    (fun r hr => prime_of_mem_primesUpTo (huSub hr))
    (fun r hr => prime_of_mem_primesUpTo (hvSub hr))).mp hprod

/-- **Boundary multiplicity bound.**  One boundary state is charged by at most
`R / (k / p) - R / k` faces, where `p` is its canonical pivot.  This is an
ownership statement, not an estimate: the whole charging set of a state is a
single integer window fixed by that state. -/
theorem card_lowWheelCanonicalDowncrossChargingFaces_le
    (R c k : ℕ) :
    (lowWheelCanonicalDowncrossChargingFaces R (c, k)).card ≤
      R / (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) - R / k := by
  have hcard := Finset.card_le_card_of_injOn primeFaceProduct
    (fun _u hu => primeFaceProduct_mem_Ioc_of_mem_chargingFaces hu)
    (primeFaceProduct_injOn_chargingFaces R (c, k))
  simpa [Nat.card_Ioc] using hcard

/-- The seat count of a boundary state never exceeds the root.  This is the
proved form of the "fewer than `R` multiplier seats" geometry. -/
theorem card_lowWheelCanonicalDowncrossChargingFaces_le_root
    (R c k : ℕ) :
    (lowWheelCanonicalDowncrossChargingFaces R (c, k)).card ≤ R :=
  le_trans (card_lowWheelCanonicalDowncrossChargingFaces_le R c k)
    (le_trans (Nat.sub_le _ _) (Nat.div_le_self _ _))

/-! ## Collapse of the face cube -/

/-- The faces that retain any downcross state at all. -/
def lowWheelCanonicalDowncrossContributingFaces (R : ℕ) : Finset (Finset ℕ) :=
  (primesUpTo R).powerset.filter fun t =>
    (lowWheelCanonicalDowncrossPart R t).Nonempty

theorem mem_lowWheelCanonicalDowncrossContributingFaces
    {R : ℕ} {t : Finset ℕ} :
    t ∈ lowWheelCanonicalDowncrossContributingFaces R ↔
      t ∈ (primesUpTo R).powerset ∧
        (lowWheelCanonicalDowncrossPart R t).Nonempty := by
  unfold lowWheelCanonicalDowncrossContributingFaces
  exact Finset.mem_filter

/-- A face carrying any downcross state has prime-face product at most the
root.  The root-side parent `primeFaceProduct t * (k / p)` is already `<= R`,
and the parent cofactor is at least one. -/
theorem primeFaceProduct_le_of_downcrossPart_nonempty
    {R : ℕ} {t : Finset ℕ}
    (h : (lowWheelCanonicalDowncrossPart R t).Nonempty) :
    primeFaceProduct t ≤ R := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨c, k⟩ := x
  obtain ⟨hp, _hpc, hpk, hdown, _hup⟩ :=
    lowWheelCanonicalDowncrossPart_adjacent_shell hx
  have hmem := mem_lowWheelCanonicalDowncrossPart.mp hx
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp hmem.1
  have hkpos : 0 < k := (Finset.mem_Icc.mp hphys.2.1).1
  have hjpos : 0 < k / lowWheelCanonicalCofactorQuotientPivot (c, k) :=
    Nat.div_pos (Nat.le_of_dvd hkpos hpk) hp.pos
  have hstep : primeFaceProduct t ≤
      primeFaceProduct t *
        (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) := by
    have hmul := Nat.mul_le_mul (le_refl (primeFaceProduct t)) hjpos
    simpa using hmul
  exact le_trans hstep hdown

/-- **Face collapse.**  At most `R` of the `2 ^ pi(R)` faces of the low-prime
Boolean cube retain any downcross state. -/
theorem card_lowWheelCanonicalDowncrossContributingFaces_le
    (R : ℕ) :
    (lowWheelCanonicalDowncrossContributingFaces R).card ≤ R := by
  have hmaps : ∀ t ∈ lowWheelCanonicalDowncrossContributingFaces R,
      primeFaceProduct t ∈ Finset.Icc 1 R := by
    intro t ht
    obtain ⟨htPow, hne⟩ :=
      mem_lowWheelCanonicalDowncrossContributingFaces.mp ht
    exact Finset.mem_Icc.mpr
      ⟨primeFaceProduct_pos_of_mem_powerset htPow,
        primeFaceProduct_le_of_downcrossPart_nonempty hne⟩
  have hinj : Set.InjOn primeFaceProduct
      (↑(lowWheelCanonicalDowncrossContributingFaces R)) := by
    intro u hu v hv hprod
    have hu' := mem_lowWheelCanonicalDowncrossContributingFaces.mp
      (Finset.mem_coe.mp hu)
    have hv' := mem_lowWheelCanonicalDowncrossContributingFaces.mp
      (Finset.mem_coe.mp hv)
    have huSub := Finset.mem_powerset.mp hu'.1
    have hvSub := Finset.mem_powerset.mp hv'.1
    exact (primeFaceProduct_eq_iff
      (fun r hr => prime_of_mem_primesUpTo (huSub hr))
      (fun r hr => prime_of_mem_primesUpTo (hvSub hr))).mp hprod
  have hcard := Finset.card_le_card_of_injOn primeFaceProduct hmaps hinj
  simpa using hcard

/-! ## Per-face window -/

/-- Every state retained by one face lies in an explicit rectangle: the cofactor
below the root, the quotient inside the reciprocal band of that face. -/
theorem lowWheelCanonicalDowncrossPart_subset_stateWindow
    (R : ℕ) (t : Finset ℕ) :
    lowWheelCanonicalDowncrossPart R t ⊆
      (Finset.Ico 1 R) ×ˢ
        (Finset.Ioc (R / primeFaceProduct t)
          (squareRootEndpoint R / primeFaceProduct t)) := by
  intro x hx
  have hmem := mem_lowWheelCanonicalDowncrossPart.mp hx
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp hmem.1
  obtain ⟨hc1, _hcR, hhigh, htop⟩ := hphys.2.2.2
  have hhigh' : R < primeFaceProduct t * x.2 := hhigh
  have htop' : x.1 * primeFaceProduct t * x.2 ≤ squareRootEndpoint R := htop
  have hc1' : 1 ≤ x.1 := hc1
  have hPpos : 0 < primeFaceProduct t := by
    rcases Nat.eq_zero_or_pos (primeFaceProduct t) with h0 | hpos
    · rw [h0] at hhigh'
      simp at hhigh'
    · exact hpos
  refine Finset.mem_product.mpr ⟨hphys.1, ?_⟩
  refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
  · have hcomm : R < x.2 * primeFaceProduct t := by
      rw [Nat.mul_comm]
      exact hhigh'
    exact (Nat.div_lt_iff_lt_mul hPpos).mpr hcomm
  · have hstep : x.2 * primeFaceProduct t ≤ squareRootEndpoint R := by
      calc x.2 * primeFaceProduct t
          = 1 * primeFaceProduct t * x.2 := by ring
        _ ≤ x.1 * primeFaceProduct t * x.2 :=
            Nat.mul_le_mul (Nat.mul_le_mul hc1' (le_refl _)) (le_refl _)
        _ ≤ squareRootEndpoint R := htop'
    exact (Nat.le_div_iff_mul_le hPpos).mpr hstep

/-- Crude but unconditional per-face state count. -/
theorem card_lowWheelCanonicalDowncrossPart_le
    (R : ℕ) (t : Finset ℕ) :
    (lowWheelCanonicalDowncrossPart R t).card ≤
      (R - 1) * squareRootEndpoint R := by
  have hsub := Finset.card_le_card
    (lowWheelCanonicalDowncrossPart_subset_stateWindow R t)
  refine hsub.trans ?_
  rw [Finset.card_product, Nat.card_Ico, Nat.card_Ioc]
  exact Nat.mul_le_mul (le_refl _)
    (le_trans (Nat.sub_le _ _) (Nat.div_le_self _ _))

/-! ## An actual unconditional bound on the ledger -/

/-- Total unsigned mass of the canonical downcross carrier.  This is exactly the
quantity that every triangle-inequality argument bounds. -/
def lowWheelCanonicalDowncrossUnsignedMass (R : ℕ) : ℕ :=
  ∑ t ∈ (primesUpTo R).powerset, (lowWheelCanonicalDowncrossPart R t).card

/-- Discarding both the Möbius weight and the face sign. -/
theorem norm_lowWheelCanonicalDowncrossLedger_le_unsignedMass (R : ℕ) :
    ‖lowWheelCanonicalDowncrossLedger R‖ ≤
      (lowWheelCanonicalDowncrossUnsignedMass R : ℝ) := by
  unfold lowWheelCanonicalDowncrossLedger lowWheelCanonicalDowncrossUnsignedMass
  push_cast
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro t _ht
  refine le_trans (norm_sum_le _ _) ?_
  have hsign : ‖((booleanCubeSign t : ℤ) : ℂ)‖ = 1 := by
    have hpow : ((booleanCubeSign t : ℤ) : ℂ) = (-1 : ℂ) ^ t.card := by
      simp [booleanCubeSign]
    rw [hpow, norm_pow, norm_neg, norm_one, one_pow]
  have hterm : ∀ x ∈ lowWheelCanonicalDowncrossPart R t,
      ‖canonicalMoebiusWeight x.1 * ((booleanCubeSign t : ℤ) : ℂ)‖ ≤ 1 := by
    intro x _hx
    rw [norm_mul, hsign, mul_one]
    exact norm_canonicalMoebiusWeight_le_one x.1
  calc ∑ x ∈ lowWheelCanonicalDowncrossPart R t,
        ‖canonicalMoebiusWeight x.1 * ((booleanCubeSign t : ℤ) : ℂ)‖
      ≤ ∑ _x ∈ lowWheelCanonicalDowncrossPart R t, (1 : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ((lowWheelCanonicalDowncrossPart R t).card : ℝ) := by simp

/-- The unsigned mass is carried by at most `R` faces, each holding at most
`(R-1) * (R^2-1)` states. -/
theorem lowWheelCanonicalDowncrossUnsignedMass_le (R : ℕ) :
    lowWheelCanonicalDowncrossUnsignedMass R ≤
      R * ((R - 1) * squareRootEndpoint R) := by
  unfold lowWheelCanonicalDowncrossUnsignedMass
  have hrestrict :
      ∑ t ∈ lowWheelCanonicalDowncrossContributingFaces R,
          (lowWheelCanonicalDowncrossPart R t).card
        = ∑ t ∈ (primesUpTo R).powerset,
            (lowWheelCanonicalDowncrossPart R t).card := by
    refine Finset.sum_subset ?_ ?_
    · intro t ht
      exact (mem_lowWheelCanonicalDowncrossContributingFaces.mp ht).1
    · intro t ht hnot
      have hempty : ¬ (lowWheelCanonicalDowncrossPart R t).Nonempty := by
        intro hne
        exact hnot
          (mem_lowWheelCanonicalDowncrossContributingFaces.mpr ⟨ht, hne⟩)
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp
  rw [← hrestrict]
  have hbound := Finset.sum_le_card_nsmul
    (lowWheelCanonicalDowncrossContributingFaces R)
    (fun t => (lowWheelCanonicalDowncrossPart R t).card)
    ((R - 1) * squareRootEndpoint R)
    (fun t _ht => card_lowWheelCanonicalDowncrossPart_le R t)
  have hbound' :
      ∑ t ∈ lowWheelCanonicalDowncrossContributingFaces R,
          (lowWheelCanonicalDowncrossPart R t).card ≤
        (lowWheelCanonicalDowncrossContributingFaces R).card *
          ((R - 1) * squareRootEndpoint R) := by
    simpa [smul_eq_mul] using hbound
  exact le_trans hbound' (Nat.mul_le_mul
    (card_lowWheelCanonicalDowncrossContributingFaces_le R) (le_refl _))

/-- **An actual unconditional inequality for the canonical downcross ledger.**
No hypothesis, no analytic input, no assumed estimate: the finite geometry alone
gives `||D_R|| <= R ^ 4`. -/
theorem norm_lowWheelCanonicalDowncrossLedger_le_quartic (R : ℕ) :
    ‖lowWheelCanonicalDowncrossLedger R‖ ≤ (R : ℝ) ^ 4 := by
  refine le_trans (norm_lowWheelCanonicalDowncrossLedger_le_unsignedMass R) ?_
  have hnat : lowWheelCanonicalDowncrossUnsignedMass R ≤ R ^ 4 := by
    refine le_trans (lowWheelCanonicalDowncrossUnsignedMass_le R) ?_
    have h1 : R - 1 ≤ R := Nat.sub_le _ _
    have h2 : squareRootEndpoint R ≤ R ^ 2 := by
      unfold squareRootEndpoint
      exact Nat.sub_le _ _
    calc R * ((R - 1) * squareRootEndpoint R)
        ≤ R * (R * R ^ 2) := Nat.mul_le_mul (le_refl R) (Nat.mul_le_mul h1 h2)
      _ = R ^ 4 := by ring
  exact_mod_cast hnat

/-! ## Why the unsigned route stops here -/

/-- Empty-face boundary witnesses: integers strictly above the root whose
least-prime quotient is still at or below the root. -/
def lowWheelCanonicalDowncrossRootWitnesses (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun k => k / k.minFac ≤ R

theorem mem_lowWheelCanonicalDowncrossRootWitnesses {R k : ℕ} :
    k ∈ lowWheelCanonicalDowncrossRootWitnesses R ↔
      k ∈ Finset.Ioc R (squareRootEndpoint R) ∧ k / k.minFac ≤ R := by
  unfold lowWheelCanonicalDowncrossRootWitnesses
  exact Finset.mem_filter

/-- Each witness is a genuine downcross state at the empty face, with cofactor
`1`; its Möbius weight and its face sign are both `+1`. -/
theorem lowWheelCanonicalDowncrossRootWitness_mem_emptyFace
    {R k : ℕ} (hR : 2 ≤ R)
    (hk : k ∈ lowWheelCanonicalDowncrossRootWitnesses R) :
    ((1 : ℕ), k) ∈ lowWheelCanonicalDowncrossPart R (∅ : Finset ℕ) := by
  have hk' := mem_lowWheelCanonicalDowncrossRootWitnesses.mp hk
  obtain ⟨hkR, hkW⟩ := Finset.mem_Ioc.mp hk'.1
  have hquot : k / k.minFac ≤ R := hk'.2
  have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le R) hkR
  have hkne : k ≠ 1 := by omega
  have hminPrime : (Nat.minFac k).Prime := Nat.minFac_prime hkne
  have hface : primeFaceProduct (∅ : Finset ℕ) = 1 := by
    simp [primeFaceProduct]
  have hpivot :
      lowWheelCanonicalCofactorQuotientPivot ((1 : ℕ), k) = Nat.minFac k := by
    simp [lowWheelCanonicalCofactorQuotientPivot]
  refine mem_lowWheelCanonicalDowncrossPart.mpr ⟨?_, ?_, ?_⟩
  · refine mem_lowWheelCanonicalPhysicalStateSet.mpr ⟨?_, ?_, ?_, ?_⟩
    · refine Finset.mem_Ico.mpr ⟨le_refl 1, ?_⟩
      show (1 : ℕ) < R
      omega
    · exact Finset.mem_Icc.mpr ⟨hkpos, hkW⟩
    · exact squarefree_one
    · refine ⟨le_refl 1, ?_, ?_, ?_⟩
      · show (1 : ℕ) < R
        omega
      · show R < primeFaceProduct (∅ : Finset ℕ) * k
        simpa [hface] using hkR
      · show 1 * primeFaceProduct (∅ : Finset ℕ) * k ≤ squareRootEndpoint R
        simpa [hface] using hkW
  · rw [hpivot]
    intro hdvd
    have hdvd1 : Nat.minFac k ∣ 1 := hdvd
    exact hminPrime.ne_one (Nat.dvd_one.mp hdvd1)
  · show primeFaceProduct (∅ : Finset ℕ) *
      (k / lowWheelCanonicalCofactorQuotientPivot ((1 : ℕ), k)) ≤ R
    simpa [hpivot, hface] using hquot

/-- The empty face alone already carries every root witness. -/
theorem card_lowWheelCanonicalDowncrossRootWitnesses_le
    {R : ℕ} (hR : 2 ≤ R) :
    (lowWheelCanonicalDowncrossRootWitnesses R).card ≤
      (lowWheelCanonicalDowncrossPart R (∅ : Finset ℕ)).card := by
  refine Finset.card_le_card_of_injOn (fun k => ((1 : ℕ), k)) ?_ ?_
  · intro k hk
    exact lowWheelCanonicalDowncrossRootWitness_mem_emptyFace hR hk
  · intro a _ha b _hb hab
    simpa using hab

/-- Every prime of the reciprocal band is a root witness: its least prime factor
is itself, so its parent is `1`. -/
theorem primes_subset_lowWheelCanonicalDowncrossRootWitnesses
    {R : ℕ} (hR : 1 ≤ R) :
    (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime ⊆
      lowWheelCanonicalDowncrossRootWitnesses R := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  refine mem_lowWheelCanonicalDowncrossRootWitnesses.mpr ⟨hq'.1, ?_⟩
  rw [hq'.2.minFac_eq, Nat.div_self hq'.2.pos]
  exact hR

/-- **Barrier for the unsigned route.**  The unsigned mass of the canonical
downcross ledger is at least `pi(R^2-1) - pi(R)`.  Since that count is
superlinear in `R`, no argument that discards the Möbius weights and the face
signs can produce the linear seam `||D_R|| <= C * R`: the remaining saving has to
come from cancellation across the ownership windows, not from bounding them
termwise. -/
theorem card_primes_le_lowWheelCanonicalDowncrossUnsignedMass
    {R : ℕ} (hR : 2 ≤ R) :
    ((Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime).card ≤
      lowWheelCanonicalDowncrossUnsignedMass R := by
  have h1 : ((Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime).card ≤
      (lowWheelCanonicalDowncrossRootWitnesses R).card :=
    Finset.card_le_card
      (primes_subset_lowWheelCanonicalDowncrossRootWitnesses (by omega))
  have h2 := card_lowWheelCanonicalDowncrossRootWitnesses_le hR
  have h3 : (lowWheelCanonicalDowncrossPart R (∅ : Finset ℕ)).card ≤
      lowWheelCanonicalDowncrossUnsignedMass R := by
    unfold lowWheelCanonicalDowncrossUnsignedMass
    exact Finset.single_le_sum
      (f := fun t => (lowWheelCanonicalDowncrossPart R t).card)
      (fun t _ht => Nat.zero_le _) (Finset.empty_mem_powerset _)
  exact le_trans (le_trans h1 h2) h3

end RHLean.Proof
