import Mathlib
import RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam
import RHLean.Proof.LowWheelCanonicalRepeatedMovableCancellation
import RHLean.Proof.LowWheelCanonicalDowncrossBoundaryMultiplicity
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity

/-!
# The oriented seam at RH scale

After `LateParentCancellation.lateParentLedger_eq_zero`, the canonical downcross
ledger *is* the oriented ledger:

`D_R = O_R`.

`SquareRootCanonicalOrientedLinearBound` asks for `‖O_R‖ ≤ C * R`.  That is
strictly stronger than the Riemann hypothesis needs, and the repository already
compiles the reason: `norm_squarePrefixMertens_le_of_canonicalDowncrossLinear`
turns it into `|M(R^2-1)| ≤ (C+1) * R`, and since consecutive square endpoints
differ by `2R` that extends to `M(x) = O(sqrt x)` for all `x` — the strong
Mertens bound, which is open and widely believed false.

The energy bridge only ever consumes `SquarePrefixEnergyBoundedStatement`,

`∀ ε > 0, ∃ C, ∀ n, ‖squarePrefixMertens n‖^2 ≤ C * (n+1)^(2+ε)`,

i.e. `M(x) ≪ x^(1/2+ε)`, which is equivalent to RH.  So the correct seam is the
`1 + ε` bound below, and the base `(n+1)` of the energy statement is exactly the
root `R`, so no off-square interpolation is duplicated here: that loss is paid
once, inside `mertensEnergyBounded_of_squarePrefixEnergyBounded`.

The first section below strengthens the ownership geometry without estimating
it: the Boolean faces charging one fixed physical state are reindexed exactly
by the squarefree integers in a single state-dependent interval.  Their signed
mass is therefore the literal Möbius mass of that interval.  This is the
correct dependence-aware replacement for treating the limiting `30/40/30`
Möbius frequencies as independent local probabilities.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

namespace SignedOwnershipInterval

/-- The exact upper endpoint of the face-product ownership interval for one
fixed physical state.  The first term is the root-side parent constraint; the
second is the physical square-endpoint product ceiling. -/
def lowWheelCanonicalDowncrossOwnershipUpper
    (R c k : ℕ) : ℕ :=
  min
    (R / (k / lowWheelCanonicalCofactorQuotientPivot (c, k)))
    (squareRootEndpoint R / (c * k))

/-- Squarefree integer products in the exact ownership interval of `(c,k)`. -/
def lowWheelCanonicalDowncrossOwnershipProducts
    (R c k : ℕ) : Finset ℕ :=
  (Finset.Ioc (R / k)
      (lowWheelCanonicalDowncrossOwnershipUpper R c k)).filter Squarefree

@[simp] theorem mem_lowWheelCanonicalDowncrossOwnershipProducts
    {R c k a : ℕ} :
    a ∈ lowWheelCanonicalDowncrossOwnershipProducts R c k ↔
      R / k < a ∧
        a ≤ lowWheelCanonicalDowncrossOwnershipUpper R c k ∧
        Squarefree a := by
  simp [lowWheelCanonicalDowncrossOwnershipProducts, and_assoc]

/-- Every charging face also satisfies the physical product ceiling, so its
product lies in the exact state-dependent ownership interval. -/
theorem primeFaceProduct_mem_exactOwnershipInterval
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k)) :
    primeFaceProduct t ∈
      Finset.Ioc (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) := by
  have hwindow := primeFaceProduct_mem_Ioc_of_mem_chargingFaces ht
  obtain ⟨_htPow, hx⟩ := mem_lowWheelCanonicalDowncrossChargingFaces.mp ht
  have hmem := mem_lowWheelCanonicalDowncrossPart.mp hx
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp hmem.1
  obtain ⟨_hcRange, hkRange, _hsq, hcarrier⟩ := hphys
  obtain ⟨hc1, _hcR, _hhigh, htop⟩ := hcarrier
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkRange).1
  have hcpos : 0 < c := by omega
  have hckpos : 0 < c * k := Nat.mul_pos hcpos hkpos
  have htop' : primeFaceProduct t * (c * k) ≤ squareRootEndpoint R := by
    calc
      primeFaceProduct t * (c * k) =
          (c * primeFaceProduct t) * k := by ring
      _ ≤ squareRootEndpoint R := htop
  have htopDiv :
      primeFaceProduct t ≤ squareRootEndpoint R / (c * k) :=
    (Nat.le_div_iff_mul_le hckpos).mpr htop'
  refine Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hwindow).1, ?_⟩
  exact le_min (Finset.mem_Ioc.mp hwindow).2 htopDiv

/-- A charging-face product is squarefree.  This is read through its nonzero
Möbius value, whose sign is the Boolean face sign. -/
theorem squarefree_primeFaceProduct_of_mem_chargingFaces
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k)) :
    Squarefree (primeFaceProduct t) := by
  obtain ⟨htPow, _hx⟩ := mem_lowWheelCanonicalDowncrossChargingFaces.mp ht
  have htSub := Finset.mem_powerset.mp htPow
  have hmu := moebius_primeFaceProduct_eq_booleanCubeSign t
    (fun q hq => prime_of_mem_primesUpTo (htSub hq))
  apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
  rw [hmu]
  simp [booleanCubeSign]

/-- **Exact ownership image.**  If `(c,k)` is charged at least once, the image
of all of its charging Boolean faces under `primeFaceProduct` is exactly the
squarefree population in its physical ownership interval. -/
theorem image_primeFaceProduct_chargingFaces_eq_ownershipProducts
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossChargingFaces R (c, k)).Nonempty) :
    (lowWheelCanonicalDowncrossChargingFaces R (c, k)).image primeFaceProduct =
      lowWheelCanonicalDowncrossOwnershipProducts R c k := by
  classical
  obtain ⟨t0, ht0⟩ := hne
  obtain ⟨_ht0Pow, hx0⟩ := mem_lowWheelCanonicalDowncrossChargingFaces.mp ht0
  have hdown0 := mem_lowWheelCanonicalDowncrossPart.mp hx0
  have hphys0 := mem_lowWheelCanonicalPhysicalStateSet.mp hdown0.1
  obtain ⟨hcRange, hkRange, hsqc, hcarrier0⟩ := hphys0
  obtain ⟨hc1, hcR, _hhigh0, _htop0⟩ := hcarrier0
  obtain ⟨hp, hpc, hpk, _hparent0, _hchild0⟩ :=
    lowWheelCanonicalDowncrossPart_adjacent_shell hx0
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkRange).1
  have hcpos : 0 < c := by omega
  have hjpos :
      0 < k / lowWheelCanonicalCofactorQuotientPivot (c, k) :=
    Nat.div_pos (Nat.le_of_dvd hkpos hpk) hp.pos
  have hckpos : 0 < c * k := Nat.mul_pos hcpos hkpos
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨t, ht, rfl⟩
    apply mem_lowWheelCanonicalDowncrossOwnershipProducts.mpr
    have hI := primeFaceProduct_mem_exactOwnershipInterval ht
    exact ⟨(Finset.mem_Ioc.mp hI).1, (Finset.mem_Ioc.mp hI).2,
      squarefree_primeFaceProduct_of_mem_chargingFaces ht⟩
  · intro ha
    obtain ⟨hlo, hupper, hsqa⟩ :=
      mem_lowWheelCanonicalDowncrossOwnershipProducts.mp ha
    have hparent :
        a ≤ R / (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) :=
      hupper.trans (min_le_left _ _)
    have htopDiv : a ≤ squareRootEndpoint R / (c * k) :=
      hupper.trans (min_le_right _ _)
    have haR : a ≤ R :=
      hparent.trans (Nat.div_le_self _ _)
    let t : Finset ℕ := squarefreePrimeFace a
    have htSub : t ⊆ primesUpTo R := by
      simpa [t] using squarefreePrimeFace_subset_primesUpTo hsqa haR
    have htPow : t ∈ (primesUpTo R).powerset :=
      Finset.mem_powerset.mpr htSub
    have hprod : primeFaceProduct t = a := by
      simpa [t] using primeFaceProduct_squarefreePrimeFace hsqa
    have hhigh : R < a * k :=
      (Nat.div_lt_iff_lt_mul hkpos).mp hlo
    have htopMul : a * (c * k) ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hckpos).mp htopDiv
    have htop : (c * a) * k ≤ squareRootEndpoint R := by
      calc
        (c * a) * k = a * (c * k) := by ring
        _ ≤ squareRootEndpoint R := htopMul
    have hparentMul :
        a * (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) ≤ R :=
      (Nat.le_div_iff_mul_le hjpos).mp hparent
    have hphysical : (c, k) ∈ lowWheelCanonicalPhysicalStateSet R t := by
      apply mem_lowWheelCanonicalPhysicalStateSet.mpr
      refine ⟨hcRange, hkRange, hsqc, ?_⟩
      unfold LowWheelTransportPairCarrier
      rw [hprod]
      exact ⟨hc1, hcR, hhigh, htop⟩
    have hx : (c, k) ∈ lowWheelCanonicalDowncrossPart R t := by
      apply mem_lowWheelCanonicalDowncrossPart.mpr
      refine ⟨hphysical, hpc, ?_⟩
      rw [hprod]
      exact hparentMul
    apply Finset.mem_image.mpr
    exact ⟨t,
      mem_lowWheelCanonicalDowncrossChargingFaces.mpr ⟨htPow, hx⟩,
      hprod⟩

/-- **Signed ownership interval.**  The Boolean alternating mass of all faces
charging one fixed physical state is exactly the Möbius mass of its integer
ownership interval.  Nonsquarefree integers may be inserted freely because
their Möbius weight is zero. -/
theorem sum_booleanCubeSign_chargingFaces_eq_moebiusOwnershipInterval
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossChargingFaces R (c, k)).Nonempty) :
    (∑ t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k),
        booleanCubeSign t) =
      ∑ a ∈ Finset.Ioc (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k), μ a := by
  classical
  let F := lowWheelCanonicalDowncrossChargingFaces R (c, k)
  let I := Finset.Ioc (R / k)
    (lowWheelCanonicalDowncrossOwnershipUpper R c k)
  have hface :
      (∑ t ∈ F, booleanCubeSign t) =
        ∑ t ∈ F, μ (primeFaceProduct t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have htData := mem_lowWheelCanonicalDowncrossChargingFaces.mp
      (by simpa [F] using ht)
    have htSub := Finset.mem_powerset.mp htData.1
    symm
    exact moebius_primeFaceProduct_eq_booleanCubeSign t
      (fun q hq => prime_of_mem_primesUpTo (htSub hq))
  have himage : F.image primeFaceProduct =
      lowWheelCanonicalDowncrossOwnershipProducts R c k := by
    simpa [F] using
      image_primeFaceProduct_chargingFaces_eq_ownershipProducts hne
  have hinj :
      ∀ a ∈ F, ∀ b ∈ F, primeFaceProduct a = primeFaceProduct b → a = b := by
    intro a ha b hb hab
    exact primeFaceProduct_injOn_chargingFaces R (c, k)
      (by simpa [F] using ha) (by simpa [F] using hb) hab
  calc
    (∑ t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k),
        booleanCubeSign t) = ∑ t ∈ F, booleanCubeSign t := by rfl
    _ = ∑ t ∈ F, μ (primeFaceProduct t) := hface
    _ = ∑ a ∈ F.image primeFaceProduct, μ a := by
      symm
      rw [Finset.sum_image]
      exact hinj
    _ = ∑ a ∈ lowWheelCanonicalDowncrossOwnershipProducts R c k, μ a := by
      rw [himage]
    _ = ∑ a ∈ I, μ a := by
      unfold lowWheelCanonicalDowncrossOwnershipProducts
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hsq : Squarefree a
      · simp [hsq]
      · simp [hsq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    _ = ∑ a ∈ Finset.Ioc (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k), μ a := by rfl

end SignedOwnershipInterval

namespace OrientedEpsilonBound

/-- **The final quantitative seam, at RH scale.**  For every `ε > 0` the
canonical oriented first-crossing ledger is `O(R^(1+ε))`. -/
def SquareRootCanonicalOrientedEpsilonBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 3 ≤ R →
        ‖LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger R‖ ≤
          C * Real.rpow (R : ℝ) (1 + ε)

private theorem one_le_cast_succ (n : ℕ) : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
  have h : (1 : ℕ) ≤ n + 1 := by omega
  exact_mod_cast h

private theorem cast_succ_pos (n : ℕ) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
  have h : (0 : ℕ) < n + 1 := by omega
  exact_mod_cast h

/-- `x ≤ x ^ (1 + δ)` for a base at least one. -/
private theorem cast_le_rpow_one_add
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (1 + δ) := by
  have h := Real.rpow_le_rpow_of_exponent_le (one_le_cast_succ n)
    (by linarith : (1 : ℝ) ≤ 1 + δ)
  simpa using h

/-- `1 ≤ x ^ (2 + ε)` for a base at least one. -/
private theorem one_le_rpow_two_add
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (1 : ℝ) ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by
  have h := Real.rpow_le_rpow_of_exponent_le (one_le_cast_succ n)
    (by linarith : (0 : ℝ) ≤ 2 + ε)
  simpa using h

/-- **The oriented `1 + ε` seam gives the square-prefix energy criterion.**

Instantiating the oriented hypothesis at `ε / 2` is what makes the exponents
line up: the square of an `R^(1+ε/2)` bound is exactly `R^(2+ε)`, and the base
of the energy statement is literally `R = n + 1`. -/
theorem squarePrefixEnergyBounded_of_canonicalOrientedEpsilon
    (horiented : SquareRootCanonicalOrientedEpsilonBound) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hO⟩ := horiented (ε / 2) (by linarith)
  refine ⟨(1 + C) ^ 2 + 9, by positivity, ?_⟩
  intro n
  have hbaseNonneg : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrpowNonneg : (0 : ℝ) ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) :=
    Real.rpow_nonneg hbaseNonneg _
  by_cases hn : 2 ≤ n
  · have hR : 3 ≤ n + 1 := by omega
    have hsplit := squarePrefixMertens_eq_mertens_sub_canonicalDowncross (n + 1) hR
    have hn1 : n + 1 - 1 = n := by omega
    rw [hn1, LateParentCancellation.downcrossLedger_eq_orientedLedger] at hsplit
    have hM : ‖mertensSummatory (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) := by
      simpa using norm_mertensSummatory_sub_le 0 (n + 1) (Nat.zero_le _)
    have hRle := cast_le_rpow_one_add (δ := ε / 2) (by linarith) n
    have hA :
        ‖squarePrefixMertens n‖ ≤
          (1 + C) * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) := by
      rw [hsplit]
      calc
        ‖mertensSummatory (n + 1) -
            LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger
              (n + 1)‖ ≤
            ‖mertensSummatory (n + 1)‖ +
              ‖LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger
                (n + 1)‖ := norm_sub_le _ _
        _ ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) +
              C * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) :=
            add_le_add (hM.trans hRle) (hO (n + 1) hR)
        _ = (1 + C) * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) := by ring
    have hprod :
        Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) =
          Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) *
            Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) := by
      have h := Real.rpow_add (cast_succ_pos n) (1 + ε / 2) (1 + ε / 2)
      have hexp : (1 + ε / 2) + (1 + ε / 2) = 2 + ε := by ring
      rw [hexp] at h
      exact h
    have hAnn : (0 : ℝ) ≤ ‖squarePrefixMertens n‖ := norm_nonneg _
    have hsq :
        ‖squarePrefixMertens n‖ ^ 2 ≤
          ((1 + C) * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2)) ^ 2 := by
      nlinarith [hAnn, hA]
    calc
      ‖squarePrefixMertens n‖ ^ 2 ≤
          ((1 + C) * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2)) ^ 2 := hsq
      _ = (1 + C) ^ 2 *
            (Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) *
              Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2)) := by ring
      _ = (1 + C) ^ 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by rw [hprod]
      _ ≤ ((1 + C) ^ 2 + 9) * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by
          nlinarith [hrpowNonneg]
  · have hnle : n ≤ 1 := by omega
    have hEnd : squarePrefixEndpoint n ≤ 3 := by
      interval_cases n <;> simp [squarePrefixEndpoint]
    have hb : ‖squarePrefixMertens n‖ ≤ ((squarePrefixEndpoint n : ℕ) : ℝ) := by
      simpa [squarePrefixMertens] using
        norm_mertensSummatory_sub_le 0 (squarePrefixEndpoint n) (Nat.zero_le _)
    have hb3 : ‖squarePrefixMertens n‖ ≤ 3 := by
      have hcast : ((squarePrefixEndpoint n : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hEnd
      exact hb.trans hcast
    have hAnn : (0 : ℝ) ≤ ‖squarePrefixMertens n‖ := norm_nonneg _
    have hsq : ‖squarePrefixMertens n‖ ^ 2 ≤ 9 := by nlinarith [hAnn, hb3]
    have hone := one_le_rpow_two_add hε n
    nlinarith [hsq, hone, sq_nonneg (1 + C)]

/-- **RH from the oriented `1 + ε` seam**, through the already-compiled bridge.
The off-square interpolation is paid exactly once, inside
`mertensEnergyBounded_of_squarePrefixEnergyBounded`. -/
theorem riemannHypothesis_of_canonicalOrientedEpsilon
    (horiented : SquareRootCanonicalOrientedEpsilonBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_squarePrefixEnergyBounded
      (squarePrefixEnergyBounded_of_canonicalOrientedEpsilon horiented))

/-- The old linear seam is a *stronger* sufficient criterion, not the canonical
target: it implies this one for every `ε`. -/
theorem orientedEpsilonBound_of_orientedLinearBound
    (hlinear : LateParentCancellation.SquareRootCanonicalOrientedLinearBound) :
    SquareRootCanonicalOrientedEpsilonBound := by
  obtain ⟨C, hC, hO⟩ := hlinear
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, R = n + 1 := ⟨R - 1, by omega⟩
  exact (hO (n + 1) hR).trans
    (mul_le_mul_of_nonneg_left (cast_le_rpow_one_add (δ := ε) (le_of_lt hε) n) hC)

end OrientedEpsilonBound

end RHLean.Proof