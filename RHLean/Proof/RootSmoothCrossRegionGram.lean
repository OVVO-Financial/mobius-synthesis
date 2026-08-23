import Mathlib
import RHLean.Proof.RecursivePrimeReplacement
import RHLean.Proof.SquareRootAncestryParentFibres
import RHLean.Proof.SquareRootCrossRegionAmplification
import RHLean.Proof.SquareRootLegalAncestryGramReduction
import RHLean.Analysis.MertensEnergyRHForward

/-!
# Root-smooth cross-region Gram

The centered distinguished-prime coefficient Gram is not used in this module.
The analytic object is the already-formalized square-root ancestry root together
with the complete smooth ancestry mass, kept signed until after recombination.

At the complete-square endpoint `X_R = R^2 - 1`, the existing ancestry theorems
identify the real root-smooth state with

`M(X_R) - 1`.

The corresponding energy is therefore exactly the squared norm of the shifted
square-prefix Mertens state.  No root norm and no smooth norm is estimated
separately.

The module also records the existing orientation decomposition

`M(X_R) = positiveSmooth(R) + matched(R)`

where `matched(R) = bornSmooth(R) - transport(R)`.  This identity is important
for notation: the born-smooth/high-transport matched channel is a signed
cross-region subchannel, but it is not by itself the full terminal square-prefix
state unless the positive-smooth term is also accounted for.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Exact terminal reconstruction of the signed ancestry root and complete
smooth mass before any norm is taken. -/
theorem rootSmoothCrossRegionState_eq_shiftedSquarePrefixMertens
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootPrimeRootReal R + squareRootSmoothMassReal R : ℝ) : ℂ) =
      RHLean.Analysis.squarePrefixMertens (R - 1) - 1 :=
  squareRootPrimeSmoothState_cast_eq_shiftedSquarePrefixMertens R hR

/-- The same terminal state in real arithmetic coordinates. -/
theorem rootSmoothCrossRegionStateReal_eq_shiftedSquarePrefixMertens_re
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeRootReal R + squareRootSmoothMassReal R =
      (RHLean.Analysis.squarePrefixMertens (R - 1)).re - 1 :=
  squareRootPrimeSmoothState_eq_shiftedSquarePrefixMertens_re R hR

/-- Exact unshifted square-prefix reconstruction in the born-smooth/high-
transport coordinates already present in the repository.  No estimate is made
on either summand. -/
theorem rootSmoothCrossRegion_squarePrefix_eq_positiveSmooth_add_matched
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.squarePrefixMertens (R - 1) =
      squareRootPositiveSmoothMass R +
        squareRootMatchedBornSmoothTransport R := by
  exact squarePrefixMertens_eq_positiveSmooth_add_matched R (by omega)

/-- Shifted form of the same exact reconstruction.  This makes explicit that
`bornSmooth - transport` is the matched signed subchannel, while the complete
root-smooth terminal state also contains the positive-smooth contribution. -/
theorem rootSmoothCrossRegionState_eq_positiveSmooth_add_matchedShift
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootPrimeRootReal R + squareRootSmoothMassReal R : ℝ) : ℂ) =
      squareRootPositiveSmoothMass R +
        (squareRootMatchedBornSmoothTransport R - 1) := by
  rw [rootSmoothCrossRegionState_eq_shiftedSquarePrefixMertens R hR]
  rw [rootSmoothCrossRegion_squarePrefix_eq_positiveSmooth_add_matched R hR]
  ring

/-- Exact root-smooth Gram reconstruction.  The full signed interaction is
retained before the norm; this is precisely `D_R + 2 O_R` from the ancestry
root and complete smooth channels. -/
theorem rootSmoothCrossRegionGram_eq_shiftedSquarePrefixEnergy
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeSmoothCrossRegionGram R =
      ‖RHLean.Analysis.squarePrefixMertens (R - 1) - 1‖ ^ 2 :=
  squareRootPrimeSmoothCrossRegionGram_eq_shiftedSquarePrefixMertens_norm_sq R hR

/-- The open RH-scale bound on the complete signed root-smooth cross-region
Gram.  This is a proposition only; no analytic estimate is asserted here. -/
def RootSmoothCrossRegionEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        squareRootPrimeSmoothCrossRegionGram R ≤
          C * Real.rpow (R : ℝ) (2 + ε)

private theorem norm_sq_le_two_shifted_add_two (z : ℂ) :
    ‖z‖ ^ 2 ≤ 2 * ‖z - 1‖ ^ 2 + 2 := by
  have hnorm : ‖z‖ ≤ ‖z - 1‖ + 1 := by
    have h := norm_add_le (z - 1) (1 : ℂ)
    simpa only [sub_add_cancel, norm_one] using h
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  have hshift : 0 ≤ ‖z - 1‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖z - 1‖ - 1)]

/-- The complete signed root-smooth RH-scale bound implies the repository's
square-prefix Mertens energy criterion.  The only auxiliary inequality removes
the harmless exceptional-source shift `-1`; it never separates root from
smooth. -/
theorem squarePrefixEnergyBounded_of_rootSmoothCrossRegionEnergyBound
    (hroot : RootSmoothCrossRegionEnergyBound) :
    RHLean.Analysis.SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases hroot ε hε with ⟨C, hC, hbound⟩
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    have hconst : 0 ≤ 2 * C + 2 := by positivity
    simpa [RHLean.Analysis.squarePrefixMertens,
      RHLean.Analysis.squarePrefixEndpoint] using hconst
  · have hR : 2 ≤ n + 1 := by omega
    have hshift := hbound (n + 1) hR
    rw [rootSmoothCrossRegionGram_eq_shiftedSquarePrefixEnergy (n + 1) hR] at hshift
    simp only [Nat.add_sub_cancel] at hshift
    have hsum := norm_sq_le_two_shifted_add_two
      (RHLean.Analysis.squarePrefixMertens n)
    have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    have hpow :
        1 ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) :=
      Real.one_le_rpow hbase (by linarith)
    nlinarith

/-- The root-smooth bound therefore implies the ordinary full Mertens energy
criterion by the already-proved square-sampling interpolation. -/
theorem mertensEnergyBounded_of_rootSmoothCrossRegionEnergyBound
    (hroot : RootSmoothCrossRegionEnergyBound) :
    RHLean.Analysis.MertensEnergyBoundedStatement :=
  RHLean.Analysis.mertensEnergyBounded_of_squarePrefixEnergyBounded
    (squarePrefixEnergyBounded_of_rootSmoothCrossRegionEnergyBound hroot)

/-- Exact terminal implication: once the complete signed root-smooth bound is
proved, the repository's constructed Mertens-to-RH forward theorem closes the
Riemann Hypothesis. -/
theorem rootSmoothCrossRegionEnergyBound_imp_riemannHypothesis
    (hroot : RootSmoothCrossRegionEnergyBound) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  change RiemannHypothesis
  exact RHLean.Analysis.riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_rootSmoothCrossRegionEnergyBound hroot)

/-! ## Exact global anti-alignment target -/

/-- The exact global signed anti-alignment target.  The complete root and smooth
channels are assembled before the inequality.  This proposition is open. -/
def RootSmoothGlobalSignedAntiAlignmentStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        2 * squareRootPrimeSmoothOffDiagonalGram R ≤
          -squareRootPrimeSmoothDiagonalGram R +
            C * Real.rpow (R : ℝ) (2 + ε)

/-- A fixed-delta anti-alignment estimate at one scale.  This is deliberately
not declared sufficient for the terminal criterion: it leaves `delta * D_R`. -/
def RootSmoothFixedDeltaAntiAlignmentAt
    (δ E : ℝ) (R : ℕ) : Prop :=
  2 * squareRootPrimeSmoothOffDiagonalGram R ≤
    -(1 - δ) * squareRootPrimeSmoothDiagonalGram R + E

/-- Exact bookkeeping for a fixed-delta estimate.  The unabsorbed term is the
joint diagonal `delta * D_R`; no root or smooth energy has been separated. -/
theorem rootSmoothCrossRegionEnergy_le_deltaDiagonal_add_error
    {δ E : ℝ} {R : ℕ}
    (h : RootSmoothFixedDeltaAntiAlignmentAt δ E R) :
    squareRootPrimeSmoothCrossRegionGram R ≤
      δ * squareRootPrimeSmoothDiagonalGram R + E := by
  unfold RootSmoothFixedDeltaAntiAlignmentAt at h
  unfold squareRootPrimeSmoothCrossRegionGram
  nlinarith

/-- The complete source parent-fibre ledger is the negative root-smooth cross
term.  The sign comes from the ancestry successor being the negative of the
complete smooth mass. -/
theorem squareRootPrimeSmoothOffDiagonalGram_eq_neg_sourceLedger
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeSmoothOffDiagonalGram R =
      -(((squareRootRootSuccessorCrossLedger
          (squareRootEndpoint R) R : ℤ) : ℝ)) := by
  let B := squareRootEndpoint R
  have hB : squareRootEndpoint R ≤ B := by simp [B]
  have hledger :
      (((squareRootRootSuccessorCrossLedger B R : ℤ) : ℝ)) =
        squareRootLegalRootReal B R * squareRootLegalSuccessorReal B R := by
    rw [squareRootRootSuccessorCrossLedger_eq_mul]
    unfold squareRootLegalRootReal squareRootLegalSuccessorReal
    push_cast
    rfl
  rw [squareRootLegalRootReal_eq_primeMass hR hB,
    squareRootLegalSuccessorReal_eq_neg_smoothMass hR hB] at hledger
  unfold squareRootPrimeSmoothOffDiagonalGram
    squareRootPrimeRootReal squareRootSmoothMassReal
  dsimp [B] at hledger
  nlinarith

/-- The same global target on the already-formalized complete root-by-parent-
fibre ledger.  It asks the entire signed ledger to absorb the joint diagonal;
no individual ledger entry is estimated. -/
def RootSmoothSourceLedgerCoercivityStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        squareRootPrimeSmoothDiagonalGram R ≤
          2 * (((squareRootRootSuccessorCrossLedger
            (squareRootEndpoint R) R : ℤ) : ℝ)) +
          C * Real.rpow (R : ℝ) (2 + ε)

/-- Parent-fibre ledger coercivity is exactly the global signed anti-alignment
statement.  This is only a sign rewrite of the complete global ledger. -/
theorem rootSmoothSourceLedgerCoercivity_iff_globalSignedAntiAlignment :
    RootSmoothSourceLedgerCoercivityStatement ↔
      RootSmoothGlobalSignedAntiAlignmentStatement := by
  constructor
  · intro hledger ε hε
    rcases hledger ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    have h := hbound R hR
    have hcross := squareRootPrimeSmoothOffDiagonalGram_eq_neg_sourceLedger R hR
    nlinarith
  · intro hanti ε hε
    rcases hanti ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    have h := hbound R hR
    have hcross := squareRootPrimeSmoothOffDiagonalGram_eq_neg_sourceLedger R hR
    nlinarith

/-- The sharp global signed anti-alignment theorem is algebraically equivalent
to the complete root-smooth RH-scale energy bound. -/
theorem rootSmoothGlobalSignedAntiAlignment_iff_crossRegionEnergyBound :
    RootSmoothGlobalSignedAntiAlignmentStatement ↔
      RootSmoothCrossRegionEnergyBound := by
  constructor
  · intro hanti ε hε
    rcases hanti ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    have h := hbound R hR
    unfold squareRootPrimeSmoothCrossRegionGram
    linarith
  · intro henergy ε hε
    rcases henergy ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    have h := hbound R hR
    unfold squareRootPrimeSmoothCrossRegionGram at h
    linarith

/-- Consequently complete parent-fibre ledger coercivity is itself exactly the
terminal root-smooth energy target. -/
theorem rootSmoothSourceLedgerCoercivity_iff_crossRegionEnergyBound :
    RootSmoothSourceLedgerCoercivityStatement ↔
      RootSmoothCrossRegionEnergyBound := by
  rw [rootSmoothSourceLedgerCoercivity_iff_globalSignedAntiAlignment,
    rootSmoothGlobalSignedAntiAlignment_iff_crossRegionEnergyBound]

/-- Any proof of the sharp global anti-alignment target closes the existing
terminal chain to the Riemann Hypothesis. -/
theorem rootSmoothGlobalSignedAntiAlignment_imp_riemannHypothesis
    (hanti : RootSmoothGlobalSignedAntiAlignmentStatement) :
    RHLean.Analysis.RiemannHypothesisStatement :=
  rootSmoothCrossRegionEnergyBound_imp_riemannHypothesis
    (rootSmoothGlobalSignedAntiAlignment_iff_crossRegionEnergyBound.mp hanti)

/-! ## Complementary Type-II fibre state -/

/-- Left endpoint of the complementary reciprocal fibre, inclusive. -/
def squareRootReplacementFibreLower (R z : ℕ) : ℕ :=
  squareRootEndpoint R / (z + 1) + 1

/-- Right endpoint of the complementary reciprocal fibre, inclusive. -/
def squareRootReplacementFibreUpper (R z : ℕ) : ℕ :=
  squareRootEndpoint R / z

/-- The quotient kernel has no mass above its diagonal. -/
theorem squareRootReplacementQuotientKernel_eq_zero_of_lt
    {z y : ℕ} (hzy : z < y) :
    squareRootReplacementQuotientKernel z y = 0 := by
  unfold squareRootReplacementQuotientKernel
  apply Finset.sum_eq_zero
  intro k _hk
  have hle : z / k ≤ z := Nat.div_le_self z k
  have hne : z / k ≠ y := by omega
  simp [hne]

/-- The diagonal coefficient of the quotient kernel is exactly one. -/
theorem squareRootReplacementQuotientKernel_self
    {z : ℕ} (hz : 1 ≤ z) :
    squareRootReplacementQuotientKernel z z = 1 := by
  classical
  unfold squareRootReplacementQuotientKernel
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 z := by simp [hz]
  calc
    (∑ k ∈ Finset.Icc 1 z, if z / k = z then (1 : ℂ) else 0) =
      ∑ k ∈ Finset.Icc 1 z, if k = 1 then (1 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hk1 : k = 1
        · subst k
          simp
        · have hkI := Finset.mem_Icc.mp hk
          have hk2 : 1 < k := by omega
          have hzpos : 0 < z := by omega
          have hlt : z / k < z := Nat.div_lt_self hzpos hk2
          have hne : z / k ≠ z := by omega
          simp [hk1, hne]
    _ = 1 := by simp [h1mem]

private theorem nat_div_eq_iff_reciprocal_interval
    {X n z : ℕ} (hn : 1 ≤ n) (hz : 1 ≤ z) :
    X / n = z ↔ X / (z + 1) < n ∧ n ≤ X / z := by
  have hnpos : 0 < n := by omega
  have hzpos : 0 < z := by omega
  have hzp : 0 < z + 1 := by omega
  constructor
  · intro hdiv
    have hlt : X / n < z + 1 := by omega
    have hxlt : X < (z + 1) * n :=
      (Nat.div_lt_iff_lt_mul hnpos).1 hlt
    have hlower : X / (z + 1) < n :=
      (Nat.div_lt_iff_lt_mul hzp).2 (by simpa [Nat.mul_comm] using hxlt)
    have hle : z ≤ X / n := by omega
    have hmul : z * n ≤ X :=
      (Nat.le_div_iff_mul_le hnpos).1 hle
    have hupper : n ≤ X / z :=
      (Nat.le_div_iff_mul_le hzpos).2 (by simpa [Nat.mul_comm] using hmul)
    exact ⟨hlower, hupper⟩
  · rintro ⟨hlower, hupper⟩
    have hmulUpper : n * z ≤ X :=
      (Nat.le_div_iff_mul_le hzpos).1 hupper
    have hzle : z ≤ X / n :=
      (Nat.le_div_iff_mul_le hnpos).2
        (by simpa [Nat.mul_comm] using hmulUpper)
    have hxlt : X < n * (z + 1) :=
      (Nat.div_lt_iff_lt_mul hzp).1 hlower
    have hlt : X / n < z + 1 :=
      (Nat.div_lt_iff_lt_mul hnpos).2
        (by simpa [Nat.mul_comm] using hxlt)
    omega

private theorem squareRoot_pred_mul_root_le_endpoint
    (R : ℕ) (hR : 2 ≤ R) :
    (R - 1) * R ≤ squareRootEndpoint R := by
  have hpred : R - 1 + 1 = R := by omega
  have hend : squareRootEndpoint R + 1 = R ^ 2 := by
    unfold squareRootEndpoint
    have hsq : 0 < R ^ 2 := by positivity
    omega
  nlinarith

/-- For every nonzero complementary quotient `z < R`, the reciprocal interval
already lies inside the physical tail `n >= R`; no extra clipping is needed. -/
theorem squareRoot_root_le_replacementFibreLower
    (R z : ℕ) (hR : 2 ≤ R) (hzR : z < R) :
    R ≤ squareRootReplacementFibreLower R z := by
  have hzr : z + 1 ≤ R := by omega
  have hmul : (R - 1) * (z + 1) ≤ (R - 1) * R :=
    Nat.mul_le_mul_left (R - 1) hzr
  have hbound : (R - 1) * (z + 1) ≤ squareRootEndpoint R :=
    hmul.trans (squareRoot_pred_mul_root_le_endpoint R hR)
  have hdiv : R - 1 ≤ squareRootEndpoint R / (z + 1) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < z + 1)).2 hbound
  unfold squareRootReplacementFibreLower
  omega

/-- The hyperbola interval attached to `1 <= z < R` is nonempty. -/
theorem squareRoot_replacementFibreLower_le_upper
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    squareRootReplacementFibreLower R z ≤
      squareRootReplacementFibreUpper R z := by
  let X := squareRootEndpoint R
  have hzr : z + 1 ≤ R := by omega
  have hzpred : z ≤ R - 1 := by omega
  have hprod1 : z * (z + 1) ≤ (R - 1) * R :=
    Nat.mul_le_mul hzpred hzr
  have hprod : z * (z + 1) ≤ X := by
    dsimp [X]
    exact hprod1.trans (squareRoot_pred_mul_root_le_endpoint R hR)
  have hzq : z ≤ X / (z + 1) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < z + 1)).2 hprod
  have hstep : (X / (z + 1) + 1) * z ≤
      (X / (z + 1)) * (z + 1) := by
    nlinarith
  have htoX : (X / (z + 1) + 1) * z ≤ X :=
    hstep.trans (Nat.div_mul_le_self X (z + 1))
  have hdiv : X / (z + 1) + 1 ≤ X / z :=
    (Nat.le_div_iff_mul_le (by omega : 0 < z)).2 htoX
  simpa [squareRootReplacementFibreLower,
    squareRootReplacementFibreUpper, X] using hdiv

/-- The physical reciprocal fibre is exactly its ordinary hyperbola interval. -/
theorem replacementTailFibre_mem_iff
    (R z n : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    (n ∈ Finset.Icc R (squareRootEndpoint R) ∧
        squareRootEndpoint R / n = z) ↔
      n ∈ Finset.Icc
        (squareRootReplacementFibreLower R z)
        (squareRootReplacementFibreUpper R z) := by
  have hroot := squareRoot_root_le_replacementFibreLower R z hR hzR
  constructor
  · rintro ⟨hnTail, hdiv⟩
    rcases Finset.mem_Icc.mp hnTail with ⟨hnR, _hnX⟩
    have hn1 : 1 ≤ n := by omega
    rcases (nat_div_eq_iff_reciprocal_interval hn1 hz).1 hdiv with
      ⟨hlower, hupper⟩
    apply Finset.mem_Icc.mpr
    constructor
    · unfold squareRootReplacementFibreLower
      omega
    · exact hupper
  · intro hnFiber
    rcases Finset.mem_Icc.mp hnFiber with ⟨hnLower, hnUpper⟩
    have hnR : R ≤ n := hroot.trans hnLower
    have hn1 : 1 ≤ n := by omega
    have hupperX :
        squareRootReplacementFibreUpper R z ≤ squareRootEndpoint R := by
      unfold squareRootReplacementFibreUpper
      exact Nat.div_le_self _ _
    have hnX : n ≤ squareRootEndpoint R := hnUpper.trans hupperX
    have hlower : squareRootEndpoint R / (z + 1) < n := by
      unfold squareRootReplacementFibreLower at hnLower
      omega
    have hdiv :=
      (nat_div_eq_iff_reciprocal_interval hn1 hz).2 ⟨hlower, hnUpper⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hnR, hnX⟩, hdiv⟩

/-- The complementary fibre state is exactly the Mertens increment on its
reciprocal hyperbola interval. -/
theorem squareRootReplacementTailMoebiusCoefficient_eq_mertensIncrement
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    squareRootReplacementTailMoebiusCoefficient R z =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R / z) -
        RHLean.Analysis.mertensSummatory (squareRootEndpoint R / (z + 1)) := by
  classical
  let L := squareRootReplacementFibreLower R z
  let H := squareRootReplacementFibreUpper R z
  have hLH : L ≤ H := by
    dsimp [L, H]
    exact squareRoot_replacementFibreLower_le_upper R z hR hz hzR
  have hset :
      (Finset.Icc R (squareRootEndpoint R)).filter
          (fun n => squareRootEndpoint R / n = z) =
        Finset.Icc L H := by
    ext n
    simp only [Finset.mem_filter]
    rw [replacementTailFibre_mem_iff R z n hR hz hzR]
  have hdisj : Disjoint (Finset.Icc 1 (L - 1)) (Finset.Icc L H) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo hnhi
    omega
  have hL1 : 1 ≤ L := by
    have hroot : R ≤ L := by
      simpa [L] using squareRoot_root_le_replacementFibreLower R z hR hzR
    omega
  have hprefix : Finset.Icc 1 H =
      Finset.Icc 1 (L - 1) ∪ Finset.Icc L H := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hM :
      RHLean.Analysis.mertensSummatory H =
        RHLean.Analysis.mertensSummatory (L - 1) +
          ∑ n ∈ Finset.Icc L H, (((μ n : ℤ) : ℂ)) := by
    calc
      RHLean.Analysis.mertensSummatory H =
          ∑ n ∈ Finset.Icc 1 H, (((μ n : ℤ) : ℂ)) :=
        RHLean.Analysis.mertensSummatory_eq_sum_Icc _
      _ = (∑ n ∈ Finset.Icc 1 (L - 1), (((μ n : ℤ) : ℂ))) +
          ∑ n ∈ Finset.Icc L H, (((μ n : ℤ) : ℂ)) := by
            rw [hprefix, Finset.sum_union hdisj]
      _ = RHLean.Analysis.mertensSummatory (L - 1) +
          ∑ n ∈ Finset.Icc L H, (((μ n : ℤ) : ℂ)) := by
            rw [← RHLean.Analysis.mertensSummatory_eq_sum_Icc (L - 1)]
  unfold squareRootReplacementTailMoebiusCoefficient
  rw [← Finset.sum_filter, hset]
  have hsum :
      (∑ n ∈ Finset.Icc L H, (((μ n : ℤ) : ℂ))) =
        RHLean.Analysis.mertensSummatory H -
          RHLean.Analysis.mertensSummatory (L - 1) := by
    rw [hM]
    ring
  rw [hsum]
  dsimp [L, H]
  simp [squareRootReplacementFibreLower,
    squareRootReplacementFibreUpper]

/-- Summing the fibre state recovers exactly the ordinary complementary Mertens
tail.  This is a partition identity and carries no additional analytic saving. -/
theorem squareRootReplacementTailMoebius_sum_eq_complementaryMertensTail
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z) =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        RHLean.Analysis.mertensSummatory (R - 1) :=
  sum_squareRootReplacementTailMoebiusCoefficient_eq_mertens_sub_pred R hR

/-- The composed dictionary-renewal endpoint reconstruction reduces to the
preceding complementary-tail partition.  The displayed endpoint equality is
therefore a consistency corollary, not a separate cancellation theorem. -/
theorem replacementDictionaryRenewal_reduces_to_tailPartition
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 =
      (RHLean.Analysis.mertensSummatory (R - 1) - 1) +
        ∑ z ∈ Finset.range R,
          squareRootReplacementTailMoebiusCoefficient R z := by
  rw [squareRootReplacementTailMoebius_sum_eq_complementaryMertensTail R hR]
  ring

end RHLean.Proof
