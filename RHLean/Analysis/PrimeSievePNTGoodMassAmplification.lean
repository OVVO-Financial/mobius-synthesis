import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixGoodMassRate
import RHLean.Analysis.PrimeSieveDyadicPacketReverseCarleson

/-!
# PNT good-mass amplification into the signed packet tree

The native Selberg--Erdos development already proves an unconditional positive
supply of good reciprocal fibres.  At fixed tolerance one has, eventually,

`const * log(N)^2 <= nativeLambdaTwoGoodRecipMass N 1`.

This module uses that theorem as an amplifier for the signed packet tree.  It
does not introduce a new discrepancy coordinate.

The first observation is that pure reverse Carleson is stronger than the RH
closure actually needs.  It is enough to control the descendant tail after one
released level by

`(x+1)^epsilon * (levelEnergy + (x+1))`.

The additive linear term is already at the critical packet-energy scale and is
therefore harmless after the usual epsilon split.

The genuinely new arithmetic target is then a bilinear good-mass charge.  At a
shifted PNT scale `N = x + B + 2`, require

`goodMass(N) * descendantEnergy`

`<= C * log(N)^2 * (x+1)^epsilon * (levelEnergy + (x+1))`.

The shift parameter lets the already-proved eventual PNT good-mass lower bound
be used globally: choose `B` to be its eventual threshold.  The logarithmic
square cancels exactly.  Thus the unconditional native PNT good-mass theorem
turns the bilinear charge into additive descendant persistence, which in turn
closes the existing packet-tree RH reduction.

This is deliberately a weak amplification target.  It only asks arithmetic to
charge descendant energy above an ambient linear floor, and it preserves the
signed prime-minus-Li packet energy throughout.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## A weaker additive persistence target -/

/-- **Additive descendant persistence.**  The tail remaining after level `J`
is released may have a full ambient linear defect.  This is strictly weaker
than the reverse-Carleson statement from the earlier development and the earlier development, but the additive term
is still critical-scale harmless. -/
def DyadicPacketAdditiveDescendantPersistenceStatement
    (cutoff : DyadicPacketCutoff) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicPacketDeepEnergy
            (primorialPNTPrimeSieveCutoff k) x (cutoff k x + 1) ≤
          C * Real.rpow ((x : ℝ) + 1) ε *
            (primeSieveDyadicPacketLevelEnergy
                (primorialPNTPrimeSieveCutoff k) x (cutoff k x) +
              ((x : ℝ) + 1))

/-- Additive persistence is already sufficient for the critical deep-tail
bound once the successor-shallow energy is controlled.  The proof uses half of
the epsilon budget for persistence and half for the shallow estimate. -/
theorem dyadicPacketDeepTailBlockBounded_of_additiveDescendantPersistence
    (cutoff : DyadicPacketCutoff)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hA : DyadicPacketAdditiveDescendantPersistenceStatement cutoff) :
    DyadicPacketDeepTailBlockBoundedStatement cutoff := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨CS, hCS, hSb⟩ := hS (ε / 2) hhalf
  obtain ⟨CA, hCA, hAb⟩ := hA (ε / 2) hhalf
  refine ⟨CS + CA * CS + CA,
    add_nonneg (add_nonneg hCS (mul_nonneg hCA hCS)) hCA, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let J := cutoff k x
  let B : ℝ := (x : ℝ) + 1
  let P : ℝ := Real.rpow B (ε / 2)
  let T : ℝ := Real.rpow B (1 + ε / 2)
  let U : ℝ := Real.rpow B (1 + ε)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact Real.rpow_nonneg hBpos.le _
  have hP1 : 1 ≤ P := by
    dsimp [P, B]
    have hbase : (1 : ℝ) ≤ (x : ℝ) + 1 := by
      have hx : (0 : ℝ) ≤ (x : ℝ) := by positivity
      linarith
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hhalf.le
    simpa using h
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact Real.rpow_nonneg hBpos.le _
  have hPT : P * T = U := by
    dsimp [P, T, U]
    rw [← Real.rpow_add hBpos]
    congr 1
    ring
  have hPB : P * B = T := by
    calc
      P * B = P * Real.rpow B 1 := by simp
      _ = Real.rpow B ((ε / 2) + 1) :=
        (Real.rpow_add hBpos (ε / 2) 1).symm
      _ = T := by
        dsimp [T]
        congr 1
        ring
  have hTU : T ≤ U := by
    calc
      T = 1 * T := by ring
      _ ≤ P * T := mul_le_mul_of_nonneg_right hP1 hT0
      _ = U := hPT
  have hs :
      primeSieveDyadicPacketShallowEnergy y x (J + 1) ≤ CS * T := by
    simpa [y, J, B, T, dyadicPacketSuccCutoff] using
      hSb k x hk hlow hup
  have ha :
      primeSieveDyadicPacketDeepEnergy y x (J + 1) ≤
        CA * P *
          (primeSieveDyadicPacketLevelEnergy y x J + B) := by
    simpa [y, J, B, P] using hAb k x hk hlow hup
  have hlevel := primeSieveDyadicPacketLevelEnergy_le_shallow_succ y x J
  have hfac0 : 0 ≤ CA * P := mul_nonneg hCA hP0
  have ha' :
      primeSieveDyadicPacketDeepEnergy y x (J + 1) ≤
        CA * P *
          (primeSieveDyadicPacketShallowEnergy y x (J + 1) + B) := by
    exact ha.trans (mul_le_mul_of_nonneg_left
      (add_le_add_right hlevel B) hfac0)
  have hCSU : CS * T ≤ CS * U :=
    mul_le_mul_of_nonneg_left hTU hCS
  have hCAPS :
      CA * P * primeSieveDyadicPacketShallowEnergy y x (J + 1) ≤
        (CA * CS) * U := by
    calc
      CA * P * primeSieveDyadicPacketShallowEnergy y x (J + 1) ≤
          CA * P * (CS * T) :=
        mul_le_mul_of_nonneg_left hs hfac0
      _ = (CA * CS) * (P * T) := by ring
      _ = (CA * CS) * U := by rw [hPT]
  have hCAPB : CA * P * B ≤ CA * U := by
    calc
      CA * P * B = CA * T := by rw [mul_assoc, hPB]
      _ ≤ CA * U := mul_le_mul_of_nonneg_left hTU hCA
  have hdecomp := primeSieveDyadicPacketDeepEnergy_eq_level_add_succ y x J
  calc
    primeSieveDyadicPacketDeepEnergy y x J =
        primeSieveDyadicPacketLevelEnergy y x J +
          primeSieveDyadicPacketDeepEnergy y x (J + 1) := hdecomp
    _ ≤ primeSieveDyadicPacketShallowEnergy y x (J + 1) +
        CA * P *
          (primeSieveDyadicPacketShallowEnergy y x (J + 1) + B) :=
      add_le_add hlevel ha'
    _ = primeSieveDyadicPacketShallowEnergy y x (J + 1) +
        CA * P * primeSieveDyadicPacketShallowEnergy y x (J + 1) +
        CA * P * B := by ring
    _ ≤ CS * T + (CA * CS) * U + CA * U :=
      add_le_add (add_le_add hs hCAPS) hCAPB
    _ ≤ CS * U + (CA * CS) * U + CA * U :=
      add_le_add (add_le_add hCSU le_rfl) le_rfl
    _ = (CS + CA * CS + CA) * U := by ring

/-! ## PNT good mass as an amplifier -/

/-- **PNT good-mass packet charge.**  This is the new arithmetic target.
For every fixed shift `B`, the already-existing positive Selberg good mass at
`N = x+B+2` charges the descendant packet energy against the parent level,
up to a logarithmic square and a subpolynomial loss.

The additive `x+1` term means only excess descendant energy above the ambient
linear floor must be charged to the parent packets. -/
def DyadicPacketPNTGoodMassChargeStatement
    (cutoff : DyadicPacketCutoff) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ B : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (k x : ℕ),
          2 ≤ k →
          primorialBlockLower k ≤ x →
          x ≤ primorialBlockUpper k →
          nativeLambdaTwoGoodRecipMass (x + B + 2) 1 *
              primeSieveDyadicPacketDeepEnergy
                (primorialPNTPrimeSieveCutoff k) x (cutoff k x + 1) ≤
            C * (Real.log ((x + B + 2 : ℕ) : ℝ)) ^ 2 *
              Real.rpow ((x : ℝ) + 1) ε *
              (primeSieveDyadicPacketLevelEnergy
                  (primorialPNTPrimeSieveCutoff k) x (cutoff k x) +
                ((x : ℝ) + 1))

/-- **Unconditional PNT amplification step.**  The square-prefix native PNT
machinery proves enough reciprocal `Lambda_2` good mass to convert the
bilinear good-mass charge into additive descendant persistence.

The eventual threshold from PNT is absorbed by the shift parameter: if the PNT
lower bound holds for every `N >= N0`, evaluate the charge at
`N = x + N0 + 2`.  The same `log(N)^2` occurs on both sides and cancels. -/
theorem dyadicPacketAdditiveDescendantPersistence_of_pntGoodMassCharge
    (cutoff : DyadicPacketCutoff)
    (hG : DyadicPacketPNTGoodMassChargeStatement cutoff) :
    DyadicPacketAdditiveDescendantPersistenceStatement cutoff := by
  have hgood :=
    nativeLambdaTwoGoodRecipMass_eventually_quadratic_squarePrefix_rate
      (1 : ℝ) (by norm_num) (by norm_num)
  rcases eventually_atTop.1 hgood with ⟨N0, hN0⟩
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := hG ε hε N0
  refine ⟨6600000 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let J := cutoff k x
  let N : ℕ := x + N0 + 2
  let Q : ℝ := (Real.log (N : ℝ)) ^ 2
  let P : ℝ := Real.rpow ((x : ℝ) + 1) ε
  let A : ℝ := primeSieveDyadicPacketLevelEnergy y x J + ((x : ℝ) + 1)
  let D : ℝ := primeSieveDyadicPacketDeepEnergy y x (J + 1)
  have hN0le : N0 ≤ N := by dsimp [N]; omega
  have hlower : (1 / 6600000 : ℝ) * Q ≤
      nativeLambdaTwoGoodRecipMass N 1 := by
    simpa [N, Q] using hN0 N hN0le
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact primeSieveDyadicPacketDeepEnergy_nonneg y x (J + 1)
  have hcharge :
      nativeLambdaTwoGoodRecipMass N 1 * D ≤ C * Q * P * A := by
    simpa [y, J, N, Q, P, A, D] using hCb k x hk hlow hup
  have hmul : (1 / 6600000 : ℝ) * Q * D ≤
      nativeLambdaTwoGoodRecipMass N 1 * D :=
    mul_le_mul_of_nonneg_right hlower hD0
  have hcombined : (1 / 6600000 : ℝ) * Q * D ≤ C * Q * P * A :=
    hmul.trans hcharge
  have hNgt : 1 < N := by dsimp [N]; omega
  have hlogpos : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hNgt
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact pow_pos hlogpos 2
  have hscaled :
      Q * ((1 / 6600000 : ℝ) * D) ≤ Q * (C * P * A) := by
    calc
      Q * ((1 / 6600000 : ℝ) * D) =
          (1 / 6600000 : ℝ) * Q * D := by ring
      _ ≤ C * Q * P * A := hcombined
      _ = Q * (C * P * A) := by ring
  have hcancel : (1 / 6600000 : ℝ) * D ≤ C * P * A :=
    (mul_le_mul_iff_right₀ hQpos).mp hscaled
  have hfinal : D ≤ (6600000 * C) * P * A := by
    calc
      D = 6600000 * ((1 / 6600000 : ℝ) * D) := by ring
      _ ≤ 6600000 * (C * P * A) :=
        mul_le_mul_of_nonneg_left hcancel (by norm_num)
      _ = (6600000 * C) * P * A := by ring
  simpa [y, J, P, A, D] using hfinal

/-- The PNT good-mass charge therefore supplies the critical deep-tail bound
when paired with the existing successor-shallow estimate. -/
theorem dyadicPacketDeepTailBlockBounded_of_pntGoodMassCharge
    (cutoff : DyadicPacketCutoff)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hG : DyadicPacketPNTGoodMassChargeStatement cutoff) :
    DyadicPacketDeepTailBlockBoundedStatement cutoff :=
  dyadicPacketDeepTailBlockBounded_of_additiveDescendantPersistence
    cutoff hS
    (dyadicPacketAdditiveDescendantPersistence_of_pntGoodMassCharge cutoff hG)

/-- **PNT-good-mass to RH amplification reduction.**  The good-mass lower
bound is unconditional and comes from the native square-prefix PNT proof.  The
only new packet-side arithmetic premise is the bilinear good-mass charge above.
Together with the already-existing coherent channel, successor-shallow packet
bound, and Mobius dispersion inputs, that charge implies RH. -/
theorem riemannHypothesis_of_dyadicPacketPNTGoodMassChargeAnalyticPackage
    (cutoff : DyadicPacketCutoff)
    (hC : DyadicCoherentChannelRHScale)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hG : DyadicPacketPNTGoodMassChargeStatement cutoff)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicPacketShallowDeepAnalyticPackage cutoff hC
  · exact dyadicPacketShallowEnergyBlockBounded_of_succ cutoff hS
  · exact dyadicPacketDeepTailBlockBounded_of_pntGoodMassCharge cutoff hS hG
  · exact hD

end RHLean.Analysis
