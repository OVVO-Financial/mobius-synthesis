import Mathlib
import RHLean.Analysis.ThreeSlotDegreeOneCriterion

/-!
# Physical degree-one mixing conjecture

This module isolates the single quantitative statement left by the exact
three-slot physical transition pushforward.  The state space remains the
canonical `Fin 27` Mobius cube.  The eight all-nonzero states are used only as
the conditioned sign sector; every zero-coordinate contribution is retained in
`physicalDegreeOneD`.

The open statement is deliberately weaker than full transition uniformity.  It
asks only for square-root-scale cancellation of the Mertens-visible degree-one
transition mass together with the explicit zero-sector defect.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The canonical eight all-nonzero states in the physical `Fin 27` cube. -/
def physicalThreeSlotNonzeroStates : Finset (Fin 27) :=
  {0, 2, 6, 8, 18, 20, 24, 26}

/-- Exact finite sum over the canonical nonzero sector
`A = {0,2,6,8,18,20,24,26}`.  This explicit operator matches the physical
transition moment definitions and avoids introducing any probabilistic state
space abstraction. -/
def physicalNonzeroStateSum (f : Fin 27 → ℝ) : ℝ :=
  f 0 + f 2 + f 6 + f 8 + f 18 + f 20 + f 24 + f 26

/-- `N_{u,v}(K)`: exact number of the first `K` physical edges from `u` to `v`. -/
def physicalTransitionN (K : ℕ) (u v : Fin 27) : ℕ :=
  threeSlotTransitionCount K u v

/-- `R_u(K)`: row total from `u` into the eight-state nonzero destination sector. -/
def physicalTransitionR (K : ℕ) (u : Fin 27) : ℤ :=
  threeSlotTransitionRowTotalOn (Finset.range K) u

/-- `T(K)`: signed degree-one mass of transitions staying in the nonzero sector. -/
def physicalDegreeOneT (K : ℕ) : ℤ :=
  threeSlotTransitionDegreeOneMass K

/-- `D(K)`: the exact residual carrying every zero-coordinate contribution. -/
def physicalDegreeOneD (K : ℕ) : ℤ :=
  threeSlotTransitionDegreeOneDefect K

/-- Exact integer pushforward:
`M(4(K+1)) = g(X_0) + T(K) + D(K)`. -/
theorem moebiusPositivePrefix_four_mul_succ_eq_physicalDegreeOne
    (K : ℕ) :
    moebiusPositivePrefix (4 * (K + 1)) =
      threeSlotDegreeOneValue (threeSlotState 0) +
        physicalDegreeOneT K + physicalDegreeOneD K := by
  simpa [physicalDegreeOneT, physicalDegreeOneD] using
    moebiusPositivePrefix_four_mul_succ_eq_transitionMass_add_defect K

/-- Analytic form of the same exact pushforward. -/
theorem mertensSummatory_four_mul_succ_eq_physicalDegreeOne
    (K : ℕ) :
    mertensSummatory (4 * (K + 1)) =
      (((threeSlotDegreeOneValue (threeSlotState 0) +
          physicalDegreeOneT K + physicalDegreeOneD K : ℤ)) : ℂ) := by
  simpa [physicalDegreeOneT, physicalDegreeOneD] using
    mertensSummatory_four_mul_succ_eq_transitionMass_add_defect K

/-- One source row of the `1/8` centering identity. -/
private theorem physicalTransitionRow_centered
    (K : ℕ) (u : Fin 27) :
    ((threeSlotTransitionMomentOn
        (Finset.range K) u threeSlotDegreeOneValue : ℤ) : ℝ) =
      physicalNonzeroStateSum (fun v =>
        (((physicalTransitionN K u v : ℕ) : ℝ) -
            ((physicalTransitionR K u : ℤ) : ℝ) / 8) *
          ((threeSlotDegreeOneValue v : ℤ) : ℝ)) := by
  (norm_num [physicalNonzeroStateSum, physicalTransitionN,
    physicalTransitionR, threeSlotTransitionCount,
    threeSlotTransitionMomentOn, threeSlotTransitionRowTotalOn,
    threeSlotDegreeOneValue, chiA, chiB, chiC]; ring)

/-- The transition mass is exactly the sum of its eight nonzero source rows. -/
private theorem physicalDegreeOneT_real_eq_rowSum (K : ℕ) :
    ((physicalDegreeOneT K : ℤ) : ℝ) =
      physicalNonzeroStateSum (fun u =>
        ((threeSlotTransitionMomentOn
            (Finset.range K) u threeSlotDegreeOneValue : ℤ) : ℝ)) := by
  norm_num [physicalNonzeroStateSum, physicalDegreeOneT,
    threeSlotTransitionDegreeOneMass]

/-- **Exact row-centering identity.**  After casting to `ℝ`, the raw degree-one
transition mass is exactly

`sum_{u,v in A} (N_{u,v}(K) - R_u(K)/8) * g(v)`

for the canonical eight-state nonzero sector `A`.  No transition probability
or equidistribution hypothesis appears in the theorem. -/
theorem physicalDegreeOneT_eq_centeredTransitionDiscrepancy
    (K : ℕ) :
    ((physicalDegreeOneT K : ℤ) : ℝ) =
      physicalNonzeroStateSum (fun u =>
        physicalNonzeroStateSum (fun v =>
          (((physicalTransitionN K u v : ℕ) : ℝ) -
              ((physicalTransitionR K u : ℤ) : ℝ) / 8) *
            ((threeSlotDegreeOneValue v : ℤ) : ℝ))) := by
  rw [physicalDegreeOneT_real_eq_rowSum]
  apply congrArg physicalNonzeroStateSum
  funext u
  exact physicalTransitionRow_centered K u

/-- **The single open arithmetic target of the physical transition route.**
For every positive epsilon, both the conditioned degree-one transition mass and
the explicit zero-sector defect cancel jointly at square-root scale.

The absolute values are separate before addition: this statement does not allow
cancellation between `T(K)` and `D(K)`. -/
def PhysicalDegreeOneMixingConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ K : ℕ,
        |((physicalDegreeOneT K : ℤ) : ℝ)| +
            |((physicalDegreeOneD K : ℤ) : ℝ)| ≤
          C * Real.rpow (K : ℝ) ((1 : ℝ) / 2 + ε)

private theorem physical_norm_intCast_complex_sq (z : ℤ) :
    ‖((z : ℤ) : ℂ)‖ ^ 2 = ((z : ℤ) : ℝ) ^ 2 := by
  calc
    ‖((z : ℤ) : ℂ)‖ ^ 2 = ((z * z : ℤ) : ℝ) := by
      rw [Complex.sq_norm]
      norm_num [Complex.normSq_apply]
    _ = ((z : ℤ) : ℝ) ^ 2 := by
      push_cast
      ring

/-- The physical mixing conjecture implies the already kernel-checked
three-slot degree-one energy criterion. -/
theorem threeSlotDegreeOneEnergy_of_physicalDegreeOneMixingConjecture
    (h : PhysicalDegreeOneMixingConjecture) :
    ThreeSlotDegreeOneEnergyBoundedStatement := by
  intro ε hε
  have hεhalf : 0 < ε / 2 := by linarith
  rcases h (ε / 2) hεhalf with ⟨C, hC, hmix⟩
  let G : ℝ :=
    |((threeSlotDegreeOneValue (threeSlotState 0) : ℤ) : ℝ)|
  have hG : 0 ≤ G := by
    dsimp [G]
    exact abs_nonneg _
  refine ⟨(C + G) ^ 2, ?_, ?_⟩
  · positivity
  · intro K
    cases K with
    | zero =>
        simpa [threeSlotWa, threeSlotWb, threeSlotWc, Real.one_rpow] using
          (sq_nonneg (C + G))
    | succ K =>
        let a : ℝ := (1 : ℝ) / 2 + ε / 2
        let R : ℝ := Real.rpow (((K + 1) + 1 : ℕ) : ℝ) a
        have ha : 0 < a := by
          dsimp [a]
          linarith
        have hbase : 0 < (((K + 1) + 1 : ℕ) : ℝ) := by positivity
        have hKle : (K : ℝ) ≤ (((K + 1) + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show K ≤ (K + 1) + 1 by omega)
        have hscale : Real.rpow (K : ℝ) a ≤ R := by
          dsimp [R]
          exact Real.rpow_le_rpow (by positivity) hKle ha.le
        have hone : (1 : ℝ) ≤ R := by
          have hbaseone : (1 : ℝ) ≤ (((K + 1) + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 1 ≤ (K + 1) + 1 by omega)
          have hr := Real.rpow_le_rpow zero_le_one hbaseone ha.le
          simpa [R, Real.one_rpow] using hr
        have hmixK :
            |((physicalDegreeOneT K : ℤ) : ℝ)| +
                |((physicalDegreeOneD K : ℤ) : ℝ)| ≤ C * R := by
          calc
            |((physicalDegreeOneT K : ℤ) : ℝ)| +
                  |((physicalDegreeOneD K : ℤ) : ℝ)|
                ≤ C * Real.rpow (K : ℝ) a := by
                    simpa [a] using hmix K
            _ ≤ C * R := mul_le_mul_of_nonneg_left hscale hC.le
        have hdecomp :
            threeSlotWa (K + 1) + threeSlotWb (K + 1) +
                threeSlotWc (K + 1) =
              threeSlotDegreeOneValue (threeSlotState 0) +
                physicalDegreeOneT K + physicalDegreeOneD K := by
          simpa [physicalDegreeOneT, physicalDegreeOneD] using
            threeSlotCombinedDegreeOne_succ_eq_transitionMass_add_defect K
        let w : ℝ :=
          ((threeSlotWa (K + 1) + threeSlotWb (K + 1) +
              threeSlotWc (K + 1) : ℤ) : ℝ)
        have hwabs :
            |w| ≤ G + |((physicalDegreeOneT K : ℤ) : ℝ)| +
              |((physicalDegreeOneD K : ℤ) : ℝ)| := by
          dsimp [w, G]
          rw [hdecomp]
          push_cast
          have htri :
              ‖((threeSlotDegreeOneValue (threeSlotState 0) : ℤ) : ℝ) +
                    (physicalDegreeOneT K : ℝ) +
                    (physicalDegreeOneD K : ℝ)‖ ≤
                ‖((threeSlotDegreeOneValue (threeSlotState 0) : ℤ) : ℝ)‖ +
                  ‖(physicalDegreeOneT K : ℝ)‖ +
                  ‖(physicalDegreeOneD K : ℝ)‖ := by
            calc
              ‖((threeSlotDegreeOneValue (threeSlotState 0) : ℤ) : ℝ) +
                    (physicalDegreeOneT K : ℝ) +
                    (physicalDegreeOneD K : ℝ)‖
                  ≤ ‖((threeSlotDegreeOneValue (threeSlotState 0) : ℤ) : ℝ) +
                        (physicalDegreeOneT K : ℝ)‖ +
                      ‖(physicalDegreeOneD K : ℝ)‖ := norm_add_le _ _
              _ ≤ (‖((threeSlotDegreeOneValue (threeSlotState 0) : ℤ) : ℝ)‖ +
                        ‖(physicalDegreeOneT K : ℝ)‖) +
                      ‖(physicalDegreeOneD K : ℝ)‖ := by
                    gcongr
                    exact norm_add_le _ _
          simpa [Real.norm_eq_abs] using htri
        have hGR : G ≤ G * R := by
          have := mul_le_mul_of_nonneg_left hone hG
          simpa using this
        have hwlinear : |w| ≤ (C + G) * R := by
          calc
            |w| ≤ G + |((physicalDegreeOneT K : ℤ) : ℝ)| +
                |((physicalDegreeOneD K : ℤ) : ℝ)| := hwabs
            _ ≤ G + C * R := by linarith
            _ ≤ G * R + C * R := by linarith
            _ = (C + G) * R := by ring
        have hCR : 0 ≤ (C + G) * R := by
          have hCG : 0 ≤ C + G := by linarith
          have hR : 0 ≤ R := by
            dsimp [R]
            exact Real.rpow_nonneg hbase.le a
          positivity
        have hwabs0 : 0 ≤ |w| := abs_nonneg w
        have habssq : |w| ^ 2 = w ^ 2 := by
          exact sq_abs w
        have hwsq : w ^ 2 ≤ ((C + G) * R) ^ 2 := by
          nlinarith
        have hRpow : R ^ 2 =
            Real.rpow (((K + 1) + 1 : ℕ) : ℝ) (1 + ε) := by
          dsimp [R]
          calc
            Real.rpow (((K + 1) + 1 : ℕ) : ℝ) a ^ 2 =
                Real.rpow (((K + 1) + 1 : ℕ) : ℝ) a *
                  Real.rpow (((K + 1) + 1 : ℕ) : ℝ) a := by ring
            _ = Real.rpow (((K + 1) + 1 : ℕ) : ℝ) (a + a) :=
                  (Real.rpow_add hbase a a).symm
            _ = Real.rpow (((K + 1) + 1 : ℕ) : ℝ) (1 + ε) := by
                  congr 1
                  dsimp [a]
                  ring
        rw [physical_norm_intCast_complex_sq]
        calc
          ((threeSlotWa (K + 1) + threeSlotWb (K + 1) +
                threeSlotWc (K + 1) : ℤ) : ℝ) ^ 2
              = w ^ 2 := by rfl
          _ ≤ ((C + G) * R) ^ 2 := hwsq
          _ = (C + G) ^ 2 * R ^ 2 := by ring
          _ = (C + G) ^ 2 *
                Real.rpow (((K + 1) + 1 : ℕ) : ℝ) (1 + ε) := by
                  rw [hRpow]

/-- **Terminal closure.**  The physical degree-one mixing conjecture alone is
sufficient for the Riemann Hypothesis through the existing protected
three-slot energy chain. -/
theorem rh_of_physicalDegreeOneMixingConjecture
    (h : PhysicalDegreeOneMixingConjecture) : RiemannHypothesis :=
  riemannHypothesis_of_threeSlotDegreeOneEnergy
    (threeSlotDegreeOneEnergy_of_physicalDegreeOneMixingConjecture h)

end RHLean.Analysis

end
