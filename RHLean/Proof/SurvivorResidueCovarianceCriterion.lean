import Mathlib
import RHLean.Proof.SurvivorResidueCovariance

/-!
# Survivor residue covariance criterion

This module turns the exact residue-fibre covariance ledger into the precise
analytic statement needed by the survivor route.

For every positive residue modulus `s`, write

```text
A(u) = sum_c -mu(c) K(c,u),
V    = sum_u A(u)^2,
D    = same-cofactor diagonal,
C    = cross-cofactor covariance.
```

The preceding module proves `V = D + C`. Here finite Cauchy--Schwarz gives the
unconditional pointwise bridge

```text
|survivorZeroMode Lambda t|^2 <= s * V = s * (D + C).
```

Thus the exact remaining analytic target is a covariance-defect estimate: the
negative cross-cofactor covariance must cancel the diagonal up to the desired
RH-scale remainder after multiplication by the chosen residue modulus.

No covariance estimate is assumed inside an algebraic identity. The only new
hypothesis below is isolated as a named power-saving statement for a prescribed
positive modulus schedule.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

/-- A prescribed positive residue modulus at every survivor stage. -/
structure SurvivorResidueModulusSchedule where
  modulus : ℕ → ℕ
  positive : ∀ t, 0 < modulus t

/-- The survivor zero mode is the complex cast of the total signed residue mass.
This is the exact bridge from the residue partition back to the original
cofactor operator. -/
theorem survivorZeroMode_eq_intCast_sum_survivorResidueSignedMass
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    survivorZeroMode Λ t =
      ((∑ u : ZMod s, survivorResidueSignedMass Λ t s u : ℤ) : ℂ) := by
  rw [sum_survivorResidueSignedMass_eq_integerZeroMode]
  unfold survivorZeroMode survivorResidueCofactorRange
  push_cast
  apply Finset.sum_congr rfl
  intro c _hc
  rw [nsmul_eq_mul']
  unfold canonicalMoebiusWeight
  ring

/-- Finite Cauchy--Schwarz on the signed residue masses. -/
theorem sq_sum_survivorResidueSignedMass_le_modulus_mul_energy
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    (((∑ u : ZMod s, survivorResidueSignedMass Λ t s u : ℤ) : ℝ)) ^ 2 ≤
      (s : ℝ) * ((survivorResidueEnergy Λ t s : ℤ) : ℝ) := by
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (ZMod s))
      (fun u => ((survivorResidueSignedMass Λ t s u : ℤ) : ℝ))
      (fun _u => (1 : ℝ))
  have hreal :
      (∑ u : ZMod s,
          ((survivorResidueSignedMass Λ t s u : ℤ) : ℝ)) ^ 2 ≤
        (s : ℝ) *
          ∑ u : ZMod s,
            ((survivorResidueSignedMass Λ t s u : ℤ) : ℝ) ^ 2 := by
    simpa [ZMod.card, nsmul_eq_mul, mul_comm] using hcs
  calc
    (((∑ u : ZMod s, survivorResidueSignedMass Λ t s u : ℤ) : ℝ)) ^ 2 =
        (∑ u : ZMod s,
          ((survivorResidueSignedMass Λ t s u : ℤ) : ℝ)) ^ 2 := by
      push_cast
      rfl
    _ ≤ (s : ℝ) *
          ∑ u : ZMod s,
            ((survivorResidueSignedMass Λ t s u : ℤ) : ℝ) ^ 2 := hreal
    _ = (s : ℝ) * ((survivorResidueEnergy Λ t s : ℤ) : ℝ) := by
      congr 1
      unfold survivorResidueEnergy
      push_cast
      simp [pow_two]

/-- Squared complex norm of an integer cast, expressed as a real integer
quadratic form. -/
private theorem survivor_norm_intCast_complex_sq (z : ℤ) :
    ‖((z : ℤ) : ℂ)‖ ^ 2 = ((z * z : ℤ) : ℝ) := by
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply]

/-- Unconditional pointwise residue-energy control of the survivor amplitude. -/
theorem norm_sq_survivorZeroMode_le_modulus_mul_residueEnergy
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    ‖survivorZeroMode Λ t‖ ^ 2 ≤
      (s : ℝ) * ((survivorResidueEnergy Λ t s : ℤ) : ℝ) := by
  rw [survivorZeroMode_eq_intCast_sum_survivorResidueSignedMass Λ t s]
  rw [survivor_norm_intCast_complex_sq]
  simpa [pow_two] using
    sq_sum_survivorResidueSignedMass_le_modulus_mul_energy Λ t s

/-- The same pointwise bridge written in the signed diagonal-plus-covariance
form. This is the key statement: the cross term is retained inside `D + C`. -/
theorem norm_sq_survivorZeroMode_le_modulus_mul_diagonal_add_crossCovariance
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    ‖survivorZeroMode Λ t‖ ^ 2 ≤
      (s : ℝ) *
        (((survivorResidueDiagonalEnergy Λ t s +
          survivorResidueCrossCofactorCovariance Λ t s : ℤ) : ℝ)) := by
  rw [← survivorResidueEnergy_eq_diagonal_add_crossCovariance]
  exact norm_sq_survivorZeroMode_le_modulus_mul_residueEnergy Λ t s

/-- Unscheduled signed covariance budget at one positive modulus. -/
def survivorResidueCovarianceBudgetAt
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℝ :=
  (s : ℝ) *
    (((survivorResidueDiagonalEnergy Λ t s +
      survivorResidueCrossCofactorCovariance Λ t s : ℤ) : ℝ))

/-- At fixed positive modulus the signed covariance budget is exactly modulus
times the positive residue energy. -/
theorem survivorResidueCovarianceBudgetAt_eq_modulus_mul_energy
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    survivorResidueCovarianceBudgetAt Λ t s =
      (s : ℝ) * ((survivorResidueEnergy Λ t s : ℤ) : ℝ) := by
  unfold survivorResidueCovarianceBudgetAt
  rw [survivorResidueEnergy_eq_diagonal_add_crossCovariance]

/-- The signed covariance budget associated with a prescribed positive modulus
schedule. It is exactly `s_t * (D_{t,s_t} + C_{t,s_t})`. -/
def survivorResidueCovarianceBudget
    (Λ : ℝ) (schedule : SurvivorResidueModulusSchedule) (t : ℕ) : ℝ := by
  letI : NeZero (schedule.modulus t) :=
    ⟨Nat.ne_of_gt (schedule.positive t)⟩
  exact survivorResidueCovarianceBudgetAt Λ t (schedule.modulus t)

/-- The scheduled covariance budget pointwise dominates the survivor energy. -/
theorem norm_sq_survivorZeroMode_le_covarianceBudget
    (Λ : ℝ) (schedule : SurvivorResidueModulusSchedule) (t : ℕ) :
    ‖survivorZeroMode Λ t‖ ^ 2 ≤
      survivorResidueCovarianceBudget Λ schedule t := by
  letI : NeZero (schedule.modulus t) :=
    ⟨Nat.ne_of_gt (schedule.positive t)⟩
  simpa [survivorResidueCovarianceBudget, survivorResidueCovarianceBudgetAt] using
    norm_sq_survivorZeroMode_le_modulus_mul_diagonal_add_crossCovariance
      Λ t (schedule.modulus t)

/-- The exact remaining translated-window analytic statement on the signed
covariance budget. The modulus schedule is an explicit input, not chosen after
seeing the survivor value. -/
def SurvivorResidueCovarianceBudgetPowerSavingStatement
    (Λ : ℝ) (schedule : SurvivorResidueModulusSchedule) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        (∑ h ∈ Finset.range H,
          survivorResidueCovarianceBudget Λ schedule (N + h)) ≤
            C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- A covariance-budget power saving immediately gives the existing survivor
zero-mode power saving, with no loss beyond finite Cauchy--Schwarz already
recorded in the budget. -/
theorem survivorResidueCovarianceBudgetPowerSaving_implies_zeroModePowerSaving
    {Λ : ℝ} {schedule : SurvivorResidueModulusSchedule}
    (hbudget : SurvivorResidueCovarianceBudgetPowerSavingStatement Λ schedule) :
    SurvivorZeroModePowerSavingStatement Λ := by
  intro ε hε
  rcases hbudget ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N H hH hHN
  unfold RHLean.Analysis.localSequenceEnergy
  calc
    (∑ h ∈ Finset.range H, ‖survivorZeroMode Λ (N + h)‖ ^ 2) ≤
        ∑ h ∈ Finset.range H,
          survivorResidueCovarianceBudget Λ schedule (N + h) := by
      apply Finset.sum_le_sum
      intro h _hh
      exact norm_sq_survivorZeroMode_le_covarianceBudget Λ schedule (N + h)
    _ ≤ C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) :=
      hbound N H hH hHN

/-- The covariance-budget criterion therefore implies the protected concrete
square-prefix local criterion. -/
theorem survivorResidueCovarianceBudgetPowerSaving_implies_squarePrefixUniformLocal
    {Λ : ℝ} (hΛ : 0 < Λ)
    {schedule : SurvivorResidueModulusSchedule}
    (hbudget : SurvivorResidueCovarianceBudgetPowerSavingStatement Λ schedule) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  exact survivorZeroModePowerSaving_implies_squarePrefixUniformLocal hΛ
    (survivorResidueCovarianceBudgetPowerSaving_implies_zeroModePowerSaving hbudget)

/-- Terminal composition with the repository's classical Mertens--RH criterion. -/
theorem survivorResidueCovarianceBudgetPowerSaving_implies_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 < Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    {schedule : SurvivorResidueModulusSchedule}
    (hbudget : SurvivorResidueCovarianceBudgetPowerSavingStatement Λ schedule) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  exact survivorZeroModePowerSaving_implies_riemannHypothesis hΛ criterion
    (survivorResidueCovarianceBudgetPowerSaving_implies_zeroModePowerSaving hbudget)

end RHLean.Proof
