import Mathlib
import RHLean.Arithmetic.PrimeAveragedFrontierIdentity
import RHLean.Analysis.MertensEnergyRHForward

/-!
# Prime-averaged Boolean-cube frontier energy diagnostic

The arithmetic cube layer proves something stronger than a merely averaged
identity: for every prime coordinate `ell <= X`, the signed first-failure
frontier mass is exactly the same ordinary Mobius prefix `M(X)`.

Consequently the naive prime-averaged frontier energy is not an independent
source of cancellation.  It is exactly

`pi(X) * ||M(X)||^2`.

This module records that equivalence explicitly.  It is a useful falsification:
a mean-square theorem for the *total signed mass* of the prime-coordinate
frontiers is just a repackaging of Mertens energy and cannot by itself be the
surviving multi-prime cube mechanism.  A genuinely new cube route must retain
richer internal frontier coordinates before summing each frontier to one scalar.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Complex Mobius mass of the first-failure Boolean-cube frontier at one fresh
prime coordinate. -/
def primeProductFrontierMobiusMass (X ell : ℕ) : ℂ :=
  ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
    (((μ (primeFaceProduct t) : ℤ) : ℂ))

/-- Every represented prime coordinate carries exactly the ordinary Mertens
prefix.  Thus the total frontier mass has no variation in the prime coordinate. -/
theorem primeProductFrontierMobiusMass_eq_mertensSummatory
    {X ell : ℕ} (hell : ell ∈ primesUpTo X) :
    primeProductFrontierMobiusMass X ell = mertensSummatory X := by
  have h := moebiusPrefix_eq_primeFrontier
    (prime_of_mem_primesUpTo hell) (mem_primesUpTo.mp hell).2
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  simpa [primeProductFrontierMobiusMass, mertensSummatory] using hc.symm

/-- Total mean-square mass over all fresh-prime frontier coordinates. -/
def primeAveragedFrontierEnergy (X : ℕ) : ℝ :=
  ∑ ell ∈ primesUpTo X, ‖primeProductFrontierMobiusMass X ell‖ ^ 2

/-- Exact collapse of the naive prime-averaged frontier energy. -/
theorem primeAveragedFrontierEnergy_eq_card_mul_mertensEnergy
    (X : ℕ) :
    primeAveragedFrontierEnergy X =
      ((primesUpTo X).card : ℝ) * ‖mertensSummatory X‖ ^ 2 := by
  unfold primeAveragedFrontierEnergy
  calc
    (∑ ell ∈ primesUpTo X, ‖primeProductFrontierMobiusMass X ell‖ ^ 2) =
        ∑ _ell ∈ primesUpTo X, ‖mertensSummatory X‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [primeProductFrontierMobiusMass_eq_mertensSummatory hell]
    _ = ((primesUpTo X).card : ℝ) * ‖mertensSummatory X‖ ^ 2 := by
      simp

/-- Naive critical mean-square target for the complete family of scalar frontier
masses.  The theorem below shows that this target is equivalent, modulo the two
small endpoints, to the protected Mertens-energy statement. -/
def PrimeAveragedFrontierEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 2 ≤ X →
        primeAveragedFrontierEnergy X ≤
          C * ((primesUpTo X).card : ℝ) *
            Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)

/-- The naive prime-averaged frontier-energy target implies Mertens energy only
because each frontier scalar is already exactly `M(X)`.  No new cancellation is
created by averaging the prime coordinate. -/
theorem mertensEnergyBounded_of_primeAveragedFrontierEnergy
    (hF : PrimeAveragedFrontierEnergyBoundedStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := hF ε hε
  let D : ℝ := C + 1
  have hD0 : 0 ≤ D := by dsimp [D]; linarith
  refine ⟨D, hD0, ?_⟩
  intro X
  by_cases hX : 2 ≤ X
  · let P : ℝ := ((primesUpTo X).card : ℝ)
    let Q : ℝ := Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)
    have h2mem : 2 ∈ primesUpTo X :=
      mem_primesUpTo.mpr ⟨Nat.prime_two, hX⟩
    have hcard : 0 < (primesUpTo X).card :=
      Finset.card_pos.mpr ⟨2, h2mem⟩
    have hP : 0 < P := by dsimp [P]; exact_mod_cast hcard
    have hQ0 : 0 ≤ Q := by
      dsimp [Q]
      exact Real.rpow_nonneg (by positivity) _
    have hraw := hCb X hX
    rw [primeAveragedFrontierEnergy_eq_card_mul_mertensEnergy] at hraw
    have hscaled :
        P * ‖mertensSummatory X‖ ^ 2 ≤ P * (C * Q) := by
      simpa [P, Q, mul_assoc, mul_left_comm, mul_comm] using hraw
    have hmain : ‖mertensSummatory X‖ ^ 2 ≤ C * Q :=
      (mul_le_mul_iff_right₀ hP).mp hscaled
    have hCD : C ≤ D := by dsimp [D]; linarith
    have hraise : C * Q ≤ D * Q :=
      mul_le_mul_of_nonneg_right hCD hQ0
    simpa [D, Q] using hmain.trans hraise
  · have hsmall : X = 0 ∨ X = 1 := by omega
    rcases hsmall with rfl | rfl
    · simpa [mertensSummatory] using hD0
    · have hpow :
          (1 : ℝ) ≤ Real.rpow (2 : ℝ) (1 + ε) :=
        Real.one_le_rpow (by norm_num) (by linarith)
      have hD1 : (1 : ℝ) ≤ D := by dsimp [D]; linarith
      have hone :
          (1 : ℝ) ≤ D * Real.rpow (2 : ℝ) (1 + ε) := by
        calc
          (1 : ℝ) ≤ D := hD1
          _ ≤ D * Real.rpow (2 : ℝ) (1 + ε) := by
            simpa using mul_le_mul_of_nonneg_left hpow hD0
      simpa [mertensSummatory, Finset.sum_range_succ] using hone

/-- Conversely, Mertens energy immediately bounds the scalar frontier energy by
the exact collapse theorem. -/
theorem primeAveragedFrontierEnergyBounded_of_mertensEnergy
    (hM : MertensEnergyBoundedStatement) :
    PrimeAveragedFrontierEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := hM ε hε
  refine ⟨C, hC, ?_⟩
  intro X _hX
  have h := hCb X
  rw [primeAveragedFrontierEnergy_eq_card_mul_mertensEnergy]
  have hcard0 : (0 : ℝ) ≤ ((primesUpTo X).card : ℝ) := by positivity
  calc
    ((primesUpTo X).card : ℝ) * ‖mertensSummatory X‖ ^ 2 ≤
        ((primesUpTo X).card : ℝ) *
          (C * Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)) :=
      mul_le_mul_of_nonneg_left h hcard0
    _ = C * ((primesUpTo X).card : ℝ) *
        Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε) := by ring

/-- Exact analytic diagnosis: the scalar prime-averaged frontier target is
nothing more than the existing Mertens-energy target. -/
theorem primeAveragedFrontierEnergyBounded_iff_mertensEnergyBounded :
    PrimeAveragedFrontierEnergyBoundedStatement ↔ MertensEnergyBoundedStatement := by
  constructor
  · exact mertensEnergyBounded_of_primeAveragedFrontierEnergy
  · exact primeAveragedFrontierEnergyBounded_of_mertensEnergy

/-- Accordingly this scalar frontier target still implies RH, but only through
its exact equivalence with Mertens energy.  This theorem is a diagnostic, not a
claim of a new independent analytic route. -/
theorem riemannHypothesis_of_primeAveragedFrontierEnergy
    (hF : PrimeAveragedFrontierEnergyBoundedStatement) :
    RiemannHypothesisStatement := by
  change RiemannHypothesis
  exact riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_primeAveragedFrontierEnergy hF)

end RHLean.Analysis
