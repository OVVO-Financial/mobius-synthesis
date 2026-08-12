import Mathlib
import RHLean.Analysis.MertensPowerGrowth
import RHLean.Analysis.NativePNTAxer
import RHLean.Analysis.NativePNTTransfer

/-!
# Quantitative statements beyond the native PNT baseline

The elementary Selberg--Erdos argument now proves the qualitative native PNT,
and the elementary Axer bridge gives `M(N) = o(N)`.  This module deliberately
records the stronger scale that remains open after that baseline is discharged.

The two target propositions are pointwise bounds at every exponent strictly
above one half:

* `|psi(N) - N| = O_epsilon(N^(1/2+epsilon))`;
* `|M(N)| = O_epsilon(N^(1/2+epsilon))`.

They are statements, not consequences asserted from the qualitative PNT.  The
Mertens target is phrased first using the repository's existing complex-valued
`mertensSummatory`, then identified exactly with the real-valued
`nativeMertensSummatory` from the Axer layer.  The existing energy criterion is
connected to the same target through `mertensPowerGrowth_of_energy`.

The intended arithmetic route remains elementary and Eulerian: finite
identities, square-prefix or prime-wheel structure, and sharper control gained
by adjoining primes.  No zero-free region, Perron formula, Tauberian theorem,
or new axiom is introduced here.
-/

noncomputable section

namespace RHLean.Analysis

/-- A pointwise power bound for the native Chebyshev error at natural endpoints. -/
def NativePNTChebyshevPowerBound (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N →
      |nativePNTError N| ≤ C * Real.rpow (N : ℝ) r

/-- The genuine post-PNT Chebyshev target: every exponent `1/2 + epsilon`. -/
def NativePNTChebyshevRHScaleStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    NativePNTChebyshevPowerBound ((1 : ℝ) / 2 + ε)

/-- A pointwise power bound for the repository's existing complex Mertens sum. -/
def MertensPowerBound (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N →
      ‖mertensSummatory N‖ ≤ C * Real.rpow (N : ℝ) r

/-- The genuine post-PNT Mertens target in the repository's standard presentation. -/
def MertensRHScaleStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    MertensPowerBound ((1 : ℝ) / 2 + ε)

/-- The same pointwise power bound in the real native Axer presentation. -/
def NativeMertensPowerBound (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N →
      |nativeMertensSummatory N| ≤ C * Real.rpow (N : ℝ) r

/-- The half-plus-epsilon Mertens target in the native real presentation. -/
def NativeMertensRHScaleStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    NativeMertensPowerBound ((1 : ℝ) / 2 + ε)

/-- The two nontrivial quantitative targets left visible after the PNT baseline. -/
def NativePNTQuantitativeTarget : Prop :=
  NativePNTChebyshevRHScaleStatement ∧ MertensRHScaleStatement

@[simp] theorem nativeMertensSummatory_zero :
    nativeMertensSummatory 0 = 0 := by
  simp [nativeMertensSummatory]

/-- The native real Mertens sum has the same one-step recurrence as the existing
complex-valued summatory function. -/
theorem nativeMertensSummatory_succ (N : ℕ) :
    nativeMertensSummatory (N + 1) =
      nativeMertensSummatory N +
        ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) := by
  unfold nativeMertensSummatory
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- The existing complex Mertens sum is exactly the complex cast of the native
real Axer sum.  The only indexing difference is the harmless `mu(0) = 0` term. -/
theorem mertensSummatory_eq_complex_nativeMertensSummatory (N : ℕ) :
    mertensSummatory N = (nativeMertensSummatory N : ℂ) := by
  induction N with
  | zero =>
      simp [mertensSummatory, nativeMertensSummatory]
  | succ N ih =>
      rw [mertensSummatory_succ, nativeMertensSummatory_succ, ih]
      push_cast
      rfl

/-- Consequently the standard complex norm and native real absolute value agree. -/
theorem norm_mertensSummatory_eq_abs_nativeMertensSummatory (N : ℕ) :
    ‖mertensSummatory N‖ = |nativeMertensSummatory N| := by
  rw [mertensSummatory_eq_complex_nativeMertensSummatory]
  simp

/-- The standard and native presentations give exactly the same pointwise
power-bound proposition, with no loss in the constant. -/
theorem mertensPowerBound_iff_nativeMertensPowerBound (r : ℝ) :
    MertensPowerBound r ↔ NativeMertensPowerBound r := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N hN
    rw [← norm_mertensSummatory_eq_abs_nativeMertensSummatory]
    exact hbound N hN
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N hN
    rw [norm_mertensSummatory_eq_abs_nativeMertensSummatory]
    exact hbound N hN

/-- Hence the half-plus-epsilon target is presentation-independent. -/
theorem mertensRHScaleStatement_iff_native :
    MertensRHScaleStatement ↔ NativeMertensRHScaleStatement := by
  constructor
  · intro h ε hε
    exact (mertensPowerBound_iff_nativeMertensPowerBound _).1 (h ε hε)
  · intro h ε hε
    exact (mertensPowerBound_iff_nativeMertensPowerBound _).2 (h ε hε)

/-- The repository's existing squared Mertens-energy statement feeds the exact
same half-plus-epsilon target.  This is a conditional interface theorem, not a
claim that the qualitative PNT proves the target. -/
theorem mertensRHScale_of_energy
    (hM : MertensEnergyBoundedStatement) :
    MertensRHScaleStatement := by
  intro ε hε
  let r : ℝ := (1 : ℝ) / 2 + ε
  have hrHalf : (1 : ℝ) / 2 < r := by
    dsimp [r]
    linarith
  have hrNonneg : 0 ≤ r := by
    dsimp [r]
    linarith
  rcases mertensPowerGrowth_of_energy hM hrHalf with ⟨K, hK, hbound⟩
  let C : ℝ := K * Real.rpow 2 r
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hshift : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  have hrpow :
      Real.rpow (((N + 1 : ℕ) : ℝ)) r ≤
        Real.rpow (2 * (N : ℝ)) r :=
    Real.rpow_le_rpow (by positivity) hshift hrNonneg
  have hscaled :
      K * Real.rpow (((N + 1 : ℕ) : ℝ)) r ≤
        K * Real.rpow (2 * (N : ℝ)) r :=
    mul_le_mul_of_nonneg_left hrpow hK
  have hfactor :
      (2 * (N : ℝ)) ^ r =
        2 ^ r * (N : ℝ) ^ r := by
    exact Real.mul_rpow (by positivity) (by positivity)
  calc
    ‖mertensSummatory N‖ ≤
        K * Real.rpow (((N + 1 : ℕ) : ℝ)) r := hbound N
    _ ≤ K * Real.rpow (2 * (N : ℝ)) r := hscaled
    _ = C * Real.rpow (N : ℝ) r := by
      dsimp [C]
      rw [hfactor]
      ring

end RHLean.Analysis
