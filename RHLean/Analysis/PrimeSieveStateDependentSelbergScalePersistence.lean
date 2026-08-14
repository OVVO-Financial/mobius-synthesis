import Mathlib
import RHLean.Analysis.NativePNTCubicContractionInequality
import RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainClosure

noncomputable section

namespace RHLean.Analysis

/-- A genuine PNT tail beginning at physical cutoff `M`. -/
def PrimeSieveStateDependentSelbergTailAbove
    (M : Nat) (alpha : Real) : Prop :=
  2 <= M ∧ 0 < alpha ∧
    forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real)

/-- One cubic contraction is available from the old cutoff `M` once the
physical scale has advanced to `L`.  The gain still uses the old tail cutoff,
so no information is discarded when the new onset is chosen. -/
def PrimeSieveStateDependentSelbergCubicGainFromTo
    (M L : Nat) (alpha c : Real) : Prop :=
  M <= L ∧
    forall N : Nat, L <= N ->
      ∃ beta : Real,
        0 <= beta ∧ beta < alpha ∧
          PrimeSieveStateDependentSelbergStateHasPowerGain
            c 3 N M alpha beta

/-- A cubic gain valid beyond `L` upgrades an old `M`-tail to the contracted
slope on the new `L`-tail. -/
theorem primeSieveStateDependentSelberg_cubicGainFromTo_step
    (M L : Nat) (alpha c : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hgain : PrimeSieveStateDependentSelbergCubicGainFromTo M L alpha c)
    (hnext : 0 < alpha - c * alpha ^ 3) :
    PrimeSieveStateDependentSelbergTailAbove
      L (alpha - c * alpha ^ 3) := by
  rcases htail with ⟨hM2, halpha, htail⟩
  rcases hgain with ⟨hML, hgain⟩
  refine ⟨hM2.trans hML, hnext, ?_⟩
  intro N hLN
  rcases hgain N hLN with ⟨beta, hbeta0, hbeta, hpower⟩
  have hMN : M <= N := hML.trans hLN
  have hN2 : 2 <= N := hM2.trans hMN
  have hM1 : 1 <= M := by omega
  have hadm : PrimeSieveStateDependentSelbergAdmissible N M alpha beta :=
    ⟨⟨hN2, hM1, hMN, halpha, htail⟩, hbeta0, hbeta⟩
  exact primeSieveStateDependentSelberg_error_le_power_contraction
    N M alpha beta c 3 hadm hpower

/-- The first `n` cubic contractions, with an explicit physical cutoff at every
stage. -/
def PrimeSieveStateDependentSelbergFiniteCubicScaleChain
    (M : Nat -> Nat) (c : Real) (a : Nat -> Real) : Nat -> Prop
  | 0 => True
  | n + 1 =>
      PrimeSieveStateDependentSelbergFiniteCubicScaleChain M c a n ∧
        PrimeSieveStateDependentSelbergCubicGainFromTo
          (M n) (M (n + 1)) (a n) c

/-- **Effective persistence.**  A finite moving-cutoff gain chain produces a
true PNT tail at every target depth, with exactly the cutoff recorded by the
chain. -/
theorem primeSieveStateDependentSelberg_finite_cubic_scale_chain_persists
    (M : Nat -> Nat) (c : Real) (a : Nat -> Real)
    (hpos : forall n : Nat, 0 < a n)
    (hrec : forall n : Nat, a (n + 1) = a n - c * (a n) ^ 3)
    (htail0 : PrimeSieveStateDependentSelbergTailAbove (M 0) (a 0))
    (n : Nat)
    (hgain : PrimeSieveStateDependentSelbergFiniteCubicScaleChain M c a n) :
    PrimeSieveStateDependentSelbergTailAbove (M n) (a n) := by
  revert hgain
  induction n with
  | zero =>
      intro _
      exact htail0
  | succ n ih =>
      intro hgain
      change
        PrimeSieveStateDependentSelbergFiniteCubicScaleChain M c a n ∧
          PrimeSieveStateDependentSelbergCubicGainFromTo
            (M n) (M (n + 1)) (a n) c at hgain
      rcases hgain with ⟨hprev, hstepGain⟩
      have htailn := ih hprev
      have hnext : 0 < a n - c * (a n) ^ 3 := by
        simpa [hrec n] using hpos (n + 1)
      have hstep := primeSieveStateDependentSelberg_cubicGainFromTo_step
        (M n) (M (n + 1)) (a n) c htailn hstepGain hnext
      rw [hrec n]
      exact hstep

/-- The scalar reciprocal-square budget and the moving-cutoff persistence chain
combine without any affine globalization. -/
theorem primeSieveStateDependentSelberg_tail_le_eta_of_cubic_scale_budget
    (M : Nat -> Nat) (c eta : Real) (a : Nat -> Real)
    (hc : 0 <= c) (heta : 0 < eta)
    (hpos : forall n : Nat, 0 < a n)
    (hrec : forall n : Nat, a (n + 1) = a n - c * (a n) ^ 3)
    (htail0 : PrimeSieveStateDependentSelbergTailAbove (M 0) (a 0))
    (n : Nat)
    (hgain : PrimeSieveStateDependentSelbergFiniteCubicScaleChain M c a n)
    (hbudget : 1 < 2 * c * (n : Real) * eta ^ 2) :
    forall N : Nat, M n <= N ->
      |nativePNTError N| <= eta * (N : Real) := by
  have hrec_le : forall j : Nat,
      a (j + 1) <= a j - c * (a j) ^ 3 := by
    intro j
    rw [hrec j]
  have haeta : a n <= eta :=
    cubic_contraction_inequality_le_eta_of_budget
      a c eta hc heta hpos hrec_le n hbudget
  have htailn :=
    primeSieveStateDependentSelberg_finite_cubic_scale_chain_persists
      M c a hpos hrec htail0 n hgain
  intro N hMN
  have hbound := htailn.2.2 N hMN
  exact hbound.trans
    (mul_le_mul_of_nonneg_right haeta (by positivity))

/-- Small target slopes have physical cutoffs of quadratic reciprocal size. -/
def NativePNTQuadraticTailScaleLaw (K : Real) : Prop :=
  0 < K ∧ forall eta : Real, 0 < eta -> eta <= 1 ->
    ∃ M : Nat,
      (M : Real) * eta ^ 2 <= K ∧
      (forall N : Nat, M <= N ->
        |nativePNTError N| <= eta * (N : Real))

/-- The exact arithmetic target for the generalized cubic engine: for each
small `eta`, exhibit a finite moving-cutoff contraction chain whose terminal
physical scale is `O(eta^(-2))`. -/
def PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw
    (K c : Real) : Prop :=
  0 < K ∧ 0 <= c ∧
    forall eta : Real, 0 < eta -> eta <= 1 ->
      ∃ M : Nat -> Nat, ∃ a : Nat -> Real, ∃ n : Nat,
        ((M n : Nat) : Real) * eta ^ 2 <= K ∧
        (forall j : Nat, 0 < a j) ∧
        (forall j : Nat, a (j + 1) = a j - c * (a j) ^ 3) ∧
        PrimeSieveStateDependentSelbergTailAbove (M 0) (a 0) ∧
        PrimeSieveStateDependentSelbergFiniteCubicScaleChain M c a n ∧
        1 < 2 * c * (n : Real) * eta ^ 2

theorem nativePNTQuadraticTailScaleLaw_of_stateDependentCubicGain
    (K c : Real)
    (hlaw : PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw K c) :
    NativePNTQuadraticTailScaleLaw K := by
  rcases hlaw with ⟨hK, hc, hlaw⟩
  refine ⟨hK, ?_⟩
  intro eta heta heta1
  rcases hlaw eta heta heta1 with
    ⟨M, a, n, hscale, hpos, hrec, htail0, hgain, hbudget⟩
  refine ⟨M n, hscale, ?_⟩
  exact primeSieveStateDependentSelberg_tail_le_eta_of_cubic_scale_budget
    M c eta a hc heta hpos hrec htail0 n hgain hbudget

/-- **Bound-changing theorem.**  Quadratic terminal cutoff growth in the small
target slope implies square-root Chebyshev error beyond the fixed scale `K`. -/
theorem nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw
    (K : Real) (hlaw : NativePNTQuadraticTailScaleLaw K)
    (N : Nat) (hN : 1 <= N) (hKN : K <= (N : Real)) :
    |nativePNTError N| <= Real.sqrt (K * (N : Real)) := by
  rcases hlaw with ⟨hK, hlaw⟩
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  let eta : Real := Real.sqrt (K / (N : Real))
  have hratio : 0 < K / (N : Real) := div_pos hK hNR
  have heta : 0 < eta := by
    dsimp [eta]
    exact Real.sqrt_pos.2 hratio
  have heta_sq : eta ^ 2 = K / (N : Real) := by
    dsimp [eta]
    exact Real.sq_sqrt hratio.le
  have hratio1 : K / (N : Real) <= 1 := (div_le_one hNR).2 hKN
  have heta1 : eta <= 1 := by
    dsimp [eta]
    calc
      Real.sqrt (K / (N : Real)) <= Real.sqrt 1 :=
        Real.sqrt_le_sqrt hratio1
      _ = 1 := by norm_num
  rcases hlaw eta heta heta1 with ⟨M, hscale, htail⟩
  have hetaN : eta ^ 2 * (N : Real) = K := by
    rw [heta_sq]
    field_simp [ne_of_gt hNR]
  have hmul := mul_le_mul_of_nonneg_right hscale hNR.le
  have hKM : K * (M : Real) <= K * (N : Real) := by
    calc
      K * (M : Real) = ((M : Real) * eta ^ 2) * (N : Real) := by
        rw [mul_assoc, hetaN]
        ring
      _ <= K * (N : Real) := hmul
  have hKM' : (M : Real) * K <= (N : Real) * K := by
    simpa [mul_comm] using hKM
  have hMNreal : (M : Real) <= (N : Real) :=
    (mul_le_mul_iff_left₀ hK).mp hKM'
  have hMN : M <= N := by exact_mod_cast hMNreal
  have hbound := htail N hMN
  have hscaled_nonneg : 0 <= eta * (N : Real) :=
    mul_nonneg heta.le hNR.le
  have hscaled_sq : (eta * (N : Real)) ^ 2 = K * (N : Real) := by
    calc
      (eta * (N : Real)) ^ 2 = eta ^ 2 * (N : Real) ^ 2 := by ring
      _ = (K / (N : Real)) * (N : Real) ^ 2 := by rw [heta_sq]
      _ = K * (N : Real) := by field_simp [ne_of_gt hNR]
  have hscaled_sqrt :
      eta * (N : Real) = Real.sqrt (K * (N : Real)) := by
    calc
      eta * (N : Real) = Real.sqrt ((eta * (N : Real)) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hscaled_nonneg]
      _ = Real.sqrt (K * (N : Real)) := by rw [hscaled_sq]
  rw [hscaled_sqrt] at hbound
  exact hbound

theorem nativePNTError_abs_le_sqrt_of_stateDependentCubicGain
    (K c : Real)
    (hlaw : PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw K c)
    (N : Nat) (hN : 1 <= N) (hKN : K <= (N : Real)) :
    |nativePNTError N| <= Real.sqrt (K * (N : Real)) := by
  exact nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw K
    (nativePNTQuadraticTailScaleLaw_of_stateDependentCubicGain K c hlaw)
    N hN hKN

end RHLean.Analysis
