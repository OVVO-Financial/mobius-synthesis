import Mathlib
import RHLean.Analysis.DynamicVioleBaseline
import RHLean.Analysis.NativePNTSquarePrefixTailGeometry
import RHLean.Proof.NearOrthogonality

/-!
# Original parameter-free Viole function

This module formalizes the original Viole Function exactly as published.  It
has no fitted coefficients and does not use `pi(x)` as an input.

For a real input `x`, set

```text
N(x) = floor(sqrt(x))^2,
t(x) = log_10(x),
C(x) = (1 + 1 / t(x))^(1 + t(x)).
```

The continuous core of the original estimator is

```text
VF(x) = N(x) / log(N(x) / C(x)).
```

The published R implementation then applies `floor` and truncates below at
zero.  The dynamic object is the parameter-free correction `C(x)`, not a pair
of calibrated coefficients.

The same estimator has an implied logarithmic base.  Its normalized form is

```text
log b_VF(x) = 1 / (1 - log(C(x)) / log(N(x))).
```

Consequently, once the correction ratio tends to zero, the implied base tends
to `exp 1 = e`.  The final theorem below isolates this elementary analytic
step from the separate limit proofs for the Euler sequence and square-floor
numerator.
-/

noncomputable section

open Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Base-ten logarithm written by change of base. -/
def originalVFLog10 (x : ℝ) : ℝ :=
  Real.log x / Real.log 10

/-- The squared floor of the square root used by the published VF numerator. -/
def originalVFSquareNumerator (x : ℝ) : ℝ :=
  ((Nat.floor (Real.sqrt x) : ℕ) : ℝ) ^ 2

/-- The parameter-free Euler correction from the original VF. -/
def originalVFEulerCorrection (x : ℝ) : ℝ :=
  let t := originalVFLog10 x
  Real.rpow (1 + 1 / t) (1 + t)

/-- The natural-log denominator appearing in the original VF. -/
def originalVFDenominator (x : ℝ) : ℝ :=
  Real.log (originalVFSquareNumerator x / originalVFEulerCorrection x)

/-- The continuous core of the published estimator, before flooring and
truncation at zero. -/
def originalVFContinuous (x : ℝ) : ℝ :=
  originalVFSquareNumerator x / originalVFDenominator x

/-- The exact integer-valued post-processing used in the published R code. -/
def originalVF (x : ℝ) : ℕ :=
  Nat.floor (max 0 (originalVFContinuous x))

/-- Ratio controlling the implied dynamic logarithmic base. -/
def originalVFCorrectionRatio (x : ℝ) : ℝ :=
  Real.log (originalVFEulerCorrection x) /
    Real.log (originalVFSquareNumerator x)

/-- The implied logarithm of the dynamic base of the original VF. -/
def originalVFImpliedLogBase (x : ℝ) : ℝ :=
  1 / (1 - originalVFCorrectionRatio x)

/-- The implied dynamic logarithmic base of the original VF. -/
def originalVFImpliedBase (x : ℝ) : ℝ :=
  Real.exp (originalVFImpliedLogBase x)

/-- The original VF implied base is positive at every input. -/
theorem originalVFImpliedBase_pos (x : ℝ) :
    0 < originalVFImpliedBase x := by
  exact Real.exp_pos _

/-- The analytic final step: if the correction contributes a vanishing share
of the main logarithm, then the original VF's implied base tends to `e`. -/
theorem originalVFImpliedBase_tendsto_e
    (hRatio : Tendsto originalVFCorrectionRatio atTop (𝓝 0)) :
    Tendsto originalVFImpliedBase atTop (𝓝 (Real.exp 1)) := by
  have hcont : ContinuousAt (fun z : ℝ => Real.exp (1 / (1 - z))) 0 := by
    fun_prop (disch := norm_num)
  change Tendsto (fun x : ℝ => Real.exp (1 / (1 - originalVFCorrectionRatio x)))
    atTop (𝓝 (Real.exp 1))
  have htarget : Real.exp (1 / (1 - (0 : ℝ))) = Real.exp 1 := by
    norm_num
  simpa only [Function.comp_apply, htarget] using hcont.tendsto.comp hRatio

/-! ## Abel return for the dynamic Viole square-block correlation

The dynamic square-clock module exposes a reciprocal cofactor coordinate because
that is where a fresh prime has a literal Euler law.  The protected block,
however, is the unweighted correlation `sum mu(m) * Resp(m)`.  Exactly as in
the canonical rough critical-correlation route, finite Abel summation returns
the reciprocal prefix profile to that unweighted object without changing the
arithmetic content.
-/

/-- Reciprocal-prefix profile of the signed Viole square-block correlation. -/
def nativePNTSignedSquareBlockCorrelationReciprocalPrefix
    (N M L n : Nat) : Real :=
  inclusivePrefix
    (fun m =>
      nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m) n

/-- Multiplication by the positive cofactor recovers the literal unweighted
Möbius-response summand. -/
theorem natCast_mul_nativePNTSignedSquareBlockCorrelationReciprocalSummand
    (N M L : Nat) {m : Nat} (hm : 0 < m) :
    (m : Real) *
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m =
      (μ : ArithmeticFunction Real) m *
        nativePNTSignedSquareBlockCofactorResponse N M L m := by
  have hm0 : (m : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  unfold nativePNTSignedSquareBlockCorrelationReciprocalSummand
  change
    (m : Real) *
        ((((μ m : Int) : Real) *
          nativePNTSignedSquareBlockCofactorResponse N M L m) / (m : Real)) =
      ((μ m : Int) : Real) *
        nativePNTSignedSquareBlockCofactorResponse N M L m
  field_simp [hm0]

/-- Exact Abel reconstruction of the protected unweighted block correlation
from its reciprocal prefix profile. -/
theorem nativePNTSignedSquareBlockMobiusCorrelation_eq_abel_reciprocalPrefix
    (N M L : Nat) :
    nativePNTSignedSquareBlockMobiusCorrelation N M L =
      (L : Real) *
          nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L L -
        ∑ k ∈ Finset.range L,
          nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k := by
  let v : Nat → Real :=
    fun m => nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m
  have habel := finite_abel_identity v (fun k : Nat => (k : Real)) L
  have hleft :
      nativePNTSignedSquareBlockMobiusCorrelation N M L =
        ∑ m ∈ Finset.range (L + 1), v m * (m : Real) := by
    have hset : Finset.Icc 1 L = Finset.range (L + 1) \ {0} := by
      ext m
      simp
      omega
    rw [nativePNTSignedSquareBlockMobiusCorrelation, hset]
    have hsub : ({0} : Finset Nat) ⊆ Finset.range (L + 1) := by
      intro m hm
      simp at hm
      subst m
      simp
    have hsplit :=
      Finset.sum_sdiff hsub (f := fun m => v m * (m : Real))
    have hweighted :
        (∑ m ∈ Finset.range (L + 1) \ {0}, v m * (m : Real)) =
          ∑ m ∈ Finset.range (L + 1) \ {0},
            (μ : ArithmeticFunction Real) m *
              nativePNTSignedSquareBlockCofactorResponse N M L m := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : m ≠ 0 := by
        have hmnot : m ∉ ({0} : Finset Nat) := (Finset.mem_sdiff.mp hm).2
        simpa using hmnot
      rw [← natCast_mul_nativePNTSignedSquareBlockCorrelationReciprocalSummand
        N M L (Nat.pos_of_ne_zero hm0)]
      ring
    rw [hweighted] at hsplit
    simpa [v] using hsplit
  rw [hleft, habel]
  unfold nativePNTSignedSquareBlockCorrelationReciprocalPrefix
  simp only [inclusivePrefix]
  have hdiff : ∀ k : Nat, (k : Real) - ((k + 1 : Nat) : Real) = -1 := by
    intro k
    push_cast
    ring
  simp_rw [hdiff, mul_neg_one]
  rw [Finset.sum_neg_distrib]
  ring

/-- Abel budget of the reciprocal prefix profile. -/
def nativePNTSignedSquareBlockCorrelationReciprocalAbelBudget
    (N M L : Nat) : Real :=
  (L : Real) *
      |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L L| +
    ∑ k ∈ Finset.range L,
      |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k|

/-- The protected block correlation is bounded by the exact reciprocal-prefix
Abel profile. -/
theorem nativePNTSignedSquareBlockMobiusCorrelation_abs_le_abelBudget
    (N M L : Nat) :
    |nativePNTSignedSquareBlockMobiusCorrelation N M L| ≤
      nativePNTSignedSquareBlockCorrelationReciprocalAbelBudget N M L := by
  rw [nativePNTSignedSquareBlockMobiusCorrelation_eq_abel_reciprocalPrefix]
  unfold nativePNTSignedSquareBlockCorrelationReciprocalAbelBudget
  calc
    |(L : Real) *
          nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L L -
        ∑ k ∈ Finset.range L,
          nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k| ≤
      |(L : Real) *
          nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L L| +
        |∑ k ∈ Finset.range L,
          nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k| :=
      abs_sub _ _
    _ ≤ (L : Real) *
          |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L L| +
        ∑ k ∈ Finset.range L,
          |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k| := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (by positivity : (0 : Real) ≤ (L : Real))]
      · exact Finset.abs_sum_le_sum_abs _ _

/-- Uniform reciprocal-prefix control returns to the unweighted block with the
sharp finite Abel factor `2L`. -/
theorem nativePNTSignedSquareBlockMobiusCorrelation_abs_le_two_mul_endpoint
    (N M L : Nat) (A : Real)
    (_hA : 0 ≤ A)
    (hprefix : ∀ k ≤ L,
      |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k| ≤ A) :
    |nativePNTSignedSquareBlockMobiusCorrelation N M L| ≤
      2 * (L : Real) * A := by
  have hprofile :=
    nativePNTSignedSquareBlockMobiusCorrelation_abs_le_abelBudget N M L
  exact hprofile.trans <| by
    unfold nativePNTSignedSquareBlockCorrelationReciprocalAbelBudget
    have hend := hprefix L le_rfl
    have hsum :
        (∑ k ∈ Finset.range L,
          |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k|) ≤
          (L : Real) * A := by
      calc
        (∑ k ∈ Finset.range L,
            |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k|) ≤
          ∑ _k ∈ Finset.range L, A := by
            apply Finset.sum_le_sum
            intro k hk
            exact hprefix k (Nat.le_of_lt (Finset.mem_range.mp hk))
        _ = (L : Real) * A := by simp
    calc
      (L : Real) *
            |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L L| +
          ∑ k ∈ Finset.range L,
            |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k| ≤
        (L : Real) * A + (L : Real) * A :=
          add_le_add
            (mul_le_mul_of_nonneg_left hend (by positivity)) hsum
      _ = 2 * (L : Real) * A := by ring

/-- A large protected block forces a reciprocal-prefix excursion on which the
fresh-prime Euler law can act. -/
theorem nativePNTSignedSquareBlockMobiusCorrelation_large_forces_reciprocalPrefix
    (N M L : Nat) (A : Real) (hA : 0 ≤ A)
    (hlarge :
      2 * (L : Real) * A <
        |nativePNTSignedSquareBlockMobiusCorrelation N M L|) :
    ∃ k : Nat, k ≤ L ∧
      A < |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k| := by
  by_contra hnone
  have hprefix : ∀ k ≤ L,
      |nativePNTSignedSquareBlockCorrelationReciprocalPrefix N M L k| ≤ A := by
    intro k hk
    apply le_of_not_gt
    intro hkLarge
    apply hnone
    exact ⟨k, hk, hkLarge⟩
  have hbound :=
    nativePNTSignedSquareBlockMobiusCorrelation_abs_le_two_mul_endpoint
      N M L A hA hprefix
  exact (not_lt_of_ge hbound) hlarge

/-- Literal unweighted Möbius-response summand of the protected block. -/
def nativePNTSignedSquareBlockCorrelationSummand
    (N M L m : Nat) : Real :=
  (μ : ArithmeticFunction Real) m *
    nativePNTSignedSquareBlockCofactorResponse N M L m

/-- On the actual protected coordinate, adjoining a fresh prime gives complete
Möbius sign cancellation except for the physical response difference.  This is
the exact object whose matched-charge/survivor decomposition supplies leakage. -/
theorem nativePNTSignedSquareBlockCorrelationSummand_add_mul_freshPrime
    (N M L : Nat) {m p : Nat}
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTSignedSquareBlockCorrelationSummand N M L m +
        nativePNTSignedSquareBlockCorrelationSummand N M L (m * p) =
      (μ : ArithmeticFunction Real) m *
        (nativePNTSignedSquareBlockCofactorResponse N M L m -
          nativePNTSignedSquareBlockCofactorResponse N M L (m * p)) := by
  unfold nativePNTSignedSquareBlockCorrelationSummand
  change
    ((μ m : Int) : Real) * nativePNTSignedSquareBlockCofactorResponse N M L m +
        ((μ (m * p) : Int) : Real) *
          nativePNTSignedSquareBlockCofactorResponse N M L (m * p) =
      ((μ m : Int) : Real) *
        (nativePNTSignedSquareBlockCofactorResponse N M L m -
          nativePNTSignedSquareBlockCofactorResponse N M L (m * p))
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  ring

/-! ## Strong-induction geometry for adjacent Viole tail advancement -/

/-- A local strong-induction law for advancing a true PNT tail from cutoff `M`
to cutoff `L` with a smaller slope.  The step may use the new slope at every
strictly smaller endpoint already beyond `L`, together with the old `M`-tail. -/
def NativePNTDirectCutoffInductionLaw
    (M L : Nat) (alpha alpha' : Real) : Prop :=
  2 <= M ∧ M <= L ∧ 0 < alpha' ∧ alpha' <= alpha ∧
    forall N : Nat, L <= N ->
      (forall q : Nat, L <= q -> q < N ->
        |nativePNTError q| <= alpha' * (q : Real)) ->
      (forall q : Nat, M <= q ->
        |nativePNTError q| <= alpha * (q : Real)) ->
      |nativePNTError N| <= alpha' * (N : Real)

/-- Once the local step can use already-contracted smaller quotients, strong
induction upgrades the old true tail directly. -/
theorem nativePNTDirectCutoffInductionLaw_step
    (M L : Nat) (alpha alpha' : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hlaw : NativePNTDirectCutoffInductionLaw M L alpha alpha') :
    PrimeSieveStateDependentSelbergTailAbove L alpha' := by
  rcases hlaw with ⟨hM2, hML, halpha', _hale, hstep⟩
  rcases htail with ⟨_hM2, _halpha, htail⟩
  refine ⟨hM2.trans hML, halpha', ?_⟩
  have hall : forall N : Nat, L <= N ->
      |nativePNTError N| <= alpha' * (N : Real) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro hLN
        exact hstep N hLN
          (fun q hLq hqN => ih q hqN hLq) htail
  exact hall

/-- Divisors whose quotient lies in the old-only transition strip
`M <= N/d < L`. -/
def nativePNTDirectCutoffTransitionDivisorSet
    (N M L : Nat) : Finset Nat :=
  nativePNTSquarePrefixSmallQuotientFiberSet N L \
    nativePNTSquarePrefixSmallQuotientFiberSet N M

/-- The transition strip is exactly the moving reciprocal annulus
`N/L < d <= N/M`. -/
theorem nativePNTDirectCutoffTransitionDivisorSet_eq_Icc
    (N M L : Nat) (hM : 1 <= M) (hL : 1 <= L) (hML : M <= L) :
    nativePNTDirectCutoffTransitionDivisorSet N M L =
      Finset.Icc (N / L + 1) (N / M) := by
  rw [nativePNTDirectCutoffTransitionDivisorSet,
    nativePNTSquarePrefixSmallQuotientFiberSet_eq_Icc N L hL,
    nativePNTSquarePrefixSmallQuotientFiberSet_eq_Icc N M hM]
  have hdiv : N / L <= N / M :=
    Nat.div_le_div_left hML (by omega)
  have hNM : N / M <= N := Nat.div_le_self N M
  ext d
  simp only [Finset.mem_sdiff, Finset.mem_Icc]
  omega

/-- Equivalent quotient-space characterization of the moving transition
annulus. -/
theorem mem_nativePNTDirectCutoffTransitionDivisorSet_iff
    (N M L d : Nat) :
    d ∈ nativePNTDirectCutoffTransitionDivisorSet N M L ↔
      d ∈ Finset.Icc 1 N ∧ M <= N / d ∧ N / d < L := by
  unfold nativePNTDirectCutoffTransitionDivisorSet
    nativePNTSquarePrefixSmallQuotientFiberSet
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
  omega

/-- At the first subdoubling endpoint the moving transition annulus is empty.
This is why the adjacent-square argument needs a finite-history seed before
strong-induction propagation can take over. -/
theorem nativePNTDirectCutoffTransitionDivisorSet_endpoint_eq_empty_of_subdoubling
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTDirectCutoffTransitionDivisorSet L M L = ∅ := by
  rw [nativePNTDirectCutoffTransitionDivisorSet_eq_Icc L M L hM
    (hM.trans hML) hML]
  have hLL : L / L = 1 := Nat.div_self (by omega)
  have hLM : L / M = 1 := by
    exact Nat.div_eq_of_lt_le (by simpa using hML) (by simpa using hsub)
  rw [hLL, hLM]
  simp

/-- Every reciprocal quotient generated by a nontrivial divisor is strictly
smaller than its endpoint. -/
theorem nativePNTDirectCutoff_recursive_quotient_lt
    (N d : Nat) (hN : 1 <= N) (hd : 2 <= d) :
    N / d < N := by
  exact Nat.div_lt_self (by omega) (by omega)

/-- At a Viole adjacent-square endpoint the old-only transition strip is empty
from `r >= 3` onward. -/
theorem violeClockDirectCutoffTransition_endpoint_eq_empty
    (r : Nat) (hr : 3 <= r) :
    nativePNTDirectCutoffTransitionDivisorSet
        (violeClockCutoff (r + 1))
        (violeClockCutoff r)
        (violeClockCutoff (r + 1)) = ∅ := by
  have hM : 1 <= violeClockCutoff r := by
    unfold violeClockCutoff
    nlinarith
  exact
    nativePNTDirectCutoffTransitionDivisorSet_endpoint_eq_empty_of_subdoubling
      (violeClockCutoff r) (violeClockCutoff (r + 1)) hM
      (violeClockCutoff_le_succ r)
      (violeClockCutoff_succ_lt_two_mul r hr)

end RHLean.Analysis