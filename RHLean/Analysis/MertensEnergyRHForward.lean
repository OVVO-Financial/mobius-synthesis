import Mathlib
import RHLean.Analysis.MertensZetaIdentityContinuation
import RHLean.Analysis.PhysicalCenteredDistinguishedPrimeOperator
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Proof.HeightShellGram

/-!
# The forward Mertens-energy implication to the Riemann hypothesis

The first half closes the protected Mertens-energy-to-RH implication.  The
second half records the centered distinguished-prime global Gram route: exact
physical prime-family reconstruction first, then the signed diagonal and all
cross-prime terms.  No absolute value is taken before the `q,q'` sum is formed.
-/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace RHLean.Analysis

open Complex
open RestrictedPrimeTransitionOperator
open RHLean.Proof

/-- The propagated reciprocal identity rules out zeta zeros strictly to the
right of the critical line. -/
theorem riemannZeta_ne_zero_of_half_lt_re
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : (1 : ℝ) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hprod :=
    riemannZeta_mul_mertensMellinContinuation_eq_one_of_half_lt_re
      hM hs hs1
  rw [hz, zero_mul] at hprod
  exact zero_ne_one hprod

private theorem GammaR_ne_zero_of_not_trivial
    {s : ℂ} (hs0 : s ≠ 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    Gammaℝ s ≠ 0 := by
  intro hGamma
  rcases Gammaℝ_eq_zero_iff.mp hGamma with ⟨n, hn⟩
  cases n with
  | zero =>
      apply hs0
      simpa using hn
  | succ n =>
      apply htriv
      refine ⟨n, ?_⟩
      simpa [Nat.cast_succ] using hn

/-- The repository's squared Mertens-energy criterion implies Mathlib's formal
Riemann hypothesis. -/
theorem riemannHypothesis_of_mertensEnergy
    (hM : MertensEnergyBoundedStatement) :
    RiemannHypothesis := by
  intro s hz hnontriv hs1
  by_cases hcrit : s.re = (1 : ℝ) / 2
  · exact hcrit
  have hnotRight : ¬(1 : ℝ) / 2 < s.re := by
    intro hright
    exact (riemannZeta_ne_zero_of_half_lt_re hM hright hs1) hz
  have hleft : s.re < (1 : ℝ) / 2 := by
    exact lt_of_le_of_ne (le_of_not_gt hnotRight) hcrit
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hGamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_trivial hs0 hnontriv
  have hcompleted : completedRiemannZeta s = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    have hdiv : completedRiemannZeta s / Gammaℝ s = 0 := by
      rw [← hdef, hz]
    simpa [hGamma] using hdiv
  have hrefCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub s, hcompleted]
  have href0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    exact (sub_eq_zero.mp h).symm
  have hrefZeta : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero href0, hrefCompleted]
    simp
  have hrefRe : (1 : ℝ) / 2 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have href1 : 1 - s ≠ 1 := by
    intro h
    exact hs0 (sub_eq_self.mp h)
  exfalso
  exact (riemannZeta_ne_zero_of_half_lt_re hM hrefRe href1) hrefZeta

/-! ## Global centered distinguished-prime reconstruction -/

/-- Canonical distinguished transport primes `R < q <= R^2 - 1`. -/
def centeredDistinguishedPrimeSet (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime

/-- Zero in the certified thirteen-coefficient operator class. -/
def zeroRestrictedPrimeTransitionOperator : RestrictedPrimeTransitionOperator where
  inactiveInactive := 0
  inactiveToActive := fun _ => 0
  activeToInactive := fun _ => 0

@[simp] theorem zeroRestrictedPrimeTransitionOperator_action
    (x : SignedPrimeHitState → ℂ) (s : SignedPrimeHitState) :
    zeroRestrictedPrimeTransitionOperator.action x s = 0 := by
  rcases s with _ | s <;>
    simp [zeroRestrictedPrimeTransitionOperator,
      RestrictedPrimeTransitionOperator.action,
      RestrictedPrimeTransitionOperator.activeInputForm]

/-- Physical centered fixed-prime channel, totalized by zero off the canonical
transport-prime set. -/
def physicalCenteredDistinguishedPrimeChannel
    (R q : ℕ) : RestrictedPrimeTransitionOperator :=
  if hq : q ∈ centeredDistinguishedPrimeSet R then
    let hfilter := Finset.mem_filter.mp hq
    let hIoc := Finset.mem_Ioc.mp hfilter.1
    physicalCenteredDistinguishedPrimeOperator R q hfilter.2 hIoc.1
  else
    zeroRestrictedPrimeTransitionOperator

@[simp] theorem physicalCenteredDistinguishedPrimeChannel_eq_zero_of_not_mem
    (R q : ℕ) (hq : q ∉ centeredDistinguishedPrimeSet R) :
    physicalCenteredDistinguishedPrimeChannel R q =
      zeroRestrictedPrimeTransitionOperator := by
  simp [physicalCenteredDistinguishedPrimeChannel, hq]

/-- Canonical transport primes lie in the complete-square natural range. -/
theorem centeredDistinguishedPrimeSet_subset_range (R : ℕ) :
    centeredDistinguishedPrimeSet R ⊆
      Finset.range (squareRootEndpoint R + 1) := by
  intro q hq
  have hIoc := (Finset.mem_filter.mp hq).1
  have hqX := (Finset.mem_Ioc.mp hIoc).2
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hqX)

/-- Coefficientwise finite sum in the restricted operator class. -/
def restrictedPrimeOperatorSum
    (S : Finset ℕ)
    (A : ℕ → RestrictedPrimeTransitionOperator) :
    RestrictedPrimeTransitionOperator where
  inactiveInactive := ∑ q ∈ S, (A q).inactiveInactive
  inactiveToActive := fun t => ∑ q ∈ S, (A q).inactiveToActive t
  activeToInactive := fun s => ∑ q ∈ S, (A q).activeToInactive s

/-- Global physical centered operator at scale `R`. -/
def globalPhysicalCenteredDistinguishedPrimeOperator
    (R : ℕ) : RestrictedPrimeTransitionOperator :=
  restrictedPrimeOperatorSum (centeredDistinguishedPrimeSet R)
    (physicalCenteredDistinguishedPrimeChannel R)

/-- **Exact global reconstruction**
`A_R^c = sum_{R<q<=R^2-1, q prime} A^c_{R,q}` before any norm. -/
theorem globalPhysicalCenteredDistinguishedPrimeOperator_reconstruction
    (R : ℕ) :
    globalPhysicalCenteredDistinguishedPrimeOperator R =
      restrictedPrimeOperatorSum (centeredDistinguishedPrimeSet R)
        (physicalCenteredDistinguishedPrimeChannel R) := rfl

@[simp] theorem globalPhysicalCenteredDistinguishedPrimeOperator_inactiveInactive
    (R : ℕ) :
    (globalPhysicalCenteredDistinguishedPrimeOperator R).inactiveInactive =
      ∑ q ∈ centeredDistinguishedPrimeSet R,
        (physicalCenteredDistinguishedPrimeChannel R q).inactiveInactive := rfl

@[simp] theorem globalPhysicalCenteredDistinguishedPrimeOperator_inactiveToActive
    (R : ℕ) (t : PrimeActiveLabel) :
    (globalPhysicalCenteredDistinguishedPrimeOperator R).inactiveToActive t =
      ∑ q ∈ centeredDistinguishedPrimeSet R,
        (physicalCenteredDistinguishedPrimeChannel R q).inactiveToActive t := rfl

@[simp] theorem globalPhysicalCenteredDistinguishedPrimeOperator_activeToInactive
    (R : ℕ) (s : PrimeActiveLabel) :
    (globalPhysicalCenteredDistinguishedPrimeOperator R).activeToInactive s =
      ∑ q ∈ centeredDistinguishedPrimeSet R,
        (physicalCenteredDistinguishedPrimeChannel R q).activeToInactive s := rfl

/-- One output coordinate of one centered fixed-prime action. -/
def centeredDistinguishedPrimeActionCoordinateShell
    (R : ℕ) (x : SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) (q : ℕ) : ℂ :=
  (physicalCenteredDistinguishedPrimeChannel R q).action x s

/-- One output coordinate after the complete distinguished-prime family has
been assembled. -/
def globalCenteredDistinguishedPrimeActionCoordinate
    (R : ℕ) (x : SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) : ℂ :=
  heightShellSum
    (centeredDistinguishedPrimeActionCoordinateShell R x s)
    (squareRootEndpoint R + 1)

/-- Action-level exact reconstruction over the physical prime set. -/
theorem globalCenteredDistinguishedPrimeActionCoordinate_reconstruction
    (R : ℕ) (x : SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) :
    globalCenteredDistinguishedPrimeActionCoordinate R x s =
      ∑ q ∈ centeredDistinguishedPrimeSet R,
        (physicalCenteredDistinguishedPrimeChannel R q).action x s := by
  classical
  unfold globalCenteredDistinguishedPrimeActionCoordinate heightShellSum
    centeredDistinguishedPrimeActionCoordinateShell
  symm
  apply Finset.sum_subset (centeredDistinguishedPrimeSet_subset_range R)
  intro q _hqRange hqNot
  rw [physicalCenteredDistinguishedPrimeChannel_eq_zero_of_not_mem R q hqNot]
  exact zeroRestrictedPrimeTransitionOperator_action x s

/-- Complete global centered action, assembled before any energy. -/
def globalCenteredDistinguishedPrimeAction
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    SignedPrimeHitState → ℂ :=
  fun s => globalCenteredDistinguishedPrimeActionCoordinate R x s

/-- Unit-weight energy after the complete `q` sum is assembled. -/
def globalCenteredDistinguishedPrimeEnergyAt
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  ‖globalCenteredDistinguishedPrimeAction R x none‖ ^ 2 +
    ∑ s : PrimeActiveLabel,
      ‖globalCenteredDistinguishedPrimeAction R x (some s)‖ ^ 2

/-- Complex signed cross-prime Gram entry
`G_R(q,q') = <A^c_{R,q}x, A^c_{R,q'}x>`. -/
def centeredCrossQGram
    (R q q' : ℕ)
    (x : SignedPrimeHitState → ℂ) : ℂ :=
  restrictedPrimeStateInner
    ((physicalCenteredDistinguishedPrimeChannel R q).action x)
    ((physicalCenteredDistinguishedPrimeChannel R q').action x)

/-- Exact sparse coefficient expansion of one cross-prime Gram entry. -/
theorem centeredCrossQGram_eq_sparseAction
    (R q q' : ℕ)
    (x : SignedPrimeHitState → ℂ) :
    centeredCrossQGram R q q' x =
      star ((physicalCenteredDistinguishedPrimeChannel R q).inactiveInactive *
          x none +
        (physicalCenteredDistinguishedPrimeChannel R q).activeInputForm x) *
      ((physicalCenteredDistinguishedPrimeChannel R q').inactiveInactive *
          x none +
        (physicalCenteredDistinguishedPrimeChannel R q').activeInputForm x) +
      ∑ s : PrimeActiveLabel,
        star ((physicalCenteredDistinguishedPrimeChannel R q).activeToInactive s *
            x none) *
          ((physicalCenteredDistinguishedPrimeChannel R q').activeToInactive s *
            x none) := by
  rfl

/-- Diagonal part of the exact global Gram. -/
def globalCenteredDistinguishedPrimeDiagonalEnergyAt
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  heightShellDiagonalEnergy
      (centeredDistinguishedPrimeActionCoordinateShell R x none)
      (squareRootEndpoint R + 1) +
    ∑ s : PrimeActiveLabel,
      heightShellDiagonalEnergy
        (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
        (squareRootEndpoint R + 1)

/-- Signed off-diagonal part of the exact global Gram. -/
def globalCenteredDistinguishedPrimeOffDiagonalGramAt
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  heightShellOffDiagonalGram (𝕜 := ℂ)
      (centeredDistinguishedPrimeActionCoordinateShell R x none)
      (squareRootEndpoint R + 1) +
    ∑ s : PrimeActiveLabel,
      heightShellOffDiagonalGram (𝕜 := ℂ)
        (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
        (squareRootEndpoint R + 1)

/-- Exact global energy identity before rewriting the pieces as cross-prime
Gram sums. -/
theorem globalCenteredDistinguishedPrimeEnergyAt_eq_diagonal_add_offDiagonal
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeEnergyAt R x =
      globalCenteredDistinguishedPrimeDiagonalEnergyAt R x +
        2 * globalCenteredDistinguishedPrimeOffDiagonalGramAt R x := by
  unfold globalCenteredDistinguishedPrimeEnergyAt
    globalCenteredDistinguishedPrimeAction
    globalCenteredDistinguishedPrimeActionCoordinate
    globalCenteredDistinguishedPrimeDiagonalEnergyAt
    globalCenteredDistinguishedPrimeOffDiagonalGramAt
  rw [energy_sum_heightShells (𝕜 := ℂ)]
  simp_rw [energy_sum_heightShells (𝕜 := ℂ)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem re_star_mul_self_eq_norm_sq (z : ℂ) :
    (star z * z).re = ‖z‖ ^ 2 := by
  calc
    (star z * z).re = Complex.normSq z := by
      change (conj z * z).re = Complex.normSq z
      rw [← Complex.normSq_eq_conj_mul_self]
      simp
    _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z

private theorem re_primeActive_sum (f : PrimeActiveLabel → ℂ) :
    (∑ s : PrimeActiveLabel, f s).re =
      ∑ s : PrimeActiveLabel, (f s).re := by
  exact map_sum (RCLike.re : ℂ →+ ℝ) f
    (Finset.univ : Finset PrimeActiveLabel)

private theorem re_add_primeActive_sum (z : ℂ) (f : PrimeActiveLabel → ℂ) :
    (z + ∑ s : PrimeActiveLabel, f s).re =
      z.re + ∑ s : PrimeActiveLabel, (f s).re := by
  change z.re + (∑ s : PrimeActiveLabel, f s).re = _
  rw [re_primeActive_sum]

private theorem centeredCrossQGram_re_eq_coordinates
    (R q q' : ℕ) (x : SignedPrimeHitState → ℂ) :
    (centeredCrossQGram R q q' x).re =
      (star ((physicalCenteredDistinguishedPrimeChannel R q).action x none) *
        (physicalCenteredDistinguishedPrimeChannel R q').action x none).re +
      ∑ s : PrimeActiveLabel,
        (star ((physicalCenteredDistinguishedPrimeChannel R q).action x (some s)) *
          (physicalCenteredDistinguishedPrimeChannel R q').action x (some s)).re := by
  unfold centeredCrossQGram restrictedPrimeStateInner
  exact re_add_primeActive_sum _ _

private theorem shellReInner_complex_eq (z w : ℂ) :
    shellReInner (𝕜 := ℂ) z w = (star z * w).re := by
  unfold shellReInner
  rw [RCLike.inner_apply']
  rfl

/-- Diagonal coordinate energy is exactly the sum of self-Gram entries. -/
theorem globalCenteredDistinguishedPrimeDiagonalEnergyAt_eq_crossQ
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeDiagonalEnergyAt R x =
      ∑ q ∈ Finset.range (squareRootEndpoint R + 1),
        (centeredCrossQGram R q q x).re := by
  classical
  unfold globalCenteredDistinguishedPrimeDiagonalEnergyAt
    heightShellDiagonalEnergy centeredDistinguishedPrimeActionCoordinateShell
  simp_rw [centeredCrossQGram_re_eq_coordinates]
  simp_rw [re_star_mul_self_eq_norm_sq]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

/-- The off-diagonal coordinate form is exactly the nested `q < q'` sum of
real cross-prime Gram entries. -/
theorem globalCenteredDistinguishedPrimeOffDiagonalGramAt_eq_crossQ
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeOffDiagonalGramAt R x =
      ∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
        ∑ q ∈ Finset.range q',
          (centeredCrossQGram R q q' x).re := by
  classical
  unfold globalCenteredDistinguishedPrimeOffDiagonalGramAt
    heightShellOffDiagonalGram centeredDistinguishedPrimeActionCoordinateShell
  simp_rw [shellReInner_complex_eq]
  simp_rw [centeredCrossQGram_re_eq_coordinates]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q' _hq'
  rw [Finset.sum_comm]

/-- **Exact requested cross-prime expansion.**  Every off-diagonal interaction
is part of the main signed object. -/
theorem globalCenteredDistinguishedPrimeEnergyAt_eq_crossQGram
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeEnergyAt R x =
      (∑ q ∈ Finset.range (squareRootEndpoint R + 1),
        (centeredCrossQGram R q q x).re) +
      2 *
        (∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
          ∑ q ∈ Finset.range q',
            (centeredCrossQGram R q q' x).re) := by
  rw [globalCenteredDistinguishedPrimeEnergyAt_eq_diagonal_add_offDiagonal,
    globalCenteredDistinguishedPrimeDiagonalEnergyAt_eq_crossQ,
    globalCenteredDistinguishedPrimeOffDiagonalGramAt_eq_crossQ]

/-! ## First global signed cross-prime Gram bound -/

/-- Cauchy is applied only after one complete scalar coordinate has been summed
over the whole distinguished-prime range.  Thus this estimate never replaces
the signed `q,q'` Gram by a sum of absolute pairwise Gram entries. -/
private theorem complexHeightShellEnergy_le_card_mul_diagonal
    (shell : ℕ → ℂ) (n : ℕ) :
    ‖heightShellSum shell n‖ ^ 2 ≤
      (n : ℝ) * heightShellDiagonalEnergy shell n := by
  unfold heightShellSum heightShellDiagonalEnergy
  have hnorm :
      ‖∑ i ∈ Finset.range n, shell i‖ ≤
        ∑ i ∈ Finset.range n, ‖shell i‖ := by
    exact norm_sum_le (Finset.range n) shell
  have hsq :
      ‖∑ i ∈ Finset.range n, shell i‖ ^ 2 ≤
        (∑ i ∈ Finset.range n, ‖shell i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcauchy :=
    Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.range n) (fun _ => (1 : ℝ)) (fun i => ‖shell i‖)
  have hcauchy' :
      (∑ i ∈ Finset.range n, ‖shell i‖) ^ 2 ≤
        (n : ℝ) * ∑ i ∈ Finset.range n, ‖shell i‖ ^ 2 := by
    simpa using hcauchy
  exact hsq.trans hcauchy'

/-- **Unconditional global signed Gram baseline.**  The complete `q` family is
assembled first in every one of the seven physical output coordinates.  Only
then is finite Cauchy applied.  Consequently all cross-prime signs survive up
to the single global norm, and the exact price of a sign-blind fallback is the
number of natural prime slots, `R^2` at a complete-square endpoint. -/
theorem globalCenteredDistinguishedPrimeEnergyAt_le_range_mul_diagonal
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeEnergyAt R x ≤
      ((squareRootEndpoint R + 1 : ℕ) : ℝ) *
        globalCenteredDistinguishedPrimeDiagonalEnergyAt R x := by
  unfold globalCenteredDistinguishedPrimeEnergyAt
    globalCenteredDistinguishedPrimeAction
    globalCenteredDistinguishedPrimeActionCoordinate
    globalCenteredDistinguishedPrimeDiagonalEnergyAt
  have hnone :=
    complexHeightShellEnergy_le_card_mul_diagonal
      (centeredDistinguishedPrimeActionCoordinateShell R x none)
      (squareRootEndpoint R + 1)
  have hactive :
      (∑ s : PrimeActiveLabel,
          ‖heightShellSum
            (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
            (squareRootEndpoint R + 1)‖ ^ 2) ≤
        ∑ s : PrimeActiveLabel,
          ((squareRootEndpoint R + 1 : ℕ) : ℝ) *
            heightShellDiagonalEnergy
              (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
              (squareRootEndpoint R + 1) := by
    apply Finset.sum_le_sum
    intro s _hs
    exact complexHeightShellEnergy_le_card_mul_diagonal
      (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
      (squareRootEndpoint R + 1)
  calc
    ‖heightShellSum
        (centeredDistinguishedPrimeActionCoordinateShell R x none)
        (squareRootEndpoint R + 1)‖ ^ 2 +
        ∑ s : PrimeActiveLabel,
          ‖heightShellSum
            (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
            (squareRootEndpoint R + 1)‖ ^ 2 ≤
      ((squareRootEndpoint R + 1 : ℕ) : ℝ) *
          heightShellDiagonalEnergy
            (centeredDistinguishedPrimeActionCoordinateShell R x none)
            (squareRootEndpoint R + 1) +
        ∑ s : PrimeActiveLabel,
          ((squareRootEndpoint R + 1 : ℕ) : ℝ) *
            heightShellDiagonalEnergy
              (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
              (squareRootEndpoint R + 1) :=
        add_le_add hnone hactive
    _ = ((squareRootEndpoint R + 1 : ℕ) : ℝ) *
        (heightShellDiagonalEnergy
            (centeredDistinguishedPrimeActionCoordinateShell R x none)
            (squareRootEndpoint R + 1) +
          ∑ s : PrimeActiveLabel,
            heightShellDiagonalEnergy
              (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
              (squareRootEndpoint R + 1)) := by
      rw [← Finset.mul_sum]
      ring

/-- At every nonzero square scale the natural shell count is exactly `R^2`, so
the preceding baseline exposes an exact quadratic Cauchy loss.  Any proof of the
critical `R^(2+epsilon)` theorem must recover essentially this whole factor from
the signed cross-`q` term rather than paying it. -/
theorem globalCenteredDistinguishedPrimeEnergyAt_le_square_mul_diagonal
    (R : ℕ) (hR : 1 ≤ R) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeEnergyAt R x ≤
      (R : ℝ) ^ 2 * globalCenteredDistinguishedPrimeDiagonalEnergyAt R x := by
  have hbound := globalCenteredDistinguishedPrimeEnergyAt_le_range_mul_diagonal R x
  have hRsqOne : 1 ≤ R ^ 2 := by
    have hp := Nat.pow_le_pow_left hR 2
    norm_num at hp ⊢
    exact hp
  have hendpoint : squareRootEndpoint R + 1 = R ^ 2 := by
    unfold squareRootEndpoint
    exact Nat.sub_add_cancel hRsqOne
  simpa [hendpoint] using hbound

/-- The same result written directly on the already-formalized exact signed
cross-prime Gram.  No absolute value appears on the off-diagonal sum. -/
theorem globalCenteredDistinguishedPrimeCrossQGram_le_square_mul_diagonal
    (R : ℕ) (hR : 1 ≤ R) (x : SignedPrimeHitState → ℂ) :
    (∑ q ∈ Finset.range (squareRootEndpoint R + 1),
        (centeredCrossQGram R q q x).re) +
      2 *
        (∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
          ∑ q ∈ Finset.range q',
            (centeredCrossQGram R q q' x).re) ≤
      (R : ℝ) ^ 2 *
        (∑ q ∈ Finset.range (squareRootEndpoint R + 1),
          (centeredCrossQGram R q q x).re) := by
  calc
    (∑ q ∈ Finset.range (squareRootEndpoint R + 1),
        (centeredCrossQGram R q q x).re) +
      2 *
        (∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
          ∑ q ∈ Finset.range q',
            (centeredCrossQGram R q q' x).re) =
      globalCenteredDistinguishedPrimeEnergyAt R x :=
        (globalCenteredDistinguishedPrimeEnergyAt_eq_crossQGram R x).symm
    _ ≤ (R : ℝ) ^ 2 *
        globalCenteredDistinguishedPrimeDiagonalEnergyAt R x :=
      globalCenteredDistinguishedPrimeEnergyAt_le_square_mul_diagonal R hR x
    _ = (R : ℝ) ^ 2 *
        (∑ q ∈ Finset.range (squareRootEndpoint R + 1),
          (centeredCrossQGram R q q x).re) := by
      rw [globalCenteredDistinguishedPrimeDiagonalEnergyAt_eq_crossQ]

/-- Open analytic proposition at the critical square-root exponent. -/
def CenteredDistinguishedPrimeGlobalGramBoundedStatement
    (x : ℕ → SignedPrimeHitState → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        globalCenteredDistinguishedPrimeEnergyAt R (x R) ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- Exact arithmetic theorem data needed to identify a chosen global centered
input family with square-prefix Mertens energy. -/
structure CenteredDistinguishedPrimeMertensReconstruction
    (x : ℕ → SignedPrimeHitState → ℂ) : Prop where
  energy_eq_squarePrefix :
    ∀ n : ℕ, 1 ≤ n →
      globalCenteredDistinguishedPrimeEnergyAt (n + 1) (x (n + 1)) =
        ‖squarePrefixMertens n‖ ^ 2

/-- Exact reconstruction plus the global Gram estimate gives the protected
square-prefix criterion. -/
theorem squarePrefixEnergyBounded_of_centeredDistinguishedPrimeGlobalGram
    {x : ℕ → SignedPrimeHitState → ℂ}
    (hrecon : CenteredDistinguishedPrimeMertensReconstruction x)
    (hgram : CenteredDistinguishedPrimeGlobalGramBoundedStatement x) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hgram ε hε
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [squarePrefixMertens, squarePrefixEndpoint, mertensSummatory] using hC
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hR : 2 ≤ n + 1 := by omega
    rw [← hrecon.energy_eq_squarePrefix n hn1]
    exact hbound (n + 1) hR

/-- Protected terminal through the existing square-prefix and Mertens chain. -/
theorem riemannHypothesis_of_centeredDistinguishedPrimeGlobalGram
    {x : ℕ → SignedPrimeHitState → ℂ}
    (hrecon : CenteredDistinguishedPrimeMertensReconstruction x)
    (hgram : CenteredDistinguishedPrimeGlobalGramBoundedStatement x) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  apply mertensEnergyBounded_of_squarePrefixEnergyBounded
  exact squarePrefixEnergyBounded_of_centeredDistinguishedPrimeGlobalGram
    hrecon hgram

end RHLean.Analysis
