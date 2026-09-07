import Mathlib
import RHLean.Analysis.DeterministicTGreenKuboComparison
import RHLean.Arithmetic.AdmissibleFaceSquarefreeImage
import RHLean.Arithmetic.PrimeFaceProductUniqueness
import RHLean.Proof.MiddlePrimeFibreCollapse

open scoped BigOperators

/-!
# Covariance capacity: record descent, and what support exhaustion still owes

`DeterministicTGreenKuboComparison` isolates the one-sided arithmetic frontier

```text
MertensPositiveLagUpperBoundedStatement :
  for every eps > 0, positiveLagPairSum K <= C * K ^ (1 + eps)
```

and proves it gives the protected Mertens energy criterion.  That target is the
right one, and it is worth being precise about its strength: the pair sum runs
over `binom(K,2)` pairs, so the trivial deterministic bound is `O(K^2)`.  A
bound `O(K)` would already give `M(x) = O(sqrt x)` outright.  What RH scale
needs is only `K^(1+eps)`, which is still a full power below the trivial bound.

Two things are recorded here.

## 1. Record descent

The excursion coordinate

```text
excursion(delta, K) = positiveLagPairSum K / K ^ (1 + delta)
```

is supercritical at `K` when it reaches `1`.  `MertensCovarianceDescentStatement`
says every supercritical scale is forced by a strictly smaller supercritical
scale.  Since the scales are natural numbers, that alone forbids a *minimal*
supercritical excursion, hence any supercritical excursion at all, hence gives
the one-sided frontier statement and the Mertens energy criterion.

This is deliberately a descent on the *signed aggregate covariance itself*.  It
never bounds `|C|` by a count of surviving pairs, and it allows every
intermediate signed correction to oscillate arbitrarily; only the normalized
excursion at the two scales is compared.

## 2. What the support-only route still owes

`MiddlePrimeFibreCollapse.norm_mertensSummatory_le_primeProductFrontierCard`
gives the exact support bound `‖M(X)‖ <= F(X, ell)` after Euler parent/child
pairing.  Once the lag-zero diagonal is kept rather than discarded, the sharp
resulting global covariance bound is

```text
C(X+1) <= (F(X,ell)^2 - Q(X+1)) / 2,
```

where `Q = sum mu(n)^2` is the exact squarefree diagonal.  The older
`F(F-1)/2` frontier maximum is a weaker consequence because `F <= Q`.

This is RH strength exactly when the exposed frontier is itself of square-root
size, which is what `PrimeProductFrontierRootScaleStatement` asks for and what
the theorem below converts into the energy criterion.

It is stated as a hypothesis because it is measured to be false for the raw
prime cube: the minimising pivot is `ell = 2`, whose frontier is the squarefree
part of the top-half window `(X/2, X]`, and its cardinality tends to
`(2/pi^2) X`.  A linear frontier still leaves a quadratic `F^2` term, so the
linear diagonal subtraction does not rescue support exhaustion.  See
`EMPIRICAL_DIAGNOSTICS.md`.

So support exhaustion alone cannot close the argument, and the next theorem has
to be a signed multi-face statement, not another cardinality statement.

## 3. The covariance bridge: what closes and what remains distinct

There are three Euler coordinates worth separating.

* The **one-face prime-product frontier** keeps the actual Mertens amplitude
  `‖M(X)‖` and replaces only the diagonal by the surviving first-failure
  population `F(X, ell)`.  This file puts that object on the same carrier as the
  global integer-order Green--Kubo covariance exactly: the difference is one
  half of the squarefree diagonal discarded by the frontier.  Restoring that
  lag-zero energy gives the sharper support bound `(F^2-Q)/2`.
* The **hierarchical terminal-correction frontier** of
  `MiddlePrimeFibreCollapse` is a different signed scalar assembled from the
  middle/top correction channel and deeper reciprocal layers.  Its covariance
  is not automatically the global pair sum.
* The **centered middle-bias residual** from `SquareRootPrimeCountGap` is the
  correct square-endpoint global carrier: it is exactly `-M(R^2-1)`.  Below we
  rewrite it into the same elementary reciprocal Euler layers and prove that,
  once the full squarefree lag-zero diagonal is used, its covariance is
  **exactly** the global covariance at the square endpoint.  No domination loss
  remains on that coordinate.

Thus `CovarianceEnvelopeDominates` is compiled below for the one-face global
frontier, while the square-root centered carrier enjoys the stronger equality
bridge.  Neither fact rescues support-only capacity: the remaining useful attack
is signed refinement/descent before absolute values, now on a carrier that is
known to be physically global.

Two thresholds also should not be conflated.  Crossing the literal `sqrt x` line
is `C(x+1) > Z(x)/2`, and `Z(x)/2 ~ (1 - 6/pi^2) x / 2 ~ 0.196 x`; that is the
threshold of the *false* Mertens conjecture, so no global bound of that shape can
be true.  The RH threshold is the strictly weaker `C(x) <= x^(1+o(1))`, and an
RH-violating excursion of exponent `eps` needs `C(x+1)` of order
`x^(1+2 eps)` — a fixed power above the target, not a constant factor.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## The normalized covariance excursion -/

/-- Aggregate positive-lag covariance at scale `K`, normalized by the critical
power `K ^ (1 + delta)`.  Reaching `1` is exactly being supercritical. -/
def mertensCovarianceExcursion (δ : ℝ) (K : ℕ) : ℝ :=
  realMertensPositiveLagPairSum K / Real.rpow (K : ℝ) (1 + δ)

/-- **No minimal supercritical covariance excursion.**

Every scale whose normalized positive-lag covariance reaches the critical
exponent is forced by a strictly smaller scale that already does.  Nothing is
assumed about how the signed corrections behave in between, and no count of
surviving pairs appears. -/
def MertensCovarianceDescentStatement : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ K : ℕ, 1 ≤ K →
    1 ≤ mertensCovarianceExcursion δ K →
      ∃ d : ℕ, 1 ≤ d ∧ d < K ∧ 1 ≤ mertensCovarianceExcursion δ d

private theorem mertensCovarianceExcursion_lt_one_aux
    (h : MertensCovarianceDescentStatement) {δ : ℝ} (hδ : 0 < δ) :
    ∀ N K : ℕ, K ≤ N → 1 ≤ K → mertensCovarianceExcursion δ K < 1 := by
  intro N
  induction N with
  | zero =>
      intro K hKN hK
      exact absurd hKN (by omega)
  | succ N ih =>
      intro K hKN hK
      by_contra hge
      push_neg at hge
      obtain ⟨d, hd1, hdK, hdex⟩ := h δ hδ K hK hge
      exact absurd hdex (not_le.mpr (ih d (by omega) hd1))

/-- **Descent kills every supercritical scale.**  A well-founded descent on the
natural-number scale leaves no supercritical excursion anywhere. -/
theorem mertensCovarianceExcursion_lt_one_of_descent
    (h : MertensCovarianceDescentStatement) {δ : ℝ} (hδ : 0 < δ)
    (K : ℕ) (hK : 1 ≤ K) :
    mertensCovarianceExcursion δ K < 1 :=
  mertensCovarianceExcursion_lt_one_aux h hδ K K le_rfl hK

/-- **Record descent gives the one-sided arithmetic frontier.** -/
theorem mertensPositiveLagUpperBounded_of_covarianceDescent
    (h : MertensCovarianceDescentStatement) :
    MertensPositiveLagUpperBoundedStatement := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro K hK
  have hlt := mertensCovarianceExcursion_lt_one_of_descent h hε K hK
  have hKnat : 0 < K := hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKnat
  have hpos : 0 < Real.rpow (K : ℝ) (1 + ε) := Real.rpow_pos_of_pos hKpos _
  unfold mertensCovarianceExcursion at hlt
  rw [div_lt_one hpos] at hlt
  linarith

/-- **Record descent gives the protected Mertens energy criterion.** -/
theorem mertensEnergyBounded_of_covarianceDescent
    (h : MertensCovarianceDescentStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_positiveLagUpperBounded
    (mertensPositiveLagUpperBounded_of_covarianceDescent h)

/-! ## What the support-only frontier route would have to supply -/

/-- Some exposed Euler frontier is of square-root size.  This is exactly the
missing input that would make the support bound `‖M(X)‖ <= F` RH strength. -/
def PrimeProductFrontierRootScaleStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 2 ≤ X →
        ∃ ell : ℕ, ell ∈ primesUpTo X ∧
          (primeProductFrontierCard X ell : ℝ) ≤
            C * Real.rpow (((X + 1 : ℕ) : ℝ)) ((1 + ε) / 2)

private theorem one_le_rpow_succ_cast {ε : ℝ} (hε : 0 < ε) (X : ℕ) :
    (1 : ℝ) ≤ Real.rpow (((X + 1 : ℕ) : ℝ)) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ (((X + 1 : ℕ) : ℝ)) := by
    have hone : (1 : ℕ) ≤ X + 1 := Nat.le_add_left 1 X
    exact_mod_cast hone
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (0 : ℝ) ≤ 1 + ε)
  simpa using h

private theorem rpow_half_sq {ε : ℝ} (B : ℝ) (hB : 0 ≤ B) :
    (Real.rpow B ((1 + ε) / 2)) ^ (2 : ℕ) = Real.rpow B (1 + ε) := by
  have hnat : (Real.rpow B ((1 + ε) / 2)) ^ (2 : ℕ) =
      Real.rpow (Real.rpow B ((1 + ε) / 2)) (((2 : ℕ) : ℝ)) :=
    (Real.rpow_natCast (Real.rpow B ((1 + ε) / 2)) 2).symm
  have hmul : Real.rpow B (((1 + ε) / 2) * ((2 : ℕ) : ℝ)) =
      Real.rpow (Real.rpow B ((1 + ε) / 2)) (((2 : ℕ) : ℝ)) :=
    Real.rpow_mul hB _ _
  have harg : ((1 + ε) / 2) * ((2 : ℕ) : ℝ) = 1 + ε := by
    push_cast
    ring
  rw [hnat, ← hmul, harg]

/-- **The exact requirement of the support-only route.**  A square-root-size
exposed Euler frontier converts the existing support bound into the Mertens
energy criterion.  Measured, the minimising frontier is linear in `X`, so this
hypothesis is where support exhaustion stops. -/
theorem mertensEnergyBounded_of_primeProductFrontierRootScale
    (h : PrimeProductFrontierRootScaleStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hfront⟩
  refine ⟨max (C ^ 2) 1, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro x
  have hBnn : (0 : ℝ) ≤ (((x + 1 : ℕ) : ℝ)) := by positivity
  have hone := one_le_rpow_succ_cast hε x
  by_cases hx : 2 ≤ x
  · obtain ⟨ell, hell, hcard⟩ := hfront x hx
    have hsupport := norm_mertensSummatory_le_primeProductFrontierCard hell
    have hle : ‖mertensSummatory x‖ ≤
        C * Real.rpow (((x + 1 : ℕ) : ℝ)) ((1 + ε) / 2) := hsupport.trans hcard
    have hsq := pow_le_pow_left₀ (norm_nonneg (mertensSummatory x)) hle 2
    have hexpand :
        (C * Real.rpow (((x + 1 : ℕ) : ℝ)) ((1 + ε) / 2)) ^ (2 : ℕ) =
          C ^ 2 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
      rw [mul_pow, rpow_half_sq (ε := ε) _ hBnn]
    rw [hexpand] at hsq
    have hmono : C ^ 2 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) ≤
        max (C ^ 2) 1 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
      have hrpow : (0 : ℝ) ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
        linarith
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hrpow
    exact hsq.trans hmono
  · have hgap := norm_mertensSummatory_sub_le 0 x (Nat.zero_le x)
    rw [mertensSummatory_zero, sub_zero, Nat.sub_zero] at hgap
    have hsmall : ‖mertensSummatory x‖ ≤ 1 := by
      have hxle : (x : ℝ) ≤ 1 := by
        have : x ≤ 1 := by omega
        exact_mod_cast this
      linarith
    have hsq := pow_le_pow_left₀ (norm_nonneg (mertensSummatory x)) hsmall 2
    have hone' : (1 : ℝ) ≤ max (C ^ 2) 1 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
      have hmax : (1 : ℝ) ≤ max (C ^ 2) 1 := le_max_right _ _
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ max (C ^ 2) 1 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) :=
            mul_le_mul hmax hone (by norm_num) (by linarith)
    calc ‖mertensSummatory x‖ ^ 2 ≤ (1 : ℝ) ^ (2 : ℕ) := hsq
      _ = 1 := one_pow 2
      _ ≤ max (C ^ 2) 1 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := hone'

/-! ## The exact one-face Euler-frontier covariance bridge -/

/-- The deterministic Möbius diagonal is exactly the number of squarefree
physical sites through `X`. -/
theorem realMertensDiagonal_eq_card_squarefreeUpTo (X : ℕ) :
    realMertensDiagonal (X + 1) = ((squarefreeUpTo X).card : ℝ) := by
  classical
  calc
    realMertensDiagonal (X + 1) =
        ∑ n ∈ Finset.range (X + 1),
          if Squarefree n then (1 : ℝ) else 0 := by
      unfold realMertensDiagonal
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hsq : Squarefree n
      · have hne : ArithmeticFunction.moebius n ≠ 0 :=
          ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
        rcases ArithmeticFunction.moebius_eq_or n with h | h | h
        · exact (hne h).elim
        · simp [realMoebiusStep, h, hsq]
        · simp [realMoebiusStep, h, hsq]
      · have hz := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        simp [realMoebiusStep, hz, hsq]
    _ = ∑ _n ∈ (Finset.range (X + 1)).filter Squarefree, (1 : ℝ) := by
      rw [Finset.sum_filter]
    _ = (((Finset.range (X + 1)).filter Squarefree).card : ℝ) := by simp
    _ = ((squarefreeUpTo X).card : ℝ) := rfl

/-- The canonical prime-face parametrization is injective, so the number of
admissible Boolean faces is exactly the number of squarefree physical sites. -/
private theorem card_admissiblePrimeFaces_eq_squarefreeUpTo (X : ℕ) :
    (admissiblePrimeFaces X).card = (squarefreeUpTo X).card := by
  classical
  have hinj : Set.InjOn primeFaceProduct
      (↑(admissiblePrimeFaces X) : Set (Finset ℕ)) := by
    intro t ht u hu hprod
    have ht' : t ∈ admissiblePrimeFaces X := by simpa using ht
    have hu' : u ∈ admissiblePrimeFaces X := by simpa using hu
    exact primeFaceProduct_injective_on_admissible_primesUpTo
      (mem_admissiblePrimeFaces.mp ht')
      (mem_admissiblePrimeFaces.mp hu') hprod
  have hcard :
      ((admissiblePrimeFaces X).image primeFaceProduct).card =
        (admissiblePrimeFaces X).card :=
    Finset.card_image_iff.mpr hinj
  calc
    (admissiblePrimeFaces X).card =
        ((admissiblePrimeFaces X).image primeFaceProduct).card := hcard.symm
    _ = (squarefreeUpTo X).card := by
      rw [image_primeFaceProduct_admissiblePrimeFaces]

/-- Every first-failure Euler face is one of the admissible squarefree faces of
the original prime cube. -/
private theorem primeProductFirstFailureBoundary_subset_admissiblePrimeFaces
    (X ell : ℕ) :
    primeProductFirstFailureBoundary (primesUpTo X) X ell ⊆
      admissiblePrimeFaces X := by
  intro t ht
  apply mem_admissiblePrimeFaces.mpr
  rcases mem_primeProductFirstFailureBoundary.mp ht with ⟨htsub, hprod, _hcross⟩
  refine ⟨?_, hprod⟩
  intro p hp
  exact (Finset.mem_erase.mp (htsub hp)).2

/-- **Frontier diagonal is a sub-diagonal of the physical carrier.**  The
surviving first-failure population can never exceed the exact squarefree
Green--Kubo diagonal. -/
theorem primeProductFrontierCard_le_realMertensDiagonal (X ell : ℕ) :
    (primeProductFrontierCard X ell : ℝ) ≤ realMertensDiagonal (X + 1) := by
  unfold primeProductFrontierCard
  rw [realMertensDiagonal_eq_card_squarefreeUpTo,
    ← card_admissiblePrimeFaces_eq_squarefreeUpTo]
  exact_mod_cast Finset.card_le_card
    (primeProductFirstFailureBoundary_subset_admissiblePrimeFaces X ell)

/-- **Exact lag-zero/off-diagonal decomposition.**  The global positive-lag
covariance is the Mertens energy after subtracting the full squarefree diagonal,
with the factor `1/2` coming from the two symmetric off-diagonal orientations. -/
theorem realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal (X : ℕ) :
    realMertensPositiveLagPairSum (X + 1) =
      (‖mertensSummatory X‖ ^ 2 - realMertensDiagonal (X + 1)) / 2 := by
  have hnorm := norm_mertensSummatory_sq_eq_realMertensLength_sq X
  have hgreen :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (X + 1)
  linarith

/-- **Exact covariance bridge.**  The one-face Euler-frontier covariance and
the global integer-order covariance differ by exactly half of the squarefree
diagonal removed by the frontier.  No estimate and no sign assumption occurs. -/
theorem primeProductFrontierSurvivingCovariance_sub_global_eq_diagonalGap
    (X ell : ℕ) :
    primeProductFrontierSurvivingCovariance X ell -
        realMertensPositiveLagPairSum (X + 1) =
      (realMertensDiagonal (X + 1) -
        (primeProductFrontierCard X ell : ℝ)) / 2 := by
  have hnorm := norm_mertensSummatory_sq_eq_realMertensLength_sq X
  have hgreen :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (X + 1)
  unfold primeProductFrontierSurvivingCovariance
  rw [hnorm]
  linarith

/-- **The Euler frontier dominates the global covariance on the same physical
prefix.**  This is the formerly unnamed first arrow for the one-face
prime-product frontier. -/
theorem realMertensPositiveLagPairSum_le_primeProductFrontierSurvivingCovariance
    (X ell : ℕ) :
    realMertensPositiveLagPairSum (X + 1) ≤
      primeProductFrontierSurvivingCovariance X ell := by
  have hgap :=
    primeProductFrontierSurvivingCovariance_sub_global_eq_diagonalGap X ell
  have hdiag := primeProductFrontierCard_le_realMertensDiagonal X ell
  linarith

/-- **Diagonal-corrected support envelope.**  The exact frontier amplitude bound
`‖M(X)‖ <= F` controls global covariance only after the *full* squarefree
lag-zero energy is restored.  This is strictly sharper than the frontier-only
maximum `F(F-1)/2` because `F <= Q`. -/
theorem realMertensPositiveLagPairSum_le_frontier_sq_sub_diagonal
    {X ell : ℕ} (hell : ell ∈ primesUpTo X) :
    realMertensPositiveLagPairSum (X + 1) ≤
      ((primeProductFrontierCard X ell : ℝ) ^ 2 -
        realMertensDiagonal (X + 1)) / 2 := by
  have hnorm := norm_mertensSummatory_le_primeProductFrontierCard hell
  have hcard0 : 0 ≤ (primeProductFrontierCard X ell : ℝ) := by positivity
  have hsq :
      ‖mertensSummatory X‖ ^ 2 ≤
        (primeProductFrontierCard X ell : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hcard0).2 hnorm
  rw [realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal X]
  linarith

/-- For a genuine exposed prime coordinate, the older frontier-maximum bound is
also a valid upper envelope.  The diagonal-corrected theorem immediately above
is stronger and is the preferred support-only statement. -/
theorem realMertensPositiveLagPairSum_le_primeProductFrontierMaximumCovariance
    {X ell : ℕ} (hell : ell ∈ primesUpTo X) :
    realMertensPositiveLagPairSum (X + 1) ≤
      primeProductFrontierMaximumCovariance X ell :=
  (realMertensPositiveLagPairSum_le_primeProductFrontierSurvivingCovariance X ell).trans
    (primeProductFrontierSurvivingCovariance_le_maximum hell)

/-! ## The centered square-root Euler carrier is already global -/

/-- The centered middle-bias coordinate written directly in the elementary
reciprocal Euler layers.  The top block is deterministic, the smooth term is the
completed low-prime state, and every remaining term samples a complete lower
Mertens state.  No absolute value or estimate is used. -/
theorem squareRootMiddleBiasResidual_eq_top_sub_smooth_add_reciprocalLayers
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleBiasResidual R =
      ((squareRootTopFibrePrimes R).card : ℂ) -
        squareRootSmoothMass (R - 1) +
        ∑ d ∈ Finset.Icc 2 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d := by
  rw [squareRootMiddleBiasResidual_eq_neg_mertens R hR,
    squarePrefixMertens_eq_smooth_sub_middle_sub_topCard R hR,
    squareRootMiddleMertensTail_eq_reciprocalPrimeLayers R hR]
  ring

/-- Covariance of the centered square-root Euler carrier, using the **global**
lag-zero squarefree energy rather than a surrogate frontier cardinality. -/
def squareRootMiddleBiasResidualCovariance (R : ℕ) : ℝ :=
  (‖squareRootMiddleBiasResidual R‖ ^ 2 -
    realMertensDiagonal (squareRootEndpoint R + 1)) / 2

/-- **Exact square-endpoint covariance bridge.**  The centered reciprocal Euler
carrier is not merely an envelope for global covariance: after restoring the
full lag-zero diagonal, it *is* the global covariance at `R^2-1`. -/
theorem squareRootMiddleBiasResidualCovariance_eq_global
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleBiasResidualCovariance R =
      realMertensPositiveLagPairSum (squareRootEndpoint R + 1) := by
  unfold squareRootMiddleBiasResidualCovariance
  rw [norm_squareRootMiddleBiasResidual_eq_mertens R hR]
  have hclock :
      squarePrefixMertens (R - 1) =
        mertensSummatory (squareRootEndpoint R) := by
    unfold squarePrefixMertens squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  rw [hclock]
  exact
    (realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal
      (squareRootEndpoint R)).symm

/-! ## The two arrows of the critical path -/

/-- **First arrow: the covariance bridge.**  A frontier route must dominate the
*global* integer-order Möbius covariance, not merely its own frontier
coordinate.  This is the step that puts the two covariance objects on one
carrier. -/
def CovarianceEnvelopeDominates (E : ℕ → ℝ) : Prop :=
  ∀ K : ℕ, 1 ≤ K → realMertensPositiveLagPairSum K ≤ E K

/-- The one-face Euler frontier, indexed on the same prefix length `K` as the
global covariance.  `pivot X` is interpreted as the Euler coordinate exposed at
cutoff `X`; primality is needed only when one additionally invokes the frontier
maximum theorem. -/
def primeProductFrontierCovarianceEnvelope
    (pivot : ℕ → ℕ) (K : ℕ) : ℝ :=
  primeProductFrontierSurvivingCovariance (K - 1) (pivot (K - 1))

/-- **`CovarianceEnvelopeDominates` is compiled for the prime-product Euler
frontier.**  The proof is only the exact diagonal-gap bridge above plus the
index change from cutoff `X` to prefix length `K = X+1`. -/
theorem covarianceEnvelopeDominates_primeProductFrontier
    (pivot : ℕ → ℕ) :
    CovarianceEnvelopeDominates (primeProductFrontierCovarianceEnvelope pivot) := by
  intro K hK
  unfold primeProductFrontierCovarianceEnvelope
  have h :=
    realMertensPositiveLagPairSum_le_primeProductFrontierSurvivingCovariance
      (K - 1) (pivot (K - 1))
  simpa [Nat.sub_add_cancel hK] using h

/-- **Second arrow: capacity.**  The envelope itself is of RH scale. -/
def CovarianceEnvelopeRootScale (E : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ K : ℕ, 1 ≤ K → E K ≤ C * Real.rpow (K : ℝ) (1 + ε)

/-- **Both arrows, and only both, close the covariance route.**

Domination without capacity bounds nothing, and capacity without domination
bounds a different object.  Together they give the one-sided arithmetic frontier
and hence the protected Mertens energy criterion. -/
theorem mertensPositiveLagUpperBounded_of_covarianceEnvelope
    {E : ℕ → ℝ} (hdom : CovarianceEnvelopeDominates E)
    (hscale : CovarianceEnvelopeRootScale E) :
    MertensPositiveLagUpperBoundedStatement := by
  intro ε hε
  rcases hscale ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro K hK
  exact (hdom K hK).trans (hbound K hK)

theorem mertensEnergyBounded_of_covarianceEnvelope
    {E : ℕ → ℝ} (hdom : CovarianceEnvelopeDominates E)
    (hscale : CovarianceEnvelopeRootScale E) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_positiveLagUpperBounded
    (mertensPositiveLagUpperBounded_of_covarianceEnvelope hdom hscale)

end RHLean.Analysis
