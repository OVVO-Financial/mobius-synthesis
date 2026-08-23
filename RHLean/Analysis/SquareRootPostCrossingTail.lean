import Mathlib
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Analysis.SquareRootShallowReciprocalCrossing
import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Analysis.NativePNTQuantitativeStatements
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Analysis.StrongMertensLogNineBalance

/-!
# The tail after a shallow reciprocal-packet crossing

The shallow crossing theorem stops the upper-middle packet after a partial
number of seats in one reciprocal prime layer.  This file identifies exactly
what remains after that stop.

There are two different objects which must not be conflated:

* the **raw transport tail**, namely the increment from the partial packet to
  the completely processed post-root packet; and
* the **coupled tail**, obtained by adding the complete square-root-smooth
  population to that raw increment.

The raw tail is not the terminal Mertens remainder.  The exact terminal identity
is

```text
M(R^2 - 1) = partial crossing residual + coupled tail.
```

Consequently, once the partial residual is bounded by an absolute shallow
depth, a critical root-scale estimate for the coupled tail is equivalent to the
standard square-prefix Mertens energy criterion.  The eventual crossing theorem
provides the required shallow residual unconditionally; it does not provide the
coupled-tail estimate.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis

/-- The remaining signed transport increment after admitting `j` seats in the
crossing layer `K` and then completing every reciprocal layer through `R-1`.

This definition deliberately contains no smooth term. -/
def squareRootPostCrossingRawTransportTail (R K j : ℕ) : ℂ :=
  squareRootTruncatedUpperMiddlePacket R (R - 1) -
    ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)

/-- The terminally relevant tail: the raw post-crossing transport increment
kept signed together with the complete square-root-smooth population. -/
def squareRootPostCrossingCoupledTail (R K j : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) +
    squareRootPostCrossingRawTransportTail R K j

/-- Completing all reciprocal layers gives exactly the negative square-root
transport.  This is the full-depth endpoint missing from the deliberately
shallow cutoff equivalence theorem. -/
theorem squareRootTruncatedUpperMiddlePacket_full_eq_neg_transport
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTruncatedUpperMiddlePacket R (R - 1) =
      -squareRootTransportPrimeFirst R := by
  classical
  have hset :
      Finset.Icc 1 (R - 1) =
        ({1} : Finset ℕ) ∪ Finset.Icc 2 (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hdrest
    rw [Finset.mem_singleton] at hd1
    subst d
    simp at hdrest
  have hM1 : mertensSummatory 1 = 1 := by
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
    simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]
  have hmiddle := squareRootMiddleMertensTail_eq_reciprocalPrimeLayers R hR
  have htransport :=
    squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR
  unfold squareRootTruncatedUpperMiddlePacket
  rw [hset, Finset.sum_union hdisj]
  simp only [Finset.sum_singleton]
  rw [squareRootReciprocalPrimeCount_one_eq_topCard R hR, hM1, mul_one,
    ← hmiddle, htransport]
  ring

/-- The full integer packet has the same transport interpretation after casting. -/
theorem squareRootTruncatedUpperMiddlePacketInt_full_cast
    (R : ℕ) (hR : 3 ≤ R) :
    ((squareRootTruncatedUpperMiddlePacketInt R (R - 1) : ℤ) : ℂ) =
      -squareRootTransportPrimeFirst R := by
  rw [squareRootTruncatedUpperMiddlePacketInt_cast_complex,
    squareRootTruncatedUpperMiddlePacket_full_eq_neg_transport R hR]

/-- Exact completion formula for the raw tail. -/
theorem partial_add_postCrossingRawTransportTail
    (R K j : ℕ) :
    ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) +
        squareRootPostCrossingRawTransportTail R K j =
      squareRootTruncatedUpperMiddlePacket R (R - 1) := by
  unfold squareRootPostCrossingRawTransportTail
  ring

/-- **Exact post-crossing terminal identity.**  The partial residual and the
coupled tail recombine to the actual Mertens value at `R^2-1`. -/
theorem partial_add_postCrossingCoupledTail_eq_mertens
    (R K j : ℕ) (hR : 3 ≤ R) :
    ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) +
        squareRootPostCrossingCoupledTail R K j =
      mertensSummatory (squareRootEndpoint R) := by
  have hprefix := squarePrefixMertens_eq_squareRootSmooth_sub_transport (R - 1)
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega : 1 ≤ R)
  unfold squarePrefixMertens squarePrefixEndpoint at hprefix
  rw [hpred] at hprefix
  rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega),
    squareRootTransportCofactorFirst_eq_primeFirst] at hprefix
  unfold squareRootPostCrossingCoupledTail
    squareRootPostCrossingRawTransportTail
  rw [squareRootTruncatedUpperMiddlePacket_full_eq_neg_transport R hR]
  calc
    ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) +
        (squareRootSmoothMass (R - 1) +
          (-squareRootTransportPrimeFirst R -
            ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ))) =
        squareRootSmoothMass (R - 1) - squareRootTransportPrimeFirst R := by
      ring
    _ = mertensSummatory (squareRootEndpoint R) := by
      simpa [squareRootEndpoint] using hprefix.symm

/-- Subtraction form: the coupled tail is exactly terminal Mertens minus the
small partial crossing residual. -/
theorem postCrossingCoupledTail_eq_mertens_sub_partial
    (R K j : ℕ) (hR : 3 ≤ R) :
    squareRootPostCrossingCoupledTail R K j =
      mertensSummatory (squareRootEndpoint R) -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) := by
  have h := partial_add_postCrossingCoupledTail_eq_mertens R K j hR
  linear_combination h

/-- A critical root-scale bound for every valid partial residual at a crossing
whose depth is at most the certified absolute shallow cap.

The universal quantification over valid `j` makes the statement independent of
an arbitrary choice of the least sufficient seat.  The elementary interpolation
theorem supplies at least one such `j` at every crossing. -/
def SquareRootPostCrossingCoupledTailBoundedStatement (K₀ : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R K j : ℕ,
        3 ≤ R →
        K ≤ K₀ →
        SquareRootPacketCrossesAt R K →
        j ≤ squareRootReciprocalPrimeLayerCard R K →
        0 ≤ squareRootCrossingLayerPartialPacketInt R K j →
        squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) →
        ‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

private theorem postCrossing_norm_sq_add_le_two (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

private theorem partialResidual_norm_le_cap
    (K₀ : ℕ)
    {R K j : ℕ}
    (hK : K ≤ K₀)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤ (K₀ : ℝ) := by
  rw [Complex.norm_intCast, abs_of_nonneg]
  · exact_mod_cast
      (le_trans (Int.le_of_lt hVK) (by exact_mod_cast hK : (K : ℤ) ≤ K₀))
  · exact_mod_cast hV0

private theorem one_le_root_rpow
    {R : ℕ} {ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) :
    (1 : ℝ) ≤ Real.rpow (R : ℝ) (2 + ε) := by
  apply Real.one_le_rpow
  · exact_mod_cast hR
  · linarith

/-! ## The unconditional tail estimate available from strong Mertens -/

/-- The strongest premise-free tail scale currently available in the repository.

This is deliberately stated for an arbitrary absolute depth cap `K₀`.  The
crossing and seat hypotheses identify the intended post-crossing residual, while
the estimate itself follows from the exact terminal identity, the bounded
partial residual, and the repository's unconditional strong Mertens theorem. -/
def SquareRootPostCrossingCoupledTailSubexpStatement (K₀ : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ R K j : ℕ,
      3 ≤ R →
      K ≤ K₀ →
      SquareRootPacketCrossesAt R K →
      j ≤ squareRootReciprocalPrimeLayerCard R K →
      0 ≤ squareRootCrossingLayerPartialPacketInt R K j →
      squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) →
      ‖squareRootPostCrossingCoupledTail R K j‖ ≤
        C * (squareRootEndpoint R : ℝ) *
            Real.exp
              (-c *
                (Real.log (squareRootEndpoint R : ℝ)) ^ ((1 : ℝ) / 10)) +
          (K₀ : ℝ)

/-- The coupled post-crossing tail satisfies the classical zero-free-region
subexponential estimate, uniformly over every valid crossing residual below an
arbitrary fixed depth cap.  No crossing theorem or RH-scale estimate is assumed. -/
theorem postCrossingCoupledTailSubexp (K₀ : ℕ) :
    SquareRootPostCrossingCoupledTailSubexpStatement K₀ := by
  rcases strongNativeMertensSubexp with ⟨c, C, hc, hC, hM⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R K j hR hK _hcross _hj hV0 hVK
  have hendpoint : 3 ≤ squareRootEndpoint R := by
    have hsquare : 2 ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left (by omega : 2 ≤ R) 2
    unfold squareRootEndpoint
    omega
  have hMbound := hM (squareRootEndpoint R) hendpoint
  rw [← norm_mertensSummatory_eq_abs_nativeMertensSummatory] at hMbound
  have hV := partialResidual_norm_le_cap K₀ hK hV0 hVK
  rw [postCrossingCoupledTail_eq_mertens_sub_partial R K j hR]
  calc
    ‖mertensSummatory (squareRootEndpoint R) -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤
        ‖mertensSummatory (squareRootEndpoint R)‖ +
          ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ C * (squareRootEndpoint R : ℝ) *
            Real.exp
              (-c *
                (Real.log (squareRootEndpoint R : ℝ)) ^ ((1 : ℝ) / 10)) +
          (K₀ : ℝ) :=
      add_le_add hMbound hV

/-- An exact negative reciprocal coefficient certificate selects an actual
shallow crossing and interpolation seat whose remaining coupled tail obeys the
unconditional subexponential estimate.  This is the general endpoint theorem;
no numerical depth occurs in its statement. -/
theorem eventually_exists_postCrossingCoupledTail_subexp_of_boundaryRat_neg
    (K₀ : ℕ) (hK₀ : 1 ≤ K₀)
    (hcoeff : squareRootPacketReciprocalBoundaryRat K₀ < 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ᶠ R : ℕ in atTop,
        ∃ K j : ℕ,
          K ≤ K₀ ∧
          SquareRootPacketCrossesAt R K ∧
          j ≤ squareRootReciprocalPrimeLayerCard R K ∧
          0 ≤ squareRootCrossingLayerPartialPacketInt R K j ∧
          squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) ∧
          ‖squareRootPostCrossingCoupledTail R K j‖ ≤
            C * (squareRootEndpoint R : ℝ) *
                Real.exp
                  (-c *
                    (Real.log (squareRootEndpoint R : ℝ)) ^ ((1 : ℝ) / 10)) +
              (K₀ : ℝ) := by
  rcases postCrossingCoupledTailSubexp K₀ with ⟨c, C, hc, hC, htail⟩
  refine ⟨c, C, hc, hC, ?_⟩
  have hcross :=
    eventually_exists_squareRootPacketCrossesAt_le_of_boundaryRat_neg
      K₀ hK₀ hcoeff
  filter_upwards [hcross, eventually_ge_atTop (3 : ℕ)] with R hcrossR hR
  rcases hcrossR with ⟨K, hK, hKcross⟩
  rcases squareRootPacketCrossing_exists_partial_residual_lt_depth hKcross with
    ⟨j, hj, hV0, hVK⟩
  refine ⟨K, j, hK, hKcross, hj, hV0, hVK, ?_⟩
  exact htail R K j hR hK hKcross hj hV0 hVK

/-- Concrete certificate corollary for the already exact native-decision negative
coefficient.  The analytic estimate remains the general strong-Mertens tail
bound above; `18800` is used only to instantiate the crossing certificate. -/
theorem eventually_exists_postCrossingCoupledTail_subexp_18800 :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ᶠ R : ℕ in atTop,
        ∃ K j : ℕ,
          K ≤ 18800 ∧
          SquareRootPacketCrossesAt R K ∧
          j ≤ squareRootReciprocalPrimeLayerCard R K ∧
          0 ≤ squareRootCrossingLayerPartialPacketInt R K j ∧
          squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) ∧
          ‖squareRootPostCrossingCoupledTail R K j‖ ≤
            C * (squareRootEndpoint R : ℝ) *
                Real.exp
                  (-c *
                    (Real.log (squareRootEndpoint R : ℝ)) ^ ((1 : ℝ) / 10)) +
              (18800 : ℝ) :=
  eventually_exists_postCrossingCoupledTail_subexp_of_boundaryRat_neg
    18800 (by norm_num) squareRootPacketReciprocalBoundaryRat_18800_neg

/-!
The two directions below show that the proposed tail estimate is neither a
consequence of the crossing theorem nor a weaker post-processing lemma: it is
exactly the square-prefix critical Mertens estimate, up to the uniformly bounded
partial residual.
-/

/-- The standard square-prefix Mertens criterion bounds every admissible coupled
post-crossing tail. -/
theorem postCrossingCoupledTailBounded_of_squarePrefixEnergyBounded
    (K₀ : ℕ) (hM : SquarePrefixEnergyBoundedStatement) :
    SquareRootPostCrossingCoupledTailBoundedStatement K₀ := by
  intro ε hε
  rcases hM ε hε with ⟨C, hC, hbound⟩
  let D : ℝ := 2 * C + 2 * (K₀ : ℝ) ^ 2
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro R K j hR hK _hcross _hj hV0 hVK
  have htail := postCrossing_norm_sq_add_le_two
    (mertensSummatory (squareRootEndpoint R))
    (-((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ))
  have htail' :
      ‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 ≤
        2 * ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 +
          2 * ‖-((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ^ 2 := by
    rw [postCrossingCoupledTail_eq_mertens_sub_partial R K j hR]
    simpa [sub_eq_add_neg] using htail
  have hMbound :
      ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤
        C * Real.rpow (R : ℝ) (2 + ε) := by
    have h := hbound (R - 1)
    have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega : 1 ≤ R)
    simpa [squarePrefixMertens, squarePrefixEndpoint, hpred] using h
  have hV := partialResidual_norm_le_cap K₀ hK hV0 hVK
  have hVsq :
      ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ^ 2 ≤
        (K₀ : ℝ) ^ 2 := by
    nlinarith [norm_nonneg
      (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ))]
  have hpow := one_le_root_rpow (by omega : 1 ≤ R) hε
  have hconst :
      2 * (K₀ : ℝ) ^ 2 ≤
        2 * (K₀ : ℝ) ^ 2 * Real.rpow (R : ℝ) (2 + ε) := by
    nlinarith
  calc
    ‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 ≤
        2 * ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 +
          2 * ‖-((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ^ 2 :=
      htail'
    _ ≤ 2 * (C * Real.rpow (R : ℝ) (2 + ε)) +
          2 * (K₀ : ℝ) ^ 2 := by
      simpa only [norm_neg] using add_le_add
        (mul_le_mul_of_nonneg_left hMbound (by norm_num))
        (mul_le_mul_of_nonneg_left hVsq (by norm_num))
    _ ≤ 2 * (C * Real.rpow (R : ℝ) (2 + ε)) +
          2 * (K₀ : ℝ) ^ 2 * Real.rpow (R : ℝ) (2 + ε) :=
      add_le_add_left hconst _
    _ = D * Real.rpow (R : ℝ) (2 + ε) := by
      dsimp [D]
      ring

/-- Conversely, an eventual shallow crossing together with the coupled-tail
bound recovers the complete square-prefix Mertens criterion.  The finite prefix
before the crossing onset is absorbed into the constant. -/
theorem squarePrefixEnergyBounded_of_postCrossingCoupledTailBounded
    (K₀ : ℕ)
    (hcross : ∀ᶠ R : ℕ in atTop,
      ∃ K : ℕ, K ≤ K₀ ∧ SquareRootPacketCrossesAt R K)
    (htail : SquareRootPostCrossingCoupledTailBoundedStatement K₀) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases htail ε hε with ⟨C, hC, htailBound⟩
  rw [eventually_atTop] at hcross
  rcases hcross with ⟨R₀, hcross⟩
  let B : ℕ := max 3 R₀
  let D : ℝ :=
    2 * C + 2 * (K₀ : ℝ) ^ 2 + (B : ℝ) ^ 4
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro n
  let R : ℕ := n + 1
  have hRpos : 1 ≤ R := by
    dsimp [R]
    omega
  have hendpoint :
      squarePrefixEndpoint n = squareRootEndpoint R := by
    dsimp [R]
    unfold squarePrefixEndpoint squareRootEndpoint
    rfl
  by_cases hlarge : B ≤ R
  · have hR3 : 3 ≤ R := (le_max_left 3 R₀).trans hlarge
    have hR₀ : R₀ ≤ R := (le_max_right 3 R₀).trans hlarge
    rcases hcross R hR₀ with ⟨K, hK, hKcross⟩
    rcases squareRootPacketCrossing_exists_partial_residual_lt_depth hKcross with
      ⟨j, hj, hV0, hVK⟩
    have htailR := htailBound R K j hR3 hK hKcross hj hV0 hVK
    have hV := partialResidual_norm_le_cap K₀ hK hV0 hVK
    have hVsq :
        ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ^ 2 ≤
          (K₀ : ℝ) ^ 2 := by
      nlinarith [norm_nonneg
        (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ))]
    have hsum := postCrossing_norm_sq_add_le_two
      (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ))
      (squareRootPostCrossingCoupledTail R K j)
    rw [partial_add_postCrossingCoupledTail_eq_mertens R K j hR3] at hsum
    have hpow := one_le_root_rpow hRpos hε
    have hconst :
        2 * (K₀ : ℝ) ^ 2 ≤
          2 * (K₀ : ℝ) ^ 2 * Real.rpow (R : ℝ) (2 + ε) := by
      nlinarith
    have hendpointBound :
        ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤
          D * Real.rpow (R : ℝ) (2 + ε) := by
      calc
        ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤
            2 * ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ^ 2 +
              2 * ‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 := hsum
        _ ≤ 2 * (K₀ : ℝ) ^ 2 +
              2 * (C * Real.rpow (R : ℝ) (2 + ε)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hVsq (by norm_num))
            (mul_le_mul_of_nonneg_left htailR (by norm_num))
        _ ≤ 2 * (K₀ : ℝ) ^ 2 * Real.rpow (R : ℝ) (2 + ε) +
              2 * (C * Real.rpow (R : ℝ) (2 + ε)) :=
          add_le_add_right hconst _
        _ ≤ D * Real.rpow (R : ℝ) (2 + ε) := by
          have hpowNonneg : 0 ≤ Real.rpow (R : ℝ) (2 + ε) :=
            Real.rpow_nonneg (by positivity) _
          calc
            2 * (K₀ : ℝ) ^ 2 * Real.rpow (R : ℝ) (2 + ε) +
                2 * (C * Real.rpow (R : ℝ) (2 + ε)) =
                (2 * C + 2 * (K₀ : ℝ) ^ 2) *
                  Real.rpow (R : ℝ) (2 + ε) := by ring
            _ ≤ D * Real.rpow (R : ℝ) (2 + ε) :=
              mul_le_mul_of_nonneg_right (by
                dsimp [D]
                nlinarith [sq_nonneg ((B : ℝ) ^ 2)]) hpowNonneg
    simpa [squarePrefixMertens, hendpoint, R] using hendpointBound
  · have hRB : R ≤ B := by omega
    have hnorm := norm_mertensSummatory_sub_le
      0 (squareRootEndpoint R) (Nat.zero_le _)
    rw [mertensSummatory_zero, sub_zero] at hnorm
    have hendpointLe : squareRootEndpoint R ≤ B ^ 2 := by
      unfold squareRootEndpoint
      exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_left hRB 2)
    have hnormB :
        ‖mertensSummatory (squareRootEndpoint R)‖ ≤ (B : ℝ) ^ 2 := by
      calc
        ‖mertensSummatory (squareRootEndpoint R)‖ ≤
            (squareRootEndpoint R : ℝ) := by
          simpa using hnorm
        _ ≤ (B ^ 2 : ℕ) := by exact_mod_cast hendpointLe
        _ = (B : ℝ) ^ 2 := by norm_cast
    have hnormSq :
        ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤ (B : ℝ) ^ 4 := by
      nlinarith [norm_nonneg (mertensSummatory (squareRootEndpoint R))]
    have hpow := one_le_root_rpow hRpos hε
    have hBterm :
        (B : ℝ) ^ 4 ≤ D * Real.rpow (R : ℝ) (2 + ε) := by
      have hBD : (B : ℝ) ^ 4 ≤ D := by
        dsimp [D]
        nlinarith
      have hDnonneg : 0 ≤ D := hD
      exact hBD.trans (by nlinarith)
    rw [squarePrefixMertens, hendpoint]
    exact hnormSq.trans hBterm

/-- Under an eventual depth-`K₀` crossing, the coupled post-crossing tail
estimate is exactly the square-prefix Mertens energy criterion. -/
theorem postCrossingCoupledTailBounded_iff_squarePrefixEnergyBounded
    (K₀ : ℕ)
    (hcross : ∀ᶠ R : ℕ in atTop,
      ∃ K : ℕ, K ≤ K₀ ∧ SquareRootPacketCrossesAt R K) :
    SquareRootPostCrossingCoupledTailBoundedStatement K₀ ↔
      SquarePrefixEnergyBoundedStatement := by
  exact ⟨squarePrefixEnergyBounded_of_postCrossingCoupledTailBounded K₀ hcross,
    postCrossingCoupledTailBounded_of_squarePrefixEnergyBounded K₀⟩

/-- Any exact negative reciprocal coefficient certificate turns the coupled
tail bound into an equivalent form of the full Mertens energy criterion. -/
theorem postCrossingCoupledTailBounded_iff_mertensEnergyBounded_of_boundaryRat_neg
    (K₀ : ℕ) (hK₀ : 1 ≤ K₀)
    (hcoeff : squareRootPacketReciprocalBoundaryRat K₀ < 0) :
    SquareRootPostCrossingCoupledTailBoundedStatement K₀ ↔
      MertensEnergyBoundedStatement := by
  calc
    SquareRootPostCrossingCoupledTailBoundedStatement K₀ ↔
        SquarePrefixEnergyBoundedStatement :=
      postCrossingCoupledTailBounded_iff_squarePrefixEnergyBounded K₀
        (eventually_exists_squareRootPacketCrossesAt_le_of_boundaryRat_neg
          K₀ hK₀ hcoeff)
    _ ↔ MertensEnergyBoundedStatement :=
      mertensEnergyBounded_iff_squarePrefixEnergyBounded.symm

/-- Concrete certificate corollary.  The value `18800` enters only here, as one
exact native-decision witness for the general negative-coefficient hypothesis. -/
theorem postCrossingCoupledTailBounded_18800_iff_mertensEnergyBounded :
    SquareRootPostCrossingCoupledTailBoundedStatement 18800 ↔
      MertensEnergyBoundedStatement :=
  postCrossingCoupledTailBounded_iff_mertensEnergyBounded_of_boundaryRat_neg
    18800 (by norm_num) squareRootPacketReciprocalBoundaryRat_18800_neg

/-- Therefore a proof of the critical coupled-tail bound would, through the
repository's premise-free Mertens forward theorem, prove the Riemann Hypothesis. -/
theorem riemannHypothesis_of_postCrossingCoupledTailBounded_18800
    (htail : SquareRootPostCrossingCoupledTailBoundedStatement 18800) :
    RiemannHypothesisStatement := by
  change RiemannHypothesis
  exact riemannHypothesis_of_mertensEnergy
    (postCrossingCoupledTailBounded_18800_iff_mertensEnergyBounded.mp htail)

end RHLean.Proof
