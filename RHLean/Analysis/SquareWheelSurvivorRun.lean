import Mathlib
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity
import RHLean.Analysis.PrimeWheelHarmonicCriterion
import RHLean.Analysis.PrimorialWheelMertensTransfer
import RHLean.Analysis.SquareWheelSurvivorIncrement
import RHLean.Analysis.SquareWheelZeroModeElimination

/-!
# Survivor-centered square-wheel run differences

The local survivor-increment theorem isolates

```text
Delta survivorZeroMode - endpointDrift
```

inside one increment of the protected nonzero response.  Its local remainder is
already unconditional, but summing local norm bounds over a long square run
would throw away exactly the cross-stage cancellation the proof route needs.

This file therefore compares two square samples directly.

For samples `a` and `b` in one primorial block, define the signed survivor run
coordinate

```text
Z_16(b) - Z_16(a)
  - (rho_b - rho_a) * R_k(U_k).
```

The block-anchor Mertens term cancels before any norm.  The exact difference
`H_{k,b} - H_{k,a}` is this survivor-centered run coordinate plus only

* `canonicalLowPrefix 16 b - canonicalLowPrefix 16 a`, and
* `lifetimeDeathMass 16 b - lifetimeDeathMass 16 a`.

Both endpoint remainders already have unconditional global bounds of the right
square-root scale.  Thus this run formulation preserves the signed survivor
correlation across all intervening square stages and never pays a sum of local
absolute values.

The second half of the file records the complementary full-Mertens statement:
a uniform RH-scale bound on every consecutive complete-square run is exactly
the pinned primorial-wheel residual criterion.  The reverse direction uses only
the first and last incomplete-square edges, both already square-root scale.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- Square-prefix Mertens in the exact low + survivor + absorbed-death
coordinates at the repository cutoff `Lambda = 16`. -/
theorem squarePrefixMertens_eq_low_add_survivor_add_death
    (n : ℕ) :
    squarePrefixMertens n =
      canonicalLowPrefix 16 n + survivorZeroMode 16 n +
        lifetimeDeathMass 16 n := by
  rw [squarePrefixMertens_eq_canonicalLow_add_high]
  rw [← lifetimeBirthMass_eq_canonicalHighPrefix]
  rw [lifetimeBirthMass_eq_active_add_death]
  rw [lifetimeActiveAtomMass_eq_survivorZeroMode (Λ := (16 : ℝ))
    (by norm_num) n]
  ring

/-- On one primorial block, subtracting two minimal-wheel residuals cancels the
common lower-block Mertens anchor exactly. -/
theorem primorialMinimalWheel_residual_squareEndpoints_sub_eq_squarePrefixMertens_sub
    (k a b : ℕ)
    (haLower : primorialBlockLower k < squarePrefixEndpoint a)
    (haUpper : squarePrefixEndpoint a ≤ primorialBlockUpper k)
    (hbLower : primorialBlockLower k < squarePrefixEndpoint b)
    (hbUpper : squarePrefixEndpoint b ≤ primorialBlockUpper k) :
    (((primorialMinimalWheelSystem k).residual
        (squarePrefixEndpoint b) : ℤ) : ℂ) -
      (((primorialMinimalWheelSystem k).residual
        (squarePrefixEndpoint a) : ℤ) : ℂ) =
      squarePrefixMertens b - squarePrefixMertens a := by
  have ha := primorialWheel_residual_cast_eq_mertens_sub k haLower haUpper
  have hb := primorialWheel_residual_cast_eq_mertens_sub k hbLower hbUpper
  have hminA :=
    primorialMinimalWheel_residual_eq_primorialWheel_residual k haUpper
  have hminB :=
    primorialMinimalWheel_residual_eq_primorialWheel_residual k hbUpper
  rw [← hminA] at ha
  rw [← hminB] at hb
  calc
    (((primorialMinimalWheelSystem k).residual
        (squarePrefixEndpoint b) : ℤ) : ℂ) -
      (((primorialMinimalWheelSystem k).residual
        (squarePrefixEndpoint a) : ℤ) : ℂ) =
      (mertensSummatory (squarePrefixEndpoint b) -
        mertensSummatory (primorialBlockLower k)) -
      (mertensSummatory (squarePrefixEndpoint a) -
        mertensSummatory (primorialBlockLower k)) := by
          rw [hb, ha]
    _ = squarePrefixMertens b - squarePrefixMertens a := by
      unfold squarePrefixMertens
      ring

/-- The cancellation-preserving run coordinate: survivor endpoint difference
minus the exact rank-one zero-mode change over the same two samples. -/
def primorialMinimalSquareWheelSurvivorRunCentered
    (k a b : ℕ) : ℂ :=
  (survivorZeroMode 16 b - survivorZeroMode 16 a) -
    (squareWheelSampleRatio (primorialMinimalWheelSystem k) b -
      squareWheelSampleRatio (primorialMinimalWheelSystem k) a) *
      ((((primorialMinimalWheelSystem k).residual
        (primorialBlockUpper k) : ℤ) : ℂ))

/-- **Exact run-level survivor centering.** -/
theorem primorialMinimalSquareWheelNonzeroResponse_sub_eq_survivorRunCentered_add_lowDiff_add_deathDiff
    (k a b : ℕ)
    (haLower : primorialBlockLower k < squarePrefixEndpoint a)
    (haUpper : squarePrefixEndpoint a ≤ primorialBlockUpper k)
    (hbLower : primorialBlockLower k < squarePrefixEndpoint b)
    (hbUpper : squarePrefixEndpoint b ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) b -
        squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) a =
      primorialMinimalSquareWheelSurvivorRunCentered k a b +
        (canonicalLowPrefix 16 b - canonicalLowPrefix 16 a) +
        (lifetimeDeathMass 16 b - lifetimeDeathMass 16 a) := by
  have hsampleB :=
    primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
      (primorialMinimalWheelSystem k) b hbLower hbUpper
  have hsampleA :=
    primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
      (primorialMinimalWheelSystem k) a haLower haUpper
  have hupper :
      (primorialMinimalWheelSystem k).upper = primorialBlockUpper k := rfl
  rw [hupper] at hsampleB hsampleA
  have hres :=
    primorialMinimalWheel_residual_squareEndpoints_sub_eq_squarePrefixMertens_sub
      k a b haLower haUpper hbLower hbUpper
  have hb := squarePrefixMertens_eq_low_add_survivor_add_death b
  have ha := squarePrefixMertens_eq_low_add_survivor_add_death a
  unfold primorialMinimalSquareWheelSurvivorRunCentered
  calc
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) b -
        squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) a =
      (((((primorialMinimalWheelSystem k).residual
          (squarePrefixEndpoint b) : ℤ) : ℂ)) -
        ((((primorialMinimalWheelSystem k).residual
          (squarePrefixEndpoint a) : ℤ) : ℂ))) -
        (squareWheelSampleRatio (primorialMinimalWheelSystem k) b -
          squareWheelSampleRatio (primorialMinimalWheelSystem k) a) *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ)) := by
              rw [hsampleB, hsampleA]
              ring
    _ = (squarePrefixMertens b - squarePrefixMertens a) -
        (squareWheelSampleRatio (primorialMinimalWheelSystem k) b -
          squareWheelSampleRatio (primorialMinimalWheelSystem k) a) *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ)) := by
              rw [hres]
    _ =
      ((canonicalLowPrefix 16 b + survivorZeroMode 16 b +
          lifetimeDeathMass 16 b) -
        (canonicalLowPrefix 16 a + survivorZeroMode 16 a +
          lifetimeDeathMass 16 a)) -
        (squareWheelSampleRatio (primorialMinimalWheelSystem k) b -
          squareWheelSampleRatio (primorialMinimalWheelSystem k) a) *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ)) := by
              rw [hb, ha]
    _ =
      ((survivorZeroMode 16 b - survivorZeroMode 16 a) -
        (squareWheelSampleRatio (primorialMinimalWheelSystem k) b -
          squareWheelSampleRatio (primorialMinimalWheelSystem k) a) *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ))) +
        (canonicalLowPrefix 16 b - canonicalLowPrefix 16 a) +
        (lifetimeDeathMass 16 b - lifetimeDeathMass 16 a) := by
          ring

/-- After subtracting the survivor-centered run coordinate, only the two
already-controlled endpoint processes remain. -/
theorem norm_nonzeroResponseRun_sub_survivorRunCentered_le_lowDiff_add_deathDiff
    (k a b : ℕ)
    (haLower : primorialBlockLower k < squarePrefixEndpoint a)
    (haUpper : squarePrefixEndpoint a ≤ primorialBlockUpper k)
    (hbLower : primorialBlockLower k < squarePrefixEndpoint b)
    (hbUpper : squarePrefixEndpoint b ≤ primorialBlockUpper k) :
    ‖(squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) b -
        squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) a) -
        primorialMinimalSquareWheelSurvivorRunCentered k a b‖ ≤
      ‖canonicalLowPrefix 16 b - canonicalLowPrefix 16 a‖ +
        ‖lifetimeDeathMass 16 b - lifetimeDeathMass 16 a‖ := by
  calc
    ‖(squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) b -
        squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) a) -
        primorialMinimalSquareWheelSurvivorRunCentered k a b‖ =
      ‖(canonicalLowPrefix 16 b - canonicalLowPrefix 16 a) +
        (lifetimeDeathMass 16 b - lifetimeDeathMass 16 a)‖ := by
          rw [primorialMinimalSquareWheelNonzeroResponse_sub_eq_survivorRunCentered_add_lowDiff_add_deathDiff
            k a b haLower haUpper hbLower hbUpper]
          congr 1
          ring
    _ ≤ ‖canonicalLowPrefix 16 b - canonicalLowPrefix 16 a‖ +
        ‖lifetimeDeathMass 16 b - lifetimeDeathMass 16 a‖ :=
      norm_add_le _ _

/-- **Unconditional run-level remainder bound.** -/
theorem norm_nonzeroResponseRun_sub_survivorRunCentered_globalBound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k a b : ℕ,
        primorialBlockLower k < squarePrefixEndpoint a →
        squarePrefixEndpoint a ≤ primorialBlockUpper k →
        primorialBlockLower k < squarePrefixEndpoint b →
        squarePrefixEndpoint b ≤ primorialBlockUpper k →
        ‖(squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) b -
            squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) a) -
            primorialMinimalSquareWheelSurvivorRunCentered k a b‖ ≤
          ((a + 1 : ℕ) : ℝ) * 17 + ((b + 1 : ℕ) : ℝ) * 17 +
            C * Real.rpow (((a + 1 : ℕ) : ℝ)) (1 + ε) +
            C * Real.rpow (((b + 1 : ℕ) : ℝ)) (1 + ε) := by
  rcases norm_lifetimeDeathMass_le_rpow
      (Λ := (16 : ℝ)) (ε := ε) (by norm_num) hε with
    ⟨C, hC, hdeath⟩
  refine ⟨C, hC, ?_⟩
  intro k a b haLower haUpper hbLower hbUpper
  have hbase :=
    norm_nonzeroResponseRun_sub_survivorRunCentered_le_lowDiff_add_deathDiff
      k a b haLower haUpper hbLower hbUpper
  have hlowAraw :=
    norm_canonicalLowPrefix_le (canonicalLowIncrementControl (16 : ℝ)) a
  have hlowBraw :=
    norm_canonicalLowPrefix_le (canonicalLowIncrementControl (16 : ℝ)) b
  norm_num [canonicalLowIncrementControl] at hlowAraw hlowBraw
  have hlowA :
      ‖canonicalLowPrefix 16 a‖ ≤ ((a + 1 : ℕ) : ℝ) * 17 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlowAraw
  have hlowB :
      ‖canonicalLowPrefix 16 b‖ ≤ ((b + 1 : ℕ) : ℝ) * 17 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlowBraw
  have hlowDiff :
      ‖canonicalLowPrefix 16 b - canonicalLowPrefix 16 a‖ ≤
        ((b + 1 : ℕ) : ℝ) * 17 + ((a + 1 : ℕ) : ℝ) * 17 := by
    exact (norm_sub_le _ _).trans (add_le_add hlowB hlowA)
  have hdeathA := hdeath a
  have hdeathB := hdeath b
  have hdeathDiff :
      ‖lifetimeDeathMass 16 b - lifetimeDeathMass 16 a‖ ≤
        C * Real.rpow (((b + 1 : ℕ) : ℝ)) (1 + ε) +
          C * Real.rpow (((a + 1 : ℕ) : ℝ)) (1 + ε) := by
    exact (norm_sub_le _ _).trans (add_le_add hdeathB hdeathA)
  calc
    ‖(squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) b -
        squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) a) -
        primorialMinimalSquareWheelSurvivorRunCentered k a b‖ ≤
      ‖canonicalLowPrefix 16 b - canonicalLowPrefix 16 a‖ +
        ‖lifetimeDeathMass 16 b - lifetimeDeathMass 16 a‖ := hbase
    _ ≤
      (((b + 1 : ℕ) : ℝ) * 17 + ((a + 1 : ℕ) : ℝ) * 17) +
        (C * Real.rpow (((b + 1 : ℕ) : ℝ)) (1 + ε) +
          C * Real.rpow (((a + 1 : ℕ) : ℝ)) (1 + ε)) :=
      add_le_add hlowDiff hdeathDiff
    _ =
      ((a + 1 : ℕ) : ℝ) * 17 + ((b + 1 : ℕ) : ℝ) * 17 +
        C * Real.rpow (((a + 1 : ℕ) : ℝ)) (1 + ε) +
        C * Real.rpow (((b + 1 : ℕ) : ℝ)) (1 + ε) := by
      ring

end RHLean.Proof

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Full maximal signed square-run criterion -/

/-- Uniform RH-scale energy bound for every nonempty consecutive run of complete
square-block increments whose bounding square endpoints lie in one synchronized
primorial block.  The constant is uniform in the wheel index and the scale is
the actual terminal square endpoint. -/
def SquareRunEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k a b : ℕ,
        1 ≤ a →
        a ≤ b →
        primorialBlockLower k ≤ squarePrefixEndpoint (a - 1) →
        squarePrefixEndpoint b ≤ primorialBlockUpper k →
        ‖∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j‖ ^ 2 ≤
          C * Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε)

private theorem squareRun_norm_sq_add_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem squarePrefixEndpoint_strictMono_run
    {a b : ℕ} (hab : a < b) :
    squarePrefixEndpoint a < squarePrefixEndpoint b := by
  have hsquare : (a + 1) ^ 2 < (b + 1) ^ 2 :=
    Nat.pow_lt_pow_left (by omega) (by norm_num : 2 ≠ 0)
  have ha := squarePrefixEndpoint_add_one a
  have hb := squarePrefixEndpoint_add_one b
  omega

private theorem squarePrefixEndpoint_mono_run
    {a b : ℕ} (hab : a ≤ b) :
    squarePrefixEndpoint a ≤ squarePrefixEndpoint b := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (squarePrefixEndpoint_strictMono_run hlt).le

private theorem squareRun_sample_bracket (x : ℕ) :
    ∃ n : ℕ, squarePrefixEndpoint n ≤ x ∧
      x < squarePrefixEndpoint (n + 1) := by
  refine ⟨Nat.sqrt (x + 1) - 1, ?_, ?_⟩
  · have h1 : Nat.sqrt (x + 1) ^ 2 ≤ x + 1 := Nat.sqrt_le' (x + 1)
    have hr1 : 1 ≤ Nat.sqrt (x + 1) := Nat.sqrt_pos.mpr (by omega)
    have h2 := squarePrefixEndpoint_add_one (Nat.sqrt (x + 1) - 1)
    have h3 : Nat.sqrt (x + 1) - 1 + 1 = Nat.sqrt (x + 1) := by omega
    rw [h3] at h2
    omega
  · have h1 : x + 1 < (Nat.sqrt (x + 1) + 1) ^ 2 := Nat.lt_succ_sqrt' (x + 1)
    have hr1 : 1 ≤ Nat.sqrt (x + 1) := Nat.sqrt_pos.mpr (by omega)
    have h2 := squarePrefixEndpoint_add_one (Nat.sqrt (x + 1) - 1 + 1)
    have h3 : Nat.sqrt (x + 1) - 1 + 1 + 1 = Nat.sqrt (x + 1) + 1 := by omega
    rw [h3] at h2
    omega

private theorem squareRun_linear_le_rpow
    {ε : ℝ} (hε : 0 < ε) (x : ℕ) :
    (((x + 1 : ℕ) : ℝ)) ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ (((x + 1 : ℕ) : ℝ)) := by
    have hone : (1 : ℕ) ≤ x + 1 := Nat.le_add_left 1 x
    exact_mod_cast hone
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  simpa using h

private theorem squareRun_rpow_mono
    {ε : ℝ} (hε : 0 < ε) {a b : ℕ} (hab : a ≤ b) :
    Real.rpow (((a + 1 : ℕ) : ℝ)) (1 + ε) ≤
      Real.rpow (((b + 1 : ℕ) : ℝ)) (1 + ε) := by
  have hbase : (((a + 1 : ℕ) : ℝ)) ≤ (((b + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_le_add_right hab 1
  exact Real.rpow_le_rpow (by positivity) hbase (by linarith)

/-- The pinned residual criterion controls every complete signed square run. -/
theorem squareRunEnergyBounded_of_primorialResidualBounded
    (hres : PrimeWheelResidualBoundedStatement primorialWheelFamily) :
    SquareRunEnergyBoundedStatement := by
  intro ε hε
  rcases hres ε hε with ⟨C, hC, hbound⟩
  refine ⟨4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro k a b ha hab hleftLower hrightUpper
  have hindex : a - 1 < b := by omega
  have hendpoint : squarePrefixEndpoint (a - 1) < squarePrefixEndpoint b :=
    squarePrefixEndpoint_strictMono_run hindex
  have hleftUpper : squarePrefixEndpoint (a - 1) ≤ primorialBlockUpper k :=
    hendpoint.le.trans hrightUpper
  have hrightLower : primorialBlockLower k < squarePrefixEndpoint b :=
    lt_of_le_of_lt hleftLower hendpoint
  have hright :
      ‖(((primorialWheelSystem k).residual (squarePrefixEndpoint b) : ℤ) : ℂ)‖ ^ 2 ≤
        C * Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε) :=
    hbound k (squarePrefixEndpoint b) hrightLower hrightUpper
  have hleft :
      ‖(((primorialWheelSystem k).residual
          (squarePrefixEndpoint (a - 1)) : ℤ) : ℂ)‖ ^ 2 ≤
        C * Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε) := by
    by_cases hstrict : primorialBlockLower k < squarePrefixEndpoint (a - 1)
    · have hraw := hbound k (squarePrefixEndpoint (a - 1)) hstrict hleftUpper
      have hmono := squareRun_rpow_mono hε hendpoint.le
      exact hraw.trans (mul_le_mul_of_nonneg_left hmono hC)
    · have heq : primorialBlockLower k = squarePrefixEndpoint (a - 1) := by omega
      rw [← heq]
      have hblock : primorialBlockLower k ≤ primorialBlockUpper k :=
        hleftLower.trans hleftUpper
      rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
        k le_rfl hblock]
      have hrpow : (0 : ℝ) ≤
          Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε) :=
        Real.rpow_nonneg (by positivity) _
      simpa using mul_nonneg hC hrpow
  rw [RHLean.Proof.sum_canonicalTotalIncrement_Ico_eq_primorialResidual_sub
    k a b ha (by omega) hleftLower hleftUpper hrightLower.le hrightUpper]
  have htwo := squareRun_norm_sq_add_le_two
    ((((primorialWheelSystem k).residual (squarePrefixEndpoint b) : ℤ) : ℂ))
    (-((((primorialWheelSystem k).residual
      (squarePrefixEndpoint (a - 1)) : ℤ) : ℂ)))
  simp only [← sub_eq_add_neg, norm_neg] at htwo
  calc
    ‖(((primorialWheelSystem k).residual (squarePrefixEndpoint b) : ℤ) : ℂ) -
        (((primorialWheelSystem k).residual
          (squarePrefixEndpoint (a - 1)) : ℤ) : ℂ)‖ ^ 2 ≤
      2 * ‖(((primorialWheelSystem k).residual
        (squarePrefixEndpoint b) : ℤ) : ℂ)‖ ^ 2 +
      2 * ‖(((primorialWheelSystem k).residual
        (squarePrefixEndpoint (a - 1)) : ℤ) : ℂ)‖ ^ 2 := htwo
    _ ≤ 2 * (C * Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε)) +
        2 * (C * Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε)) := by
      gcongr
    _ = (4 * C) * Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε) := by
      ring

private theorem squareRun_shortResidual_sq_lt_nine
    {k m x : ℕ}
    (hmLower : squarePrefixEndpoint m ≤ primorialBlockLower k)
    (hlower : primorialBlockLower k < x)
    (hright : x < squarePrefixEndpoint (m + 1))
    (hupper : x ≤ primorialBlockUpper k) :
    ‖(((primorialWheelSystem k).residual x : ℤ) : ℂ)‖ ^ 2 <
      9 * (((x + 1 : ℕ) : ℝ)) := by
  rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
    k hlower.le hupper]
  have hnorm := norm_mertensSummatory_sub_le
    (primorialBlockLower k) x hlower.le
  have hgapNat : x - primorialBlockLower k < 2 * m + 3 := by
    have hgap := sub_squarePrefixEndpoint_lt_gap m x
      (hmLower.trans hlower.le) hright
    omega
  have hgapReal : (((x - primorialBlockLower k : ℕ) : ℝ)) <
      (((2 * m + 3 : ℕ) : ℝ)) := by exact_mod_cast hgapNat
  have hsqGapNat := squareGap_sq_le_nine_mul_succ m x
    (hmLower.trans hlower.le)
  have hsqGapReal : (((2 * m + 3 : ℕ) : ℝ)) ^ 2 ≤
      9 * (((x + 1 : ℕ) : ℝ)) := by exact_mod_cast hsqGapNat
  have h0 : 0 ≤ ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ :=
    norm_nonneg _
  have h1 : 0 ≤ (((x - primorialBlockLower k : ℕ) : ℝ)) := by positivity
  have h2 : 0 ≤ (((2 * m + 3 : ℕ) : ℝ)) := by positivity
  nlinarith

private theorem squareRun_firstEdge_sq_le_nine
    {k m x : ℕ}
    (hmLower : squarePrefixEndpoint m ≤ primorialBlockLower k)
    (hLowerNext : primorialBlockLower k < squarePrefixEndpoint (m + 1))
    (hnextx : squarePrefixEndpoint (m + 1) ≤ x) :
    ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
        mertensSummatory (primorialBlockLower k)‖ ^ 2 ≤
      9 * (((x + 1 : ℕ) : ℝ)) := by
  have hnorm := norm_mertensSummatory_sub_le (primorialBlockLower k)
    (squarePrefixEndpoint (m + 1)) hLowerNext.le
  have hgapNat :
      squarePrefixEndpoint (m + 1) - primorialBlockLower k ≤ 2 * m + 3 := by
    rw [squarePrefixEndpoint_succ_eq_add_gap m]
    omega
  have hgapReal :
      (((squarePrefixEndpoint (m + 1) - primorialBlockLower k : ℕ) : ℝ)) ≤
        (((2 * m + 3 : ℕ) : ℝ)) := by exact_mod_cast hgapNat
  have hmx : squarePrefixEndpoint m ≤ x :=
    hmLower.trans (hLowerNext.le.trans hnextx)
  have hsqGapNat := squareGap_sq_le_nine_mul_succ m x hmx
  have hsqGapReal : (((2 * m + 3 : ℕ) : ℝ)) ^ 2 ≤
      9 * (((x + 1 : ℕ) : ℝ)) := by exact_mod_cast hsqGapNat
  have h0 : 0 ≤ ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
      mertensSummatory (primorialBlockLower k)‖ := norm_nonneg _
  have h1 : 0 ≤
      (((squarePrefixEndpoint (m + 1) - primorialBlockLower k : ℕ) : ℝ)) := by
    positivity
  have h2 : 0 ≤ (((2 * m + 3 : ℕ) : ℝ)) := by positivity
  nlinarith

/-- Conversely, a maximal signed square-run bound controls every pinned wheel
residual.  The only losses are the two square-root-scale edge fragments. -/
theorem primorialResidualBounded_of_squareRunEnergyBounded
    (hrun : SquareRunEnergyBoundedStatement) :
    PrimeWheelResidualBoundedStatement primorialWheelFamily := by
  intro ε hε
  rcases hrun ε hε with ⟨C, hC, hrunBound⟩
  refine ⟨4 * C + 54, by linarith, ?_⟩
  intro k x hlower hupper
  change primorialBlockLower k < x at hlower
  change x ≤ primorialBlockUpper k at hupper
  change ‖(((primorialWheelSystem k).residual x : ℤ) : ℂ)‖ ^ 2 ≤ _
  obtain ⟨m, hmLower, hLowerNext⟩ :=
    squareRun_sample_bracket (primorialBlockLower k)
  by_cases hshort : x < squarePrefixEndpoint (m + 1)
  · have hs := squareRun_shortResidual_sq_lt_nine hmLower hlower hshort hupper
    have hlin := squareRun_linear_le_rpow hε x
    have hp0 : 0 ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) :=
      Real.rpow_nonneg (by positivity) _
    calc
      ‖(((primorialWheelSystem k).residual x : ℤ) : ℂ)‖ ^ 2 ≤
          9 * (((x + 1 : ℕ) : ℝ)) := hs.le
      _ ≤ 9 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) :=
        mul_le_mul_of_nonneg_left hlin (by norm_num)
      _ ≤ (4 * C + 54) * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
        apply mul_le_mul_of_nonneg_right _ hp0
        linarith
  · have hnextx : squarePrefixEndpoint (m + 1) ≤ x := by omega
    obtain ⟨n, hnLower, hnNext⟩ := squareRun_sample_bracket x
    have hmn : m + 1 ≤ n := by
      by_contra hnot
      have hnm : n ≤ m := by omega
      have hmono := squarePrefixEndpoint_mono_run
        (Nat.add_le_add_right hnm 1)
      omega
    have hsampleLower : primorialBlockLower k ≤ squarePrefixEndpoint n :=
      hLowerNext.le.trans (squarePrefixEndpoint_mono_run hmn)
    have hsampleUpper : squarePrefixEndpoint n ≤ primorialBlockUpper k :=
      hnLower.trans hupper
    have hrightEdge :=
      norm_sq_primorialWheelResidual_sub_squareEndpoint_lt_nine_mul_succ
        k n x hsampleLower hnLower hnNext hupper
    have hleftEdge := squareRun_firstEdge_sq_le_nine
      hmLower hLowerNext hnextx
    by_cases heq : n = m + 1
    · subst n
      rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
        k hlower.le hupper]
      have hrightM :
          ‖mertensSummatory x -
            mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 <
            9 * (((x + 1 : ℕ) : ℝ)) := by
        rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
            k hlower.le hupper,
          RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
            k hsampleLower hsampleUpper] at hrightEdge
        convert hrightEdge using 1
        ring
      have hsplit :
          mertensSummatory x - mertensSummatory (primorialBlockLower k) =
            (mertensSummatory (squarePrefixEndpoint (m + 1)) -
              mertensSummatory (primorialBlockLower k)) +
            (mertensSummatory x -
              mertensSummatory (squarePrefixEndpoint (m + 1))) := by ring
      rw [hsplit]
      have htwo := squareRun_norm_sq_add_le_two
        (mertensSummatory (squarePrefixEndpoint (m + 1)) -
          mertensSummatory (primorialBlockLower k))
        (mertensSummatory x - mertensSummatory (squarePrefixEndpoint (m + 1)))
      have hlin := squareRun_linear_le_rpow hε x
      have hp0 : 0 ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) :=
        Real.rpow_nonneg (by positivity) _
      calc
        ‖(mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)) +
          (mertensSummatory x -
            mertensSummatory (squarePrefixEndpoint (m + 1)))‖ ^ 2 ≤
          2 * ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)‖ ^ 2 +
          2 * ‖mertensSummatory x -
            mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 := htwo
        _ ≤ 36 * (((x + 1 : ℕ) : ℝ)) := by nlinarith
        _ ≤ 36 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) :=
          mul_le_mul_of_nonneg_left hlin (by norm_num)
        _ ≤ (4 * C + 54) * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
          apply mul_le_mul_of_nonneg_right _ hp0
          linarith
    · have hstrict : m + 1 < n := by omega
      have ha : 1 ≤ m + 2 := by omega
      have hab : m + 2 ≤ n := by omega
      have hrunRaw := hrunBound k (m + 2) n ha hab
        hLowerNext.le hsampleUpper
      have hrunEq := RHLean.Proof.sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub
        (m + 2) n ha (by omega)
      rw [hrunEq] at hrunRaw
      have hmiddle :
          ‖mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 ≤
            C * Real.rpow (((squarePrefixEndpoint n + 1 : ℕ) : ℝ))
              (1 + ε) := by
        simpa [squarePrefixMertens] using hrunRaw
      have hmiddleMono := squareRun_rpow_mono hε hnLower
      have hmiddleX :
          ‖mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 ≤
            C * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) :=
        hmiddle.trans (mul_le_mul_of_nonneg_left hmiddleMono hC)
      have hrightM :
          ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)‖ ^ 2 <
            9 * (((x + 1 : ℕ) : ℝ)) := by
        rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
            k hlower.le hupper,
          RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
            k hsampleLower hsampleUpper] at hrightEdge
        convert hrightEdge using 1
        ring
      rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
        k hlower.le hupper]
      have hsplit :
          mertensSummatory x - mertensSummatory (primorialBlockLower k) =
            (mertensSummatory (squarePrefixEndpoint (m + 1)) -
              mertensSummatory (primorialBlockLower k)) +
            ((mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (squarePrefixEndpoint (m + 1))) +
             (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n))) := by
        ring
      rw [hsplit]
      have hinner := squareRun_norm_sq_add_le_two
        (mertensSummatory (squarePrefixEndpoint n) -
          mertensSummatory (squarePrefixEndpoint (m + 1)))
        (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n))
      have houter := squareRun_norm_sq_add_le_two
        (mertensSummatory (squarePrefixEndpoint (m + 1)) -
          mertensSummatory (primorialBlockLower k))
        ((mertensSummatory (squarePrefixEndpoint n) -
          mertensSummatory (squarePrefixEndpoint (m + 1))) +
         (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)))
      have hlin := squareRun_linear_le_rpow hε x
      calc
        ‖(mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)) +
          ((mertensSummatory (squarePrefixEndpoint n) -
            mertensSummatory (squarePrefixEndpoint (m + 1))) +
           (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)))‖ ^ 2 ≤
          2 * ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)‖ ^ 2 +
          2 * ‖(mertensSummatory (squarePrefixEndpoint n) -
            mertensSummatory (squarePrefixEndpoint (m + 1))) +
           (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n))‖ ^ 2 :=
          houter
        _ ≤ 2 * ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)‖ ^ 2 +
          4 * ‖mertensSummatory (squarePrefixEndpoint n) -
            mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 +
          4 * ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)‖ ^ 2 := by
          nlinarith
        _ ≤ 4 * (C * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε)) +
            54 * (((x + 1 : ℕ) : ℝ)) := by
          nlinarith
        _ ≤ 4 * (C * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε)) +
            54 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
          gcongr
        _ = (4 * C + 54) * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
          ring

/-- Maximal signed complete-square runs and pinned primorial residuals are the
same RH-scale criterion. -/
theorem squareRunEnergyBounded_iff_primorialResidualBounded :
    SquareRunEnergyBoundedStatement ↔
      PrimeWheelResidualBoundedStatement primorialWheelFamily := by
  exact ⟨primorialResidualBounded_of_squareRunEnergyBounded,
    squareRunEnergyBounded_of_primorialResidualBounded⟩

/-- Hence maximal signed square runs are also exactly the repository's global
Mertens energy criterion. -/
theorem squareRunEnergyBounded_iff_mertensEnergy :
    SquareRunEnergyBoundedStatement ↔ MertensEnergyBoundedStatement := by
  exact squareRunEnergyBounded_iff_primorialResidualBounded.trans
    primorialWheel_residualBounded_iff_mertensEnergy

end RHLean.Analysis
