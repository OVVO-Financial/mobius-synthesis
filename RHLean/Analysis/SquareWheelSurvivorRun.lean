import Mathlib
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity
import RHLean.Analysis.SquareWheelSurvivorIncrement

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

No estimate for the survivor-centered run coordinate is asserted here.
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

/-- **Exact run-level survivor centering.**  Two nonzero-response samples in one
primorial block differ by the survivor-centered run coordinate plus only the
low-prefix and death-process endpoint differences.  No sum over intermediate
square increments appears. -/
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

/-- **Unconditional run-level remainder bound.**  For every positive `epsilon`,
the whole difference between `H_b-H_a` and the signed survivor-centered run
coordinate is bounded by the already-proved low-prefix linear term and the
subpolynomial death-process endpoints.  No local increment norm is summed. -/
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
