import Mathlib
import RHLean.Arithmetic.PrimorialWheelScaleGrowth
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity
import RHLean.Analysis.PrimeWheelHarmonicCriterion
import RHLean.Analysis.PrimeWheelRHBridge

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

private theorem norm_sq_add_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem two_mul_rpow_endpoint_le
    {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    2 * Real.rpow ((primorialEndpoint k + 1 : ℕ) : ℝ) (1 + ε) ≤
      Real.rpow 2 (-ε) *
        Real.rpow ((primorialEndpoint (k + 1) + 1 : ℕ) : ℝ) (1 + ε) := by
  have hscaleNat := two_mul_primorialEndpoint_add_one_le_succ hk
  have hscale :
      (2 : ℝ) * ((primorialEndpoint k + 1 : ℕ) : ℝ) ≤
        ((primorialEndpoint (k + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hscaleNat
  have hexp : 0 ≤ 1 + ε := by linarith
  have hpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ (2 : ℝ) * ((primorialEndpoint k + 1 : ℕ) : ℝ))
    hscale hexp
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hq0 : 0 ≤ Real.rpow 2 (-ε) := Real.rpow_nonneg (by norm_num) _
  have hfactor :
      Real.rpow 2 (-ε) * Real.rpow 2 (1 + ε) = 2 := by
    calc
      Real.rpow 2 (-ε) * Real.rpow 2 (1 + ε) =
          Real.rpow 2 ((-ε) + (1 + ε)) :=
        (Real.rpow_add htwo (-ε) (1 + ε)).symm
      _ = Real.rpow 2 1 := by
        congr 1
        ring
      _ = 2 := by norm_num
  calc
    2 * Real.rpow ((primorialEndpoint k + 1 : ℕ) : ℝ) (1 + ε) =
        (Real.rpow 2 (-ε) * Real.rpow 2 (1 + ε)) *
          Real.rpow ((primorialEndpoint k + 1 : ℕ) : ℝ) (1 + ε) := by
      rw [hfactor]
    _ = Real.rpow 2 (-ε) *
        (Real.rpow 2 (1 + ε) *
          Real.rpow ((primorialEndpoint k + 1 : ℕ) : ℝ) (1 + ε)) := by ring
    _ = Real.rpow 2 (-ε) *
        Real.rpow ((2 : ℝ) * ((primorialEndpoint k + 1 : ℕ) : ℝ))
          (1 + ε) := by
      apply congrArg (fun t : ℝ => Real.rpow 2 (-ε) * t)
      exact (Real.mul_rpow (by norm_num) (by positivity)).symm
    _ ≤ Real.rpow 2 (-ε) *
        Real.rpow ((primorialEndpoint (k + 1) + 1 : ℕ) : ℝ) (1 + ε) :=
      mul_le_mul_of_nonneg_left hpow hq0

/-- A global Mertens-energy bound immediately controls every synchronized
primorial residual. -/
theorem primorialWheel_residualBounded_of_mertensEnergy
    (hM : MertensEnergyBoundedStatement) :
    PrimeWheelResidualBoundedStatement primorialWheelFamily := by
  intro ε hε
  rcases hM ε hε with ⟨C, hC, hbound⟩
  refine ⟨4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro k x hlower hupper
  change primorialBlockLower k < x at hlower
  change x ≤ primorialBlockUpper k at hupper
  change ‖(((primorialWheelSystem k).residual x : ℤ) : ℂ)‖ ^ 2 ≤ _
  rw [primorialWheel_residual_cast_eq_mertens_sub k hlower hupper]
  have hsq := norm_sq_add_le_two
    (mertensSummatory x) (-mertensSummatory (primorialBlockLower k))
  have hbaseNat : primorialBlockLower k + 1 ≤ x + 1 := by omega
  have hbase :
      ((primorialBlockLower k + 1 : ℕ) : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast hbaseNat
  have hpow := Real.rpow_le_rpow (by positivity) hbase (by linarith : 0 ≤ 1 + ε)
  have hlowerBound := (hbound (primorialBlockLower k)).trans
    (mul_le_mul_of_nonneg_left hpow hC)
  have hlowerNegBound :
      ‖-mertensSummatory (primorialBlockLower k)‖ ^ 2 ≤
        C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
    simpa only [norm_neg] using hlowerBound
  have hxBound := hbound x
  calc
    ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ^ 2 =
        ‖mertensSummatory x + -mertensSummatory (primorialBlockLower k)‖ ^ 2 := by
      rw [sub_eq_add_neg]
    _ ≤ 2 * ‖mertensSummatory x‖ ^ 2 +
          2 * ‖-mertensSummatory (primorialBlockLower k)‖ ^ 2 := hsq
    _ ≤ 2 * (C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)) +
          2 * (C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hxBound (by norm_num))
        (mul_le_mul_of_nonneg_left hlowerNegBound (by norm_num))
    _ = 4 * C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by ring

/-- The synchronized primorial residual estimate controls all endpoint Mertens
values.  The proof is an elementary contracting recurrence using the factor-two
shifted growth of successive primorial endpoints after the first block. -/
theorem primorialWheel_endpointEnergyBounded_of_residualBounded
    (hR : PrimeWheelResidualBoundedStatement primorialWheelFamily) :
    ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ k : ℕ,
          ‖mertensSummatory (primorialEndpoint k)‖ ^ 2 ≤
            D * Real.rpow ((primorialEndpoint k + 1 : ℕ) : ℝ) (1 + ε) := by
  intro ε hε
  rcases hR ε hε with ⟨C, hC, hbound⟩
  let q : ℝ := Real.rpow 2 (-ε)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let T : ℝ := (2 * C) / (1 - q)
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hT0 : 0 ≤ T := div_nonneg (mul_nonneg (by norm_num) hC) hden.le
  have hTrel : (1 - q) * T = 2 * C := by
    dsimp [T]
    field_simp
  let B0 : ℝ := ‖mertensSummatory (primorialEndpoint 0)‖ ^ 2
  let B1 : ℝ := ‖mertensSummatory (primorialEndpoint 1)‖ ^ 2
  let D : ℝ := B0 + B1 + 1 + T
  have hB0 : 0 ≤ B0 := sq_nonneg _
  have hB1 : 0 ≤ B1 := sq_nonneg _
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hcontract : q * D + 2 * C ≤ D := by
    dsimp [D]
    nlinarith
  refine ⟨D, hD0, ?_⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk0 : k = 0
      · subst k
        have hbase :
            (1 : ℝ) ≤ ((primorialEndpoint 0 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le (primorialEndpoint 0))
        have hpow := Real.one_le_rpow hbase (by linarith : 0 ≤ 1 + ε)
        have hBD : B0 ≤ D := by dsimp [D]; nlinarith
        calc
          ‖mertensSummatory (primorialEndpoint 0)‖ ^ 2 = B0 := rfl
          _ ≤ D := hBD
          _ ≤ D * Real.rpow ((primorialEndpoint 0 + 1 : ℕ) : ℝ) (1 + ε) := by
            simpa using mul_le_mul_of_nonneg_left hpow hD0
      by_cases hk1 : k = 1
      · subst k
        have hbase :
            (1 : ℝ) ≤ ((primorialEndpoint 1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le (primorialEndpoint 1))
        have hpow := Real.one_le_rpow hbase (by linarith : 0 ≤ 1 + ε)
        have hBD : B1 ≤ D := by dsimp [D]; nlinarith
        calc
          ‖mertensSummatory (primorialEndpoint 1)‖ ^ 2 = B1 := rfl
          _ ≤ D := hBD
          _ ≤ D * Real.rpow ((primorialEndpoint 1 + 1 : ℕ) : ℝ) (1 + ε) := by
            simpa using mul_le_mul_of_nonneg_left hpow hD0
      have hkge : 2 ≤ k := by omega
      let j := k - 1
      have hj1 : 1 ≤ j := by dsimp [j]; omega
      have hjk : j < k := by dsimp [j]; omega
      have hprev := ih j hjk
      have hjupper : primorialBlockUpper j = primorialEndpoint k := by
        unfold primorialBlockUpper
        congr 1
        dsimp [j]
        omega
      have hjlower : primorialBlockLower j = primorialEndpoint j := rfl
      have hinc0 := hbound j (primorialBlockUpper j)
        (by change primorialBlockLower j < primorialBlockUpper j
            exact primorialEndpoint_strictMono (Nat.lt_succ_self j))
        (by change primorialBlockUpper j ≤ primorialBlockUpper j; exact le_rfl)
      have hinc :
          ‖(((primorialWheelSystem j).residual (primorialBlockUpper j) : ℤ) : ℂ)‖ ^ 2 ≤
            C * Real.rpow ((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ) (1 + ε) := by
        simpa [primorialWheelFamily, primorialBlockUpper] using hinc0
      have hres := primorialWheel_endpointResidual_cast_eq_mertens_sub j
      have hsum :
          mertensSummatory (primorialEndpoint k) =
            mertensSummatory (primorialEndpoint j) +
              (((primorialWheelSystem j).residual (primorialBlockUpper j) : ℤ) : ℂ) := by
        rw [hres, hjupper, hjlower]
        ring
      have hadd := norm_sq_add_le_two
        (mertensSummatory (primorialEndpoint j))
        ((((primorialWheelSystem j).residual (primorialBlockUpper j) : ℤ) : ℂ))
      have hscale := two_mul_rpow_endpoint_le hε hj1
      have hsD :
          2 * (D * Real.rpow ((primorialEndpoint j + 1 : ℕ) : ℝ) (1 + ε)) ≤
            (q * D) * Real.rpow ((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ) (1 + ε) := by
        calc
          2 * (D * Real.rpow ((primorialEndpoint j + 1 : ℕ) : ℝ) (1 + ε)) =
              D * (2 * Real.rpow ((primorialEndpoint j + 1 : ℕ) : ℝ) (1 + ε)) := by ring
          _ ≤ D * (q * Real.rpow ((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ) (1 + ε)) :=
            mul_le_mul_of_nonneg_left hscale hD0
          _ = (q * D) * Real.rpow ((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ) (1 + ε) := by ring
      rw [hsum]
      calc
        ‖mertensSummatory (primorialEndpoint j) +
            (((primorialWheelSystem j).residual (primorialBlockUpper j) : ℤ) : ℂ)‖ ^ 2
            ≤ 2 * ‖mertensSummatory (primorialEndpoint j)‖ ^ 2 +
                2 * ‖(((primorialWheelSystem j).residual
                  (primorialBlockUpper j) : ℤ) : ℂ)‖ ^ 2 := hadd
        _ ≤ 2 * (D * Real.rpow ((primorialEndpoint j + 1 : ℕ) : ℝ) (1 + ε)) +
              2 * (C * Real.rpow ((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ) (1 + ε)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hprev (by norm_num))
            (mul_le_mul_of_nonneg_left hinc (by norm_num))
        _ ≤ (q * D) * Real.rpow ((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ) (1 + ε) +
              2 * (C * Real.rpow ((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ) (1 + ε)) :=
          add_le_add hsD le_rfl
        _ = (q * D + 2 * C) *
              Real.rpow ((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ) (1 + ε) := by ring
        _ ≤ D * Real.rpow ((primorialEndpoint k + 1 : ℕ) : ℝ) (1 + ε) := by
          have hpownonneg := Real.rpow_nonneg
            (show 0 ≤ (((primorialEndpoint (j + 1) + 1 : ℕ) : ℝ)) by positivity)
            (1 + ε)
          have hlast := mul_le_mul_of_nonneg_right hcontract hpownonneg
          have hjk' : j + 1 = k := by dsimp [j]; omega
          simpa [hjk'] using hlast

/-- The primorial residual criterion is exactly the ordinary global
Mertens-energy criterion.  No prime-number theorem or asymptotic prime estimate
enters this transfer. -/
theorem primorialWheel_residualBounded_iff_mertensEnergy :
    PrimeWheelResidualBoundedStatement primorialWheelFamily ↔
      MertensEnergyBoundedStatement := by
  constructor
  · intro hR ε hε
    rcases hR ε hε with ⟨C, hC, hresidual⟩
    rcases primorialWheel_endpointEnergyBounded_of_residualBounded hR ε hε with
      ⟨D, hD, hendpoint⟩
    let K : ℝ := 2 * D + 2 * C
    have hK0 : 0 ≤ K := by dsimp [K]; nlinarith
    refine ⟨K, hK0, ?_⟩
    intro x
    by_cases hx0 : x = 0
    · subst x
      simpa [mertensSummatory] using hK0
    by_cases hx1 : x = 1
    · subst x
      have h := hendpoint 0
      have hDK : D ≤ K := by dsimp [K]; nlinarith
      have hp := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2) (1 + ε)
      simpa [primorialEndpoint_zero, K] using
        h.trans (mul_le_mul_of_nonneg_right hDK hp)
    have hx2 : 2 ≤ x := by omega
    let k := primorialBlockIndex x
    have hlower : primorialBlockLower k < x :=
      primorialBlockLower_blockIndex_lt hx2
    have hupper : x ≤ primorialBlockUpper k :=
      le_primorialBlockUpper_blockIndex x
    have hprefix := primorialWheel_residual_cast_eq_mertens_sub k hlower hupper
    have hsum :
        mertensSummatory x = mertensSummatory (primorialBlockLower k) +
          (((primorialWheelSystem k).residual x : ℤ) : ℂ) := by
      rw [hprefix]
      ring
    have hadd := norm_sq_add_le_two
      (mertensSummatory (primorialBlockLower k))
      ((((primorialWheelSystem k).residual x : ℤ) : ℂ))
    have hendpointLower :
        ‖mertensSummatory (primorialBlockLower k)‖ ^ 2 ≤
          D * Real.rpow ((primorialBlockLower k + 1 : ℕ) : ℝ) (1 + ε) := by
      simpa [primorialBlockLower] using hendpoint k
    have hbaseNat : primorialBlockLower k + 1 ≤ x + 1 := by omega
    have hbase :
        ((primorialBlockLower k + 1 : ℕ) : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
      exact_mod_cast hbaseNat
    have hpow := Real.rpow_le_rpow (by positivity) hbase (by linarith : 0 ≤ 1 + ε)
    have hendpointX := hendpointLower.trans
      (mul_le_mul_of_nonneg_left hpow hD)
    have hlowerFam : (primorialWheelFamily k).lower < x := by
      change primorialBlockLower k < x
      exact hlower
    have hupperFam : x ≤ (primorialWheelFamily k).upper := by
      change x ≤ primorialBlockUpper k
      exact hupper
    have hresidual0 := hresidual k x hlowerFam hupperFam
    have hresidualX :
        ‖(((primorialWheelSystem k).residual x : ℤ) : ℂ)‖ ^ 2 ≤
          C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
      simpa [primorialWheelFamily] using hresidual0
    rw [hsum]
    calc
      ‖mertensSummatory (primorialBlockLower k) +
          (((primorialWheelSystem k).residual x : ℤ) : ℂ)‖ ^ 2
          ≤ 2 * ‖mertensSummatory (primorialBlockLower k)‖ ^ 2 +
              2 * ‖(((primorialWheelSystem k).residual x : ℤ) : ℂ)‖ ^ 2 := hadd
      _ ≤ 2 * (D * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)) +
            2 * (C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hendpointX (by norm_num))
          (mul_le_mul_of_nonneg_left hresidualX (by norm_num))
      _ = K * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
        dsimp [K]
        ring
  · exact primorialWheel_residualBounded_of_mertensEnergy

/-- Canonical, fully proved global transfer package for the concrete primorial
wheel family. -/
def primorialWheelMertensBridge :
    PrimeWheelMertensBridge primorialWheelFamily where
  residual_iff_mertensEnergy := primorialWheel_residualBounded_iff_mertensEnergy

end RHLean.Analysis
