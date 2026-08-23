import Mathlib
import RHLean.Proof.SquareRootMertensEndpointAmplification
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Fixed square-root amplification closes the Mertens energy exponent

The open square-root endpoint theorem allows an arbitrary fixed absolute
amplification constant `A`:

`(M(R^2-1)-1)^2 <= A * R^2 * K_R`,

where `K_R` controls the shifted critical energy on all lower arguments `y<R`.
A subunit contraction is not required.  For each `epsilon > 0`, choose an onset
at which `4*A <= R^epsilon`.  Strong induction on the physical integer `x`
then closes the full shifted Mertens estimate.  The unfinished part of one
square block contributes only `O(R^2)` after squaring.

Thus the fixed-amplification endpoint statement implies the repository's
standard Mertens energy criterion.  The only number-theoretic input is the open
endpoint statement itself; everything here is deterministic square-root
bookkeeping.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

/-- Shifted complex Mertens energy.  The shift by one is the exceptional source
omitted from the canonical ancestry universe. -/
def shiftedMertensEnergy (x : ℕ) : ℝ :=
  ‖RHLean.Analysis.mertensSummatory x - 1‖ ^ 2

/-- The shifted complex energy is the real square of the integer Mertens
numerator used by the endpoint amplification theorem. -/
theorem shiftedMertensEnergy_eq_intSquare (x : ℕ) :
    shiftedMertensEnergy x =
      (((mertensSummatoryInt x - 1 : ℤ) : ℝ) ^ 2) := by
  unfold shiftedMertensEnergy
  rw [← mertensSummatoryInt_cast x]
  have hcast :
      (((mertensSummatoryInt x : ℤ) : ℂ) - 1) =
        (((mertensSummatoryInt x - 1 : ℤ) : ℂ)) := by
    push_cast
    ring
  rw [hcast, Complex.norm_intCast]
  exact sq_abs (((mertensSummatoryInt x - 1 : ℤ) : ℝ))

/-- Crude shifted bound used only on the finite base range. -/
theorem norm_shiftedMertens_le_succ (x : ℕ) :
    ‖RHLean.Analysis.mertensSummatory x - 1‖ ≤ ((x + 1 : ℕ) : ℝ) := by
  have hM := RHLean.Analysis.norm_mertensSummatory_sub_le 0 x (Nat.zero_le x)
  rw [RHLean.Analysis.mertensSummatory_zero, sub_zero] at hM
  calc
    ‖RHLean.Analysis.mertensSummatory x - 1‖ ≤
        ‖RHLean.Analysis.mertensSummatory x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = ‖RHLean.Analysis.mertensSummatory x‖ + 1 := by norm_num
    _ ≤ (x : ℝ) + 1 := add_le_add_right hM 1
    _ = ((x + 1 : ℕ) : ℝ) := by norm_cast

private theorem shifted_norm_sq_add_le_two (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

private theorem rpow_sq_one_add (r ε : ℝ) (hr : 0 ≤ r) :
    Real.rpow (r ^ 2) (1 + ε) = Real.rpow r (2 + 2 * ε) := by
  have htwo : Real.rpow r (2 : ℝ) = r ^ (2 : ℕ) :=
    Real.rpow_natCast r 2
  calc
    Real.rpow (r ^ 2) (1 + ε) =
        Real.rpow (Real.rpow r (2 : ℝ)) (1 + ε) := by
      congr 1
      exact htwo.symm
    _ = Real.rpow r ((2 : ℝ) * (1 + ε)) :=
      (Real.rpow_mul hr (2 : ℝ) (1 + ε)).symm
    _ = Real.rpow r (2 + 2 * ε) := by ring_nf

private theorem rpow_two_add_two_mul_eq_sq_mul_rpow_sq
    (r ε : ℝ) (hr : 0 < r) :
    Real.rpow r (2 + 2 * ε) =
      r ^ 2 * (Real.rpow r ε) ^ 2 := by
  have htwo : Real.rpow r (2 : ℝ) = r ^ (2 : ℕ) :=
    Real.rpow_natCast r 2
  have hsplit :
      Real.rpow r (2 + 2 * ε) = Real.rpow r (2 : ℝ) * Real.rpow r (2 * ε) :=
    Real.rpow_add (x := r) hr 2 (2 * ε)
  -- `Real.rpow_add` is stated with `^` notation, whose head symbol is
  -- `HPow.hPow` rather than `Real.rpow`; `rw` matches on that head, so the
  -- lemma is applied as a term (which is checked up to unfolding the `Pow`
  -- instance) instead of being rewritten in.
  have hdouble :
      Real.rpow r (2 * ε) = Real.rpow r ε * Real.rpow r ε := by
    rw [show (2 : ℝ) * ε = ε + ε by ring]
    exact Real.rpow_add (x := r) hr ε ε
  rw [hsplit, htwo, hdouble]
  ring

/-- A fixed absolute endpoint amplification constant gives the full shifted
Mertens critical-energy bound, with an arbitrarily small exponent loss. -/
theorem shiftedMertensEnergyBounded_of_squareRootEndpointAmplification
    (hamp : SquareRootMertensEndpointAmplificationStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x : ℕ,
          shiftedMertensEnergy x ≤
            C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
  rintro ε hε
  rcases hamp with ⟨A, -, hamp⟩
  have htend :
      Filter.Tendsto (fun R : ℕ => Real.rpow (R : ℝ) ε)
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ R : ℕ in Filter.atTop,
      4 * A ≤ Real.rpow (R : ℝ) ε :=
    (Filter.tendsto_atTop.1 htend) (4 * A)
  rcases (Filter.eventually_atTop.1 hevent) with ⟨N, hN⟩
  let R0 : ℕ := max 2 N
  let C : ℝ := 36 + ((R0 ^ 2 + 1 : ℕ) : ℝ)
  have hbaseline : (0 : ℝ) ≤ ((R0 ^ 2 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  have hC36 : 36 ≤ C := by
    dsimp [C]
    linarith
  have hCR0 : ((R0 ^ 2 + 1 : ℕ) : ℝ) ≤ C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
      have hbase : (1 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
        have hone : (1 : ℕ) ≤ x + 1 := by omega
        exact_mod_cast hone
      have hexp : (1 : ℝ) ≤ 1 + ε := by linarith
      have hbasePow :
          ((x + 1 : ℕ) : ℝ) ≤ Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hbase hexp
      by_cases hxbase : x < R0 ^ 2
      · have hnorm := norm_shiftedMertens_le_succ x
        have hx1Nat : x + 1 ≤ R0 ^ 2 + 1 :=
          Nat.succ_le_succ hxbase.le
        have hx1 : ((x + 1 : ℕ) : ℝ) ≤ ((R0 ^ 2 + 1 : ℕ) : ℝ) := by
          exact_mod_cast hx1Nat
        have hxpos : (0 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by positivity
        have hsq : shiftedMertensEnergy x ≤ ((x + 1 : ℕ) : ℝ) ^ 2 := by
          unfold shiftedMertensEnergy
          have hnonneg : 0 ≤ ‖RHLean.Analysis.mertensSummatory x - 1‖ :=
            norm_nonneg _
          nlinarith [sq_nonneg (‖RHLean.Analysis.mertensSummatory x - 1‖ -
            ((x + 1 : ℕ) : ℝ))]
        have hxC : ((x + 1 : ℕ) : ℝ) ≤ C := hx1.trans hCR0
        have hlin : ((x + 1 : ℕ) : ℝ) ^ 2 ≤ C * ((x + 1 : ℕ) : ℝ) := by
          have hmul := mul_nonneg hxpos (sub_nonneg.mpr hxC)
          nlinarith
        exact hsq.trans (hlin.trans
          (mul_le_mul_of_nonneg_left hbasePow hC))
      · have hxlarge : R0 ^ 2 ≤ x := Nat.le_of_not_gt hxbase
        let R : ℕ := Nat.sqrt x
        have hRsq : R ^ 2 ≤ x := Nat.sqrt_le' x
        have hxltNext : x < (R + 1) ^ 2 := Nat.lt_succ_sqrt' x
        have h2R0 : 2 ≤ R0 := le_max_left 2 N
        have hNR0 : N ≤ R0 := le_max_right 2 N
        have hR0 : R0 ≤ R := by
          by_contra hnot
          have hRlt : R + 1 ≤ R0 := by omega
          have hsquares : (R + 1) ^ 2 ≤ R0 ^ 2 :=
            Nat.pow_le_pow_left hRlt 2
          exact absurd (lt_of_lt_of_le (hxltNext.trans_le hsquares) hxlarge)
            (lt_irrefl x)
        have hR2 : 2 ≤ R := h2R0.trans hR0
        have hRpos : 0 < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
        have hRnonneg : 0 ≤ (R : ℝ) := le_of_lt hRpos
        have hNleR : N ≤ R := hNR0.trans hR0
        have honset : 4 * A ≤ Real.rpow (R : ℝ) ε := hN R hNleR
        let K : ℝ := C * Real.rpow (R : ℝ) ε
        have hrpowNonneg : 0 ≤ Real.rpow (R : ℝ) ε :=
          Real.rpow_nonneg hRnonneg ε
        have hKnonneg : 0 ≤ K := mul_nonneg hC hrpowNonneg
        have hEnvelope : LowerMertensCriticalEnvelope R K := by
          refine ⟨hKnonneg, ?_⟩
          intro y hyR
          have hRleSq : R ≤ R ^ 2 := by nlinarith [hR2]
          have hRx : R ≤ x := hRleSq.trans hRsq
          have hyx : y < x := hyR.trans_le hRx
          have hiy := ih y hyx
          rw [shiftedMertensEnergy_eq_intSquare] at hiy
          have hy1R : y + 1 ≤ R := by omega
          have hpowMono :
              Real.rpow ((y + 1 : ℕ) : ℝ) ε ≤ Real.rpow (R : ℝ) ε :=
            Real.rpow_le_rpow (by positivity) (by exact_mod_cast hy1R)
              (by linarith)
          have hfactor :
              Real.rpow ((y + 1 : ℕ) : ℝ) (1 + ε) =
                ((y + 1 : ℕ) : ℝ) * Real.rpow ((y + 1 : ℕ) : ℝ) ε := by
            calc
              Real.rpow ((y + 1 : ℕ) : ℝ) (1 + ε) =
                  Real.rpow ((y + 1 : ℕ) : ℝ) 1 *
                    Real.rpow ((y + 1 : ℕ) : ℝ) ε :=
                Real.rpow_add (x := ((y + 1 : ℕ) : ℝ)) (by positivity) 1 ε
              _ = ((y + 1 : ℕ) : ℝ) * Real.rpow ((y + 1 : ℕ) : ℝ) ε := by
                have hrpowOne :
                    Real.rpow ((y + 1 : ℕ) : ℝ) 1 = ((y + 1 : ℕ) : ℝ) :=
                  Real.rpow_one _
                rw [hrpowOne]
          rw [hfactor] at hiy
          dsimp [K]
          have hcy : 0 ≤ C * ((y + 1 : ℕ) : ℝ) := mul_nonneg hC (by positivity)
          calc
            (((mertensSummatoryInt y - 1 : ℤ) : ℝ) ^ 2) ≤
                C * (((y + 1 : ℕ) : ℝ) * Real.rpow ((y + 1 : ℕ) : ℝ) ε) := hiy
            _ = (C * ((y + 1 : ℕ) : ℝ)) * Real.rpow ((y + 1 : ℕ) : ℝ) ε := by
              ring
            _ ≤ (C * ((y + 1 : ℕ) : ℝ)) * Real.rpow (R : ℝ) ε :=
              mul_le_mul_of_nonneg_left hpowMono hcy
            _ = (C * Real.rpow (R : ℝ) ε) * ((y + 1 : ℕ) : ℝ) := by ring
        have hendpointInt := hamp R K hR2 hEnvelope
        let e : ℕ := squareRootEndpoint R
        have hedef : e = R ^ 2 - 1 := rfl
        have heLe : e ≤ x := by
          rw [hedef]
          omega
        have hendpoint :
            shiftedMertensEnergy e ≤ A * (R : ℝ) ^ 2 * K := by
          rw [shiftedMertensEnergy_eq_intSquare]
          exact hendpointInt
        have hrpowSq :
            (R : ℝ) ^ 2 * (Real.rpow (R : ℝ) ε) ^ 2 =
              Real.rpow ((R : ℝ) ^ 2) (1 + ε) := by
          rw [rpow_sq_one_add (R : ℝ) ε hRnonneg,
            rpow_two_add_two_mul_eq_sq_mul_rpow_sq (R : ℝ) ε hRpos]
        have hRsqSucc : R ^ 2 ≤ x + 1 := by omega
        have htargetBase : ((R : ℝ) ^ 2) ≤ ((x + 1 : ℕ) : ℝ) := by
          exact_mod_cast hRsqSucc
        have htargetPow :
            Real.rpow ((R : ℝ) ^ 2) (1 + ε) ≤
              Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) :=
          Real.rpow_le_rpow (by positivity) htargetBase (by linarith)
        have hendpointTarget :
            2 * shiftedMertensEnergy e ≤
              (C / 2) * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
          have hhalf : 2 * A ≤ Real.rpow (R : ℝ) ε / 2 := by linarith
          have hTnonneg :
              0 ≤ C * (R : ℝ) ^ 2 * Real.rpow (R : ℝ) ε :=
            mul_nonneg (mul_nonneg hC (by positivity)) hrpowNonneg
          have hmul := mul_le_mul_of_nonneg_right hhalf hTnonneg
          have hscale :
              2 * (A * (R : ℝ) ^ 2 * K) ≤
                (C / 2) *
                  ((R : ℝ) ^ 2 * (Real.rpow (R : ℝ) ε) ^ 2) := by
            dsimp [K]
            calc
              2 * (A * (R : ℝ) ^ 2 * (C * Real.rpow (R : ℝ) ε)) =
                  2 * A * (C * (R : ℝ) ^ 2 * Real.rpow (R : ℝ) ε) := by ring
              _ ≤ Real.rpow (R : ℝ) ε / 2 *
                    (C * (R : ℝ) ^ 2 * Real.rpow (R : ℝ) ε) := hmul
              _ = (C / 2) *
                    ((R : ℝ) ^ 2 * (Real.rpow (R : ℝ) ε) ^ 2) := by ring
          calc
            2 * shiftedMertensEnergy e ≤ 2 * (A * (R : ℝ) ^ 2 * K) := by
              linarith
            _ ≤ (C / 2) *
                  ((R : ℝ) ^ 2 * (Real.rpow (R : ℝ) ε) ^ 2) := hscale
            _ = (C / 2) * Real.rpow ((R : ℝ) ^ 2) (1 + ε) := by rw [hrpowSq]
            _ ≤ (C / 2) * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) :=
              mul_le_mul_of_nonneg_left htargetPow (by linarith)
        have hgapNat : x - e ≤ 3 * R := by
          have hsquare : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
          rw [hsquare] at hxltNext
          rw [hedef]
          omega
        have hgap := RHLean.Analysis.norm_mertensSummatory_sub_le e x heLe
        have hgapR :
            ‖RHLean.Analysis.mertensSummatory x -
                RHLean.Analysis.mertensSummatory e‖ ≤ 3 * (R : ℝ) :=
          hgap.trans (by exact_mod_cast hgapNat)
        have hgapSq :
            ‖RHLean.Analysis.mertensSummatory x -
                RHLean.Analysis.mertensSummatory e‖ ^ 2 ≤
              9 * (R : ℝ) ^ 2 := by
          have hn : 0 ≤ ‖RHLean.Analysis.mertensSummatory x -
              RHLean.Analysis.mertensSummatory e‖ := norm_nonneg _
          nlinarith [sq_nonneg (‖RHLean.Analysis.mertensSummatory x -
            RHLean.Analysis.mertensSummatory e‖ - 3 * (R : ℝ))]
        have hgapTarget :
            2 * ‖RHLean.Analysis.mertensSummatory x -
                RHLean.Analysis.mertensSummatory e‖ ^ 2 ≤
              (C / 2) * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
          have hC2 : 18 ≤ C / 2 := by linarith
          have h18 : 18 * (R : ℝ) ^ 2 ≤ (C / 2) * ((x + 1 : ℕ) : ℝ) := by
            calc
              18 * (R : ℝ) ^ 2 ≤ 18 * ((x + 1 : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_left htargetBase (by norm_num)
              _ ≤ (C / 2) * ((x + 1 : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_right hC2 (by positivity)
          calc
            2 * ‖RHLean.Analysis.mertensSummatory x -
                RHLean.Analysis.mertensSummatory e‖ ^ 2 ≤
                18 * (R : ℝ) ^ 2 := by linarith
            _ ≤ (C / 2) * ((x + 1 : ℕ) : ℝ) := h18
            _ ≤ (C / 2) * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) :=
              mul_le_mul_of_nonneg_left hbasePow (by linarith)
        have hsplitComplex :
            RHLean.Analysis.mertensSummatory x - 1 =
              (RHLean.Analysis.mertensSummatory e - 1) +
                (RHLean.Analysis.mertensSummatory x -
                  RHLean.Analysis.mertensSummatory e) := by ring
        calc
          shiftedMertensEnergy x =
              ‖(RHLean.Analysis.mertensSummatory e - 1) +
                (RHLean.Analysis.mertensSummatory x -
                  RHLean.Analysis.mertensSummatory e)‖ ^ 2 := by
            unfold shiftedMertensEnergy
            rw [hsplitComplex]
          _ ≤ 2 * shiftedMertensEnergy e +
                2 * ‖RHLean.Analysis.mertensSummatory x -
                  RHLean.Analysis.mertensSummatory e‖ ^ 2 :=
            shifted_norm_sq_add_le_two _ _
          _ ≤ (C / 2) * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) +
                (C / 2) * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) :=
            add_le_add hendpointTarget hgapTarget
          _ = C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by ring

/-- The fixed endpoint amplification theorem therefore implies the repository's
standard complex Mertens energy criterion. -/
theorem mertensEnergyBounded_of_squareRootEndpointAmplification
    (hamp : SquareRootMertensEndpointAmplificationStatement) :
    RHLean.Analysis.MertensEnergyBoundedStatement := by
  intro ε hε
  rcases shiftedMertensEnergyBounded_of_squareRootEndpointAmplification
      hamp ε hε with ⟨C, hC, hshift⟩
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro x
  have hdecomp :
      RHLean.Analysis.mertensSummatory x =
        (RHLean.Analysis.mertensSummatory x - 1) + 1 := by ring
  have hsq := shifted_norm_sq_add_le_two
    (RHLean.Analysis.mertensSummatory x - 1) (1 : ℂ)
  rw [← hdecomp] at hsq
  have hbasePow :
      1 ≤ Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
    have hbase : (1 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
      have hone : (1 : ℕ) ≤ x + 1 := by omega
      exact_mod_cast hone
    have hexp : 0 ≤ 1 + ε := by linarith
    exact Real.one_le_rpow hbase hexp
  calc
    ‖RHLean.Analysis.mertensSummatory x‖ ^ 2 ≤
        2 * shiftedMertensEnergy x + 2 := by
      simpa [shiftedMertensEnergy] using hsq
    _ ≤ 2 * (C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)) + 2 := by
      linarith [hshift x]
    _ ≤ (2 * C + 2) * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
      have hexpand :
          (2 * C + 2) * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) =
            2 * (C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)) +
              2 * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by ring
      rw [hexpand]
      linarith

end RHLean.Proof
