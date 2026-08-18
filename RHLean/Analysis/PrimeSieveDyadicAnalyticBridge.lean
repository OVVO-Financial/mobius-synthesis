import Mathlib
import RHLean.Analysis.PrimeSieveDyadicCoherentAbel
import RHLean.Analysis.MobiusSynthesisBoundaryBridge
import RHLean.Proof.TerminalMertensForward

/-!
# Dyadic analytic package implies the canonical RH boundary

An earlier layer isolated the exact decomposition

`H = dyadicCoherentChannel - 2 * centeredDyadicWaveletError`

and the boundary-free block Abel formula for the wavelet channel.  It also named
sample-level energy and Mobius-dispersion targets suggested by finite diagnostics.

There is one centering issue to handle before those ideas can be used as a genuine
reduction: `primorialSquareZeroModeCenter` evaluates the wavelet not only at the
complete-square sample `X_n`, but also at the arithmetic block endpoints `L_k` and
`U_k`.  Those endpoints are not generally complete-square samples.  This module
therefore introduces the minimal block-uniform strengthening of the energy and
dispersion predicates, proves that it implies the original sample predicates, and
then closes the exact implication chain.

The proved route is

```text
block-uniform Abel-potential energy
  + block-uniform Mobius dispersion
      -> raw dyadic wavelet RH scale on every point of a primorial block
      -> centered dyadic wavelet RH scale on square samples

dyadic coherent-channel RH scale
  + centered dyadic wavelet RH scale
      -> NonzeroResponseRHScale
      -> projected-renewal quadratic bound
      -> Riemann Hypothesis.
```

No instance of the three analytic hypotheses is proved here.  The contribution of
this file is to certify that these hypotheses are sufficient and to identify the
endpoint-uniform form actually required by the square-wheel centering operator.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Block-uniform versions of the analytic targets -/

/-- Critical-scale `L2` energy bound for the boundary-free Abel coefficient field,
uniformly at every integer point of every synchronized primorial block.  The
predicate is the restriction of this statement to complete-square samples. -/
def DyadicAbelPotentialEnergyBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicAbelPotentialEnergy
            (primorialPNTPrimeSieveCutoff k) x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- Mobius dispersion against the boundary-free Abel coefficient field, uniformly
at every integer point of every synchronized primorial block. -/
def DyadicMobiusDispersionBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        ‖primeSieveDyadicWaveletPNTError
            (primorialPNTPrimeSieveCutoff k) x‖ ^ 2 ≤
          C * Real.rpow ((x : ℝ) + 1) ε *
            primeSieveDyadicAbelPotentialEnergy
              (primorialPNTPrimeSieveCutoff k) x

/-- The block-uniform energy statement specializes to the sample-level target. -/
theorem dyadicAbelPotentialEnergyBounded_of_blockBounded
    (hE : DyadicAbelPotentialEnergyBlockBoundedStatement) :
    DyadicAbelPotentialEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := hE ε hε
  refine ⟨C, hC, ?_⟩
  intro k n hk hlow hup
  have h := hCb k (squarePrefixEndpoint n) hk hlow.le hup
  have hcast : ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) =
      (squarePrefixEndpoint n : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast]
  exact h

/-- The block-uniform dispersion statement specializes to the sample-level target. -/
theorem dyadicMobiusDispersionBounded_of_blockBounded
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    DyadicMobiusDispersionBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := hD ε hε
  refine ⟨C, hC, ?_⟩
  intro k n hk hlow hup
  have h := hCb k (squarePrefixEndpoint n) hk hlow.le hup
  have hcast : ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) =
      (squarePrefixEndpoint n : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast]
  exact h

/-! ## Energy plus dispersion gives a raw wavelet power bound -/

/-- Uniform pointwise power bound for the uncentered dyadic wavelet prime error on
every point of every synchronized primorial block. -/
def DyadicWaveletBlockPowerBound (r : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (k x : ℕ),
      2 ≤ k →
      primorialBlockLower k ≤ x →
      x ≤ primorialBlockUpper k →
      ‖primeSieveDyadicWaveletPNTError
          (primorialPNTPrimeSieveCutoff k) x‖ ≤
        K * Real.rpow ((x : ℝ) + 1) r

/-- RH-scale version of the block-uniform raw wavelet bound. -/
def DyadicWaveletBlockRHScale : Prop :=
  ∀ ε : ℝ, 0 < ε →
    DyadicWaveletBlockPowerBound ((1 : ℝ) / 2 + ε)

/-- Critical `L2` Abel-potential energy together with epsilon-loss Mobius dispersion
implies the square-root-scale pointwise wavelet bound on the full primorial block. -/
theorem dyadicWaveletBlockRHScale_of_energy_dispersion
    (hE : DyadicAbelPotentialEnergyBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    DyadicWaveletBlockRHScale := by
  intro ε hε
  obtain ⟨CE, hCE, hEb⟩ := hE ε hε
  obtain ⟨CD, hCD, hDb⟩ := hD ε hε
  set Q := Real.sqrt (CD * CE) with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  refine ⟨Q, hQ0, ?_⟩
  intro k x hk hlow hup
  have henergy := hEb k x hk hlow hup
  have hdisp := hDb k x hk hlow hup
  have hbase : 0 < (x : ℝ) + 1 := by positivity
  have hfac0 : 0 ≤ CD * Real.rpow ((x : ℝ) + 1) ε :=
    mul_nonneg hCD (Real.rpow_nonneg (by positivity) _)
  have hsq :
      ‖primeSieveDyadicWaveletPNTError
          (primorialPNTPrimeSieveCutoff k) x‖ ^ 2 ≤
        (CD * CE) * Real.rpow ((x : ℝ) + 1) (1 + 2 * ε) := by
    calc
      ‖primeSieveDyadicWaveletPNTError
          (primorialPNTPrimeSieveCutoff k) x‖ ^ 2 ≤
          CD * Real.rpow ((x : ℝ) + 1) ε *
            primeSieveDyadicAbelPotentialEnergy
              (primorialPNTPrimeSieveCutoff k) x := hdisp
      _ ≤ (CD * Real.rpow ((x : ℝ) + 1) ε) *
            (CE * Real.rpow ((x : ℝ) + 1) (1 + ε)) :=
        mul_le_mul_of_nonneg_left henergy hfac0
      _ = (CD * CE) *
            (Real.rpow ((x : ℝ) + 1) ε *
              Real.rpow ((x : ℝ) + 1) (1 + ε)) := by ring
      _ = (CD * CE) *
            Real.rpow ((x : ℝ) + 1) (ε + (1 + ε)) := by
        exact congrArg (fun z : ℝ => (CD * CE) * z)
          (Real.rpow_add hbase ε (1 + ε)).symm
      _ = (CD * CE) * Real.rpow ((x : ℝ) + 1) (1 + 2 * ε) := by
        have hexp : ε + (1 + ε) = 1 + 2 * ε := by ring
        rw [hexp]
  have hQ2 : Q * Q = CD * CE := by
    rw [hQdef]
    exact Real.mul_self_sqrt (mul_nonneg hCD hCE)
  have hrpow :
      Real.rpow ((x : ℝ) + 1) (1 + 2 * ε) =
        Real.rpow ((x : ℝ) + 1) ((1 : ℝ) / 2 + ε) *
          Real.rpow ((x : ℝ) + 1) ((1 : ℝ) / 2 + ε) := by
    calc
      Real.rpow ((x : ℝ) + 1) (1 + 2 * ε) =
          Real.rpow ((x : ℝ) + 1)
            (((1 : ℝ) / 2 + ε) + ((1 : ℝ) / 2 + ε)) := by
        have hexp : 1 + 2 * ε =
            ((1 : ℝ) / 2 + ε) + ((1 : ℝ) / 2 + ε) := by ring
        rw [hexp]
      _ = Real.rpow ((x : ℝ) + 1) ((1 : ℝ) / 2 + ε) *
          Real.rpow ((x : ℝ) + 1) ((1 : ℝ) / 2 + ε) :=
        Real.rpow_add hbase ((1 : ℝ) / 2 + ε) ((1 : ℝ) / 2 + ε)
  have hsq' :
      ‖primeSieveDyadicWaveletPNTError
          (primorialPNTPrimeSieveCutoff k) x‖ ^ 2 ≤
        (Q * Real.rpow ((x : ℝ) + 1) ((1 : ℝ) / 2 + ε)) ^ 2 := by
    calc
      ‖primeSieveDyadicWaveletPNTError
          (primorialPNTPrimeSieveCutoff k) x‖ ^ 2 ≤
          (CD * CE) * Real.rpow ((x : ℝ) + 1) (1 + 2 * ε) := hsq
      _ = (Q * Real.rpow ((x : ℝ) + 1) ((1 : ℝ) / 2 + ε)) ^ 2 := by
        rw [← hQ2, hrpow]
        ring
  exact
    (sq_le_sq₀
      (norm_nonneg _)
      (mul_nonneg hQ0 (Real.rpow_nonneg (by positivity) _))).1 hsq'

/-! ## Center the wavelet without losing square-root scale -/

/-- Uniform power bound for the dyadic wavelet after the actual square-wheel
zero-mode centering. -/
def DyadicWaveletCenteredPowerBound (r : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (k n : ℕ),
      2 ≤ k →
      primorialBlockLower k < squarePrefixEndpoint n →
      squarePrefixEndpoint n ≤ primorialBlockUpper k →
      ‖primorialDyadicWaveletPNTErrorCenteredResponse k n‖ ≤
        K * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r

/-- RH-scale centered-wavelet target. -/
def DyadicWaveletCenteredRHScale : Prop :=
  ∀ ε : ℝ, 0 < ε →
    DyadicWaveletCenteredPowerBound ((1 : ℝ) / 2 + ε)

/-- `Real.rpow` and real power notation agree definitionally. -/
private theorem dyadic_rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-- `rpow` is antitone in the base for a nonpositive exponent. -/
private theorem dyadic_rpow_anti_base {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : c ≤ 0) :
    Real.rpow b c ≤ Real.rpow a c := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : a ^ (-c) ≤ b ^ (-c) :=
    Real.rpow_le_rpow ha.le hab (by linarith)
  have ha' : (0 : ℝ) < a ^ (-c) := Real.rpow_pos_of_pos ha _
  simp only [dyadic_rpow_eq]
  rw [show c = -(-c) by ring, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have h := one_div_le_one_div_of_le ha' h1
  simpa [one_div] using h

/-- Absorb one factor of the positive base into a real exponent. -/
private theorem dyadic_base_mul_rpow_sub_one {a σ : ℝ} (ha : 0 < a) :
    a * Real.rpow a (σ - 1) = Real.rpow a σ := by
  simp only [dyadic_rpow_eq]
  rw [Real.rpow_sub ha σ 1, Real.rpow_one]
  field_simp

/-- Norm of the square-wheel zero-mode coupling coefficient. -/
private theorem dyadic_norm_sampleRatio_eq (k n : ℕ) :
    ‖squareWheelSampleRatio (primorialMinimalWheelSystem k) n‖ =
      (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) /
        ((primorialMinimalWheelSystem k).modulus : ℝ) := by
  unfold squareWheelSampleRatio
  rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast,
    div_eq_inv_mul]

/-- Fine coupling bound used to transport a block-uniform power estimate through
the actual square-wheel centering coefficient. -/
private theorem dyadic_norm_sampleRatio_le_fine {k n : ℕ} (hk : 2 ≤ k) :
    ‖squareWheelSampleRatio (primorialMinimalWheelSystem k) n‖ ≤
      ((squarePrefixEndpoint n : ℝ) + 1) /
        (3 * ((primorialBlockUpper k : ℝ) + 1)) := by
  rw [dyadic_norm_sampleRatio_eq]
  have hlenNat :
      squareWheelSampleLength (primorialMinimalWheelSystem k) n ≤
        squarePrefixEndpoint n := Nat.sub_le _ _
  have hlen :
      (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) ≤
        (squarePrefixEndpoint n : ℝ) + 1 := by
    have : (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) ≤
        (squarePrefixEndpoint n : ℝ) := by
      exact_mod_cast hlenNat
    linarith
  have h6 : 6 * primorialBlockUpper k < primorialMinimalTorusModulus k :=
    six_mul_primorialBlockUpper_lt_minimalTorusModulus hk
  have hU : 30 ≤ primorialBlockUpper k := thirty_le_primorialBlockUpper hk
  have hmodNat : 3 * (primorialBlockUpper k + 1) ≤ primorialMinimalTorusModulus k := by
    omega
  have hmod :
      3 * ((primorialBlockUpper k : ℝ) + 1) ≤
        ((primorialMinimalWheelSystem k).modulus : ℝ) := by
    have : ((3 * (primorialBlockUpper k + 1) : ℕ) : ℝ) ≤
        ((primorialMinimalTorusModulus k : ℕ) : ℝ) := by
      exact_mod_cast hmodNat
    push_cast at this
    calc
      3 * ((primorialBlockUpper k : ℝ) + 1) =
          3 * (primorialBlockUpper k : ℝ) + 3 := by ring
      _ ≤ (primorialMinimalTorusModulus k : ℝ) := by linarith
  have hden : (0 : ℝ) < 3 * ((primorialBlockUpper k : ℝ) + 1) := by positivity
  have h1b :
      1 / ((primorialMinimalWheelSystem k).modulus : ℝ) ≤
        1 / (3 * ((primorialBlockUpper k : ℝ) + 1)) :=
    one_div_le_one_div_of_le hden hmod
  have h1bnn : (0 : ℝ) ≤ 1 / ((primorialMinimalWheelSystem k).modulus : ℝ) := by
    positivity
  calc
    (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) /
        ((primorialMinimalWheelSystem k).modulus : ℝ) =
        (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) *
          (1 / ((primorialMinimalWheelSystem k).modulus : ℝ)) := by ring
    _ ≤ ((squarePrefixEndpoint n : ℝ) + 1) *
          (1 / (3 * ((primorialBlockUpper k : ℝ) + 1))) :=
      mul_le_mul hlen h1b h1bnn (by positivity)
    _ = ((squarePrefixEndpoint n : ℝ) + 1) /
          (3 * ((primorialBlockUpper k : ℝ) + 1)) := by ring

/-- A block-uniform wavelet RH-scale bound survives the repository's actual
three-point square-wheel zero-mode centering.  The fine coupling coefficient
absorbs the possible size of the upper-endpoint value. -/
theorem dyadicWaveletCenteredRHScale_of_blockRHScale
    (hW : DyadicWaveletBlockRHScale) :
    DyadicWaveletCenteredRHScale := by
  intro ε hε
  set εs := min ε (1 / 2 : ℝ) with hεsdef
  have hεs0 : 0 < εs := by
    rw [hεsdef]
    exact lt_min hε (by norm_num)
  obtain ⟨Q, hQ0, hQb⟩ := hW εs hεs0
  set σ := 1 / 2 + εs with hσdef
  have hσ0 : 0 ≤ σ := by
    rw [hσdef]
    linarith
  have hσu : σ ≤ 1 := by
    have hmin : εs ≤ 1 / 2 := by
      rw [hεsdef]
      exact min_le_right _ _
    rw [hσdef]
    linarith
  refine ⟨3 * Q, by positivity, ?_⟩
  intro k n hk hlow hup
  have hblock : primorialBlockLower k ≤ primorialBlockUpper k :=
    hlow.le.trans hup
  set ρ := squareWheelSampleRatio (primorialMinimalWheelSystem k) n
  set WX := primeSieveDyadicWaveletPNTError
    (primorialPNTPrimeSieveCutoff k) (squarePrefixEndpoint n)
  set WL := primeSieveDyadicWaveletPNTError
    (primorialPNTPrimeSieveCutoff k) (primorialBlockLower k)
  set WU := primeSieveDyadicWaveletPNTError
    (primorialPNTPrimeSieveCutoff k) (primorialBlockUpper k)
  have hX0 := hQb k (squarePrefixEndpoint n) hk hlow.le hup
  have hL0 := hQb k (primorialBlockLower k) hk le_rfl hblock
  have hU0 := hQb k (primorialBlockUpper k) hk hblock le_rfl
  have hX : ‖WX‖ ≤
      Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    simpa [WX, hσdef] using hX0
  have hL : ‖WL‖ ≤
      Q * Real.rpow ((primorialBlockLower k : ℝ) + 1) σ := by
    simpa [WL, hσdef] using hL0
  have hU : ‖WU‖ ≤
      Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by
    simpa [WU, hσdef] using hU0
  have hLX : (primorialBlockLower k : ℝ) + 1 ≤
      (squarePrefixEndpoint n : ℝ) + 1 := by
    have : (primorialBlockLower k : ℝ) ≤ (squarePrefixEndpoint n : ℝ) := by
      exact_mod_cast hlow.le
    linarith
  have hXU : (squarePrefixEndpoint n : ℝ) + 1 ≤
      (primorialBlockUpper k : ℝ) + 1 := by
    have : (squarePrefixEndpoint n : ℝ) ≤ (primorialBlockUpper k : ℝ) := by
      exact_mod_cast hup
    linarith
  have hLmono :
      Real.rpow ((primorialBlockLower k : ℝ) + 1) σ ≤
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
    Real.rpow_le_rpow (by positivity) hLX hσ0
  have hLmonoU :
      Real.rpow ((primorialBlockLower k : ℝ) + 1) σ ≤
        Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
    Real.rpow_le_rpow (by positivity) (hLX.trans hXU) hσ0
  have hfirst : ‖WX - WL‖ ≤
      2 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    have hL2 : ‖WL‖ ≤ Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
      hL.trans (mul_le_mul_of_nonneg_left hLmono hQ0)
    calc
      ‖WX - WL‖ ≤ ‖WX‖ + ‖WL‖ := norm_sub_le _ _
      _ ≤ Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ +
            Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
        add_le_add hX hL2
      _ = 2 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by ring
  have hsecondRaw : ‖WU - WL‖ ≤
      2 * Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by
    have hL2 : ‖WL‖ ≤ Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
      hL.trans (mul_le_mul_of_nonneg_left hLmonoU hQ0)
    calc
      ‖WU - WL‖ ≤ ‖WU‖ + ‖WL‖ := norm_sub_le _ _
      _ ≤ Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ +
            Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
        add_le_add hU hL2
      _ = 2 * Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by ring
  have hρfine := dyadic_norm_sampleRatio_le_fine (n := n) hk
  have hρR : ‖ρ‖ * ‖WU - WL‖ ≤
      (((squarePrefixEndpoint n : ℝ) + 1) /
          (3 * ((primorialBlockUpper k : ℝ) + 1))) *
        (2 * Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ) := by
    simpa [ρ] using
      (mul_le_mul hρfine hsecondRaw (norm_nonneg _) (by positivity))
  have hUpos : (0 : ℝ) < (primorialBlockUpper k : ℝ) + 1 := by positivity
  have hXpos : (0 : ℝ) < (squarePrefixEndpoint n : ℝ) + 1 := by positivity
  have hAB :
      (((squarePrefixEndpoint n : ℝ) + 1) /
          (3 * ((primorialBlockUpper k : ℝ) + 1))) *
        (2 * Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ) =
      (2 / 3 * Q) *
        (((squarePrefixEndpoint n : ℝ) + 1) *
          Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1)) := by
    simp only [dyadic_rpow_eq]
    rw [Real.rpow_sub hUpos σ 1, Real.rpow_one]
    field_simp
  have hanti :
      Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1) ≤
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) (σ - 1) :=
    dyadic_rpow_anti_base hXpos hXU (by linarith)
  have hfin :
      ((squarePrefixEndpoint n : ℝ) + 1) *
          Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1) ≤
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    calc
      ((squarePrefixEndpoint n : ℝ) + 1) *
          Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1) ≤
          ((squarePrefixEndpoint n : ℝ) + 1) *
            Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) (σ - 1) :=
        mul_le_mul_of_nonneg_left hanti (by positivity)
      _ = Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
        dyadic_base_mul_rpow_sub_one hXpos
  have hsecond : ‖ρ‖ * ‖WU - WL‖ ≤
      (2 / 3 * Q) * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    calc
      ‖ρ‖ * ‖WU - WL‖ ≤
          (2 / 3 * Q) *
            (((squarePrefixEndpoint n : ℝ) + 1) *
              Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1)) := by
        rw [← hAB]
        exact hρR
      _ ≤ (2 / 3 * Q) *
            Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
  have htri :
      ‖primorialDyadicWaveletPNTErrorCenteredResponse k n‖ ≤
        ‖WX - WL‖ + ‖ρ‖ * ‖WU - WL‖ := by
    unfold primorialDyadicWaveletPNTErrorCenteredResponse
      primorialSquareZeroModeCenter
    change ‖(WX - WL) - ρ * (WU - WL)‖ ≤
      ‖WX - WL‖ + ‖ρ‖ * ‖WU - WL‖
    calc
      ‖(WX - WL) - ρ * (WU - WL)‖ ≤
          ‖WX - WL‖ + ‖ρ * (WU - WL)‖ := norm_sub_le _ _
      _ = ‖WX - WL‖ + ‖ρ‖ * ‖WU - WL‖ := by rw [norm_mul]
  have htotal :
      ‖primorialDyadicWaveletPNTErrorCenteredResponse k n‖ ≤
        3 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    calc
      ‖primorialDyadicWaveletPNTErrorCenteredResponse k n‖ ≤
          ‖WX - WL‖ + ‖ρ‖ * ‖WU - WL‖ := htri
      _ ≤ 2 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ +
            (2 / 3 * Q) * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
        add_le_add hfirst hsecond
      _ ≤ 3 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
        have hr0 : 0 ≤ Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
          Real.rpow_nonneg (by positivity) _
        nlinarith
  have hbase1 : (1 : ℝ) ≤ (squarePrefixEndpoint n : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (squarePrefixEndpoint n : ℝ) := Nat.cast_nonneg _
    linarith
  have hraise :
      Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ ≤
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) ((1 : ℝ) / 2 + ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hbase1
    have hmin : εs ≤ ε := by
      rw [hεsdef]
      exact min_le_left _ _
    rw [hσdef]
    linarith
  have hcast : ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) =
      (squarePrefixEndpoint n : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast]
  exact htotal.trans (mul_le_mul_of_nonneg_left hraise (by positivity))

/-- The block-uniform energy and dispersion hypotheses therefore imply the centered
wavelet RH-scale target consumed by the canonical decomposition. -/
theorem dyadicWaveletCenteredRHScale_of_energy_dispersion
    (hE : DyadicAbelPotentialEnergyBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    DyadicWaveletCenteredRHScale :=
  dyadicWaveletCenteredRHScale_of_blockRHScale
    (dyadicWaveletBlockRHScale_of_energy_dispersion hE hD)

/-! ## Close the canonical synthesis frontier -/

/-- The three analytic hypotheses isolated by the dyadic decomposition imply the
repository's canonical `NonzeroResponseRHScale` frontier. -/
theorem nonzeroResponseRHScale_of_dyadicAnalyticPackage
    (hC : DyadicCoherentChannelRHScale)
    (hE : DyadicAbelPotentialEnergyBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    MobiusSynthesisBoundary.NonzeroResponseRHScale := by
  have hW : DyadicWaveletCenteredRHScale :=
    dyadicWaveletCenteredRHScale_of_energy_dispersion hE hD
  intro ε hε
  obtain ⟨KC, hKC, hCb⟩ := hC ε hε
  obtain ⟨KW, hKW, hWb⟩ := hW ε hε
  refine ⟨KC + 2 * KW, by positivity, ?_⟩
  intro k n hk hlow hup
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_dyadicCoherent_sub_two_wavelet
    k n hlow hup]
  have htwo :
      ‖(2 : ℂ) * primorialDyadicWaveletPNTErrorCenteredResponse k n‖ =
        2 * ‖primorialDyadicWaveletPNTErrorCenteredResponse k n‖ := by
    rw [norm_mul]
    norm_num
  calc
    ‖primorialDyadicCoherentChannel k n -
        2 * primorialDyadicWaveletPNTErrorCenteredResponse k n‖ ≤
      ‖primorialDyadicCoherentChannel k n‖ +
        ‖(2 : ℂ) * primorialDyadicWaveletPNTErrorCenteredResponse k n‖ :=
      norm_sub_le _ _
    _ = ‖primorialDyadicCoherentChannel k n‖ +
        2 * ‖primorialDyadicWaveletPNTErrorCenteredResponse k n‖ := by
      rw [htwo]
    _ ≤ KC * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ)
            ((1 : ℝ) / 2 + ε) +
        2 * (KW * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ)
            ((1 : ℝ) / 2 + ε)) := by
      exact add_le_add (hCb k n hk hlow hup)
        (mul_le_mul_of_nonneg_left (hWb k n hk hlow hup) (by norm_num))
    _ = (KC + 2 * KW) *
        Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ)
          ((1 : ℝ) / 2 + ε) := by ring

/-- The same dyadic analytic package implies the projected-renewal quadratic bound
at every nonnegative cutoff. -/
theorem projectedRenewalQuadraticBounded_of_dyadicAnalyticPackage
    (hC : DyadicCoherentChannelRHScale)
    (hE : DyadicAbelPotentialEnergyBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    ∀ Λ : ℝ, 0 ≤ Λ →
      RHLean.Proof.CanonicalGapAncestryQuadraticClosure.ProjectedRenewalQuadraticBoundedStatement
        Λ :=
  MobiusSynthesisBoundaryBridge.projectedRenewalQuadraticBounded_of_nonzeroResponseRHScale
    (nonzeroResponseRHScale_of_dyadicAnalyticPackage hC hE hD)

/-- **Terminal bridge.**  Proving the coherent-channel RH-scale estimate and
the block-uniform boundary-free energy plus Mobius-dispersion estimates is sufficient
to prove Mathlib's Riemann Hypothesis through the repository's existing unconditional
terminal chain. -/
theorem riemannHypothesis_of_dyadicAnalyticPackage
    (hC : DyadicCoherentChannelRHScale)
    (hE : DyadicAbelPotentialEnergyBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  have hscale : MobiusSynthesisBoundary.NonzeroResponseRHScale :=
    nonzeroResponseRHScale_of_dyadicAnalyticPackage hC hE hD
  have hquad :
      RHLean.Proof.CanonicalGapAncestryQuadraticClosure.ProjectedRenewalQuadraticBoundedStatement
        0 :=
    MobiusSynthesisBoundaryBridge.projectedRenewalQuadraticBounded_of_nonzeroResponseRHScale
      hscale 0 (le_refl (0 : ℝ))
  exact
    RHLean.Proof.TerminalMertensForward.projectedRenewalQuadraticBounded_imp_riemannHypothesis_unconditional
      (le_refl (0 : ℝ)) hquad

end RHLean.Analysis
