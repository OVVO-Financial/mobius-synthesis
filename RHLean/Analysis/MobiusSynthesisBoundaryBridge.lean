import Mathlib
import RHLean.Analysis.MobiusSynthesisBoundary
import RHLean.Analysis.PrimeSievePNTCentering
import RHLean.Analysis.PrimorialWheelMertensTransfer
import RHLean.Proof.CanonicalGapAncestryQuadraticClosure

/-!
# Bridge: synthesis boundary target ↔ projected renewal quadratic bound

This module proves the missing connecting theorem between the two frozen
research targets of the repository:

* `RHLean.Analysis.MobiusSynthesisBoundary.NonzeroResponseRHScale`, the
  pointwise RH-scale power bound for the canonical nonzero square-wheel
  response `H_{k,n}` on synchronized primorial blocks; and

* `RHLean.Proof.CanonicalGapAncestryQuadraticClosure.ProjectedRenewalQuadraticBoundedStatement`,
  the translated-window bound for the complete signed projected-renewal Gram
  value consumed by the premise-free RH bridge.

The route is exact and uses only machinery already in the repository:

1. The zero-mode centering identity
   `H_{k,n} = (M(X_n) - M(L_k)) - ρ_{k,n} (M(U_k) - M(L_k))`
   (`primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter`), together
   with the uniform coupling bound `ρ_{k,n} < 1/6` and the fine coupling bound
   `ρ_{k,n} ≤ (X_n+1)/(3(U_k+1))`, converts the pointwise response bound into
   a bound for every pinned primorial residual `M(x) - M(L_k)`
   (`PrimeWheelResidualBoundedStatement primorialWheelFamily`).  Interpolation
   between consecutive complete squares costs one square gap, which is
   square-root scale.

2. The already-proved contracting block recursion
   `primorialWheel_residualBounded_iff_mertensEnergy` turns the residual bound
   into the global Mertens energy criterion, hence into
   `SquarePrefixUniformLocalBoundedStatement`, the canonical high-sector
   statement `(HS)`, and finally the projected-renewal quadratic bound via
   `projectedRenewalQuadraticBounded_iff_canonicalHigh`.

Both directions are proved; the two predicates are equivalent (the reverse
direction uses the same centering identity to bound `H_{k,n}` from the global
Mertens energy bound).  No axioms, `sorry`s, or new analytic assumptions are
introduced.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

namespace MobiusSynthesisBoundaryBridge

open RHLean.Arithmetic

/-! ## Small concrete primorial numerics -/

private theorem count_prime_two : Nat.count Nat.Prime 2 = 0 := by
  simp [Nat.count_succ, Nat.count_zero, Nat.not_prime_zero, Nat.not_prime_one]

private theorem count_prime_three : Nat.count Nat.Prime 3 = 1 := by
  simp [Nat.count_succ, Nat.count_zero, Nat.not_prime_zero, Nat.not_prime_one,
    Nat.prime_two]

private theorem wheelPrime_zero_eq : wheelPrime 0 = 2 := by
  unfold wheelPrime
  have h := Nat.nth_count (p := Nat.Prime) Nat.prime_two
  rwa [count_prime_two] at h

private theorem wheelPrime_one_eq : wheelPrime 1 = 3 := by
  unfold wheelPrime
  have h := Nat.nth_count (p := Nat.Prime) Nat.prime_three
  rwa [count_prime_three] at h

private theorem primorialEndpoint_one_eq : primorialEndpoint 1 = 2 := by
  have h := primorialEndpoint_succ 0
  rw [primorialEndpoint_zero, wheelPrime_zero_eq] at h
  simpa using h

private theorem primorialEndpoint_two_eq : primorialEndpoint 2 = 6 := by
  have h := primorialEndpoint_succ 1
  rw [primorialEndpoint_one_eq, wheelPrime_one_eq] at h
  simpa using h

private theorem six_le_primorialBlockLower {k : ℕ} (hk : 2 ≤ k) :
    6 ≤ primorialBlockLower k := by
  have h := primorialEndpoint_strictMono.monotone hk
  rw [primorialEndpoint_two_eq] at h
  exact h

/-- `Real.rpow` and the real power notation agree definitionally; this equation
lets `rw`-based lemmas from mathlib apply to `Real.rpow`-spelled goals. -/
private theorem rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-! ## Square-sample selection by natural square root -/

/-- Every point is bracketed by two consecutive complete-square endpoints. -/
private theorem sqrt_sample_bracket (x : ℕ) :
    ∃ n : ℕ, squarePrefixEndpoint n ≤ x ∧ x < squarePrefixEndpoint (n + 1) := by
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

/-- The distance from a bracketed point to its preceding complete-square
endpoint is at most `3 (x+1)^{1/2}`. -/
private theorem sub_le_gap_of_bracket {n x : ℕ}
    (hleft : squarePrefixEndpoint n ≤ x)
    (hright : x < squarePrefixEndpoint (n + 1)) :
    ((x - squarePrefixEndpoint n : ℕ) : ℝ) ≤
      3 * Real.rpow ((x : ℝ) + 1) (1 / 2 : ℝ) := by
  have hgapNat := sub_squarePrefixEndpoint_lt_gap n x hleft hright
  have hsqNat := squareGap_sq_le_nine_mul_succ n x hleft
  have hp0 : 0 ≤ Real.rpow ((x : ℝ) + 1) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hpsq :
      Real.rpow ((x : ℝ) + 1) (1 / 2 : ℝ) *
        Real.rpow ((x : ℝ) + 1) (1 / 2 : ℝ) = (x : ℝ) + 1 := by
    simp only [rpow_eq]
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < (x : ℝ) + 1)]
    norm_num
  have hcast1 : ((x - squarePrefixEndpoint n : ℕ) : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) := by
    exact_mod_cast hgapNat.le
  have hcast2 : ((2 * n + 3 : ℕ) : ℝ) ^ 2 ≤ 9 * ((x : ℝ) + 1) := by
    have : (((2 * n + 3) ^ 2 : ℕ) : ℝ) ≤ ((9 * (x + 1) : ℕ) : ℝ) := by
      exact_mod_cast hsqNat
    push_cast at this
    push_cast
    linarith
  have hg0 : (0 : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) := by positivity
  have h3p : ((2 * n + 3 : ℕ) : ℝ) ≤ 3 * Real.rpow ((x : ℝ) + 1) (1 / 2 : ℝ) := by
    nlinarith [hp0, hpsq, hcast2, hg0]
  exact hcast1.trans h3p

/-! ## rpow helpers -/

/-- rpow is antitone in the base for nonpositive exponents. -/
private theorem rpow_anti_base {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : c ≤ 0) : Real.rpow b c ≤ Real.rpow a c := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : a ^ (-c) ≤ b ^ (-c) :=
    Real.rpow_le_rpow ha.le hab (by linarith)
  have ha' : (0 : ℝ) < a ^ (-c) := Real.rpow_pos_of_pos ha _
  simp only [rpow_eq]
  rw [show c = -(-c) by ring, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have h := one_div_le_one_div_of_le ha' h1
  simpa [one_div] using h

/-- Absorb one factor of the base into the exponent. -/
private theorem base_mul_rpow_sub_one {a σ : ℝ} (ha : 0 < a) :
    a * Real.rpow a (σ - 1) = Real.rpow a σ := by
  simp only [rpow_eq]
  rw [Real.rpow_sub ha σ 1, Real.rpow_one]
  field_simp

/-! ## Sample-ratio facts -/

private theorem norm_sampleRatio_eq (k n : ℕ) :
    ‖squareWheelSampleRatio (primorialMinimalWheelSystem k) n‖ =
      (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) /
        ((primorialMinimalWheelSystem k).modulus : ℝ) := by
  unfold squareWheelSampleRatio
  rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast,
    div_eq_inv_mul]

/-- The coupling ratio never reaches `1/6` on admissible samples from block
two onward. -/
private theorem norm_sampleRatio_lt_one_sixth {k n : ℕ} (hk : 2 ≤ k)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    ‖squareWheelSampleRatio (primorialMinimalWheelSystem k) n‖ < 1 / 6 := by
  rw [norm_sampleRatio_eq]
  exact primorialMinimalSquareSampleRatio_lt_one_sixth hk hupper

/-- Fine coupling bound: the ratio is at most `(X_n+1)/(3(U_k+1))`. -/
private theorem norm_sampleRatio_le_fine {k n : ℕ} (hk : 2 ≤ k) :
    ‖squareWheelSampleRatio (primorialMinimalWheelSystem k) n‖ ≤
      ((squarePrefixEndpoint n : ℝ) + 1) /
        (3 * ((primorialBlockUpper k : ℝ) + 1)) := by
  rw [norm_sampleRatio_eq]
  have hlenNat :
      squareWheelSampleLength (primorialMinimalWheelSystem k) n ≤
        squarePrefixEndpoint n := Nat.sub_le _ _
  have hlen :
      (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) ≤
        (squarePrefixEndpoint n : ℝ) + 1 := by
    have : (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) ≤
        (squarePrefixEndpoint n : ℝ) := by exact_mod_cast hlenNat
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

/-! ## Core estimates for a fixed block `k ≥ 2`

Throughout, `hH` is the pointwise power bound for `H_{k,n}` at exponent `σ`
restricted to the block `k`, with base written as `(X_n : ℝ) + 1`. -/

section FixedBlock

variable {k : ℕ} {K σ : ℝ}

/-- The pointwise response bound controls the full block increment
`M(U_k) - M(L_k)`. -/
private theorem norm_endpoint_block_residual_le
    (hk : 2 ≤ k) (hK : 0 ≤ K) (hσl : (1 : ℝ) / 2 ≤ σ)
    (hH : ∀ n : ℕ,
      primorialBlockLower k < squarePrefixEndpoint n →
      squarePrefixEndpoint n ≤ primorialBlockUpper k →
      ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
        K * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ) :
    ‖mertensSummatory (primorialBlockUpper k) -
        mertensSummatory (primorialBlockLower k)‖ ≤
      (6 / 5 * (K + 3)) *
        Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by
  obtain ⟨m, hmle, hmgt⟩ := sqrt_sample_bracket (primorialBlockUpper k)
  have hLlow : 6 ≤ primorialBlockLower k := six_le_primorialBlockLower hk
  have hdouble : 2 * primorialBlockLower k ≤ primorialBlockUpper k :=
    two_mul_primorialEndpoint_le_succ k
  -- the selected sample lies strictly inside the block
  have hLX : primorialBlockLower k < squarePrefixEndpoint m := by
    by_contra hcon
    push_neg at hcon
    have h1 := squarePrefixEndpoint_add_one m
    have h2 := squarePrefixEndpoint_add_one (m + 1)
    have hexp : (m + 1 + 1) ^ 2 = (m + 1) ^ 2 + (2 * m + 3) := by ring
    have hL2m : primorialBlockLower k ≤ 2 * m + 2 := by omega
    have hm2 : 2 ≤ m := by omega
    have hA1 : 2 * m + 4 ≤ (m + 1) ^ 2 := by nlinarith
    omega
  have hXU : squarePrefixEndpoint m ≤ primorialBlockUpper k := hmle
  -- centering identity at the selected sample
  have hcenter :=
    primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter k m hLX hXU
  rw [primorialSquareZeroModeCenter] at hcenter
  set ρ := squareWheelSampleRatio (primorialMinimalWheelSystem k) m with hρdef
  set MU := mertensSummatory (primorialBlockUpper k)
  set ML := mertensSummatory (primorialBlockLower k)
  set MX := mertensSummatory (squarePrefixEndpoint m)
  set Hm := squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) m
  -- (1 - ρ) (MU - ML) = (MU - MX) + H
  have halg : (1 - ρ) * (MU - ML) = (MU - MX) + Hm := by
    linear_combination -hcenter
  -- lower bound the coefficient
  have hρnorm : ‖ρ‖ < 1 / 6 := norm_sampleRatio_lt_one_sixth hk hXU
  have hcoeff : (5 / 6 : ℝ) ≤ ‖(1 : ℂ) - ρ‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ρ
    rw [norm_one] at h
    linarith
  -- bound the right-hand side
  have hMUX : ‖MU - MX‖ ≤
      ((primorialBlockUpper k - squarePrefixEndpoint m : ℕ) : ℝ) :=
    norm_mertensSummatory_sub_le (squarePrefixEndpoint m)
      (primorialBlockUpper k) hXU
  have hgap := sub_le_gap_of_bracket hmle hmgt
  have hbase1 : (1 : ℝ) ≤ (primorialBlockUpper k : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (primorialBlockUpper k : ℝ) := Nat.cast_nonneg _
    linarith
  have hhalf :
      Real.rpow ((primorialBlockUpper k : ℝ) + 1) (1 / 2 : ℝ) ≤
        Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
    Real.rpow_le_rpow_of_exponent_le hbase1 hσl
  have hHb := hH m hLX hXU
  have hXcast :
      ((squarePrefixEndpoint m : ℝ) + 1) ≤ ((primorialBlockUpper k : ℝ) + 1) := by
    have : (squarePrefixEndpoint m : ℝ) ≤ (primorialBlockUpper k : ℝ) := by
      exact_mod_cast hXU
    linarith
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hHmono :
      Real.rpow ((squarePrefixEndpoint m : ℝ) + 1) σ ≤
        Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
    Real.rpow_le_rpow (by positivity) hXcast hσ0
  have hHU : ‖Hm‖ ≤ K * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
    hHb.trans (mul_le_mul_of_nonneg_left hHmono hK)
  -- combine
  have hprod : ‖(1 : ℂ) - ρ‖ * ‖MU - ML‖ ≤
      (K + 3) * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by
    calc
      ‖(1 : ℂ) - ρ‖ * ‖MU - ML‖ = ‖(1 - ρ) * (MU - ML)‖ := (norm_mul _ _).symm
      _ = ‖(MU - MX) + Hm‖ := by rw [halg]
      _ ≤ ‖MU - MX‖ + ‖Hm‖ := norm_add_le _ _
      _ ≤ 3 * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ +
            K * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by
        have h1 : ‖MU - MX‖ ≤
            3 * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
          hMUX.trans (hgap.trans (by linarith))
        linarith
      _ = (K + 3) * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by ring
  have hRnn : (0 : ℝ) ≤ ‖MU - ML‖ := norm_nonneg _
  nlinarith [hprod, hcoeff, hRnn,
    mul_le_mul_of_nonneg_right hcoeff hRnn]

/-- The pointwise response bound controls the pinned residual at every complete
square sample strictly inside the block. -/
private theorem norm_square_sample_residual_le
    (hk : 2 ≤ k) (hK : 0 ≤ K) (hσl : (1 : ℝ) / 2 ≤ σ) (hσu : σ ≤ 1)
    (hH : ∀ n : ℕ,
      primorialBlockLower k < squarePrefixEndpoint n →
      squarePrefixEndpoint n ≤ primorialBlockUpper k →
      ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
        K * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ)
    {n : ℕ}
    (hLX : primorialBlockLower k < squarePrefixEndpoint n)
    (hXU : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    ‖mertensSummatory (squarePrefixEndpoint n) -
        mertensSummatory (primorialBlockLower k)‖ ≤
      (K + 2 / 5 * (K + 3)) *
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
  have hcenter :=
    primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter k n hLX hXU
  rw [primorialSquareZeroModeCenter] at hcenter
  set ρ := squareWheelSampleRatio (primorialMinimalWheelSystem k) n with hρdef
  set MU := mertensSummatory (primorialBlockUpper k)
  set ML := mertensSummatory (primorialBlockLower k)
  set MX := mertensSummatory (squarePrefixEndpoint n)
  set Hn := squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n
  have hid : MX - ML = Hn + ρ * (MU - ML) := by
    linear_combination -hcenter
  have htri : ‖MX - ML‖ ≤ ‖Hn‖ + ‖ρ‖ * ‖MU - ML‖ := by
    rw [hid]
    calc
      ‖Hn + ρ * (MU - ML)‖ ≤ ‖Hn‖ + ‖ρ * (MU - ML)‖ := norm_add_le _ _
      _ = ‖Hn‖ + ‖ρ‖ * ‖MU - ML‖ := by rw [norm_mul]
  have hHb := hH n hLX hXU
  have hR := norm_endpoint_block_residual_le hk hK hσl hH
  have hρfine := norm_sampleRatio_le_fine (n := n) hk
  -- multiply the two bounds
  have hρR : ‖ρ‖ * ‖MU - ML‖ ≤
      (((squarePrefixEndpoint n : ℝ) + 1) /
          (3 * ((primorialBlockUpper k : ℝ) + 1))) *
        ((6 / 5 * (K + 3)) *
          Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ) :=
    mul_le_mul hρfine hR (norm_nonneg _) (by positivity)
  -- rewrite the product bound as a fine power of X_n + 1
  have hUpos : (0 : ℝ) < (primorialBlockUpper k : ℝ) + 1 := by positivity
  have hXpos : (0 : ℝ) < (squarePrefixEndpoint n : ℝ) + 1 := by positivity
  have hAB :
      (((squarePrefixEndpoint n : ℝ) + 1) /
          (3 * ((primorialBlockUpper k : ℝ) + 1))) *
        ((6 / 5 * (K + 3)) *
          Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ) =
      (2 / 5 * (K + 3)) *
        (((squarePrefixEndpoint n : ℝ) + 1) *
          Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1)) := by
    simp only [rpow_eq]
    rw [Real.rpow_sub hUpos σ 1, Real.rpow_one]
    field_simp
    ring
  have hXcast :
      ((squarePrefixEndpoint n : ℝ) + 1) ≤ ((primorialBlockUpper k : ℝ) + 1) := by
    have : (squarePrefixEndpoint n : ℝ) ≤ (primorialBlockUpper k : ℝ) := by
      exact_mod_cast hXU
    linarith
  have hanti :
      Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1) ≤
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) (σ - 1) :=
    rpow_anti_base hXpos hXcast (by linarith)
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
        base_mul_rpow_sub_one hXpos
  have hK3 : (0 : ℝ) ≤ 2 / 5 * (K + 3) := by linarith
  have hρRfinal : ‖ρ‖ * ‖MU - ML‖ ≤
      (2 / 5 * (K + 3)) *
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    calc
      ‖ρ‖ * ‖MU - ML‖ ≤
          (2 / 5 * (K + 3)) *
            (((squarePrefixEndpoint n : ℝ) + 1) *
              Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1)) := by
        rw [← hAB]
        exact hρR
      _ ≤ (2 / 5 * (K + 3)) *
            Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
        mul_le_mul_of_nonneg_left hfin hK3
  calc
    ‖MX - ML‖ ≤ ‖Hn‖ + ‖ρ‖ * ‖MU - ML‖ := htri
    _ ≤ K * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ +
          (2 / 5 * (K + 3)) *
            Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
      linarith
    _ = (K + 2 / 5 * (K + 3)) *
          Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by ring

/-- The pointwise response bound controls the pinned residual at every point of
the block, at the cost of one square-gap interpolation. -/
private theorem norm_block_residual_le
    (hk : 2 ≤ k) (hK : 0 ≤ K) (hσl : (1 : ℝ) / 2 ≤ σ) (hσu : σ ≤ 1)
    (hH : ∀ n : ℕ,
      primorialBlockLower k < squarePrefixEndpoint n →
      squarePrefixEndpoint n ≤ primorialBlockUpper k →
      ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
        K * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ)
    {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ≤
      (K + 2 / 5 * (K + 3) + 3) * Real.rpow ((x : ℝ) + 1) σ := by
  obtain ⟨n, hnle, hngt⟩ := sqrt_sample_bracket x
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hbase1 : (1 : ℝ) ≤ (x : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
    linarith
  have hhalf :
      Real.rpow ((x : ℝ) + 1) (1 / 2 : ℝ) ≤ Real.rpow ((x : ℝ) + 1) σ :=
    Real.rpow_le_rpow_of_exponent_le hbase1 hσl
  have hgap := sub_le_gap_of_bracket hnle hngt
  have hK1 : (0 : ℝ) ≤ K + 2 / 5 * (K + 3) := by linarith
  by_cases hcase : primorialBlockLower k < squarePrefixEndpoint n
  · -- interpolate from the preceding complete square inside the block
    have hXU : squarePrefixEndpoint n ≤ primorialBlockUpper k :=
      hnle.trans hupper
    have hB := norm_square_sample_residual_le hk hK hσl hσu hH hcase hXU
    have htri :
        ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ≤
          ‖mertensSummatory x -
              mertensSummatory (squarePrefixEndpoint n)‖ +
            ‖mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (primorialBlockLower k)‖ := by
      have hsplit :
          mertensSummatory x - mertensSummatory (primorialBlockLower k) =
            (mertensSummatory x -
              mertensSummatory (squarePrefixEndpoint n)) +
            (mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (primorialBlockLower k)) := by ring
      rw [hsplit]
      exact norm_add_le _ _
    have hMxX :
        ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)‖ ≤
          ((x - squarePrefixEndpoint n : ℕ) : ℝ) :=
      norm_mertensSummatory_sub_le (squarePrefixEndpoint n) x hnle
    have hXmono :
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ ≤
          Real.rpow ((x : ℝ) + 1) σ := by
      apply Real.rpow_le_rpow (by positivity) _ hσ0
      have : (squarePrefixEndpoint n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hnle
      linarith
    have h1 :
        ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)‖ ≤
          3 * Real.rpow ((x : ℝ) + 1) σ :=
      hMxX.trans (hgap.trans (by linarith))
    have h2 :
        ‖mertensSummatory (squarePrefixEndpoint n) -
            mertensSummatory (primorialBlockLower k)‖ ≤
          (K + 2 / 5 * (K + 3)) * Real.rpow ((x : ℝ) + 1) σ :=
      hB.trans (mul_le_mul_of_nonneg_left hXmono hK1)
    calc
      ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ≤
          ‖mertensSummatory x -
              mertensSummatory (squarePrefixEndpoint n)‖ +
            ‖mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (primorialBlockLower k)‖ := htri
      _ ≤ 3 * Real.rpow ((x : ℝ) + 1) σ +
            (K + 2 / 5 * (K + 3)) * Real.rpow ((x : ℝ) + 1) σ := by
        linarith
      _ = (K + 2 / 5 * (K + 3) + 3) * Real.rpow ((x : ℝ) + 1) σ := by ring
  · -- the whole pinned interval lies inside one square gap
    push_neg at hcase
    have hMxL :
        ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ≤
          ((x - primorialBlockLower k : ℕ) : ℝ) :=
      norm_mertensSummatory_sub_le (primorialBlockLower k) x hlower.le
    have hsubNat : x - primorialBlockLower k ≤ x - squarePrefixEndpoint n :=
      Nat.sub_le_sub_left hcase x
    have hsub :
        ((x - primorialBlockLower k : ℕ) : ℝ) ≤
          ((x - squarePrefixEndpoint n : ℕ) : ℝ) := by exact_mod_cast hsubNat
    have hrpow0 : (0 : ℝ) ≤ Real.rpow ((x : ℝ) + 1) σ :=
      Real.rpow_nonneg (by positivity) _
    calc
      ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ≤
          ((x - primorialBlockLower k : ℕ) : ℝ) := hMxL
      _ ≤ ((x - squarePrefixEndpoint n : ℕ) : ℝ) := hsub
      _ ≤ 3 * Real.rpow ((x : ℝ) + 1) (1 / 2 : ℝ) := hgap
      _ ≤ 3 * Real.rpow ((x : ℝ) + 1) σ := by linarith
      _ ≤ (K + 2 / 5 * (K + 3) + 3) * Real.rpow ((x : ℝ) + 1) σ := by
        nlinarith

end FixedBlock

/-! ## The residual criterion from the RH-scale response bound -/

/-- The synthesis boundary target implies the RH-scale bound for every pinned
primorial wheel residual. -/
theorem primeWheelResidualBounded_of_nonzeroResponseRHScale
    (hscale : MobiusSynthesisBoundary.NonzeroResponseRHScale) :
    PrimeWheelResidualBoundedStatement primorialWheelFamily := by
  intro ε hε
  have hεs0 : 0 < min (ε / 2) (1 / 2 : ℝ) :=
    lt_min (by linarith) (by norm_num)
  obtain ⟨K, hK, hbound⟩ := hscale (min (ε / 2) (1 / 2 : ℝ)) hεs0
  set εs := min (ε / 2) (1 / 2 : ℝ) with hεsdef
  set σ := 1 / 2 + εs with hσdef
  have hσl : (1 : ℝ) / 2 ≤ σ := by
    have : (0 : ℝ) < εs := hεs0
    rw [hσdef]; linarith
  have hσu : σ ≤ 1 := by
    have : εs ≤ 1 / 2 := min_le_right _ _
    rw [hσdef]; linarith
  have hεshalf : εs ≤ ε / 2 := min_le_left _ _
  set KD := K + 2 / 5 * (K + 3) + 3 + 6 with hKDdef
  have hKD0 : (0 : ℝ) ≤ KD := by rw [hKDdef]; linarith
  refine ⟨KD ^ 2, by positivity, ?_⟩
  intro k x hlow hup
  change primorialBlockLower k < x at hlow
  change x ≤ primorialBlockUpper k at hup
  change ‖(((primorialWheelSystem k).residual x : ℤ) : ℂ)‖ ^ 2 ≤ _
  rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le k hlow.le hup]
  have hxpos : (0 : ℝ) < (x : ℝ) + 1 := by positivity
  have hbase1 : (1 : ℝ) ≤ (x : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
    linarith
  have hrpow0 : (0 : ℝ) ≤ Real.rpow ((x : ℝ) + 1) σ :=
    Real.rpow_nonneg (by positivity) _
  -- uniform norm bound over all blocks
  have hnorm :
      ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ≤
        KD * Real.rpow ((x : ℝ) + 1) σ := by
    by_cases hk : 2 ≤ k
    · -- large blocks: the analytic estimate
      have hH : ∀ n : ℕ,
          primorialBlockLower k < squarePrefixEndpoint n →
          squarePrefixEndpoint n ≤ primorialBlockUpper k →
          ‖squareWheelNonzeroSampleResponse
              (primorialMinimalWheelSystem k) n‖ ≤
            K * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
        intro n hl hu
        have h := hbound k n hk hl hu
        have hcast : ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) =
            (squarePrefixEndpoint n : ℝ) + 1 := by push_cast; ring
        rw [hcast] at h
        exact h
      have h := norm_block_residual_le hk hK hσl hσu hH hlow hup
      have hstep : (K + 2 / 5 * (K + 3) + 3) * Real.rpow ((x : ℝ) + 1) σ ≤
          KD * Real.rpow ((x : ℝ) + 1) σ := by
        apply mul_le_mul_of_nonneg_right _ hrpow0
        rw [hKDdef]; linarith
      exact h.trans hstep
    · -- the two initial blocks are finite: `x ≤ 6`
      push_neg at hk
      have hUsmall : primorialBlockUpper k ≤ 6 := by
        have hmono : primorialEndpoint (k + 1) ≤ primorialEndpoint 2 :=
          primorialEndpoint_strictMono.monotone (by omega)
        rw [primorialEndpoint_two_eq] at hmono
        exact hmono
      have hx6 : x ≤ 6 := hup.trans hUsmall
      have hMxL :
          ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ≤
            ((x - primorialBlockLower k : ℕ) : ℝ) :=
        norm_mertensSummatory_sub_le (primorialBlockLower k) x hlow.le
      have hsix : ((x - primorialBlockLower k : ℕ) : ℝ) ≤ 6 := by
        have : x - primorialBlockLower k ≤ 6 := by omega
        exact_mod_cast this
      have hone : (1 : ℝ) ≤ Real.rpow ((x : ℝ) + 1) σ :=
        Real.one_le_rpow hbase1 (by linarith)
      calc
        ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ≤
            ((x - primorialBlockLower k : ℕ) : ℝ) := hMxL
        _ ≤ 6 := hsix
        _ ≤ 6 * Real.rpow ((x : ℝ) + 1) σ := by linarith
        _ ≤ KD * Real.rpow ((x : ℝ) + 1) σ := by
          apply mul_le_mul_of_nonneg_right _ hrpow0
          rw [hKDdef]; linarith
  -- square the bound and pass to the target exponent
  have hsq :
      ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ^ 2 ≤
        (KD * Real.rpow ((x : ℝ) + 1) σ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  have hsplit :
      (KD * Real.rpow ((x : ℝ) + 1) σ) ^ 2 =
        KD ^ 2 * Real.rpow ((x : ℝ) + 1) (σ + σ) := by
    simp only [rpow_eq]
    rw [Real.rpow_add hxpos σ σ]
    ring
  have hexp :
      Real.rpow ((x : ℝ) + 1) (σ + σ) ≤ Real.rpow ((x : ℝ) + 1) (1 + ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hbase1
    rw [hσdef]
    linarith
  have hfinal :
      ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ^ 2 ≤
        KD ^ 2 * Real.rpow ((x : ℝ) + 1) (1 + ε) := by
    calc
      ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ ^ 2 ≤
          (KD * Real.rpow ((x : ℝ) + 1) σ) ^ 2 := hsq
      _ = KD ^ 2 * Real.rpow ((x : ℝ) + 1) (σ + σ) := hsplit
      _ ≤ KD ^ 2 * Real.rpow ((x : ℝ) + 1) (1 + ε) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
  have hcast : ((x + 1 : ℕ) : ℝ) = (x : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  exact hfinal

/-! ## The reverse arrow: from Mertens energy back to the response bound -/

/-- The global Mertens energy criterion implies the synthesis boundary target.
This is the quantitative converse, using the same centering identity. -/
theorem nonzeroResponseRHScale_of_mertensEnergyBounded
    (hM : MertensEnergyBoundedStatement) :
    MobiusSynthesisBoundary.NonzeroResponseRHScale := by
  intro ε hε
  have hεs0 : 0 < min ε (1 / 2 : ℝ) := lt_min hε (by norm_num)
  obtain ⟨C, hC, hCb⟩ := hM (2 * min ε (1 / 2 : ℝ)) (by linarith)
  set εs := min ε (1 / 2 : ℝ) with hεsdef
  set σ := 1 / 2 + εs with hσdef
  have hσl : (1 : ℝ) / 2 ≤ σ := by
    rw [hσdef]; linarith
  have hσu : σ ≤ 1 := by
    have : εs ≤ 1 / 2 := min_le_right _ _
    rw [hσdef]; linarith
  set Q := Real.sqrt C with hQdef
  have hQ0 : (0 : ℝ) ≤ Q := Real.sqrt_nonneg _
  -- pointwise Mertens bound in norm form
  have hMy : ∀ y : ℕ, ‖mertensSummatory y‖ ≤
      Q * Real.rpow ((y : ℝ) + 1) σ := by
    intro y
    have h1 := hCb y
    have hcast : ((y + 1 : ℕ) : ℝ) = (y : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h1
    have hypos : (0 : ℝ) < (y : ℝ) + 1 := by positivity
    have h2 : Real.rpow ((y : ℝ) + 1) (1 + 2 * εs) =
        Real.rpow ((y : ℝ) + 1) σ * Real.rpow ((y : ℝ) + 1) σ := by
      simp only [rpow_eq]
      rw [← Real.rpow_add hypos]
      congr 1
      rw [hσdef]
      ring
    have hQ2 : Q * Q = C := by
      rw [hQdef]
      exact Real.mul_self_sqrt hC
    have h3 : ‖mertensSummatory y‖ ^ 2 ≤
        (Q * Real.rpow ((y : ℝ) + 1) σ) ^ 2 := by
      calc
        ‖mertensSummatory y‖ ^ 2 ≤
            C * Real.rpow ((y : ℝ) + 1) (1 + 2 * εs) := h1
        _ = (Q * Real.rpow ((y : ℝ) + 1) σ) ^ 2 := by
          rw [h2, ← hQ2]
          ring
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hQ0 (Real.rpow_nonneg (by positivity) _))).1 h3
  refine ⟨3 * Q, by positivity, ?_⟩
  intro k n hk hlow hup
  -- centering identity
  have hcenter :=
    primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter k n hlow hup
  rw [primorialSquareZeroModeCenter] at hcenter
  set ρ := squareWheelSampleRatio (primorialMinimalWheelSystem k) n with hρdef
  set MU := mertensSummatory (primorialBlockUpper k)
  set ML := mertensSummatory (primorialBlockLower k)
  set MX := mertensSummatory (squarePrefixEndpoint n)
  have htri :
      ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
        ‖MX - ML‖ + ‖ρ‖ * ‖MU - ML‖ := by
    rw [hcenter]
    calc
      ‖(MX - ML) - ρ * (MU - ML)‖ ≤ ‖MX - ML‖ + ‖ρ * (MU - ML)‖ :=
        norm_sub_le _ _
      _ = ‖MX - ML‖ + ‖ρ‖ * ‖MU - ML‖ := by rw [norm_mul]
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hXpos : (0 : ℝ) < (squarePrefixEndpoint n : ℝ) + 1 := by positivity
  have hUpos : (0 : ℝ) < (primorialBlockUpper k : ℝ) + 1 := by positivity
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
  -- first term
  have hfirst : ‖MX - ML‖ ≤
      2 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    have hX := hMy (squarePrefixEndpoint n)
    have hL := hMy (primorialBlockLower k)
    have hLX2 : ‖ML‖ ≤ Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
      hL.trans (mul_le_mul_of_nonneg_left hLmono hQ0)
    calc
      ‖MX - ML‖ ≤ ‖MX‖ + ‖ML‖ := norm_sub_le _ _
      _ ≤ Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ +
            Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
        have := hX
        linarith
      _ = 2 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by ring
  -- second term via the fine coupling bound
  have hsecondRaw : ‖MU - ML‖ ≤
      2 * Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by
    have hU := hMy (primorialBlockUpper k)
    have hL := hMy (primorialBlockLower k)
    have hLU : (primorialBlockLower k : ℝ) + 1 ≤
        (primorialBlockUpper k : ℝ) + 1 := le_trans hLX hXU
    have hLmono2 :
        Real.rpow ((primorialBlockLower k : ℝ) + 1) σ ≤
          Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
      Real.rpow_le_rpow (by positivity) hLU hσ0
    have hL2 : ‖ML‖ ≤ Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ :=
      hL.trans (mul_le_mul_of_nonneg_left hLmono2 hQ0)
    calc
      ‖MU - ML‖ ≤ ‖MU‖ + ‖ML‖ := norm_sub_le _ _
      _ ≤ Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ +
            Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by
        have := hU
        linarith
      _ = 2 * Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ := by ring
  have hρfine := norm_sampleRatio_le_fine (n := n) hk
  have hρR : ‖ρ‖ * ‖MU - ML‖ ≤
      (((squarePrefixEndpoint n : ℝ) + 1) /
          (3 * ((primorialBlockUpper k : ℝ) + 1))) *
        (2 * Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ) :=
    mul_le_mul hρfine hsecondRaw (norm_nonneg _) (by positivity)
  have hAB :
      (((squarePrefixEndpoint n : ℝ) + 1) /
          (3 * ((primorialBlockUpper k : ℝ) + 1))) *
        (2 * Q * Real.rpow ((primorialBlockUpper k : ℝ) + 1) σ) =
      (2 / 3 * Q) *
        (((squarePrefixEndpoint n : ℝ) + 1) *
          Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1)) := by
    simp only [rpow_eq]
    rw [Real.rpow_sub hUpos σ 1, Real.rpow_one]
    field_simp
  have hanti :
      Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1) ≤
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) (σ - 1) :=
    rpow_anti_base hXpos hXU (by linarith)
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
        base_mul_rpow_sub_one hXpos
  have hsecond : ‖ρ‖ * ‖MU - ML‖ ≤
      (2 / 3 * Q) * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    calc
      ‖ρ‖ * ‖MU - ML‖ ≤
          (2 / 3 * Q) *
            (((squarePrefixEndpoint n : ℝ) + 1) *
              Real.rpow ((primorialBlockUpper k : ℝ) + 1) (σ - 1)) := by
        rw [← hAB]
        exact hρR
      _ ≤ (2 / 3 * Q) *
            Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
  -- assemble and raise the exponent to `1/2 + ε`
  have hbase1 : (1 : ℝ) ≤ (squarePrefixEndpoint n : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (squarePrefixEndpoint n : ℝ) := Nat.cast_nonneg _
    linarith
  have hraise :
      Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ ≤
        Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) (1 / 2 + ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hbase1
    have : εs ≤ ε := min_le_left _ _
    rw [hσdef]
    linarith
  have hrpow0 : (0 : ℝ) ≤
      Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ :=
    Real.rpow_nonneg (by positivity) _
  have htotal :
      ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
        3 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
    calc
      ‖squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) n‖ ≤
          ‖MX - ML‖ + ‖ρ‖ * ‖MU - ML‖ := htri
      _ ≤ 2 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ +
            (2 / 3 * Q) *
              Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
        linarith
      _ ≤ 3 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := by
        nlinarith
  have hcast : ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) =
      (squarePrefixEndpoint n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  calc
    ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
        3 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) σ := htotal
    _ ≤ 3 * Q * Real.rpow ((squarePrefixEndpoint n : ℝ) + 1) (1 / 2 + ε) :=
      mul_le_mul_of_nonneg_left hraise (by positivity)

/-! ## Main connecting theorems -/

/-- **Forward connecting theorem.**  The synthesis boundary target
`NonzeroResponseRHScale` implies the projected-renewal quadratic bound for
every nonnegative cutoff `Λ`. -/
theorem projectedRenewalQuadraticBounded_of_nonzeroResponseRHScale
    (hscale : MobiusSynthesisBoundary.NonzeroResponseRHScale) :
    ∀ Λ : ℝ, 0 ≤ Λ →
      RHLean.Proof.CanonicalGapAncestryQuadraticClosure.ProjectedRenewalQuadraticBoundedStatement
        Λ := by
  intro Λ hΛ
  have hres : PrimeWheelResidualBoundedStatement primorialWheelFamily :=
    primeWheelResidualBounded_of_nonzeroResponseRHScale hscale
  have hM : MertensEnergyBoundedStatement :=
    primorialWheel_residualBounded_iff_mertensEnergy.mp hres
  have hSq : SquarePrefixUniformLocalBoundedStatement :=
    squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded.mpr hM
  have hHigh : RHLean.Proof.CanonicalHighUniformLocalBoundedStatement Λ :=
    (RHLean.Proof.canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized
      Λ).mpr hSq
  exact
    (RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh
      hΛ).mpr hHigh

/-- **Reverse connecting theorem.**  The projected-renewal quadratic bound at
any single nonnegative cutoff recovers the synthesis boundary target. -/
theorem nonzeroResponseRHScale_of_projectedRenewalQuadraticBounded
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hquad :
      RHLean.Proof.CanonicalGapAncestryQuadraticClosure.ProjectedRenewalQuadraticBoundedStatement
        Λ) :
    MobiusSynthesisBoundary.NonzeroResponseRHScale := by
  have hHigh : RHLean.Proof.CanonicalHighUniformLocalBoundedStatement Λ :=
    (RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh
      hΛ).mp hquad
  have hSq : SquarePrefixUniformLocalBoundedStatement :=
    (RHLean.Proof.canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized
      Λ).mp hHigh
  have hM : MertensEnergyBoundedStatement :=
    squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded.mp hSq
  exact nonzeroResponseRHScale_of_mertensEnergyBounded hM

/-- **Equivalence.**  The orphaned synthesis boundary target and the
projected-renewal quadratic bound of the premise-free RH bridge are the same
statement, uniformly over all nonnegative cutoffs. -/
theorem nonzeroResponseRHScale_iff_projectedRenewalQuadraticBounded :
    MobiusSynthesisBoundary.NonzeroResponseRHScale ↔
      (∀ Λ : ℝ, 0 ≤ Λ →
        RHLean.Proof.CanonicalGapAncestryQuadraticClosure.ProjectedRenewalQuadraticBoundedStatement
          Λ) := by
  constructor
  · exact projectedRenewalQuadraticBounded_of_nonzeroResponseRHScale
  · intro h
    exact nonzeroResponseRHScale_of_projectedRenewalQuadraticBounded
      (le_refl (0 : ℝ)) (h 0 (le_refl (0 : ℝ)))

end MobiusSynthesisBoundaryBridge

end RHLean.Analysis
