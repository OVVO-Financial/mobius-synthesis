import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Proof.SquareRootMertensEndpointAmplification
import RHLean.Arithmetic.TopPrimeReplacementIsolation

/-!
# Recursive prime replacement at a square endpoint

This module implements the first exact nonlocal replacement step forced by
`TopPrimeReplacementIsolation`.

For a square-root cutoff `R`, truncate the Möbius divisor convolution at
`d < R`:

`C_R(n) = sum_{d | n, d < R} mu(d)`.

Because the full divisor Möbius sum vanishes away from `n = 1`, `C_R(n)` is
zero for `1 < n < R`.  Applying the repository's exact Möbius renewal telescope
at `X_R = R^2 - 1` therefore gives

`M(X_R) = M(R-1) - sum_{R <= n <= X_R} C_R(n) M(floor(X_R/n))`.

Every reciprocal argument on the right is strictly below `R`.  Thus the
unmatched population is not an independent error: it is an exact signed family
of lower-scale Mertens states.

For a top prime `q > X_R/2`, the local insertion obstruction remains, but its
replacement coefficient is now part of the complete quotient fibre
`floor(X_R/n) = 1`, together with composite `n`.  This is the intended wholesale,
nonlocal arena for cancellation.

No absolute value is applied to an individual residual fibre in this module.
The final row energy is recorded only as a diagnostic after complete quotient-
fibre recombination; no quantitative row bound is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Möbius seed retained strictly below the square-root cutoff. -/
def squareRootReplacementSeed (R d : ℕ) : ℂ :=
  if d < R then (((μ d : ℤ) : ℂ)) else 0

/-- Truncated divisor Möbius coefficient.  This is the complete signed
replacement coefficient at physical index `n`, before any norm is taken. -/
def squareRootReplacementKernel (R n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, squareRootReplacementSeed R d

/-- Below the root cutoff the truncated divisor sum is already the full Möbius
divisor sum, hence it vanishes except at `n = 1`. -/
theorem squareRootReplacementKernel_eq_ite_of_lt_root
    {R n : ℕ} (hn1 : 1 ≤ n) (hnR : n < R) :
    squareRootReplacementKernel R n = if n = 1 then 1 else 0 := by
  have hn0 : n ≠ 0 := by omega
  unfold squareRootReplacementKernel squareRootReplacementSeed
  calc
    (∑ d ∈ n.divisors,
        if d < R then (((μ d : ℤ) : ℂ)) else 0) =
      ∑ d ∈ n.divisors, (((μ d : ℤ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hddata := Nat.mem_divisors.mp hd
        have hdn : d ≤ n := Nat.le_of_dvd (by omega) hddata.1
        have hdR : d < R := hdn.trans_lt hnR
        simp [hdR]
    _ = if n = 1 then 1 else 0 :=
      RHLean.Analysis.sum_divisors_moebius_eq_ite n

/-- Summing the truncated seed through any cutoff containing `R-1` gives the
ordinary Mertens prefix at `R-1`. -/
theorem sum_squareRootReplacementSeed_eq_mertens_pred
    {R X : ℕ} (hR : 2 ≤ R) (hRX : R - 1 ≤ X) :
    (∑ d ∈ Finset.Icc 1 X, squareRootReplacementSeed R d) =
      RHLean.Analysis.mertensSummatory (R - 1) := by
  have hfilter :
      (Finset.Icc 1 X).filter (fun d => d < R) = Finset.Icc 1 (R - 1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  unfold squareRootReplacementSeed
  rw [← Finset.sum_filter, hfilter]
  exact (RHLean.Analysis.mertensSummatory_eq_sum_Icc (R - 1)).symm

/-- On the complete prefix below `R`, the replacement kernel contributes only
the `n = 1` term, which is exactly `M(X)`. -/
theorem sum_replacementKernel_below_root_eq_mertens
    {R X : ℕ} (hR : 2 ≤ R) :
    (∑ n ∈ Finset.Icc 1 (R - 1),
        squareRootReplacementKernel R n *
          RHLean.Analysis.mertensSummatory (X / n)) =
      RHLean.Analysis.mertensSummatory X := by
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 (R - 1) := by
    simp
    omega
  calc
    (∑ n ∈ Finset.Icc 1 (R - 1),
        squareRootReplacementKernel R n *
          RHLean.Analysis.mertensSummatory (X / n)) =
      ∑ n ∈ Finset.Icc 1 (R - 1),
        if n = 1 then RHLean.Analysis.mertensSummatory X else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnIcc := Finset.mem_Icc.mp hn
          have hnR : n < R := by omega
          rw [squareRootReplacementKernel_eq_ite_of_lt_root hnIcc.1 hnR]
          by_cases hnone : n = 1
          · subst n
            simp
          · simp [hnone]
    _ = RHLean.Analysis.mertensSummatory X := by
      simp [h1mem]

/-- Every residual reciprocal cutoff in the square-endpoint tail is genuinely
lower scale. -/
theorem squareRootEndpoint_div_lt_root_of_root_le
    {R n : ℕ} (hR : 2 ≤ R) (hn : R ≤ n) :
    squareRootEndpoint R / n < R := by
  have hnpos : 0 < n := by omega
  apply (Nat.div_lt_iff_lt_mul hnpos).2
  have hsqpos : 0 < R ^ 2 := by positivity
  have hsub : R ^ 2 - 1 < R ^ 2 := Nat.sub_lt hsqpos (by norm_num)
  have hXlt : squareRootEndpoint R < R * R := by
    simpa [squareRootEndpoint, pow_two] using hsub
  have hmul : R * R ≤ R * n := Nat.mul_le_mul_left R hn
  exact hXlt.trans_le hmul

/-- **Exact recursive replacement identity.**  At `X_R = R^2 - 1`, all
nontrivial truncated-divisor coefficients occur at indices `n >= R`, hence all
Mertens states produced by the replacement have argument strictly below `R`. -/
theorem mertensEndpoint_eq_pred_sub_recursiveReplacement
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
      RHLean.Analysis.mertensSummatory (R - 1) -
        ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          squareRootReplacementKernel R n *
            RHLean.Analysis.mertensSummatory (squareRootEndpoint R / n) := by
  let X := squareRootEndpoint R
  have hRX : R ≤ X := by
    dsimp [X]
    unfold squareRootEndpoint
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hpredX : R - 1 ≤ X := by omega
  have hset :
      Finset.Icc 1 X =
        Finset.Icc 1 (R - 1) ∪ Finset.Icc R X := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj :
      Disjoint (Finset.Icc 1 (R - 1)) (Finset.Icc R X) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo hnhi
    omega
  have htel :=
    RHLean.Analysis.sum_convolveOne_mul_mertensSummatory_div
      (squareRootReplacementSeed R) X
  change
    (∑ n ∈ Finset.Icc 1 X,
        squareRootReplacementKernel R n *
          RHLean.Analysis.mertensSummatory (X / n)) =
      ∑ d ∈ Finset.Icc 1 X, squareRootReplacementSeed R d at htel
  rw [sum_squareRootReplacementSeed_eq_mertens_pred hR hpredX] at htel
  rw [hset, Finset.sum_union hdisj,
    sum_replacementKernel_below_root_eq_mertens hR] at htel
  dsimp [X] at htel ⊢
  rw [← htel]
  ring

/-- The exact residual tail, retained as a signed lower-scale Mertens family. -/
def squareRootRecursiveReplacementResidual (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    squareRootReplacementKernel R n *
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R / n)

/-- The endpoint is exactly the preceding lower-scale Mertens value minus the
recursive residual family. -/
theorem mertensEndpoint_eq_pred_sub_recursiveResidual
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
      RHLean.Analysis.mertensSummatory (R - 1) -
        squareRootRecursiveReplacementResidual R := by
  simpa [squareRootRecursiveReplacementResidual] using
    mertensEndpoint_eq_pred_sub_recursiveReplacement R hR

/-! ## Recombination by reciprocal quotient -/

/-- Complete signed coefficient carried by the physical tail indices whose
reciprocal cutoff is exactly `y`.  The complete fibre is summed before any norm. -/
def squareRootReplacementTailCoefficient (R y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    if squareRootEndpoint R / n = y then
      squareRootReplacementKernel R n
    else 0

/-- Final lower-scale coefficient row.  The preceding value `M(R-1)` is the
single Kronecker term; the entire physical replacement tail is subtracted only
after each reciprocal quotient fibre has been recombined. -/
def squareRootReplacementCoefficient (R y : ℕ) : ℂ :=
  (if y = R - 1 then 1 else 0) - squareRootReplacementTailCoefficient R y

/-- Recombining equal reciprocal cutoffs loses nothing: the physical residual
family is exactly the sum of the fully signed quotient-fibre coefficients times
the corresponding lower-scale Mertens values. -/
theorem sum_replacementTailCoefficient_mul_mertens_eq_residual
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ Finset.range R,
        squareRootReplacementTailCoefficient R y *
          RHLean.Analysis.mertensSummatory y) =
      squareRootRecursiveReplacementResidual R := by
  classical
  unfold squareRootReplacementTailCoefficient
    squareRootRecursiveReplacementResidual
  calc
    (∑ y ∈ Finset.range R,
        (∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * RHLean.Analysis.mertensSummatory y) =
      ∑ y ∈ Finset.range R,
        ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          (if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * RHLean.Analysis.mertensSummatory y := by
            apply Finset.sum_congr rfl
            intro y _hy
            rw [Finset.sum_mul]
    _ =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        ∑ y ∈ Finset.range R,
          (if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * RHLean.Analysis.mertensSummatory y := by
            rw [Finset.sum_comm]
    _ =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          RHLean.Analysis.mertensSummatory (squareRootEndpoint R / n) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnR : R ≤ n := (Finset.mem_Icc.mp hn).1
            have hylt : squareRootEndpoint R / n < R :=
              squareRootEndpoint_div_lt_root_of_root_le hR hnR
            have hymem : squareRootEndpoint R / n ∈ Finset.range R :=
              Finset.mem_range.mpr hylt
            calc
              (∑ y ∈ Finset.range R,
                (if squareRootEndpoint R / n = y then
                  squareRootReplacementKernel R n
                else 0) * RHLean.Analysis.mertensSummatory y) =
                ∑ y ∈ Finset.range R,
                  if squareRootEndpoint R / n = y then
                    squareRootReplacementKernel R n *
                      RHLean.Analysis.mertensSummatory y
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro y _hy
                    by_cases heq : squareRootEndpoint R / n = y <;>
                      simp [heq]
              _ = squareRootReplacementKernel R n *
                    RHLean.Analysis.mertensSummatory
                      (squareRootEndpoint R / n) := by
                    simp [hymem]

/-- **Exact recombined lower-triangular row.**  The completed-square Mertens
value is a single signed linear combination of Mertens values at `y < R`.
There are no arbitrary-point or fibrewise error terms left. -/
theorem mertensEndpoint_eq_recombinedReplacementRow
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
      ∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          RHLean.Analysis.mertensSummatory y := by
  have htail := sum_replacementTailCoefficient_mul_mertens_eq_residual R hR
  have hpredlt : R - 1 < R := by omega
  have hpredmem : R - 1 ∈ Finset.range R := Finset.mem_range.mpr hpredlt
  have hpred :
      (∑ y ∈ Finset.range R,
        (if y = R - 1 then (1 : ℂ) else 0) *
          RHLean.Analysis.mertensSummatory y) =
        RHLean.Analysis.mertensSummatory (R - 1) := by
    simp [hpredmem]
  calc
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
        RHLean.Analysis.mertensSummatory (R - 1) -
          squareRootRecursiveReplacementResidual R :=
      mertensEndpoint_eq_pred_sub_recursiveResidual R hR
    _ =
        (∑ y ∈ Finset.range R,
          (if y = R - 1 then (1 : ℂ) else 0) *
            RHLean.Analysis.mertensSummatory y) -
        ∑ y ∈ Finset.range R,
          squareRootReplacementTailCoefficient R y *
            RHLean.Analysis.mertensSummatory y := by rw [hpred, htail]
    _ =
      ∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          RHLean.Analysis.mertensSummatory y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _hy
      unfold squareRootReplacementCoefficient
      ring

/-- Weighted coefficient row energy after complete signed quotient-fibre
recombination.  It is recorded as a diagnostic for the next involution layer;
this module deliberately makes no quantitative claim about its size. -/
def squareRootReplacementRowEnergy (R : ℕ) : ℝ :=
  ∑ y ∈ Finset.range R,
    (((y + 1 : ℕ) : ℝ)) * ‖squareRootReplacementCoefficient R y‖ ^ 2

/-! ## Reciprocal-fibre zero mode and Type-II dictionary -/

/-- Total signed mass of the physical replacement boundary.  It is the response
of the replacement operator to the constant vector; it is not expected to be
small by itself. -/
def squareRootReplacementBoundaryMass (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    squareRootReplacementKernel R n

/-- Total coefficient of the recombined lower-triangular replacement row. -/
def squareRootReplacementRowMass (R : ℕ) : ℂ :=
  ∑ y ∈ Finset.range R, squareRootReplacementCoefficient R y

/-- Möbius mass of one reciprocal fibre in the complementary physical tail. -/
def squareRootReplacementTailMoebiusCoefficient (R y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    if squareRootEndpoint R / n = y then (((μ n : ℤ) : ℂ)) else 0

/-- Hyperbola quotient kernel.  It counts the positive integers `k <= z` whose
reciprocal quotient `floor(z/k)` is exactly `y`, cast to `ℂ`. -/
def squareRootReplacementQuotientKernel (z y : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 z, if z / k = y then 1 else 0

/-- Multiplying a positive physical index by a prime, while remaining below the
endpoint, strictly lowers its reciprocal quotient.  Thus prime insertion lives
entirely in the reciprocal-scale difference space. -/
theorem div_mul_prime_lt_div_of_mul_le
    {X n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hfit : n * p ≤ X) :
    X / (n * p) < X / n := by
  have hnpos : 0 < n := by omega
  have hp1 : 1 < p := hp.one_lt
  have hpone : 1 ≤ p := by omega
  have hn_mul_le : n ≤ n * p := by
    simpa using Nat.mul_le_mul_left n hpone
  have hnX : n ≤ X := hn_mul_le.trans hfit
  have hq1 : 1 ≤ X / n :=
    (Nat.one_le_div_iff hnpos).2 hnX
  have hqpos : 0 < X / n := by omega
  have hdrop : (X / n) / p < X / n :=
    Nat.div_lt_self hqpos hp1
  rwa [Nat.div_div_eq_div_mul] at hdrop

/-- Square-endpoint specialization of strict reciprocal-scale descent. -/
theorem squareRootReplacement_primeInsertion_strictly_lowers_scale
    {R n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hfit : n * p ≤ squareRootEndpoint R) :
    squareRootEndpoint R / (n * p) < squareRootEndpoint R / n :=
  div_mul_prime_lt_div_of_mul_le hn hp hfit

/-- The complete physical boundary mass is the sum of the reciprocal-fibre
replacement coefficients. -/
theorem sum_squareRootReplacementTailCoefficient_eq_boundaryMass
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ Finset.range R,
        squareRootReplacementTailCoefficient R y) =
      squareRootReplacementBoundaryMass R := by
  classical
  unfold squareRootReplacementTailCoefficient
    squareRootReplacementBoundaryMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnR : R ≤ n := (Finset.mem_Icc.mp hn).1
  have hylt : squareRootEndpoint R / n < R :=
    squareRootEndpoint_div_lt_root_of_root_le hR hnR
  have hymem : squareRootEndpoint R / n ∈ Finset.range R :=
    Finset.mem_range.mpr hylt
  simp [hymem]

/-- The replacement row's constant response is `1 - S_R`. -/
theorem squareRootReplacementRowMass_eq_one_sub_boundaryMass
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootReplacementRowMass R =
      1 - squareRootReplacementBoundaryMass R := by
  have hpredlt : R - 1 < R := by omega
  have hpredmem : R - 1 ∈ Finset.range R :=
    Finset.mem_range.mpr hpredlt
  unfold squareRootReplacementRowMass squareRootReplacementCoefficient
  rw [Finset.sum_sub_distrib,
    sum_squareRootReplacementTailCoefficient_eq_boundaryMass R hR]
  simp [hpredmem]

/-- Exact shifted-row decomposition.  This is an algebraic separation of the
constant mode, not a request to estimate `S_R` independently. -/
theorem mertensEndpoint_sub_one_eq_shiftedReplacementRow_sub_boundaryMass
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 =
      (∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          (RHLean.Analysis.mertensSummatory y - 1)) -
        squareRootReplacementBoundaryMass R := by
  rw [mertensEndpoint_eq_recombinedReplacementRow R hR]
  have hmass := squareRootReplacementRowMass_eq_one_sub_boundaryMass R hR
  unfold squareRootReplacementRowMass at hmass
  calc
    (∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          RHLean.Analysis.mertensSummatory y) - 1 =
      (∑ y ∈ Finset.range R,
        (squareRootReplacementCoefficient R y *
            (RHLean.Analysis.mertensSummatory y - 1) +
          squareRootReplacementCoefficient R y)) - 1 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _hy
        ring
    _ =
      (∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          (RHLean.Analysis.mertensSummatory y - 1)) +
        (∑ y ∈ Finset.range R,
          squareRootReplacementCoefficient R y) - 1 := by
        rw [Finset.sum_add_distrib]
    _ =
      (∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          (RHLean.Analysis.mertensSummatory y - 1)) -
        squareRootReplacementBoundaryMass R := by
      rw [hmass]
      ring

/-- Generic reciprocal-fibre recombination for an arbitrary lower-scale test
function.  The existing Mertens residual theorem is the specialization
`f = M`. -/
theorem sum_replacementTailCoefficient_mul
    (R : ℕ) (hR : 2 ≤ R) (f : ℕ → ℂ) :
    (∑ y ∈ Finset.range R,
        squareRootReplacementTailCoefficient R y * f y) =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n) := by
  classical
  unfold squareRootReplacementTailCoefficient
  calc
    (∑ y ∈ Finset.range R,
        (∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * f y) =
      ∑ y ∈ Finset.range R,
        ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          (if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * f y := by
            apply Finset.sum_congr rfl
            intro y _hy
            rw [Finset.sum_mul]
    _ =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        ∑ y ∈ Finset.range R,
          (if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * f y := by
            rw [Finset.sum_comm]
    _ =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnR : R ≤ n := (Finset.mem_Icc.mp hn).1
            have hylt : squareRootEndpoint R / n < R :=
              squareRootEndpoint_div_lt_root_of_root_le hR hnR
            have hymem : squareRootEndpoint R / n ∈ Finset.range R :=
              Finset.mem_range.mpr hylt
            calc
              (∑ y ∈ Finset.range R,
                (if squareRootEndpoint R / n = y then
                  squareRootReplacementKernel R n
                else 0) * f y) =
                ∑ y ∈ Finset.range R,
                  if squareRootEndpoint R / n = y then
                    squareRootReplacementKernel R n * f y
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro y _hy
                    by_cases heq : squareRootEndpoint R / n = y <;>
                      simp [heq]
              _ = squareRootReplacementKernel R n *
                    f (squareRootEndpoint R / n) := by
                    simp [hymem]

/-- Complementary Möbius seed supported at divisors `d >= R`. -/
private def squareRootReplacementTailSeed (R d : ℕ) : ℂ :=
  if R ≤ d then (((μ d : ℤ) : ℂ)) else 0

/-- On the physical tail, the truncated replacement kernel is the negative of
the complementary large-divisor Möbius sum. -/
private theorem squareRootReplacementKernel_eq_neg_tailSeedSum
    {R n : ℕ} (hR : 2 ≤ R) (hn : R ≤ n) :
    squareRootReplacementKernel R n =
      -(∑ d ∈ n.divisors, squareRootReplacementTailSeed R d) := by
  have hn1 : n ≠ 1 := by omega
  have hfull := RHLean.Analysis.sum_divisors_moebius_eq_ite n
  rw [if_neg hn1] at hfull
  unfold squareRootReplacementKernel squareRootReplacementSeed
    squareRootReplacementTailSeed
  have hzero :
      (∑ d ∈ n.divisors,
          if d < R then (((μ d : ℤ) : ℂ)) else 0) +
        (∑ d ∈ n.divisors,
          if R ≤ d then (((μ d : ℤ) : ℂ)) else 0) = 0 := by
    calc
      (∑ d ∈ n.divisors,
          if d < R then (((μ d : ℤ) : ℂ)) else 0) +
        (∑ d ∈ n.divisors,
          if R ≤ d then (((μ d : ℤ) : ℂ)) else 0) =
        ∑ d ∈ n.divisors,
          ((if d < R then (((μ d : ℤ) : ℂ)) else 0) +
            (if R ≤ d then (((μ d : ℤ) : ℂ)) else 0)) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ d ∈ n.divisors, (((μ d : ℤ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hdR : d < R
        · simp [hdR, Nat.not_le_of_gt hdR]
        · have hRd : R ≤ d := Nat.le_of_not_gt hdR
          simp [hdR, hRd]
      _ = 0 := hfull
  calc
    (∑ d ∈ n.divisors,
        if d < R then (((μ d : ℤ) : ℂ)) else 0) =
      ((∑ d ∈ n.divisors,
          if d < R then (((μ d : ℤ) : ℂ)) else 0) +
        (∑ d ∈ n.divisors,
          if R ≤ d then (((μ d : ℤ) : ℂ)) else 0)) -
        (∑ d ∈ n.divisors,
          if R ≤ d then (((μ d : ℤ) : ℂ)) else 0) := by ring
    _ = -(∑ d ∈ n.divisors,
          if R ≤ d then (((μ d : ℤ) : ℂ)) else 0) := by
      rw [hzero]
      ring

/-- The complementary seed convolution is `-C_R(n)` on the physical tail and
zero below it. -/
private theorem sum_squareRootReplacementTailSeed_divisors_eq_ite
    {R n : ℕ} (hR : 2 ≤ R) (hn1 : 1 ≤ n) :
    (∑ d ∈ n.divisors, squareRootReplacementTailSeed R d) =
      if R ≤ n then -squareRootReplacementKernel R n else 0 := by
  by_cases hnR : R ≤ n
  · rw [if_pos hnR]
    have h := squareRootReplacementKernel_eq_neg_tailSeedSum hR hnR
    rw [h]
    ring
  · rw [if_neg hnR]
    apply Finset.sum_eq_zero
    intro d hd
    unfold squareRootReplacementTailSeed
    have hddata := Nat.mem_divisors.mp hd
    have hdn : d ≤ n := Nat.le_of_dvd (by omega) hddata.1
    have hnot : ¬ R ≤ d := by omega
    simp [hnot]

/-- Generic hyperbola Fubini for a divisor convolution tested against an
arbitrary reciprocal-scale function. -/
private theorem sum_convolveOne_mul_floorWeight
    (g f : ℕ → ℂ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ n.divisors, g d) * f (X / n)) =
      ∑ d ∈ Finset.Icc 1 X,
        g d * ∑ k ∈ Finset.Icc 1 (X / d), f (X / d / k) := by
  classical
  have hstep : ∀ n ∈ Finset.Icc 1 X,
      (∑ d ∈ n.divisors, g d) * f (X / n) =
        ∑ p ∈ n.divisorsAntidiagonal,
          g p.1 * f (X / p.1 / p.2) := by
    intro n _hn
    have hanti :
        (∑ p ∈ n.divisorsAntidiagonal,
          g p.1 * f (X / p.1 / p.2)) =
        ∑ d ∈ n.divisors, g d * f (X / d / (n / d)) :=
      Nat.sum_divisorsAntidiagonal
        (f := fun a b => g a * f (X / a / b))
    rw [hanti, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mem_divisors] at hd
    have harg : X / d / (n / d) = X / n := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hd.1]
    rw [harg]
  calc
    (∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ n.divisors, g d) * f (X / n)) =
      ∑ n ∈ Finset.Icc 1 X,
        ∑ p ∈ n.divisorsAntidiagonal,
          g p.1 * f (X / p.1 / p.2) :=
        Finset.sum_congr rfl hstep
    _ = ∑ d ∈ Finset.Icc 1 X,
        ∑ k ∈ Finset.Icc 1 (X / d),
          g d * f (X / d / k) :=
      RHLean.Analysis.sum_Icc_divisorsAntidiagonal_eq_sum_div
        (fun d k => g d * f (X / d / k)) X
    _ = ∑ d ∈ Finset.Icc 1 X,
        g d * ∑ k ∈ Finset.Icc 1 (X / d), f (X / d / k) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]

/-- **Exact Type-II transform of the replacement tail.**  Every test of the
`C_R`-weighted tail is the negative complementary Möbius tail tested against
all reciprocal descendants `floor(floor(X_R/d)/k)`. -/
theorem sum_replacementKernel_mul_floorWeight_eq_neg_tailTypeII
    (R : ℕ) (hR : 2 ≤ R) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n)) =
      -(∑ d ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ d : ℤ) : ℂ)) *
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
            f (squareRootEndpoint R / d / k)) := by
  classical
  have hfilter :
      (Finset.Icc 1 (squareRootEndpoint R)).filter (fun n => R ≤ n) =
        Finset.Icc R (squareRootEndpoint R) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hwhole :=
    sum_convolveOne_mul_floorWeight
      (squareRootReplacementTailSeed R) f (squareRootEndpoint R)
  have hleft :
      (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        (∑ d ∈ n.divisors, squareRootReplacementTailSeed R d) *
          f (squareRootEndpoint R / n)) =
        -(∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          squareRootReplacementKernel R n *
            f (squareRootEndpoint R / n)) := by
    calc
      (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        (∑ d ∈ n.divisors, squareRootReplacementTailSeed R d) *
          f (squareRootEndpoint R / n)) =
        ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          if R ≤ n then
            -(squareRootReplacementKernel R n *
              f (squareRootEndpoint R / n))
          else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
            rw [sum_squareRootReplacementTailSeed_divisors_eq_ite hR hn1]
            by_cases hnR : R ≤ n <;> simp [hnR]
      _ = ∑ n ∈ (Finset.Icc 1 (squareRootEndpoint R)).filter (fun n => R ≤ n),
          -(squareRootReplacementKernel R n *
            f (squareRootEndpoint R / n)) := by
            rw [Finset.sum_filter]
      _ = ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          -(squareRootReplacementKernel R n *
            f (squareRootEndpoint R / n)) := by rw [hfilter]
      _ = -(∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          squareRootReplacementKernel R n *
            f (squareRootEndpoint R / n)) := by
            rw [Finset.sum_neg_distrib]
  have hright :
      (∑ d ∈ Finset.Icc 1 (squareRootEndpoint R),
        squareRootReplacementTailSeed R d *
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
            f (squareRootEndpoint R / d / k)) =
        ∑ d ∈ Finset.Icc R (squareRootEndpoint R),
          (((μ d : ℤ) : ℂ)) *
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
              f (squareRootEndpoint R / d / k) := by
    calc
      (∑ d ∈ Finset.Icc 1 (squareRootEndpoint R),
        squareRootReplacementTailSeed R d *
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
            f (squareRootEndpoint R / d / k)) =
        ∑ d ∈ Finset.Icc 1 (squareRootEndpoint R),
          if R ≤ d then
            (((μ d : ℤ) : ℂ)) *
              ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
                f (squareRootEndpoint R / d / k)
          else 0 := by
            apply Finset.sum_congr rfl
            intro d _hd
            unfold squareRootReplacementTailSeed
            by_cases hdR : R ≤ d <;> simp [hdR]
      _ = ∑ d ∈ (Finset.Icc 1 (squareRootEndpoint R)).filter (fun d => R ≤ d),
          (((μ d : ℤ) : ℂ)) *
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
              f (squareRootEndpoint R / d / k) := by
            rw [Finset.sum_filter]
      _ = ∑ d ∈ Finset.Icc R (squareRootEndpoint R),
          (((μ d : ℤ) : ℂ)) *
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
              f (squareRootEndpoint R / d / k) := by rw [hfilter]
  have hneg :
      -(∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n)) =
        ∑ d ∈ Finset.Icc R (squareRootEndpoint R),
          (((μ d : ℤ) : ℂ)) *
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
              f (squareRootEndpoint R / d / k) := by
    calc
      -(∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n)) =
        ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          (∑ d ∈ n.divisors, squareRootReplacementTailSeed R d) *
            f (squareRootEndpoint R / n) := hleft.symm
      _ = ∑ d ∈ Finset.Icc 1 (squareRootEndpoint R),
          squareRootReplacementTailSeed R d *
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
              f (squareRootEndpoint R / d / k) := hwhole
      _ = ∑ d ∈ Finset.Icc R (squareRootEndpoint R),
          (((μ d : ℤ) : ℂ)) *
            ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
              f (squareRootEndpoint R / d / k) := hright
  calc
    (∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n)) =
      -(-(∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n))) := by ring
    _ = -(∑ d ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ d : ℤ) : ℂ)) *
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
            f (squareRootEndpoint R / d / k)) := by rw [hneg]

/-- Grouping the complementary Möbius tail by its reciprocal quotient loses no
information. -/
theorem sum_squareRootReplacementTailMoebiusCoefficient_mul
    (R : ℕ) (hR : 2 ≤ R) (F : ℕ → ℂ) :
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z * F z) =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ n : ℤ) : ℂ)) * F (squareRootEndpoint R / n) := by
  classical
  unfold squareRootReplacementTailMoebiusCoefficient
  calc
    (∑ z ∈ Finset.range R,
        (∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          if squareRootEndpoint R / n = z then (((μ n : ℤ) : ℂ)) else 0) *
          F z) =
      ∑ z ∈ Finset.range R,
        ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          (if squareRootEndpoint R / n = z then (((μ n : ℤ) : ℂ)) else 0) *
            F z := by
              apply Finset.sum_congr rfl
              intro z _hz
              rw [Finset.sum_mul]
    _ =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        ∑ z ∈ Finset.range R,
          (if squareRootEndpoint R / n = z then (((μ n : ℤ) : ℂ)) else 0) *
            F z := by rw [Finset.sum_comm]
    _ =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ n : ℤ) : ℂ)) * F (squareRootEndpoint R / n) := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnR : R ≤ n := (Finset.mem_Icc.mp hn).1
          have hylt : squareRootEndpoint R / n < R :=
            squareRootEndpoint_div_lt_root_of_root_le hR hnR
          have hymem : squareRootEndpoint R / n ∈ Finset.range R :=
            Finset.mem_range.mpr hylt
          calc
            (∑ z ∈ Finset.range R,
              (if squareRootEndpoint R / n = z then (((μ n : ℤ) : ℂ)) else 0) *
                F z) =
              ∑ z ∈ Finset.range R,
                if squareRootEndpoint R / n = z then
                  (((μ n : ℤ) : ℂ)) * F z
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro z _hz
                  by_cases heq : squareRootEndpoint R / n = z <;> simp [heq]
            _ = (((μ n : ℤ) : ℂ)) * F (squareRootEndpoint R / n) := by
              simp [hymem]

/-- The fibre masses `t_R(z)` sum to the complementary Mertens tail. -/
theorem sum_squareRootReplacementTailMoebiusCoefficient_eq_mertens_sub_pred
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z) =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        RHLean.Analysis.mertensSummatory (R - 1) := by
  have hgroup :=
    sum_squareRootReplacementTailMoebiusCoefficient_mul R hR (fun _ => 1)
  have htail :
      (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z) =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ n : ℤ) : ℂ)) := by simpa using hgroup
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hset :
      Finset.Icc 1 (squareRootEndpoint R) =
        Finset.Icc 1 (R - 1) ∪
          Finset.Icc R (squareRootEndpoint R) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj :
      Disjoint (Finset.Icc 1 (R - 1))
        (Finset.Icc R (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo hnhi
    omega
  have hsplit :
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
        RHLean.Analysis.mertensSummatory (R - 1) +
          ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
            (((μ n : ℤ) : ℂ)) := by
    calc
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
        ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          (((μ n : ℤ) : ℂ)) :=
        RHLean.Analysis.mertensSummatory_eq_sum_Icc _
      _ = (∑ n ∈ Finset.Icc 1 (R - 1), (((μ n : ℤ) : ℂ))) +
          ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
            (((μ n : ℤ) : ℂ)) := by rw [hset, Finset.sum_union hdisj]
      _ = RHLean.Analysis.mertensSummatory (R - 1) +
          ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
            (((μ n : ℤ) : ℂ)) := by
        rw [← RHLean.Analysis.mertensSummatory_eq_sum_Icc (R - 1)]
  rw [htail]
  rw [hsplit]
  ring

/-- Shifted unit renewal on one lower scale. -/
private theorem sum_shiftedMertens_div_eq_one_sub
    {z : ℕ} (hz : 1 ≤ z) :
    (∑ k ∈ Finset.Icc 1 z,
        (RHLean.Analysis.mertensSummatory (z / k) - 1)) =
      1 - (z : ℂ) := by
  calc
    (∑ k ∈ Finset.Icc 1 z,
        (RHLean.Analysis.mertensSummatory (z / k) - 1)) =
      (∑ k ∈ Finset.Icc 1 z,
        RHLean.Analysis.mertensSummatory (z / k)) -
        ∑ k ∈ Finset.Icc 1 z, (1 : ℂ) := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - (z : ℂ) := by
      rw [RHLean.Analysis.sum_mertensSummatory_div_eq_one hz]
      simp [Nat.card_Icc]

/-- On every `z < R`, the quotient kernel sends the shifted lower-scale Mertens
state to `1-z`.  This is the existing unit Möbius renewal identity written in
the common reciprocal-fibre coordinates. -/
theorem sum_quotientKernel_mul_shiftedMertens_eq_one_sub
    (R z : ℕ) (hz : 1 ≤ z) (hzR : z < R) :
    (∑ y ∈ Finset.range R,
        squareRootReplacementQuotientKernel z y *
          (RHLean.Analysis.mertensSummatory y - 1)) =
      1 - (z : ℂ) := by
  classical
  unfold squareRootReplacementQuotientKernel
  calc
    (∑ y ∈ Finset.range R,
        (∑ k ∈ Finset.Icc 1 z, if z / k = y then 1 else 0) *
          (RHLean.Analysis.mertensSummatory y - 1)) =
      ∑ y ∈ Finset.range R,
        ∑ k ∈ Finset.Icc 1 z,
          (if z / k = y then 1 else 0) *
            (RHLean.Analysis.mertensSummatory y - 1) := by
              apply Finset.sum_congr rfl
              intro y _hy
              rw [Finset.sum_mul]
    _ =
      ∑ k ∈ Finset.Icc 1 z,
        ∑ y ∈ Finset.range R,
          (if z / k = y then 1 else 0) *
            (RHLean.Analysis.mertensSummatory y - 1) := by
              rw [Finset.sum_comm]
    _ =
      ∑ k ∈ Finset.Icc 1 z,
        (RHLean.Analysis.mertensSummatory (z / k) - 1) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkI := Finset.mem_Icc.mp hk
          have hq1 : 1 ≤ z / k :=
            (Nat.one_le_div_iff hkI.1).2 hkI.2
          have hqle : z / k ≤ z := Nat.div_le_self z k
          have hqR : z / k < R := hqle.trans_lt hzR
          have hqmem : z / k ∈ Finset.range R := Finset.mem_range.mpr hqR
          calc
            (∑ y ∈ Finset.range R,
              (if z / k = y then 1 else 0) *
                (RHLean.Analysis.mertensSummatory y - 1)) =
              ∑ y ∈ Finset.range R,
                if z / k = y then
                  RHLean.Analysis.mertensSummatory y - 1
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro y _hy
                  by_cases heq : z / k = y <;> simp [heq]
            _ = RHLean.Analysis.mertensSummatory (z / k) - 1 := by
              simp [hqmem]
    _ = 1 - (z : ℂ) := sum_shiftedMertens_div_eq_one_sub hz

/-- **Coefficientwise fibre dictionary.**  The `C_R`-weighted reciprocal fibre
is the negative lower-triangular hyperbola transform of the complementary
Möbius fibres.  This is the exact `C_R ↔ μ` dictionary requested by the
zero-mode analysis. -/
theorem squareRootReplacementTailCoefficient_eq_neg_tailMoebiusKernel
    (R y : ℕ) (hR : 2 ≤ R) :
    squareRootReplacementTailCoefficient R y =
      -(∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z *
          squareRootReplacementQuotientKernel z y) := by
  let f : ℕ → ℂ := fun u => if u = y then 1 else 0
  have htype :=
    sum_replacementKernel_mul_floorWeight_eq_neg_tailTypeII R hR f
  have hgroup :=
    sum_squareRootReplacementTailMoebiusCoefficient_mul R hR
      (fun z => squareRootReplacementQuotientKernel z y)
  have hleft :
      squareRootReplacementTailCoefficient R y =
        ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          squareRootReplacementKernel R n *
            f (squareRootEndpoint R / n) := by
    unfold squareRootReplacementTailCoefficient f
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases heq : squareRootEndpoint R / n = y <;> simp [heq]
  calc
    squareRootReplacementTailCoefficient R y =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n) := hleft
    _ = -(∑ d ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ d : ℤ) : ℂ)) *
          squareRootReplacementQuotientKernel
            (squareRootEndpoint R / d) y) := by
      simpa [f, squareRootReplacementQuotientKernel] using htype
    _ = -(∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z *
          squareRootReplacementQuotientKernel z y) := by
      rw [hgroup]

/-- The shifted `C_R`-weighted fibre sum is exactly the first hyperbola moment
of the complementary Möbius fibres minus their mass.  This is where the two
large terms begin to recombine; no absolute value appears. -/
theorem sum_replacementTailCoefficient_mul_shiftedMertens_eq_tailFirstMoment
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ Finset.range R,
        squareRootReplacementTailCoefficient R y *
          (RHLean.Analysis.mertensSummatory y - 1)) =
      ∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z * ((z : ℂ) - 1) := by
  let f : ℕ → ℂ := fun y => RHLean.Analysis.mertensSummatory y - 1
  have hfibre := sum_replacementTailCoefficient_mul R hR f
  have htype :=
    sum_replacementKernel_mul_floorWeight_eq_neg_tailTypeII R hR f
  have hgroup :=
    sum_squareRootReplacementTailMoebiusCoefficient_mul R hR
      (fun z => (z : ℂ) - 1)
  calc
    (∑ y ∈ Finset.range R,
        squareRootReplacementTailCoefficient R y *
          (RHLean.Analysis.mertensSummatory y - 1)) =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          f (squareRootEndpoint R / n) := by simpa [f] using hfibre
    _ = -(∑ d ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ d : ℤ) : ℂ)) *
          ∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
            f (squareRootEndpoint R / d / k)) := htype
    _ = -(∑ d ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ d : ℤ) : ℂ)) *
          (1 - ((squareRootEndpoint R / d : ℕ) : ℂ))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hdI := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      have hz1 : 1 ≤ squareRootEndpoint R / d :=
        (Nat.one_le_div_iff hdpos).2 hdI.2
      rw [show (∑ k ∈ Finset.Icc 1 (squareRootEndpoint R / d),
          f (squareRootEndpoint R / d / k)) =
        1 - ((squareRootEndpoint R / d : ℕ) : ℂ) by
          simpa [f] using sum_shiftedMertens_div_eq_one_sub hz1]
    _ = ∑ d ∈ Finset.Icc R (squareRootEndpoint R),
        (((μ d : ℤ) : ℂ)) *
          (((squareRootEndpoint R / d : ℕ) : ℂ) - 1) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ = ∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z * ((z : ℂ) - 1) := by
      rw [hgroup]

/-- The shifted final replacement row is the predecessor shifted Mertens value
minus the shifted physical tail. -/
theorem sum_replacementCoefficient_mul_shiftedMertens_eq_pred_sub_tail
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          (RHLean.Analysis.mertensSummatory y - 1)) =
      (RHLean.Analysis.mertensSummatory (R - 1) - 1) -
        ∑ y ∈ Finset.range R,
          squareRootReplacementTailCoefficient R y *
            (RHLean.Analysis.mertensSummatory y - 1) := by
  have hpredlt : R - 1 < R := by omega
  have hpredmem : R - 1 ∈ Finset.range R := Finset.mem_range.mpr hpredlt
  unfold squareRootReplacementCoefficient
  calc
    (∑ y ∈ Finset.range R,
        ((if y = R - 1 then 1 else 0) -
          squareRootReplacementTailCoefficient R y) *
          (RHLean.Analysis.mertensSummatory y - 1)) =
      (∑ y ∈ Finset.range R,
        (if y = R - 1 then 1 else 0) *
          (RHLean.Analysis.mertensSummatory y - 1)) -
        ∑ y ∈ Finset.range R,
          squareRootReplacementTailCoefficient R y *
            (RHLean.Analysis.mertensSummatory y - 1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ = (RHLean.Analysis.mertensSummatory (R - 1) - 1) -
        ∑ y ∈ Finset.range R,
          squareRootReplacementTailCoefficient R y *
            (RHLean.Analysis.mertensSummatory y - 1) := by
      simp [hpredmem]

/-- **Termwise zero-mode cancellation after the fibre dictionary.**  The shifted
replacement row and the complementary Möbius first moment are both large, but
once the Type-II transform is inserted their `z`-terms cancel as
`-(z-1)t_R(z) + z t_R(z) = t_R(z)`.  Only the ordinary lower-triangular Möbius
tail remains. -/
theorem shiftedReplacementRow_add_tailMoebiusMoment_eq_endpoint
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          (RHLean.Analysis.mertensSummatory y - 1)) +
      (∑ z ∈ Finset.range R,
        (z : ℂ) * squareRootReplacementTailMoebiusCoefficient R z) =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 := by
  have hrow :=
    sum_replacementCoefficient_mul_shiftedMertens_eq_pred_sub_tail R hR
  have htail :=
    sum_replacementTailCoefficient_mul_shiftedMertens_eq_tailFirstMoment R hR
  have hmass :=
    sum_squareRootReplacementTailMoebiusCoefficient_eq_mertens_sub_pred R hR
  have hcombine :
      -(∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z * ((z : ℂ) - 1)) +
        (∑ z ∈ Finset.range R,
          (z : ℂ) * squareRootReplacementTailMoebiusCoefficient R z) =
        ∑ z ∈ Finset.range R,
          squareRootReplacementTailMoebiusCoefficient R z := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _hz
    ring
  rw [hrow, htail]
  calc
    (RHLean.Analysis.mertensSummatory (R - 1) - 1) -
        (∑ z ∈ Finset.range R,
          squareRootReplacementTailMoebiusCoefficient R z * ((z : ℂ) - 1)) +
      (∑ z ∈ Finset.range R,
        (z : ℂ) * squareRootReplacementTailMoebiusCoefficient R z) =
      (RHLean.Analysis.mertensSummatory (R - 1) - 1) +
        ∑ z ∈ Finset.range R,
          squareRootReplacementTailMoebiusCoefficient R z := by
      rw [← hcombine]
      ring
    _ = RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 := by
      rw [hmass]
      ring

/-- Dual form of the constant mode: `S_R` is the negative first moment of the
complementary Möbius reciprocal fibres.  This is a coordinate identity only;
it does not assert that either large term is small. -/
theorem squareRootReplacementBoundaryMass_eq_neg_tailMoebiusMoment
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootReplacementBoundaryMass R =
      -(∑ z ∈ Finset.range R,
        (z : ℂ) * squareRootReplacementTailMoebiusCoefficient R z) := by
  have hsplit :=
    mertensEndpoint_sub_one_eq_shiftedReplacementRow_sub_boundaryMass R hR
  have hjoint :=
    shiftedReplacementRow_add_tailMoebiusMoment_eq_endpoint R hR
  let P : ℂ := ∑ y ∈ Finset.range R,
    squareRootReplacementCoefficient R y *
      (RHLean.Analysis.mertensSummatory y - 1)
  let Q : ℂ := ∑ z ∈ Finset.range R,
    (z : ℂ) * squareRootReplacementTailMoebiusCoefficient R z
  have heq : P - squareRootReplacementBoundaryMass R = P + Q := by
    calc
      P - squareRootReplacementBoundaryMass R =
        RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 := by
          simpa [P] using hsplit.symm
      _ = P + Q := by simpa [P, Q] using hjoint.symm
  calc
    squareRootReplacementBoundaryMass R =
      P - (P - squareRootReplacementBoundaryMass R) := by ring
    _ = P - (P + Q) := by rw [heq]
    _ = -Q := by ring
    _ = -(∑ z ∈ Finset.range R,
        (z : ℂ) * squareRootReplacementTailMoebiusCoefficient R z) := by rfl

end RHLean.Proof
