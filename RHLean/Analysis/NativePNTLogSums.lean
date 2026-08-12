import Mathlib
import RHLean.Analysis.NativePNTSelberg

/-!
# Sharp logarithmic sum estimates for the native PNT route

`RHLean.Analysis.NativePNTSelberg` brackets `log(N!)` between
`N log N - N + 1` and `N log N`.  That pair has error `O(N)`, which is already
the size of the main term targeted by Selberg's symmetry formula, so it cannot
feed the summatory `Lambda_2` estimate.

This module sharpens the upper side to

`log(N!) <= N log N - N + 1 + log N`,

which together with the existing lower bound gives the `O(log N)` two-sided
estimate

`|log(N!) - (N log N - N + 1)| <= log N`.

It also proves the quadratic logarithmic summatory estimate

`sum_{n <= N} log^2 n = N log^2 N - 2 N log N + 2 N + O(log^2 N)`

by an explicit antiderivative and the monotone sum-integral comparison.  No
asymptotic or prime-distribution input is used.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

/-- Multiplicative form of the elementary logarithmic increment lower bound
`log(n+1) - log n >= 1/(n+1)`.  Stating it without division keeps it linear in
the atoms used by the factorial induction. -/
theorem nativeOne_le_succ_mul_log_succ_sub_log
    (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) ≤ ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsuccpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hratio :
      Real.log ((n : ℝ) / ((n : ℝ) + 1)) =
        Real.log (n : ℝ) - Real.log ((n : ℝ) + 1) :=
    Real.log_div (ne_of_gt hnpos) (ne_of_gt hsuccpos)
  have h := Real.log_le_sub_one_of_pos
    (show 0 < ((n : ℝ) / ((n : ℝ) + 1)) by positivity)
  rw [hratio] at h
  have hcancel :
      ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1) - 1) = -1 := by
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_left h hsuccpos.le
  rw [hcancel] at hmul
  linarith

/-- **Sharp upper bound for `log(N!)`.**  This is the companion of
`nativeLogFactorial_lower`, improving `nativeLogFactorial_upper` from an `O(N)`
error term to an `O(log N)` one. -/
theorem nativeLogFactorial_upper_sharp :
    ∀ N : ℕ, 1 ≤ N →
      Real.log ((Nat.factorial N : ℕ) : ℝ) ≤
        (N : ℝ) * Real.log N - (N : ℝ) + 1 + Real.log N := by
  intro N hN
  induction N with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have ih' := ih hn1
        have hnpos : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hn0)
        have hkey := nativeOne_le_succ_mul_log_succ_sub_log n hn1
        have hfac :
            Real.log ((Nat.factorial (n + 1) : ℕ) : ℝ) =
              Real.log ((n + 1 : ℕ) : ℝ) +
                Real.log ((Nat.factorial n : ℕ) : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul,
            Real.log_mul (by positivity)
              (by exact_mod_cast (Nat.factorial_ne_zero n))]
        rw [hfac]
        push_cast
        push_cast at ih'
        nlinarith [ih', hkey]

/-- **`log(N!) = N log N - N + 1 + O(log N)`** with an explicit constant. -/
theorem nativeLogFactorial_sub_main_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |Real.log ((Nat.factorial N : ℕ) : ℝ) -
        ((N : ℝ) * Real.log N - (N : ℝ) + 1)| ≤ Real.log N := by
  have hlow := nativeLogFactorial_lower N hN
  have hup := nativeLogFactorial_upper_sharp N hN
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  rw [abs_le]
  constructor <;> linarith

/-- The same `O(log N)` estimate written for the finite logarithmic mass
`sum_{n <= N} log n`, which is the form consumed by the summatory Selberg
reindexing. -/
theorem nativeLogMass_sub_main_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |nativeLogMass N - ((N : ℝ) * Real.log N - (N : ℝ) + 1)| ≤
      Real.log N := by
  unfold nativeLogMass
  rw [← nativeLogFactorial_eq_sum_log]
  exact nativeLogFactorial_sub_main_abs_le N hN

/-- The sharp logarithmic mass estimate centered at the conventional
`N log N - N` main term. -/
theorem nativeLogMass_sub_stirlingMain_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |nativeLogMass N - ((N : ℝ) * Real.log N - (N : ℝ))| ≤ Real.log N + 1 := by
  have h := nativeLogMass_sub_main_abs_le N hN
  have hrearrange :
      nativeLogMass N - ((N : ℝ) * Real.log N - (N : ℝ)) =
        (nativeLogMass N - ((N : ℝ) * Real.log N - (N : ℝ) + 1)) + 1 := by
    ring
  rw [hrearrange]
  calc
    |(nativeLogMass N - ((N : ℝ) * Real.log N - (N : ℝ) + 1)) + 1| ≤
        |nativeLogMass N - ((N : ℝ) * Real.log N - (N : ℝ) + 1)| + |(1 : ℝ)| :=
      abs_add_le _ _
    _ ≤ Real.log N + 1 := by norm_num; linarith

/-! ## Quadratic logarithmic mass -/

/-- The elementary antiderivative of `log^2 x` on the nonzero reals. -/
def nativeLogSquarePrimitive (x : ℝ) : ℝ :=
  x * (Real.log x) ^ 2 - 2 * (x * Real.log x) + 2 * x

/-- Finite quadratic logarithmic mass through `N`. -/
def nativeLogSquareMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (Real.log (n : ℝ)) ^ 2

/-- Main term for the quadratic logarithmic mass. -/
def nativeLogSquareMain (N : ℕ) : ℝ :=
  (N : ℝ) * (Real.log N) ^ 2 -
    2 * (N : ℝ) * Real.log N + 2 * (N : ℝ)

/-- The derivative of the explicit primitive is exactly `log^2`. -/
theorem nativeLogSquarePrimitive_hasDerivAt
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt nativeLogSquarePrimitive ((Real.log x) ^ 2) x := by
  have hlog := Real.hasDerivAt_log hx
  have hid := hasDerivAt_id x
  have hlogsq := hlog.mul hlog
  have hfirst := hid.mul hlogsq
  have hsecond := hid.mul hlog
  have h := (hfirst.sub (hsecond.const_mul 2)).add (hid.const_mul 2)
  convert h using 1
  · funext y
    simp [nativeLogSquarePrimitive, pow_two]
  · simp [id, pow_two]
    field_simp [hx]
    ring

/-- Exact integral of `log^2` on `[1,N]`. -/
theorem nativeIntegral_logSquare (N : ℕ) (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..(N : ℝ), (Real.log x) ^ 2) =
      nativeLogSquareMain N - 2 := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ),
      HasDerivAt nativeLogSquarePrimitive ((Real.log x) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hNreal] at hx
    apply nativeLogSquarePrimitive_hasDerivAt
    linarith [hx.1]
  have hcont : ContinuousOn (fun x : ℝ => (Real.log x) ^ 2)
      (Set.uIcc (1 : ℝ) (N : ℝ)) := by
    intro x hx
    rw [Set.uIcc_of_le hNreal] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    simpa [pow_two] using
      ((Real.hasDerivAt_log hx0).continuousAt.mul
        (Real.hasDerivAt_log hx0).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => (Real.log x) ^ 2)
      MeasureTheory.volume (1 : ℝ) (N : ℝ) := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  simp [nativeLogSquarePrimitive, nativeLogSquareMain]
  ring

/-- `log^2` is monotone on every interval contained in `[1,+∞)`. -/
theorem nativeLogSquare_monotoneOn (N : ℕ) (_hN : 1 ≤ N) :
    MonotoneOn (fun x : ℝ => (Real.log x) ^ 2)
      (Set.Icc (1 : ℝ) (N : ℝ)) := by
  intro x hx y hy hxy
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx.1
  have hylog : 0 ≤ Real.log y := Real.log_nonneg hy.1
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.log_le_log (by linarith [hx.1]) hxy
  nlinarith

private theorem nativeLogSquare_shift_sum_eq (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2) =
      nativeLogSquareMass N := by
  unfold nativeLogSquareMass
  have himage :
      (Finset.Ico 1 N).image (fun n : ℕ => n + 1) = Finset.Icc 2 N := by
    ext m
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_Icc]
    constructor
    · rintro ⟨n, ⟨hn1, hnN⟩, rfl⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨hm2, hmN⟩
      refine ⟨m - 1, ⟨by omega, by omega⟩, ?_⟩
      omega
  have hdecomp : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · intro hm
      by_cases hm1 : m = 1
      · exact Or.inl hm1
      · exact Or.inr ⟨by omega, hm.2⟩
    · rintro (rfl | hm)
      · exact ⟨le_rfl, hN⟩
      · exact ⟨by omega, hm.2⟩
  calc
    (∑ n ∈ Finset.Ico 1 N, (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2) =
        ∑ m ∈ (Finset.Ico 1 N).image (fun n : ℕ => n + 1),
          (Real.log (m : ℝ)) ^ 2 := by
      symm
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      exact Nat.add_right_cancel hab
    _ = ∑ m ∈ Finset.Icc 2 N, (Real.log (m : ℝ)) ^ 2 := by
      rw [himage]
    _ = ∑ m ∈ Finset.Icc 1 N, (Real.log (m : ℝ)) ^ 2 := by
      rw [hdecomp]
      simp

private theorem nativeLogSquareMass_eq_Ico_add_top (N : ℕ) (hN : 1 ≤ N) :
    nativeLogSquareMass N =
      (∑ n ∈ Finset.Ico 1 N, (Real.log (n : ℝ)) ^ 2) +
        (Real.log (N : ℝ)) ^ 2 := by
  unfold nativeLogSquareMass
  have hdecomp : Finset.Icc 1 N = insert N (Finset.Ico 1 N) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    constructor
    · intro hm
      by_cases hmN : m = N
      · exact Or.inl hmN
      · exact Or.inr ⟨hm.1, by omega⟩
    · rintro (rfl | hm)
      · exact ⟨hN, le_rfl⟩
      · exact ⟨hm.1, by omega⟩
  rw [hdecomp, Finset.sum_insert]
  · ring
  · simp

/-- Explicit two-sided bracket obtained from the monotone integral sandwich. -/
theorem nativeLogSquareMass_bounds (N : ℕ) (hN : 1 ≤ N) :
    nativeLogSquareMain N - 2 ≤ nativeLogSquareMass N ∧
      nativeLogSquareMass N ≤
        nativeLogSquareMain N - 2 + (Real.log (N : ℝ)) ^ 2 := by
  have hmono := nativeLogSquare_monotoneOn N hN
  have hmono' :
      MonotoneOn (fun x : ℝ => (Real.log x) ^ 2)
        (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    simpa using hmono
  have hlowerInt := MonotoneOn.integral_le_sum_Ico
    (f := fun x : ℝ => (Real.log x) ^ 2) hN hmono'
  have hupperInt := MonotoneOn.sum_le_integral_Ico
    (f := fun x : ℝ => (Real.log x) ^ 2) hN hmono'
  have hI := nativeIntegral_logSquare N hN
  have hshift := nativeLogSquare_shift_sum_eq N hN
  have htop := nativeLogSquareMass_eq_Ico_add_top N hN
  constructor
  · calc
      nativeLogSquareMain N - 2 =
          ∫ x in (1 : ℝ)..(N : ℝ), (Real.log x) ^ 2 := hI.symm
      _ ≤ ∑ n ∈ Finset.Ico 1 N,
          (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 := by simpa using hlowerInt
      _ = nativeLogSquareMass N := hshift
  · calc
      nativeLogSquareMass N =
          (∑ n ∈ Finset.Ico 1 N, (Real.log (n : ℝ)) ^ 2) +
            (Real.log (N : ℝ)) ^ 2 := htop
      _ ≤ (∫ x in (1 : ℝ)..(N : ℝ), (Real.log x) ^ 2) +
            (Real.log (N : ℝ)) ^ 2 := by
          simpa using (add_le_add_right hupperInt ((Real.log (N : ℝ)) ^ 2))
      _ = nativeLogSquareMain N - 2 + (Real.log (N : ℝ)) ^ 2 := by rw [hI]

/-- **Quadratic logarithmic summatory estimate.**

`sum_{n <= N} log^2 n = N log^2 N - 2 N log N + 2 N + O(log^2 N)`

with a completely explicit error. -/
theorem nativeLogSquareMass_sub_main_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |nativeLogSquareMass N - nativeLogSquareMain N| ≤
      (Real.log (N : ℝ)) ^ 2 + 2 := by
  have hb := nativeLogSquareMass_bounds N hN
  have hsq : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

end RHLean.Analysis
