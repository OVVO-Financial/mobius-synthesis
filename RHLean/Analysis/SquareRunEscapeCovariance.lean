import Mathlib
import RHLean.Analysis.BlockCovarianceRefinement
import RHLean.Analysis.SquareWheelSurvivorRun

open scoped BigOperators

/-!
# The run-level seam: escape covariance across square time

`SquareWheelSurvivorRun` proves

```text
SquareRunEnergyBoundedStatement
  <-> PrimeWheelResidualBoundedStatement primorialWheelFamily
  <-> MertensEnergyBoundedStatement,
```

so a uniform bound on every consecutive complete-square run finishes the wheel
and the arbitrary-`x` interpolation as deterministic bookkeeping.  The seam
should therefore be stated at run level, and this file does that.

For a run `I = [a, b]` of complete square blocks, write the window objects

```text
squareRunMass       a b = M((b+1)^2) - M(a^2)
squareRunDiagonal   a b = Q((b+1)^2) - Q(a^2)
squareRunCovariance a b = the exact within-window Möbius pair covariance.
```

`squareRunMass_sq_eq` is the exact window Green--Kubo identity

```text
(sum_{j in I} Delta_j)^2 = Q_I + 2 * C_I,
```

with `Q_I` the singleton squarefree diagonal, hence at most the window length.

Splitting `C_I` into a *descended* part and an *escape* part gives

```text
(sum_{j in I} Delta_j)^2 = Q_I + 2 * descended + 2 * escape.
```

The escape part is defined as the remainder, so the decomposition below is exact for any
proposed descended part.  Two hypotheses then finish the criterion:

* `SquareRunDescendedNonpositive` — the descended contribution does not add
  positive covariance.  This is what complete fresh-prime pair-cube cancellation
  and lower-scale family covariance descent are for: every post-root family is
  covariance-isomorphic to a prefix below `sqrt W`
  (`largePrimeFamilyPairSum_postRoot`), and complete pair cubes cancel.
* `SquareRunTopEscapeCovarianceBoundedStatement` — the escape covariance is of
  RH scale, uniformly over consecutive runs.

`squareRunEnergyBounded_of_topEscapeCovarianceBounded` proves those two give
`SquareRunEnergyBoundedStatement`, and
`mertensEnergyBounded_of_topEscapeCovarianceBounded` chains through the existing
equivalence to the global Mertens energy criterion.

**What the escape part must contain.**  It is *not* enough to control
family interaction separately inside each `Delta_j`.  The window covariance
`C_I` contains the cross-square-block pairs `2 * sum_{a <= i < j <= b} Delta_i
Delta_j` as well, and any descended part that omits them leaves them in the
escape remainder by construction.  That is deliberate: the definition of escape
as a remainder makes the identity exact and makes the omission visible instead
of silent.

**What this file does not do.**  Nesting supplies a chronological coordinate and
proves that controlling the escape on every signed run suffices.  It does not
produce the cancellation.  The negative feedback still has to come from the
fresh-prime arithmetic as square time advances — the four-corner pair identity
of `DeterministicTGreenKuboComparison` cancels every interior order-crossing
shell and leaves the top-escape shell, and the remaining native theorem is that
those escapes cannot maintain a positive supercritical record through square
time.

No estimate, asymptotic input or RH hypothesis is proved here.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Proof

/-! ## Exact window objects for a consecutive square run -/

/-- Signed Möbius mass of the complete-square run `[a, b]`. -/
def squareRunMass (a b : ℕ) : ℝ :=
  realMertensLength ((b + 1) ^ 2) - realMertensLength (a ^ 2)

/-- Squarefree diagonal of the same window. -/
def squareRunDiagonal (a b : ℕ) : ℝ :=
  realMertensDiagonal ((b + 1) ^ 2) - realMertensDiagonal (a ^ 2)

/-- Exact Möbius pair covariance carried strictly inside the window. -/
def squareRunCovariance (a b : ℕ) : ℝ :=
  signedBlockInnerCovariance realMoebiusStep (a ^ 2) ((b + 1) ^ 2)

/-- **Window Green--Kubo for a square run.**  No absolute value is taken and no
block is bounded on its own. -/
theorem squareRunMass_sq_eq (a b : ℕ) :
    squareRunMass a b ^ 2 =
      squareRunDiagonal a b + 2 * squareRunCovariance a b :=
  signedBlockPrefix_sub_sq_eq_energy_sub_add_two_mul_inner realMoebiusStep
    (a ^ 2) ((b + 1) ^ 2)

/-- The run diagonal is at most the window's right endpoint: no conjecture. -/
theorem squareRunDiagonal_le (a b : ℕ) :
    squareRunDiagonal a b ≤ (((b + 1) ^ 2 : ℕ) : ℝ) := by
  have hle := realMertensDiagonal_le ((b + 1) ^ 2)
  have hnn := realMertensDiagonal_nonneg (a ^ 2)
  unfold squareRunDiagonal
  linarith

/-- **Sharp run-diagonal bound.**  Only sites actually traversed by the run can
contribute to its squarefree diagonal, so the diagonal is bounded by the exact
window length `(b+1)^2-a^2`, not by the whole prefix up to `(b+1)^2`. -/
theorem squareRunDiagonal_le_windowLength (a b : ℕ) (hab : a ≤ b) :
    squareRunDiagonal a b ≤
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) := by
  have hsq : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hsplit :=
    Finset.sum_range_add_sum_Ico (fun n => realMoebiusStep n ^ 2) hsq
  have hdiag :
      squareRunDiagonal a b =
        ∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), realMoebiusStep n ^ 2 := by
    unfold squareRunDiagonal realMertensDiagonal
    linarith [hsplit]
  rw [hdiag]
  calc
    (∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), realMoebiusStep n ^ 2) ≤
        ∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), (1 : ℝ) := by
      exact Finset.sum_le_sum (fun n _hn => realMoebiusStep_sq_le_one n)
    _ = ((Finset.Ico (a ^ 2) ((b + 1) ^ 2)).card : ℝ) := by simp
    _ = ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) := by
      rw [Nat.card_Ico]

/-! ## Splitting the window covariance -/

/-- Whatever a descent argument does not account for.  Defined as a remainder,
so the decomposition below is exact for every proposed `descended`. -/
def squareRunEscapeCovariance (descended : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  squareRunCovariance a b - descended a b

/-- **Exact escape decomposition of a signed square run.** -/
theorem squareRunMass_sq_eq_diagonal_add_descended_add_escape
    (descended : ℕ → ℕ → ℝ) (a b : ℕ) :
    squareRunMass a b ^ 2 =
      squareRunDiagonal a b + 2 * descended a b +
        2 * squareRunEscapeCovariance descended a b := by
  have h := squareRunMass_sq_eq a b
  unfold squareRunEscapeCovariance
  linarith

/-- The descended contribution adds no positive covariance.  This is the target
of complete fresh-prime pair-cube cancellation together with lower-scale family
covariance descent. -/
def SquareRunDescendedNonpositive (descended : ℕ → ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, a ≤ b → descended a b ≤ 0

/-- **The final native seam.**  Uniformly over consecutive complete-square runs,
the escape covariance is of RH scale. -/
def SquareRunTopEscapeCovarianceBoundedStatement
    (descended : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, a ≤ b →
        squareRunEscapeCovariance descended a b ≤
          C * Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε)

/-! ## Coherent persistence pressure -/

/-- A run `[a,b]` carries coherent average bias at least `eta` when the absolute
signed run mass is at least `eta` times the number of complete square blocks in
the run.  This is deliberately a run-level condition: no pointwise bound on an
individual square block is imposed. -/
def SquareRunCoherentBiasAtLeast (eta : ℝ) (a b : ℕ) : Prop :=
  eta * (((b + 1 - a : ℕ) : ℝ)) ≤ |squareRunMass a b|

/-- **Unconditional covariance pressure.**  A coherent run of
`ell = b+1-a` square blocks with average signed bias at least `eta` forces the
actual within-window Möbius covariance to be at least

`(eta^2 * ell^2 - ((b+1)^2-a^2)) / 2`.

No Euler-descent hypothesis enters this statement.  It is the exact
Green--Kubo cost of coherent persistence after charging only the sites actually
visited by the run to the diagonal. -/
theorem squareRunCovariance_ge_of_coherentBias
    (a b : ℕ) (hab : a ≤ b)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hcoh : SquareRunCoherentBiasAtLeast eta a b) :
    ((eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 -
        ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ))) / 2 ≤
      squareRunCovariance a b := by
  have hlen : 0 ≤ (((b + 1 - a : ℕ) : ℝ)) := by positivity
  have hleft : 0 ≤ eta * (((b + 1 - a : ℕ) : ℝ)) :=
    mul_nonneg heta hlen
  have habs : 0 ≤ |squareRunMass a b| := abs_nonneg _
  have hmassSq :
      (eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 ≤ squareRunMass a b ^ 2 := by
    calc
      (eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 ≤ |squareRunMass a b| ^ 2 := by
        unfold SquareRunCoherentBiasAtLeast at hcoh
        nlinarith
      _ = squareRunMass a b ^ 2 := sq_abs _
  have hid := squareRunMass_sq_eq a b
  have hdiag := squareRunDiagonal_le_windowLength a b hab
  nlinarith

/-- **Coherent persistence has to escape.**  If the descended Euler interior is
nonpositive, every covariance unit forced by the preceding unconditional
pressure law must be carried by the top-escape remainder. -/
theorem squareRunEscapeCovariance_ge_of_coherentBias
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (a b : ℕ) (hab : a ≤ b)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hcoh : SquareRunCoherentBiasAtLeast eta a b) :
    ((eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 -
        ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ))) / 2 ≤
      squareRunEscapeCovariance descended a b := by
  have hraw := squareRunCovariance_ge_of_coherentBias a b hab eta heta hcoh
  have hdesc := hneg a b hab
  unfold squareRunEscapeCovariance
  linarith

/-- **Persistence-length budget.**  If the top escape covariance on the same
run is at most `B`, then coherent average bias `eta` can persist only while

`(eta * ell)^2 <= ((b+1)^2-a^2) + 2 B`.

The diagonal term is now the exact physical run length.  Large individual
square blocks remain allowed; only sustained signed alignment consumes the
quadratic left-hand side. -/
theorem squareRunCoherentBias_sq_le_of_escape_le
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (a b : ℕ) (hab : a ≤ b)
    (eta : ℝ) (heta : 0 ≤ eta) (B : ℝ)
    (hcoh : SquareRunCoherentBiasAtLeast eta a b)
    (hesc : squareRunEscapeCovariance descended a b ≤ B) :
    (eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 ≤
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) + 2 * B := by
  have hpressure :=
    squareRunEscapeCovariance_ge_of_coherentBias
      hneg a b hab eta heta hcoh
  nlinarith

/-- **Literal non-persistence contrapositive.**  Under a top-escape budget `B`,
a proposed coherent run is impossible as soon as its squared coherent mass
exceeds the exact run-diagonal budget plus twice the escape budget. -/
theorem squareRunCoherentBias_cannot_persist_of_escape_budget
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (a b : ℕ) (hab : a ≤ b)
    (eta : ℝ) (heta : 0 ≤ eta) (B : ℝ)
    (hesc : squareRunEscapeCovariance descended a b ≤ B)
    (hsuper :
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) + 2 * B <
        (eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2) :
    ¬ SquareRunCoherentBiasAtLeast eta a b := by
  intro hcoh
  have hbudget :=
    squareRunCoherentBias_sq_le_of_escape_le
      hneg a b hab eta heta B hcoh hesc
  linarith

/-! ## The run mass is the square-run energy coordinate -/

private theorem natCast_le_rpow_one_add {ε : ℝ} (hε : 0 < ε) (x : ℕ) :
    (((x + 1 : ℕ) : ℝ)) ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ (((x + 1 : ℕ) : ℝ)) := by
    have hone : (1 : ℕ) ≤ x + 1 := Nat.le_add_left 1 x
    exact_mod_cast hone
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  simpa using h

theorem sum_canonicalTotalIncrement_eq_squareRunMass_cast
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) =
      ((squareRunMass a b : ℝ) : ℂ) := by
  have hb : squarePrefixMertens b = ((realMertensLength ((b + 1) ^ 2) : ℝ) : ℂ) := by
    have h1 := realMertensLength_cast_eq_mertensSummatory (squarePrefixEndpoint b)
    rw [squarePrefixEndpoint_add_one b] at h1
    exact h1.symm
  have ha' : squarePrefixMertens (a - 1) =
      ((realMertensLength (a ^ 2) : ℝ) : ℂ) := by
    have h1 :=
      realMertensLength_cast_eq_mertensSummatory (squarePrefixEndpoint (a - 1))
    rw [squarePrefixEndpoint_add_one (a - 1)] at h1
    have hpred : a - 1 + 1 = a := Nat.sub_add_cancel ha
    rw [hpred] at h1
    exact h1.symm
  rw [sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub a b ha hab, hb, ha']
  unfold squareRunMass
  push_cast
  ring

theorem norm_sum_canonicalTotalIncrement_sq_eq_squareRunMass_sq
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    ‖∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j‖ ^ 2 =
      squareRunMass a b ^ 2 := by
  rw [sum_canonicalTotalIncrement_eq_squareRunMass_cast a b ha hab,
    Complex.norm_real, Real.norm_eq_abs]
  exact sq_abs _

/-! ## The reduction -/

/-- **Escape control gives the maximal signed square-run criterion.** -/
theorem squareRunEnergyBounded_of_topEscapeCovarianceBounded
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (hesc : SquareRunTopEscapeCovarianceBoundedStatement descended) :
    SquareRunEnergyBoundedStatement := by
  intro ε hε
  rcases hesc ε hε with ⟨C, hC, hbound⟩
  refine ⟨1 + 2 * C, by linarith, ?_⟩
  intro k a b ha hab _hleft _hright
  rw [norm_sum_canonicalTotalIncrement_sq_eq_squareRunMass_sq a b ha (by omega)]
  have hid := squareRunMass_sq_eq_diagonal_add_descended_add_escape descended a b
  have hd := hneg a b hab
  have he := hbound a b hab
  have hdiagRaw := squareRunDiagonal_le a b
  have hcast : (((b + 1) ^ 2 : ℕ) : ℝ) =
      (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) := by
    rw [squarePrefixEndpoint_add_one b]
  rw [hcast] at hdiagRaw
  have hlin := natCast_le_rpow_one_add hε (squarePrefixEndpoint b)
  linarith

/-- **Hence the global Mertens energy criterion**, through the equivalence
already proved for maximal signed square runs. -/
theorem mertensEnergyBounded_of_topEscapeCovarianceBounded
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (hesc : SquareRunTopEscapeCovarianceBoundedStatement descended) :
    MertensEnergyBoundedStatement :=
  squareRunEnergyBounded_iff_mertensEnergy.mp
    (squareRunEnergyBounded_of_topEscapeCovarianceBounded hneg hesc)

end RHLean.Analysis
