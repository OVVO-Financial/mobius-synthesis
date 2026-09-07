import Mathlib
import RHLean.Analysis.PrimeWheelRunOthelloBoundary

open scoped BigOperators

/-!
# Square-run top-escape classification after global fresh-prime ownership

`PrimeWheelRunOthelloBoundary` assigns every nonzero physical covariance pair
in a square run to its unique first differing Euler prime.  This file records
the geometric consequence that matters for the attempted fresh-prime cube
closure.

On a subdoubling run `[a^2,(b+1)^2)`, if a prime `p` divides a physical endpoint
`n`, then stripping `p` sends that endpoint strictly below the run anchor
`a^2`.  Hence a first-owner pair in such a run is necessarily a boundary cube:
its fresh parent is not another physical site of the run.  In particular, the
same-prime negative covariance leaf `(m,p*m)` is empty inside a subdoubling
window.

Therefore the natural fixed-prime descended leaf contributes exactly zero on
the very windows where the frozen-prefix mechanism applies, and its top-escape
remainder is literally the whole square-run covariance.  The final theorem
makes the quantitative consequence explicit: an RH-scale bound on this natural
top escape is equivalent to `MertensEnergyBoundedStatement`.  Thus ownership
and four-corner cancellation close the combinatorial classification, but do not
by themselves reduce the remaining quantitative theorem below RH strength.

No analytic estimate or RH hypothesis is asserted here.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- On a subdoubling physical run, stripping any prime divisor from a visited
endpoint sends the resulting fresh parent strictly below the run anchor. -/
theorem squarefreePrimeFamilyParent_lt_runAnchor_of_dvd
    {p a b n : ℕ} (hp : p.Prime)
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hpn : p ∣ n)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    squarefreePrimeFamilyParent p n < a ^ 2 := by
  have hnTop : n < (b + 1) ^ 2 := (Finset.mem_Ico.mp hn).2
  have hparentEq : p * squarefreePrimeFamilyParent p n = n :=
    prime_mul_squarefreePrimeFamilyParent_eq hpn
  by_contra hnot
  have hanchor : a ^ 2 ≤ squarefreePrimeFamilyParent p n :=
    Nat.le_of_not_gt hnot
  have htwo : 2 * a ^ 2 ≤ p * squarefreePrimeFamilyParent p n :=
    Nat.mul_le_mul hp.two_le hanchor
  rw [hparentEq] at htwo
  omega

/-- Consequently the unique first-owner realization of any nonzero pair in a
subdoubling run crosses the lower anchor in the coordinate carrying its owner.
The owner cube is a boundary cube, not a complete cube internal to the run. -/
theorem squareRunFreshPrimeOwner_parent_below_anchor
    {a b m n : ℕ} (_hab : a ≤ b)
    (hm : m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hmn : m < n)
    (hm0 : realMoebiusStep m ≠ 0)
    (hn0 : realMoebiusStep n ≠ 0)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    let p := squarefreePairFreshPrimeOwner m n
    squarefreePrimeFamilyParent p m < a ^ 2 ∨
      squarefreePrimeFamilyParent p n < a ^ 2 := by
  let p := squarefreePairFreshPrimeOwner m n
  have hmsq := squarefree_of_realMoebiusStep_ne_zero hm0
  have hnsq := squarefree_of_realMoebiusStep_ne_zero hn0
  have hmpos : 0 < m := by
    by_contra hz
    have : m = 0 := by omega
    subst m
    simp [realMoebiusStep] at hm0
  have hnpos : 0 < n := lt_trans hmpos hmn
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hmsq hnsq (by omega)
  rcases squarefreePairFreshPrimeOwner_dvd_xor
      hmsq hnsq (by omega) hmpos hnpos with h | h
  · left
    exact squarefreePrimeFamilyParent_lt_runAnchor_of_dvd hp hm h.1 hsub
  · right
    exact squarefreePrimeFamilyParent_lt_runAnchor_of_dvd hp hn h.1 hsub

/-- Same-`p` family covariance that remains wholly inside the physical run.
Each contributing pair is `(m,p*m)` with `p` fresh to `m`, hence has signed
weight `-mu(m)^2`. -/
def squareRunPrimeLeafCovariance (p a b : ℕ) : ℝ :=
  -∑ m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
    if 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2 then
      realMoebiusStep m ^ 2
    else 0

/-- The same-prime family leaf is sign-definite and can only help the upper
covariance bound. -/
theorem squareRunPrimeLeafCovariance_nonpos (p a b : ℕ) :
    squareRunPrimeLeafCovariance p a b ≤ 0 := by
  unfold squareRunPrimeLeafCovariance
  have hsum :
      0 ≤ ∑ m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
        if 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2 then
          realMoebiusStep m ^ 2
        else 0 := by
    apply Finset.sum_nonneg
    intro m hm
    split_ifs <;> positivity
  linarith

/-- The fixed-prime leaf is an admissible nonpositive descended term. -/
theorem squareRunPrimeLeafDescendedNonpositive (p : ℕ) :
    SquareRunDescendedNonpositive (squareRunPrimeLeafCovariance p) := by
  intro a b _hab
  exact squareRunPrimeLeafCovariance_nonpos p a b

/-- The magnitude of the negative same-prime leaf is at most the exact physical
window length. -/
theorem neg_squareRunPrimeLeafCovariance_le_windowLength
    (p a b : ℕ) (_hab : a ≤ b) :
    -squareRunPrimeLeafCovariance p a b ≤
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) := by
  unfold squareRunPrimeLeafCovariance
  rw [neg_neg]
  calc
    (∑ m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
        if 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2 then
          realMoebiusStep m ^ 2
        else 0) ≤
        ∑ _m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases h : 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2
      · simp [h, realMoebiusStep_sq_le_one m]
      · simp [h]
    _ = ((Finset.Ico (a ^ 2) ((b + 1) ^ 2)).card : ℝ) := by simp
    _ = ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) := by
      rw [Nat.card_Ico]

/-- On a subdoubling run no prime family can have both `m` and `p*m` inside the
window.  The nonpositive same-family descended leaf is therefore empty. -/
theorem squareRunPrimeLeafCovariance_eq_zero_of_subdoubling
    {p a b : ℕ} (hp : p.Prime)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    squareRunPrimeLeafCovariance p a b = 0 := by
  unfold squareRunPrimeLeafCovariance
  have hzero :
      (∑ m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
        if 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2 then
          realMoebiusStep m ^ 2
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    by_cases h : 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2
    · have hmA : a ^ 2 ≤ m := (Finset.mem_Ico.mp hm).1
      have hmul : 2 * a ^ 2 ≤ p * m := Nat.mul_le_mul hp.two_le hmA
      omega
    · simp [h]
  rw [hzero]
  norm_num

/-- Adjacent square blocks are subdoubling from radius `3` onward. -/
theorem squareRunPrimeLeafCovariance_adjacent_eq_zero
    {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r) :
    squareRunPrimeLeafCovariance p r r = 0 := by
  apply squareRunPrimeLeafCovariance_eq_zero_of_subdoubling hp
  nlinarith

/-- Thus on a subdoubling run the natural top escape is not a smaller residual:
it is literally the entire square-run covariance. -/
theorem squareRunPrimeLeafEscape_eq_covariance_of_subdoubling
    {p a b : ℕ} (hp : p.Prime)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    squareRunEscapeCovariance (squareRunPrimeLeafCovariance p) a b =
      squareRunCovariance a b := by
  unfold squareRunEscapeCovariance
  have hleaf := squareRunPrimeLeafCovariance_eq_zero_of_subdoubling hp hsub
  rw [hleaf]
  ring

/-- The run diagonal is nonnegative on every forward run. -/
theorem squareRunDiagonal_nonneg (a b : ℕ) (hab : a ≤ b) :
    0 ≤ squareRunDiagonal a b := by
  have hsq : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hsplit :=
    Finset.sum_range_add_sum_Ico (fun n => realMoebiusStep n ^ 2) hsq
  have hsum :
      0 ≤ ∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), realMoebiusStep n ^ 2 := by
    exact Finset.sum_nonneg (fun n hn => sq_nonneg (realMoebiusStep n))
  unfold squareRunDiagonal realMertensDiagonal
  linarith

private theorem squareRun_root_rpow_eq_endpoint_rpow
    (r : ℕ) (ε : ℝ) :
    Real.rpow ((r + 1 : ℕ) : ℝ) (2 + 2 * ε) =
      Real.rpow ((((r + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
  have hx : (0 : ℝ) ≤ (((r + 1 : ℕ) : ℝ)) := by positivity
  have htwo :
      Real.rpow (((r + 1 : ℕ) : ℝ)) (2 : ℝ) =
        (((r + 1 : ℕ) : ℝ)) ^ (2 : ℕ) :=
    Real.rpow_natCast (((r + 1 : ℕ) : ℝ)) 2
  calc
    Real.rpow (((r + 1 : ℕ) : ℝ)) (2 + 2 * ε) =
        Real.rpow (((r + 1 : ℕ) : ℝ)) ((2 : ℝ) * (1 + ε)) := by
          congr 1
          ring
    _ = Real.rpow (Real.rpow (((r + 1 : ℕ) : ℝ)) (2 : ℝ)) (1 + ε) :=
      Real.rpow_mul hx (2 : ℝ) (1 + ε)
    _ = Real.rpow ((((r + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
      rw [htwo]
      norm_cast

private theorem squareRun_endpoint_le_rpow
    {ε : ℝ} (hε : 0 < ε) (b : ℕ) :
    ((((b + 1) ^ 2 : ℕ) : ℝ)) ≤
      Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
  have hbasePos : 0 < (b + 1) ^ 2 := by positivity
  have hbaseNat : 1 ≤ (b + 1) ^ 2 := by omega
  have hbase : (1 : ℝ) ≤ ((((b + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hbaseNat
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  simpa using h

/-- Mertens energy control bounds the natural prime-leaf escape.  The leaf costs
only one linear window term, so all critical-scale content remains in the
original run covariance. -/
theorem squareRunPrimeLeafTopEscapeBounded_of_mertensEnergy
    (p : ℕ) (hM : MertensEnergyBoundedStatement) :
    SquareRunTopEscapeCovarianceBoundedStatement
      (squareRunPrimeLeafCovariance p) := by
  intro ε hε
  have hS := squarePrefixEnergyBounded_of_mertensEnergyBounded hM
  rcases hS (2 * ε) (by linarith) with ⟨C, hC, hbound⟩
  refine ⟨2 * C + 1, by linarith, ?_⟩
  intro a b hab
  let P : ℝ := Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)
  have hB : realMertensLength ((b + 1) ^ 2) ^ 2 ≤ C * P := by
    have hnorm :
        ‖squarePrefixMertens b‖ ^ 2 =
          realMertensLength ((b + 1) ^ 2) ^ 2 := by
      unfold squarePrefixMertens
      rw [norm_mertensSummatory_sq_eq_realMertensLength_sq,
        squarePrefixEndpoint_add_one]
    calc
      realMertensLength ((b + 1) ^ 2) ^ 2 =
          ‖squarePrefixMertens b‖ ^ 2 := hnorm.symm
      _ ≤ C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε) := hbound b
      _ = C * P := by
        dsimp [P]
        exact congrArg (fun t : ℝ => C * t)
          (squareRun_root_rpow_eq_endpoint_rpow b ε)
  have hA : realMertensLength (a ^ 2) ^ 2 ≤ C * P := by
    by_cases ha0 : a = 0
    · subst a
      have hP : 0 ≤ P := by
        dsimp [P]
        exact Real.rpow_nonneg (by positivity) _
      simpa [realMertensLength] using mul_nonneg hC hP
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have haB : a ≤ b + 1 := by omega
      have haBase : (((a : ℕ) : ℝ)) ≤ (((b + 1 : ℕ) : ℝ)) := by exact_mod_cast haB
      have hpowRoot :
          Real.rpow (a : ℝ) (2 + 2 * ε) ≤
            Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε) :=
        Real.rpow_le_rpow (by positivity) haBase (by linarith)
      have hpred : a - 1 + 1 = a := Nat.sub_add_cancel ha1
      have hnorm :
          ‖squarePrefixMertens (a - 1)‖ ^ 2 =
            realMertensLength (a ^ 2) ^ 2 := by
        unfold squarePrefixMertens
        rw [norm_mertensSummatory_sq_eq_realMertensLength_sq,
          squarePrefixEndpoint_add_one, hpred]
      have haReal :
          realMertensLength (a ^ 2) ^ 2 ≤
            C * Real.rpow (a : ℝ) (2 + 2 * ε) := by
        calc
          realMertensLength (a ^ 2) ^ 2 =
              ‖squarePrefixMertens (a - 1)‖ ^ 2 := hnorm.symm
          _ ≤ C * Real.rpow ((a - 1 + 1 : ℕ) : ℝ) (2 + 2 * ε) :=
            hbound (a - 1)
          _ = C * Real.rpow (a : ℝ) (2 + 2 * ε) := by rw [hpred]
      have hmono :
          C * Real.rpow (a : ℝ) (2 + 2 * ε) ≤
            C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε) :=
        mul_le_mul_of_nonneg_left hpowRoot hC
      calc
        realMertensLength (a ^ 2) ^ 2 ≤
            C * Real.rpow (a : ℝ) (2 + 2 * ε) := haReal
        _ ≤ C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε) := hmono
        _ = C * P := by
          dsimp [P]
          exact congrArg (fun t : ℝ => C * t)
            (squareRun_root_rpow_eq_endpoint_rpow b ε)
  have hmass : squareRunMass a b ^ 2 ≤ 4 * C * P := by
    unfold squareRunMass
    nlinarith [sq_nonneg
      (realMertensLength ((b + 1) ^ 2) + realMertensLength (a ^ 2))]
  have hdiag := squareRunDiagonal_nonneg a b hab
  have hid := squareRunMass_sq_eq a b
  have hcov : squareRunCovariance a b ≤ 2 * C * P := by
    nlinarith
  have hleaf := neg_squareRunPrimeLeafCovariance_le_windowLength p a b hab
  have hwindow :
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) ≤ ((((b + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_le ((b + 1) ^ 2) (a ^ 2)
  have hlin : ((((b + 1) ^ 2 : ℕ) : ℝ)) ≤ P := by
    dsimp [P]
    exact squareRun_endpoint_le_rpow hε b
  unfold squareRunEscapeCovariance
  calc
    squareRunCovariance a b - squareRunPrimeLeafCovariance p a b ≤
        2 * C * P + (-squareRunPrimeLeafCovariance p a b) := by linarith
    _ ≤ 2 * C * P + ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) :=
      add_le_add_left hleaf _
    _ ≤ 2 * C * P + P := by
      gcongr
      exact hwindow.trans hlin
    _ = (2 * C + 1) * P := by ring

/-- **Exact quantitative classification.**  Once the natural nonpositive
same-prime leaves are charged, an RH-scale square-time top-escape bound is
neither weaker nor stronger than the repository's global Mertens energy
criterion: the two statements are equivalent. -/
theorem squareRunPrimeLeafTopEscapeBounded_iff_mertensEnergy
    (p : ℕ) :
    SquareRunTopEscapeCovarianceBoundedStatement
        (squareRunPrimeLeafCovariance p) ↔
      MertensEnergyBoundedStatement := by
  constructor
  · intro hesc
    exact mertensEnergyBounded_of_topEscapeCovarianceBounded
      (squareRunPrimeLeafDescendedNonpositive p) hesc
  · exact squareRunPrimeLeafTopEscapeBounded_of_mertensEnergy p

end RHLean.Analysis