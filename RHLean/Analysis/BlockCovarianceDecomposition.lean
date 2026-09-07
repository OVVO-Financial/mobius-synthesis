import Mathlib
import RHLean.Analysis.DeterministicTGreenKuboComparison

open scoped BigOperators

/-!
# Signed block covariance: partition the pair sum instead of counting atoms

The Green--Kubo square expansion is an identity about *pairs*.  Partitioning the
index range into disjoint physical blocks partitions those pairs into two kinds:
pairs inside one block, and pairs straddling two blocks.  Nothing is estimated
and nothing changes carrier, so a block decomposition of the global Möbius
covariance is a genuine refinement of the same object rather than a second
object needing a bridge.

## The algebra

For a signed block sequence `B : N -> R` write

```text
S K = sum_{j<K} B j            (total signed mass)
E K = sum_{j<K} (B j)^2        (block energy)
X K = sum_{j<K} B j * S j      (cross-block covariance)
```

Then `S K ^ 2 = E K + 2 * X K`, so

```text
2 * X K = S K ^ 2 - E K.
```

That single rearrangement is the point of this file.  **Cross-block coherence is
not a free adversary**: it is pinned by the total mass and the block energy.  A
route that first replaces the signed blocks by magnitudes, `|S| <= sum |B j|`,
and only then squares, is allowing every block to align independently — an
option the identity above forbids.  `signedBlockPrefix_abs_sq_sub_sq` measures exactly
what that step discards: twice the cross-covariance defect, and nothing else.

The two-block prototype is the first Euler face.  With `a` seats of weight `+1`
and `b` seats of weight `-1`,

```text
C = a(a-1)/2 + b(b-1)/2 - a b = ((a - b)^2 - (a + b)) / 2,
```

which is linear, or negative, when `a ~ b`, while bounding the two blocks
independently returns `~ (a+b)^2 / 2`.  The gap is exactly `2ab`, the cross term.

## The square blocks

Instantiating at the literal square blocks `[j^2, (j+1)^2)` gives

```text
M(R^2)^2 = block energy + 2 * cross-block covariance
```

and, telescoping the prefix objects,

```text
C_global(R^2) = sum_{j<R} C_j  +  cross-block covariance,
```

with `C_j` the covariance inside block `j`.  This is the partition statement:
the global integer-order covariance *is* the within-block covariance plus the
cross-block covariance, on one carrier, with no domination hypothesis anywhere.

No estimate, asymptotic input or RH hypothesis appears in this file.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## Generic signed-block algebra -/

/-- Total signed mass of the first `K` blocks. -/
def signedBlockPrefix (B : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, B j

/-- Block energy: the diagonal of the block-level square expansion. -/
def signedBlockEnergy (B : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, B j ^ 2

/-- Cross-block covariance: the sum over pairs of *distinct* blocks. -/
def signedBlockCrossCovariance (B : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, B j * signedBlockPrefix B j

@[simp] theorem signedBlockPrefix_zero (B : ℕ → ℝ) : signedBlockPrefix B 0 = 0 := by
  simp [signedBlockPrefix]

@[simp] theorem signedBlockPrefix_succ (B : ℕ → ℝ) (K : ℕ) :
    signedBlockPrefix B (K + 1) = signedBlockPrefix B K + B K := by
  simp [signedBlockPrefix, Finset.sum_range_succ]

@[simp] theorem signedBlockEnergy_zero (B : ℕ → ℝ) : signedBlockEnergy B 0 = 0 := by
  simp [signedBlockEnergy]

@[simp] theorem signedBlockEnergy_succ (B : ℕ → ℝ) (K : ℕ) :
    signedBlockEnergy B (K + 1) = signedBlockEnergy B K + B K ^ 2 := by
  simp [signedBlockEnergy, Finset.sum_range_succ]

@[simp] theorem signedBlockCrossCovariance_zero (B : ℕ → ℝ) :
    signedBlockCrossCovariance B 0 = 0 := by
  simp [signedBlockCrossCovariance]

@[simp] theorem signedBlockCrossCovariance_succ (B : ℕ → ℝ) (K : ℕ) :
    signedBlockCrossCovariance B (K + 1) =
      signedBlockCrossCovariance B K + B K * signedBlockPrefix B K := by
  simp [signedBlockCrossCovariance, Finset.sum_range_succ]

/-- **Block Green--Kubo expansion.**  Exact, for an arbitrary signed block
sequence, with no absolute value anywhere. -/
theorem signedBlockPrefix_sq_eq_energy_add_two_mul_cross (B : ℕ → ℝ) (K : ℕ) :
    signedBlockPrefix B K ^ 2 = signedBlockEnergy B K + 2 * signedBlockCrossCovariance B K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [signedBlockPrefix_succ, signedBlockEnergy_succ, signedBlockCrossCovariance_succ]
      nlinarith [ih]

/-- **Cross-block coherence is pinned, not free.**  It is determined by the
total signed mass and the block energy, so it cannot be treated as an
independent adversary that aligns every deeper block. -/
theorem two_mul_signedBlockCrossCovariance_eq (B : ℕ → ℝ) (K : ℕ) :
    2 * signedBlockCrossCovariance B K = signedBlockPrefix B K ^ 2 - signedBlockEnergy B K := by
  have h := signedBlockPrefix_sq_eq_energy_add_two_mul_cross B K
  linarith

/-- The cross-block object is literally the sum over ordered pairs of distinct
blocks. -/
theorem signedBlockCrossCovariance_eq_doubleSum (B : ℕ → ℝ) (K : ℕ) :
    signedBlockCrossCovariance B K =
      ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j, B i * B j := by
  unfold signedBlockCrossCovariance signedBlockPrefix
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem signedBlockEnergy_abs (B : ℕ → ℝ) (K : ℕ) :
    signedBlockEnergy (fun j => |B j|) K = signedBlockEnergy B K := by
  unfold signedBlockEnergy
  refine Finset.sum_congr rfl ?_
  intro j _hj
  exact sq_abs (B j)

/-- **Exactly what magnitude-first bounding discards.**

Replacing the signed block masses by their magnitudes and only then squaring
changes the answer by precisely twice the cross-covariance defect.  The block
energy is untouched, so every unit of loss is cross-block cancellation that was
thrown away. -/
theorem signedBlockPrefix_abs_sq_sub_sq (B : ℕ → ℝ) (K : ℕ) :
    signedBlockPrefix (fun j => |B j|) K ^ 2 - signedBlockPrefix B K ^ 2 =
      2 * (signedBlockCrossCovariance (fun j => |B j|) K -
        signedBlockCrossCovariance B K) := by
  have habs := signedBlockPrefix_sq_eq_energy_add_two_mul_cross (fun j => |B j|) K
  have hsig := signedBlockPrefix_sq_eq_energy_add_two_mul_cross B K
  have henergy := signedBlockEnergy_abs B K
  rw [henergy] at habs
  linarith

/-! ## The two-block prototype -/

/-- **First-face prototype.**  With `a` unit seats of one sign and `b` of the
other, the exact pair sum is `((a - b)^2 - (a + b)) / 2`: the two within-block
quadratics are cancelled by the negative cross term. -/
theorem twoBlockSignedPairSum (a b : ℝ) :
    a * (a - 1) / 2 + b * (b - 1) / 2 - a * b =
      ((a - b) ^ 2 - (a + b)) / 2 := by
  ring

/-- **The cost of forgetting the opposition.**  Bounding the two blocks
independently and then squaring overstates the pair sum by exactly `2ab`. -/
theorem twoBlockAbsoluteLoss (a b : ℝ) :
    ((a + b) ^ 2 - (a + b)) / 2 - ((a - b) ^ 2 - (a + b)) / 2 = 2 * (a * b) := by
  ring

/-! ## Interval form, by prefix differences only -/

/-- Covariance carried strictly inside the window `[a, b)`, defined from the
prefix objects alone. -/
def signedBlockInnerCovariance (B : ℕ → ℝ) (a b : ℕ) : ℝ :=
  signedBlockCrossCovariance B b - signedBlockCrossCovariance B a -
    signedBlockPrefix B a * (signedBlockPrefix B b - signedBlockPrefix B a)

/-- **Green--Kubo on a window.**  No interval induction is needed: the identity
for a window is the difference of the two prefix identities. -/
theorem signedBlockPrefix_sub_sq_eq_energy_sub_add_two_mul_inner
    (B : ℕ → ℝ) (a b : ℕ) :
    (signedBlockPrefix B b - signedBlockPrefix B a) ^ 2 =
      (signedBlockEnergy B b - signedBlockEnergy B a) + 2 * signedBlockInnerCovariance B a b := by
  have hb := signedBlockPrefix_sq_eq_energy_add_two_mul_cross B b
  have ha := signedBlockPrefix_sq_eq_energy_add_two_mul_cross B a
  unfold signedBlockInnerCovariance
  linear_combination hb - ha

/-! ## The literal square blocks -/

/-- Signed Möbius mass of the physical square block `[j^2, (j+1)^2)`. -/
def realSquareBlockMass (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2), realMoebiusStep n

/-- The square blocks partition the prefix: their signed masses telescope to the
Mertens value at the square endpoint. -/
theorem signedBlockPrefix_realSquareBlockMass (R : ℕ) :
    signedBlockPrefix realSquareBlockMass R = realMertensLength (R ^ 2) := by
  induction R with
  | zero => norm_num [signedBlockPrefix, realMertensLength]
  | succ R ih =>
      rw [signedBlockPrefix_succ, ih]
      have hle : R ^ 2 ≤ (R + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hsplit := Finset.sum_range_add_sum_Ico realMoebiusStep hle
      unfold realMertensLength realSquareBlockMass
      exact hsplit

/-- **Square-block Green--Kubo.**  The Mertens energy at a square endpoint is
the block energy plus twice the cross-block covariance.  No absolute value is
taken and no block is bounded on its own. -/
theorem realMertensLength_sq_eq_blockEnergy_add_two_mul_cross (R : ℕ) :
    realMertensLength (R ^ 2) ^ 2 =
      signedBlockEnergy realSquareBlockMass R +
        2 * signedBlockCrossCovariance realSquareBlockMass R := by
  rw [← signedBlockPrefix_realSquareBlockMass R]
  exact signedBlockPrefix_sq_eq_energy_add_two_mul_cross _ _

/-- Covariance carried strictly inside the square block `j`. -/
def realSquareBlockInnerCovariance (j : ℕ) : ℝ :=
  realMertensPositiveLagPairSum ((j + 1) ^ 2) -
    realMertensPositiveLagPairSum (j ^ 2) -
    realMertensLength (j ^ 2) * realSquareBlockMass j

/-- **The partition identity: no bridge is needed.**

The global integer-order Möbius covariance at a square endpoint is exactly the
sum of the within-block covariances plus the cross-block covariance of the
signed block masses.  Both sides are the same pair sum on the same carrier,
split by whether a pair lies inside one square block or straddles two. -/
theorem realMertensPositiveLagPairSum_eq_inner_add_cross (R : ℕ) :
    realMertensPositiveLagPairSum (R ^ 2) =
      (∑ j ∈ Finset.range R, realSquareBlockInnerCovariance j) +
        signedBlockCrossCovariance realSquareBlockMass R := by
  induction R with
  | zero => norm_num
  | succ R ih =>
      have hR : realSquareBlockInnerCovariance R =
          realMertensPositiveLagPairSum ((R + 1) ^ 2) -
            realMertensPositiveLagPairSum (R ^ 2) -
            realMertensLength (R ^ 2) * realSquareBlockMass R := rfl
      rw [Finset.sum_range_succ, signedBlockCrossCovariance_succ,
        signedBlockPrefix_realSquareBlockMass R, hR]
      linarith [ih]

end RHLean.Analysis
