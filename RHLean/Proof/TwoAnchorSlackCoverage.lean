import Mathlib

/-!
# Anchor coverage of the square-root slack invariant

Fix a constant `K` and write, for a prefix point `x`,

```text
M(x) = sum_{n <= x} mu(n),   Q(x) = sum_{n <= x} |mu(n)|,
S_K(x) = K^2 Q(x) - M(x)^2.
```

The frozen-prefix induction advances one completed factor-base block `(L,U]` at a
time and must preserve `S_K >= 0` throughout the new shell.  Expanding `S_K(x)`
against either frozen endpoint gives an exact identity carrying a **cross term**
that records the signed orientation of the excursion relative to that endpoint:

```text
S_K(x) = S_K(L) + K^2 (Q(x)-Q(L)) - 2 M(L) A(x) - A(x)^2,   A(x) = M(x)-M(L),
S_K(x) = S_K(U) - K^2 (Q(U)-Q(x)) + 2 M(U) B(x) - B(x)^2,   B(x) = M(U)-M(x).
```

Discarding the cross term is legitimate exactly when it is favourable, and the two
directions then become the *same* statement about an anchor value `c` and an
interior value `y = M(x)`:

```text
c covers y        <->  c (y - c) <= 0
obligation at c   :    c^2 + (y - c)^2 <= K^2 Q(x)
```

(For the left endpoint `c = M(L)`; for the right endpoint `c = M(U)`, where
`c (y - c) <= 0` is literally the favourable-right-cross condition `0 <= c (c-y)`
and `(y-c)^2 = B(x)^2`.)  So left and right filling are one lemma applied to two
frozen values, and this module proves:

* `slack_nonneg_of_anchor` — one covering anchor plus its obligation gives the
  slack invariant, with `anchor_excess_eq_cross` showing that the exact price of
  the reduction is the discarded cross term itself;
* `covers_of_nonpos_of_nonneg`, `covers_of_mul_nonpos` — a nonpositive and a
  nonnegative anchor cover **every** real value, so opposite-sign endpoints give
  total coverage;
* `not_covers_iff_of_pos`, `not_covers_iff_of_neg` — the uncovered set of a
  same-sign anchor pair is exactly the excursions beyond both anchors, so anchor
  selection alone is not universal;
* `exists_not_covers` — no single anchor is universal, in either direction;
* `slack_nonneg_of_endpoint_reserve` — an unfavourable cross term does not break
  the backward identity; it is absorbed by a quantitative endpoint reserve.

Everything here is exact finite algebra over `ℝ`.  No estimate for `M` or `Q` is
assumed or proved: the arithmetic obligation appears only as a hypothesis.  The
closing section instantiates the sign geometry at exactly recomputed Mertens data
for the primorial blocks `(19#, 23#]` and `(23#, 29#]`.
-/

noncomputable section

namespace RHLean.Proof

namespace TwoAnchor

/-- Square-root slack at a prefix point with Mertens value `m` and squarefree
count `q`: `S_K = K^2 q - m^2`.  The envelope `|m| <= K sqrt q` holds exactly when
this is nonnegative. -/
def slack (K m q : ℝ) : ℝ := K ^ 2 * q - m ^ 2

theorem slack_nonneg_iff (K m q : ℝ) : 0 ≤ slack K m q ↔ m ^ 2 ≤ K ^ 2 * q := by
  unfold slack
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Exact forward (left-anchor) slack identity. -/
theorem slack_forward (K a y qL qx : ℝ) :
    slack K y qx =
      slack K a qL + K ^ 2 * (qx - qL) - 2 * a * (y - a) - (y - a) ^ 2 := by
  unfold slack
  ring

/-- Exact backward (right-anchor) slack identity. -/
theorem slack_backward (K b y qU qx : ℝ) :
    slack K y qx =
      slack K b qU - K ^ 2 * (qU - qx) + 2 * b * (b - y) - (b - y) ^ 2 := by
  unfold slack
  ring

/-! ## The anchor relation -/

/-- The anchor value `c` **covers** the interior value `y` when the cross term of
the slack identity taken at `c` is favourable.  For a left anchor this is
`M(L)(M(x)-M(L)) <= 0`; for a completed right anchor it is the same inequality,
written there as `0 <= M(U)(M(U)-M(x))`. -/
def Covers (c y : ℝ) : Prop := c * (y - c) ≤ 0

theorem covers_iff_of_pos {c : ℝ} (hc : 0 < c) (y : ℝ) : Covers c y ↔ y ≤ c := by
  unfold Covers
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem covers_iff_of_neg {c : ℝ} (hc : c < 0) (y : ℝ) : Covers c y ↔ c ≤ y := by
  unfold Covers
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- An anchor sitting at a zero of `M` covers everything, and costs nothing. -/
theorem covers_zero (y : ℝ) : Covers 0 y := by
  unfold Covers
  simp

/-- **The price of dropping a favourable cross term is the cross term itself.**
The anchor obligation exceeds the true requirement `y^2 <= K^2 q` by exactly
`-2c(y-c)`, so a covering anchor of small absolute value is nearly lossless and a
large one is expensive. -/
theorem anchor_excess_eq_cross (c y : ℝ) :
    c ^ 2 + (y - c) ^ 2 - y ^ 2 = -2 * c * (y - c) := by
  ring

/-- **Anchor lemma.**  A covering anchor turns the signed shell obligation into a
pure magnitude obligation. -/
theorem slack_nonneg_of_anchor {K c y q : ℝ} (hcov : Covers c y)
    (hobl : c ^ 2 + (y - c) ^ 2 ≤ K ^ 2 * q) :
    0 ≤ slack K y q := by
  unfold Covers at hcov
  unfold slack
  nlinarith [hcov, hobl]

/-- The forward obligation of the issue's notation is the anchor obligation. -/
theorem left_obligation_iff {K a y qL qx : ℝ} :
    (y - a) ^ 2 ≤ K ^ 2 * (qx - qL) + slack K a qL ↔
      a ^ 2 + (y - a) ^ 2 ≤ K ^ 2 * qx := by
  unfold slack
  constructor
  · intro h; linarith
  · intro h; linarith

/-- The backward obligation of the issue's notation is the anchor obligation. -/
theorem right_obligation_iff {K b y qU qx : ℝ} :
    (b - y) ^ 2 + K ^ 2 * (qU - qx) ≤ slack K b qU ↔
      b ^ 2 + (y - b) ^ 2 ≤ K ^ 2 * qx := by
  unfold slack
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Forward filling from a favourable left endpoint. -/
theorem slack_nonneg_of_left_favorable {K a y qL qx : ℝ}
    (hcross : a * (y - a) ≤ 0)
    (hmag : (y - a) ^ 2 ≤ K ^ 2 * (qx - qL) + slack K a qL) :
    0 ≤ slack K y qx := by
  refine slack_nonneg_of_anchor ?_ (left_obligation_iff.mp hmag)
  exact hcross

/-- Backward filling from a favourable right endpoint. -/
theorem slack_nonneg_of_right_favorable {K b y qU qx : ℝ}
    (hcross : 0 ≤ b * (b - y))
    (hmag : (b - y) ^ 2 + K ^ 2 * (qU - qx) ≤ slack K b qU) :
    0 ≤ slack K y qx := by
  refine slack_nonneg_of_anchor ?_ (right_obligation_iff.mp hmag)
  unfold Covers
  nlinarith [hcross]

/-- Backward filling closes with **no** orientation hypothesis whenever the
completed endpoint carries enough quantitative reserve.  An unfavourable right
cross term is therefore not a refutation of backward filling: it is a demand on
`S_K(U)`.  This is the exact sense in which a backward-only programme stays
logically available at the extremizer. -/
theorem slack_nonneg_of_endpoint_reserve {K b y qU qx : ℝ}
    (hreserve :
      K ^ 2 * (qU - qx) + (b - y) ^ 2 - 2 * b * (b - y) ≤ slack K b qU) :
    0 ≤ slack K y qx := by
  rw [slack_backward K b y qU qx]
  linarith

/-- The reserve demanded at `y` by the backward route, made explicit: it is the
exact quantity `S_K(U)` must dominate, cross term included.  Note what this says:
the reserve hypothesis of `slack_nonneg_of_endpoint_reserve` is *equivalent* to its
conclusion, so keeping the cross term is a re-parameterization, not a reduction.
The anchor route is useful precisely because it discards the cross term and turns
a signed statement into a magnitude statement — at the price
`anchor_excess_eq_cross`. -/
theorem endpoint_reserve_eq {K b y qU qx : ℝ} :
    slack K b qU - (K ^ 2 * (qU - qx) + (b - y) ^ 2 - 2 * b * (b - y)) =
      slack K y qx := by
  rw [slack_backward K b y qU qx]
  ring

/-! ## Coverage and its exact failure -/

/-- **Two-anchor coverage.**  A nonpositive and a nonnegative anchor cover every
real value: the first covers `[c, ∞)` and the second `(-∞, c']`. -/
theorem covers_of_nonpos_of_nonneg {c c' : ℝ} (hc : c ≤ 0) (hc' : 0 ≤ c') (y : ℝ) :
    Covers c y ∨ Covers c' y := by
  rcases le_or_gt c y with h | h
  · left
    unfold Covers
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) (sub_nonneg.mpr h)]
  · right
    unfold Covers
    nlinarith [mul_nonneg hc' (show (0 : ℝ) ≤ c' - y by linarith)]

/-- Opposite-sign frozen endpoints give total coverage: every interior value has
at least one favourable anchor. -/
theorem covers_of_mul_nonpos {c c' : ℝ} (h : c * c' ≤ 0) (y : ℝ) :
    Covers c y ∨ Covers c' y := by
  rcases le_or_gt c 0 with hc | hc
  · rcases le_or_gt 0 c' with hc' | hc'
    · exact covers_of_nonpos_of_nonneg hc hc' y
    · refine Or.inl ?_
      have hc0 : 0 ≤ c := by nlinarith
      rw [show c = 0 from le_antisymm hc hc0]
      exact covers_zero y
  · have hc' : c' ≤ 0 := by nlinarith
    exact (covers_of_nonpos_of_nonneg hc' (le_of_lt hc) y).symm

/-- No single anchor is universal: every nonzero anchor value misses a half-line
of interior values.  In particular no theorem of the form "the completed right
endpoint controls every interior point through a favourable cross term" can hold. -/
theorem exists_not_covers {c : ℝ} (hc : c ≠ 0) : ∃ y : ℝ, ¬ Covers c y := by
  rcases lt_trichotomy c 0 with h | h | h
  · refine ⟨c - 1, ?_⟩
    unfold Covers
    push_neg
    nlinarith
  · exact absurd h hc
  · refine ⟨c + 1, ?_⟩
    unfold Covers
    push_neg
    nlinarith

/-- **Sharpness for positive same-sign anchors.**  The uncovered set is exactly the
excursions beyond both anchors. -/
theorem not_covers_iff_of_pos {c c' y : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    (¬ Covers c y ∧ ¬ Covers c' y) ↔ max c c' < y := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [covers_iff_of_pos hc y] at h1
    rw [covers_iff_of_pos hc' y] at h2
    exact max_lt (not_le.mp h1) (not_le.mp h2)
  · intro h
    rw [max_lt_iff] at h
    refine ⟨?_, ?_⟩
    · rw [covers_iff_of_pos hc y]
      exact not_le.mpr h.1
    · rw [covers_iff_of_pos hc' y]
      exact not_le.mpr h.2

/-- **Sharpness for negative same-sign anchors.** -/
theorem not_covers_iff_of_neg {c c' y : ℝ} (hc : c < 0) (hc' : c' < 0) :
    (¬ Covers c y ∧ ¬ Covers c' y) ↔ y < min c c' := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [covers_iff_of_neg hc y] at h1
    rw [covers_iff_of_neg hc' y] at h2
    exact lt_min (not_le.mp h1) (not_le.mp h2)
  · intro h
    rw [lt_min_iff] at h
    refine ⟨?_, ?_⟩
    · rw [covers_iff_of_neg hc y]
      exact not_le.mpr h.1
    · rw [covers_iff_of_neg hc' y]
      exact not_le.mpr h.2

/-- **Multi-anchor coverage.**  Anchors may be taken from any list of frozen
values, not only from the two endpoints of the current block; the covering
condition is unchanged. -/
theorem exists_covers_of_mem {anchors : List ℝ} {c c' : ℝ}
    (hc : c ∈ anchors) (hc' : c' ∈ anchors) (h : c * c' ≤ 0) (y : ℝ) :
    ∃ a ∈ anchors, Covers a y := by
  rcases covers_of_mul_nonpos h y with hy | hy
  · exact ⟨c, hc, hy⟩
  · exact ⟨c', hc', hy⟩

/-! ## Exact primorial-endpoint data

All values below are exact recomputations by a segmented odd-part Möbius sieve:

```text
M(17#) = -25,  M(19#) = 278,  M(23#) = 3516,  M(29#) = -5012,
M(x_*) = -15335 at the all-prefix normalized bottleneck x_* = 1109331447
```

of the block `(23#, 29#]`, with `Q(x_*) = 674392719`. -/

/-- `M(17#)`. -/
def mSeventeen : ℝ := -25

/-- `M(19#)`. -/
def mNineteen : ℝ := 278

/-- `M(23#)`. -/
def mTwentyThree : ℝ := 3516

/-- `M(29#)`. -/
def mTwentyNine : ℝ := -5012

/-- `M(x_*)` at the normalized bottleneck of the block `(23#, 29#]`. -/
def mBottleneck : ℝ := -15335

/-! ### The block `(23#, 29#]` is covered -/

theorem twentyThree_mul_twentyNine_nonpos : mTwentyThree * mTwentyNine ≤ 0 := by
  unfold mTwentyThree mTwentyNine
  norm_num

/-- Opposite-sign endpoints: every interior value of the `29#` block has a
favourable anchor. -/
theorem twentyNine_block_covered (y : ℝ) :
    Covers mTwentyThree y ∨ Covers mTwentyNine y :=
  covers_of_mul_nonpos twentyThree_mul_twentyNine_nonpos y

/-- At the actual extremizer the left endpoint covers. -/
theorem bottleneck_covered_left : Covers mTwentyThree mBottleneck := by
  unfold Covers mTwentyThree mBottleneck
  norm_num

/-- At the actual extremizer the completed right endpoint does **not** cover.  This
is what falsifies right-anchor orientation as the pointwise mechanism: the
normalized bottleneck of the block is exactly a point the completed endpoint fails
to orient. -/
theorem bottleneck_not_covered_right : ¬ Covers mTwentyNine mBottleneck := by
  unfold Covers mTwentyNine mBottleneck
  push_neg
  norm_num

/-- The two exact cross-term values at the bottleneck. -/
theorem bottleneck_cross_terms :
    -2 * mTwentyThree * (mBottleneck - mTwentyThree) = 132560232 ∧
      2 * mTwentyNine * (mTwentyNine - mBottleneck) = -103477752 := by
  unfold mTwentyThree mTwentyNine mBottleneck
  constructor <;> norm_num

/-! ### The preceding block `(19#, 23#]` is a genuine same-sign gap -/

theorem nineteen_mul_twentyThree_pos : 0 < mNineteen * mTwentyThree := by
  unfold mNineteen mTwentyThree
  norm_num

/-- The endpoints of the preceding mature block have the **same** sign, and its
uncovered set is exactly `{y : 3516 < y}`.  An anchor-bracketing property for
consecutive primorial endpoints is therefore false as stated. -/
theorem nineteen_block_uncovered_iff (y : ℝ) :
    (¬ Covers mNineteen y ∧ ¬ Covers mTwentyThree y) ↔ 3516 < y := by
  have hn : (0 : ℝ) < mNineteen := by unfold mNineteen; norm_num
  have ht : (0 : ℝ) < mTwentyThree := by unfold mTwentyThree; norm_num
  have h := not_covers_iff_of_pos hn ht (y := y)
  have hmax : max mNineteen mTwentyThree = 3516 := by
    unfold mNineteen mTwentyThree
    exact max_eq_right (by norm_num)
  rw [hmax] at h
  exact h

/-- The gap is witnessed by a real prefix: the crest of the block `(19#, 23#]` is
`M = 5971`, at `x = 220260118`, and neither endpoint covers it.  The exact scan
finds `7933289` such uncovered prefixes in that block. -/
theorem nineteen_block_crest_uncovered :
    ¬ Covers mNineteen 5971 ∧ ¬ Covers mTwentyThree 5971 :=
  (nineteen_block_uncovered_iff 5971).mpr (by norm_num)

/-- Coverage is restored for the same block by admitting the anchor from one
further completed block: `M(17#) = -25` has the opposite sign to `M(23#) = 3516`.
This is the exact sense in which "anchors from more than one adjacent completed
block" repairs the same-sign case. -/
theorem nineteen_block_covered_by_earlier_anchor (y : ℝ) :
    Covers mSeventeen y ∨ Covers mTwentyThree y := by
  refine covers_of_mul_nonpos ?_ y
  unfold mSeventeen mTwentyThree
  norm_num

end TwoAnchor

end RHLean.Proof
