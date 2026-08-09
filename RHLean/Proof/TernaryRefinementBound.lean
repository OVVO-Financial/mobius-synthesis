import Mathlib

/-!
# The one-prime ternary refinement: exactness and a crude uniform bound

Fix a later prime `q` and one inherited parent channel.  Split its underlying sum
into the three `q`-adic classes

```text
X_0 = sum_{q ∤ n} a_n,   X_1 = sum_{q ‖ n} a_n,   X_2 = sum_{q^2 | n} a_n,
```

where `a_n` is the parent weight with the local `q`-factor stripped.  The local
Möbius factor is `(1, -1, 0)` on those classes, so the parent value is `P = X_0 - X_1`.
The refinement produces

```text
C = ((q-1)^2/q^2) (X_0 + X_1 + X_2),
S = ((2q-1)/q^2) X_0 - ((2q-1)(q-1)/q^2) (X_1 + X_2),
W = -(1/q) X_1 + ((q-1)/q) X_2.
```

Substituting `X_0 = P + X_1` writes the children as a `3 × 3` matrix acting on
`(P, X_1, X_2)`.  This module works with the **cleared** children

```text
cNum = q^2 C,      sNum = q^2 S,      wNum = q W,
```

so that every statement is a polynomial identity or inequality with no division.

Two facts are proved:

* `refinement_exact` — `cNum + sNum + q * wNum = q^2 P`.  The refinement is exact:
  the three children sum to the parent value.  This is the content of the local
  Möbius factor `(1, -1, 0)` and is a bare `ring` identity.
* `frobenius_poly` — the Frobenius bound.  The three squared row norms are below
  `6`, `8` and `1` for every `q ≥ 2`, so

  ```text
  |C|^2 + |S|^2 + |W|^2 ≤ 15 (|P|^2 + |X_1|^2 + |X_2|^2),
  ```

  stated here in cleared form.  The constant is deliberately crude: the row-norm
  suprema are exactly `6`, `8`, `1` as `q → ∞`, and at `q = 11` the true total is
  about `10.41`.  Nothing here needs it to be sharp.

The bound is deterministic — no arithmetic input about `a_n` is used, only the
shape of the refinement.  What it does **not** do is control `X_1` and `X_2`: those
are the hidden channels, and reducing them to smaller cutoffs is a separate step.
-/

noncomputable section

namespace RHLean.Proof

namespace TernaryRefinement

/-- `q^2` times the `C`-child, as a linear form in `(P, X_1, X_2)`. -/
def cNum (q P X1 X2 : ℝ) : ℝ := (q - 1) ^ 2 * (P + 2 * X1 + X2)

/-- `q^2` times the `S`-child. -/
def sNum (q P X1 X2 : ℝ) : ℝ := (2 * q - 1) * (P - (q - 2) * X1 - (q - 1) * X2)

/-- `q` times the `W`-child.  It does not involve `P`. -/
def wNum (q X1 X2 : ℝ) : ℝ := -X1 + (q - 1) * X2

/-- **The refinement is exact.**  The three children sum to the parent value
`P = X_0 - X_1`, with no remainder, for every `q`. -/
theorem refinement_exact (q P X1 X2 : ℝ) :
    cNum q P X1 X2 + sNum q P X1 X2 + q * wNum q X1 X2 = q ^ 2 * P := by
  unfold cNum sNum wNum
  ring

/-- Cauchy-Schwarz in three real coordinates, via the Lagrange identity. -/
theorem inner_sq_le (a b c x y z : ℝ) :
    (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (a * z - c * x), sq_nonneg (b * z - c * y)]

/-- **Frobenius bound for one prime refinement.**  In cleared form: dividing by
`q^4` gives `|C|^2 + |S|^2 + |W|^2 ≤ 15 (|P|^2 + |X_1|^2 + |X_2|^2)`. -/
theorem frobenius_poly {q : ℝ} (hq : 2 ≤ q) (P X1 X2 : ℝ) :
    cNum q P X1 X2 ^ 2 + sNum q P X1 X2 ^ 2 + q ^ 2 * wNum q X1 X2 ^ 2 ≤
      15 * q ^ 4 * (P ^ 2 + X1 ^ 2 + X2 ^ 2) := by
  have hV : (0 : ℝ) ≤ P ^ 2 + X1 ^ 2 + X2 ^ 2 := by positivity
  set V := P ^ 2 + X1 ^ 2 + X2 ^ 2 with hVdef
  have h1 : (P + 2 * X1 + X2) ^ 2 ≤ 6 * V := by
    have h := inner_sq_le 1 2 1 P X1 X2
    rw [hVdef]
    nlinarith [h]
  have h2 : (P - (q - 2) * X1 - (q - 1) * X2) ^ 2 ≤ (1 + (q - 2) ^ 2 + (q - 1) ^ 2) * V := by
    have h := inner_sq_le 1 (-(q - 2)) (-(q - 1)) P X1 X2
    rw [hVdef]
    nlinarith [h]
  have h3 : (-X1 + (q - 1) * X2) ^ 2 ≤ (1 + (q - 1) ^ 2) * V := by
    have h := inner_sq_le 0 (-1) (q - 1) P X1 X2
    rw [hVdef]
    nlinarith [h]
  have hc : cNum q P X1 X2 ^ 2 ≤ 6 * q ^ 4 * V := by
    have e : cNum q P X1 X2 ^ 2 = (q - 1) ^ 4 * (P + 2 * X1 + X2) ^ 2 := by
      unfold cNum; ring
    have hp : (0 : ℝ) ≤ (q - 1) ^ 4 := by positivity
    have hb : (q - 1) ^ 4 ≤ q ^ 4 := by nlinarith
    calc cNum q P X1 X2 ^ 2 = (q - 1) ^ 4 * (P + 2 * X1 + X2) ^ 2 := e
      _ ≤ (q - 1) ^ 4 * (6 * V) := mul_le_mul_of_nonneg_left h1 hp
      _ ≤ q ^ 4 * (6 * V) := by
          refine mul_le_mul_of_nonneg_right hb ?_
          linarith
      _ = 6 * q ^ 4 * V := by ring
  have hs : sNum q P X1 X2 ^ 2 ≤ 8 * q ^ 4 * V := by
    have e : sNum q P X1 X2 ^ 2 =
        (2 * q - 1) ^ 2 * (P - (q - 2) * X1 - (q - 1) * X2) ^ 2 := by
      unfold sNum; ring
    have hp : (0 : ℝ) ≤ (2 * q - 1) ^ 2 := sq_nonneg _
    have hb : (2 * q - 1) ^ 2 * (1 + (q - 2) ^ 2 + (q - 1) ^ 2) ≤ 8 * q ^ 4 := by nlinarith
    calc sNum q P X1 X2 ^ 2
        = (2 * q - 1) ^ 2 * (P - (q - 2) * X1 - (q - 1) * X2) ^ 2 := e
      _ ≤ (2 * q - 1) ^ 2 * ((1 + (q - 2) ^ 2 + (q - 1) ^ 2) * V) :=
          mul_le_mul_of_nonneg_left h2 hp
      _ = ((2 * q - 1) ^ 2 * (1 + (q - 2) ^ 2 + (q - 1) ^ 2)) * V := by ring
      _ ≤ (8 * q ^ 4) * V := mul_le_mul_of_nonneg_right hb hV
      _ = 8 * q ^ 4 * V := by ring
  have hw : q ^ 2 * wNum q X1 X2 ^ 2 ≤ q ^ 4 * V := by
    have e : wNum q X1 X2 ^ 2 = (-X1 + (q - 1) * X2) ^ 2 := by unfold wNum; ring
    have hp : (0 : ℝ) ≤ q ^ 2 := sq_nonneg _
    have hb : q ^ 2 * (1 + (q - 1) ^ 2) ≤ q ^ 4 := by nlinarith
    calc q ^ 2 * wNum q X1 X2 ^ 2 = q ^ 2 * (-X1 + (q - 1) * X2) ^ 2 := by rw [e]
      _ ≤ q ^ 2 * ((1 + (q - 1) ^ 2) * V) := mul_le_mul_of_nonneg_left h3 hp
      _ = (q ^ 2 * (1 + (q - 1) ^ 2)) * V := by ring
      _ ≤ q ^ 4 * V := mul_le_mul_of_nonneg_right hb hV
  linarith

/-- The three squared row norms, in cleared form, are below `6`, `8` and `1`.
The certificates are `(q-1)^4 < q^4`, `32q^3 - 50q^2 + 30q - 6 > 0` and `2q - 2 > 0`. -/
theorem row_norm_bounds {q : ℝ} (hq : 2 ≤ q) :
    (q - 1) ^ 4 ≤ q ^ 4 ∧
      (2 * q - 1) ^ 2 * (1 + (q - 2) ^ 2 + (q - 1) ^ 2) ≤ 8 * q ^ 4 ∧
      q ^ 2 * (1 + (q - 1) ^ 2) ≤ q ^ 4 := by
  refine ⟨?_, by nlinarith, by nlinarith⟩
  gcongr <;> linarith

end TernaryRefinement

end RHLean.Proof
