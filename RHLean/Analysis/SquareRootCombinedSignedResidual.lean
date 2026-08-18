import Mathlib
import RHLean.Analysis.SquareRootMatchedTransport

/-!
# The combined signed residual of the square-root matched transport

The matched module centres the cofactor-first transport term `T_R` against the
smooth logarithmic-integral main term and exposes the exact three-term split

`T_R = T_R^sm + Q_R + E_R`,

with `Q_R` the aggregate reciprocal-cutoff floor rounding and `E_R` the
aggregate prime-counting discrepancy.  That split is exact, but it invites a
step that destroys the object being estimated: bounding `Q_R` and `E_R`
separately and recombining by the triangle inequality.  `E_R` carries the large
prime-count drift, so a separate absolute bound on it is far weaker than the
signed cancellation actually available against `Q_R` and against the born-smooth
mass.

This module keeps the two together.  The combined signed residual

`D_R = Q_R + E_R`

is *defined* channel by channel, as the single weight

`(pi(floor(X/c)) - pi(R)) - (Li(X/c) - Li(R))`,

before the cofactor sum is ever taken, so no later step can reach one summand
without the other.  The theorems below record

* `D_R = Q_R + E_R` (the combination is the existing pair, not a new object);
* `T_R = T_R^sm + D_R` (two-term centering);
* `A_R^born - T_R = (A_R^born - T_R^sm) - D_R` (matched form);
* the Gram identity showing the combined form has exactly the norm of the
  original matched object, so the RH-scale target is unchanged; and
* the equivalence of the combined RH-scale statement with the square-prefix
  criterion `‖A_R^born - T_R‖^2 ≪_eps R^(2+eps)` already stated in the matched
  module.

The one-way triangle bound is also recorded, precisely to show what separating
the residuals costs: the inequality runs from the separated norms to the matched
norm and admits no converse.

No analytic estimate is proved, assumed, or axiomatized here.  Every statement
is an exact finite identity, an exact norm identity, or a named proposition.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Pointwise combined signed residual on one cofactor channel: the exact prime
count at the reciprocal cutoff minus the smooth logarithmic-integral weight.

Both the floor rounding and the prime-counting discrepancy of the channel are
already inside this single difference, so the two are never available as
separate summands. -/
def squareRootTransportCombinedResidualWeight (R c : ℕ) : ℂ :=
  squareRootTransportRawWeight R c - squareRootTransportLiSmoothWeight R c

/-- The combined signed residual `D_R`, formed from the pointwise combined
weight. -/
def squareRootTransportCombinedResidual (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    canonicalMoebiusWeight c * squareRootTransportCombinedResidualWeight R c

/-- Channel by channel, the combined weight is exactly the floor correction plus
the prime-counting discrepancy of that same channel. -/
theorem squareRootTransportCombinedResidualWeight_eq_rounding_add_error
    (R c : ℕ) :
    squareRootTransportCombinedResidualWeight R c =
      squareRootTransportRoundingWeight R c +
        (squareRootTransportRawWeight R c -
          squareRootTransportLiDiscWeight R c) := by
  unfold squareRootTransportCombinedResidualWeight
    squareRootTransportRoundingWeight
  ring

/-- The combined signed residual is exactly `Q_R + E_R`.  It is the existing
pair of aggregates, combined, not a new arithmetic object. -/
theorem squareRootTransportCombinedResidual_eq_floor_add_error (R : ℕ) :
    squareRootTransportCombinedResidual R =
      squareRootTransportFloorCorrection R +
        squareRootTransportPNTError R := by
  unfold squareRootTransportCombinedResidual squareRootTransportFloorCorrection
    squareRootTransportPNTError
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro c _hc
  rw [squareRootTransportCombinedResidualWeight_eq_rounding_add_error]
  ring

/-- Exact two-term PNT centering of the transport: `T_R = T_R^sm + D_R`. -/
theorem squareRootTransportCofactorFirst_eq_smoothMain_add_combinedResidual
    (R : ℕ) :
    squareRootTransportCofactorFirst R =
      squareRootTransportSmoothMain R +
        squareRootTransportCombinedResidual R := by
  rw [squareRootTransportCofactorFirst_eq_smooth_add_floor_add_error,
    squareRootTransportCombinedResidual_eq_floor_add_error]
  ring

/-- Exact insertion of the two-term centering into the matched object:
`A_R^born - T_R = (A_R^born - T_R^sm) - D_R`. -/
theorem squareRootMatchedBornSmoothTransport_eq_pntMain_sub_combinedResidual
    (R : ℕ) :
    squareRootMatchedBornSmoothTransport R =
      squareRootMatchedBornSmoothPNTMain R -
        squareRootTransportCombinedResidual R := by
  rw [squareRootMatchedBornSmoothTransport_eq_pntMain_sub_floor_sub_error,
    squareRootTransportCombinedResidual_eq_floor_add_error]
  ring

/-- Concrete signed form of the combined residual.  Each cofactor channel carries
exactly the signed prime-counting discrepancy at its own reciprocal cutoff, with
the flooring already absorbed into the discrete prime count. -/
theorem squareRootTransportCombinedResidual_eq_primeCount_sub_liSmooth
    (R : ℕ) :
    squareRootTransportCombinedResidual R =
      ∑ c ∈ Finset.Ico 1 R,
        canonicalMoebiusWeight c *
          ((∑ q ∈ Finset.Ioc R (squareRootEndpoint R / c),
              if q.Prime then (1 : ℂ) else 0) -
            squareRootTransportLiSmoothWeight R c) := by
  unfold squareRootTransportCombinedResidual
    squareRootTransportCombinedResidualWeight
  refine Finset.sum_congr rfl ?_
  intro c hc
  have hc1 : 1 ≤ c := (Finset.mem_Ico.mp hc).1
  rw [squareRootTransportRawWeight_eq_primeCountDifference hc1]

/-- The combined form is literally the joint form already exposed by the matched
module: `pntMain - D_R` is `pntMain - Q_R - E_R`. -/
theorem squareRootMatchedCombined_eq_pntMain_sub_floor_sub_error (R : ℕ) :
    squareRootMatchedBornSmoothPNTMain R -
        squareRootTransportCombinedResidual R =
      squareRootMatchedBornSmoothPNTMain R -
        squareRootTransportFloorCorrection R -
          squareRootTransportPNTError R := by
  rw [squareRootTransportCombinedResidual_eq_floor_add_error]
  ring

/-- The combined residual preserves the signed Gram exactly.  Centering the
transport changes no norm, so the RH-scale target is untouched. -/
theorem squareRootMatchedCombinedGram_eq_matchedGram (R : ℕ) :
    ‖squareRootMatchedBornSmoothPNTMain R -
        squareRootTransportCombinedResidual R‖ ^ 2 =
      ‖squareRootMatchedBornSmoothTransport R‖ ^ 2 := by
  rw [squareRootMatchedBornSmoothTransport_eq_pntMain_sub_combinedResidual]

/-- **The cost of separating.**  Once `Q_R` and `E_R` are normed apart, only this
one-way inequality survives; the signed cancellation between them, and between
them and the born-smooth mass, is discarded and cannot be recovered.  There is no
converse, which is why the attack is stated on the combined residual. -/
theorem matchedNorm_le_separatedNorms (R : ℕ) :
    ‖squareRootMatchedBornSmoothTransport R‖ ≤
      ‖squareRootMatchedBornSmoothPNTMain R‖ +
        ‖squareRootTransportFloorCorrection R‖ +
          ‖squareRootTransportPNTError R‖ := by
  rw [squareRootMatchedBornSmoothTransport_eq_pntMain_sub_floor_sub_error]
  have h1 :
      ‖squareRootMatchedBornSmoothPNTMain R -
          squareRootTransportFloorCorrection R -
            squareRootTransportPNTError R‖ ≤
        ‖squareRootMatchedBornSmoothPNTMain R -
            squareRootTransportFloorCorrection R‖ +
          ‖squareRootTransportPNTError R‖ :=
    norm_sub_le _ _
  have h2 :
      ‖squareRootMatchedBornSmoothPNTMain R -
          squareRootTransportFloorCorrection R‖ ≤
        ‖squareRootMatchedBornSmoothPNTMain R‖ +
          ‖squareRootTransportFloorCorrection R‖ :=
    norm_sub_le _ _
  linarith

/-- The RH-scale target stated on the combined signed residual.  This is a named
proposition only; nothing here asserts or assumes it. -/
def SquareRootMatchedCombinedBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖squareRootMatchedBornSmoothPNTMain R -
            squareRootTransportCombinedResidual R‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- The combined-residual target is exactly the square-prefix RH criterion
`‖A_R^born - T_R‖^2 ≪_eps R^(2+eps)`; centering costs nothing and gains nothing
by itself. -/
theorem squareRootMatchedCombinedBounded_iff_matchedTransportBounded :
    SquareRootMatchedCombinedBoundedStatement ↔
      SquareRootMatchedTransportBoundedStatement := by
  unfold SquareRootMatchedCombinedBoundedStatement
    SquareRootMatchedTransportBoundedStatement
  simp only [squareRootMatchedCombinedGram_eq_matchedGram]

/-- The combined-residual target is also exactly the joint target already stated
in the matched module, confirming that the joint statement never intended a
separate bound on `Q_R` or on `E_R`. -/
theorem squareRootMatchedCombinedBounded_iff_pntJointBounded :
    SquareRootMatchedCombinedBoundedStatement ↔
      SquareRootMatchedPNTJointBoundedStatement := by
  unfold SquareRootMatchedCombinedBoundedStatement
    SquareRootMatchedPNTJointBoundedStatement
  simp only [squareRootMatchedCombined_eq_pntMain_sub_floor_sub_error]

end RHLean.Proof
