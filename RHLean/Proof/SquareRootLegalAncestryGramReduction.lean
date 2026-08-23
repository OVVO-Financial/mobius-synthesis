import Mathlib
import RHLean.Proof.SquareRootAncestrySuccessor

/-!
# Square-root legal-ancestry Gram reduction

This module isolates the experiment-led square-root induction target without
changing the repository's canonical ancestry coordinates.

At the complete-square endpoint `X_R = R^2 - 1`, the native ancestry renewal is

`M(X_R) - 1 = U_R - S_R`,

where `U_R` is the transport-oriented root and `S_R` is the complete successor
pushforward.  The root is already lower-triangular in Mertens values below `R`.
The successor is retained as the full legal smooth ancestry state.

The analytic target below allows any absolute amplification constant `A`.  This
is intentional: repeated physical descent uses square roots, so a fixed
amplification is compatible with an `x^epsilon` loss after only logarithmically
many ancestry generations.  No subunit contraction is built into the statement.

The final exact equivalence rewrites the complete root-successor Gram defect as
one prime-root versus smooth-mass anti-alignment inequality.  No diagonal is
bounded separately and no ancestry generation is truncated.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

/-- A scale-`R` lower critical envelope.  The empirical quantity `K(R)` is the
least such `K` after adding the harmless baseline `1`, but the theorem is stated
monotonically for every admissible envelope. -/
def LowerMertensCriticalEnvelope (R : ℕ) (K : ℝ) : Prop :=
  0 ≤ K ∧
    ∀ y : ℕ, y < R →
      (((mertensSummatoryInt y - 1 : ℤ) : ℝ) ^ 2) ≤
        K * (((y + 1 : ℕ) : ℝ))

/-- Real root coordinate of the legal ancestry renewal at `X_R = R^2 - 1`. -/
def squareRootLegalRootReal (B R : ℕ) : ℝ :=
  ((sourceRootPrefix B (R - 1) : ℤ) : ℝ)

/-- Real successor coordinate of the same legal ancestry renewal. -/
def squareRootLegalSuccessorReal (B R : ℕ) : ℝ :=
  ((sourceSuccessorPrefix B (R - 1) : ℤ) : ℝ)

/-- The irreducible two-channel Gram defect. -/
def squareRootLegalAncestryGramDefect (B R : ℕ) : ℝ :=
  (squareRootLegalRootReal B R - squareRootLegalSuccessorReal B R) ^ 2

/-- Exact Gram expansion with the forced negative cross term retained. -/
theorem squareRootLegalAncestryGramDefect_eq_expanded (B R : ℕ) :
    squareRootLegalAncestryGramDefect B R =
      squareRootLegalRootReal B R ^ 2 +
        squareRootLegalSuccessorReal B R ^ 2 -
        2 * squareRootLegalRootReal B R * squareRootLegalSuccessorReal B R := by
  unfold squareRootLegalAncestryGramDefect
  ring

/-- At a complete square endpoint, the legal root-minus-successor residual is
exactly `M(R^2-1)-1` in the integer Mertens normalization. -/
theorem sourceRootPrefix_sub_sourceSuccessorPrefix_eq_mertensInt_sub_one
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    sourceRootPrefix B (R - 1) - sourceSuccessorPrefix B (R - 1) =
      mertensSummatoryInt (squareRootEndpoint R) - 1 := by
  have hR1 : 1 ≤ R := by omega
  have hclock : 1 ≤ R - 1 := by omega
  have hend :
      RHLean.Analysis.squarePrefixEndpoint (R - 1) = squareRootEndpoint R :=
    squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR1
  have hB' : RHLean.Analysis.squarePrefixEndpoint (R - 1) ≤ B := by
    rw [hend]
    exact hB
  have hrenew :
      sourcePrefix B (R - 1) =
        sourceRootPrefix B (R - 1) - sourceSuccessorPrefix B (R - 1) := by
    simpa [sourceRootPrefix, sourceSuccessorPrefix] using
      sourcePrefix_renewal B (R - 1)
  have hsum :=
    sourcePrefix_add_indicator_eq_mertens_sum
      (B := B) (x := R - 1) hB'
  have hsum' :
      sourcePrefix B (R - 1) + 1 =
        mertensSummatoryInt (RHLean.Analysis.squarePrefixEndpoint (R - 1)) := by
    simpa [indicator, hclock, mertensSummatoryInt] using hsum
  rw [hend, hrenew] at hsum'
  omega

/-- The Gram defect is literally the empirical numerator used in the fixed-`A`
square-root experiment. -/
theorem squareRootLegalAncestryGramDefect_eq_mertensNumerator
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    squareRootLegalAncestryGramDefect B R =
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) := by
  have h :=
    sourceRootPrefix_sub_sourceSuccessorPrefix_eq_mertensInt_sub_one hR hB
  have hsq := congrArg (fun z : ℤ => ((z : ℝ) ^ 2)) h
  simpa [squareRootLegalAncestryGramDefect,
    squareRootLegalRootReal, squareRootLegalSuccessorReal] using hsq

/-- The successor coordinate is exactly the negative complete smooth ancestry
mass.  This keeps every legal ancestry generation through the full source
weight; nothing is truncated. -/
theorem sourceSuccessorPrefix_eq_neg_smoothMassInt
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    sourceSuccessorPrefix B (R - 1) =
      -squareRootAncestrySmoothMassInt R := by
  rw [sourceSuccessorPrefix_eq_neg_activeSmooth_sum,
    activeSmoothSource_sum_eq_smoothIntegerMass hR hB]

/-- The real root coordinate is the existing lower-Mertens prime transform. -/
theorem squareRootLegalRootReal_eq_primeMass
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    squareRootLegalRootReal B R =
      ((squareRootAncestryRootPrimeMass R : ℤ) : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sourceRootPrefix_eq_lowerMertensPrimeTransform hR hB)
  simpa [squareRootLegalRootReal] using h

/-- The real successor coordinate is the negative smooth ancestry mass. -/
theorem squareRootLegalSuccessorReal_eq_neg_smoothMass
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    squareRootLegalSuccessorReal B R =
      -((squareRootAncestrySmoothMassInt R : ℤ) : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sourceSuccessorPrefix_eq_neg_smoothMassInt hR hB)
  simpa [squareRootLegalSuccessorReal] using h

/-- Exact prime-root plus smooth-mass form of the residual.  The square is not
estimated here; this theorem only exposes the two signed populations whose
anti-alignment must be proved. -/
theorem squareRootLegalAncestryGramDefect_eq_prime_add_smooth_sq
    {B R : ℕ} (hR : 2 ≤ R)
    (hB : squareRootEndpoint R ≤ B) :
    squareRootLegalAncestryGramDefect B R =
      (((squareRootAncestryRootPrimeMass R : ℤ) : ℝ) +
        ((squareRootAncestrySmoothMassInt R : ℤ) : ℝ)) ^ 2 := by
  unfold squareRootLegalAncestryGramDefect
  rw [squareRootLegalRootReal_eq_primeMass hR hB,
    squareRootLegalSuccessorReal_eq_neg_smoothMass hR hB]
  ring

/-- Open endpoint theorem suggested by the empirical `A_R` experiment.  It asks
only for one absolute amplification constant and quantifies monotonically over
all lower critical envelopes. -/
def SquareRootLegalAncestryGramAmplificationStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ, ∀ B : ℕ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      squareRootEndpoint R ≤ B →
      squareRootLegalAncestryGramDefect B R ≤
        A * (R : ℝ) ^ 2 * K

/-- Real value of the lower-triangular prime-root transform. -/
def squareRootPrimeRootReal (R : ℕ) : ℝ :=
  ((squareRootAncestryRootPrimeMass R : ℤ) : ℝ)

/-- Real value of the complete smooth ancestry mass. -/
def squareRootSmoothMassReal (R : ℕ) : ℝ :=
  ((squareRootAncestrySmoothMassInt R : ℤ) : ℝ)

/-! ## Exact prime-root / smooth cross-region Gram -/

/-- The two diagonal energies of the exact root-smooth object.  They are kept
only as part of the joint Gram; no separate diagonal estimate is proposed. -/
def squareRootPrimeSmoothDiagonalGram (R : ℕ) : ℝ :=
  squareRootPrimeRootReal R ^ 2 + squareRootSmoothMassReal R ^ 2

/-- The fully signed root-smooth cross term.  The empirical anti-alignment is
precisely the statement that this quantity is negative with magnitude close to
one half of the diagonal Gram. -/
def squareRootPrimeSmoothOffDiagonalGram (R : ℕ) : ℝ :=
  squareRootPrimeRootReal R * squareRootSmoothMassReal R

/-- The complete signed cross-region Gram `D_R + 2 O_R`.  No prime fibre,
pairwise absolute value, or new state coordinate appears in this definition. -/
def squareRootPrimeSmoothCrossRegionGram (R : ℕ) : ℝ :=
  squareRootPrimeSmoothDiagonalGram R +
    2 * squareRootPrimeSmoothOffDiagonalGram R

/-- The joint Gram is exactly the square of the already-existing signed
prime-root plus complete smooth ancestry state. -/
theorem squareRootPrimeSmoothCrossRegionGram_eq_residual_sq (R : ℕ) :
    squareRootPrimeSmoothCrossRegionGram R =
      (squareRootPrimeRootReal R + squareRootSmoothMassReal R) ^ 2 := by
  unfold squareRootPrimeSmoothCrossRegionGram
    squareRootPrimeSmoothDiagonalGram squareRootPrimeSmoothOffDiagonalGram
  ring

/-- Exact state reconstruction before squaring: the root plus smooth channel is
`M(R^2-1)-1`.  This removes the ambient ancestry bound `B` entirely from the
analytic object. -/
theorem squareRootPrimeSmoothState_eq_mertensInt_sub_one
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeRootReal R + squareRootSmoothMassReal R =
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) := by
  have hB : squareRootEndpoint R ≤ squareRootEndpoint R := le_rfl
  have hres :=
    sourceRootPrefix_sub_sourceSuccessorPrefix_eq_mertensInt_sub_one
      (B := squareRootEndpoint R) (R := R) hR hB
  have hreal :
      squareRootLegalRootReal (squareRootEndpoint R) R -
          squareRootLegalSuccessorReal (squareRootEndpoint R) R =
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) := by
    change
      ((sourceRootPrefix (squareRootEndpoint R) (R - 1) : ℤ) : ℝ) -
          ((sourceSuccessorPrefix (squareRootEndpoint R) (R - 1) : ℤ) : ℝ) =
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ))
    exact_mod_cast hres
  rw [squareRootLegalRootReal_eq_primeMass hR hB,
    squareRootLegalSuccessorReal_eq_neg_smoothMass hR hB] at hreal
  simpa [squareRootPrimeRootReal, squareRootSmoothMassReal] using hreal

/-- The same state reconstruction, now as a literal equality in the repository's
complex square-prefix Mertens state. -/
theorem squareRootPrimeSmoothState_cast_eq_shiftedSquarePrefixMertens
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootPrimeRootReal R + squareRootSmoothMassReal R : ℝ) : ℂ) =
      RHLean.Analysis.squarePrefixMertens (R - 1) - 1 := by
  rw [squareRootPrimeSmoothState_eq_mertensInt_sub_one R hR]
  have hR1 : 1 ≤ R := by omega
  have hend :
      RHLean.Analysis.squarePrefixEndpoint (R - 1) = squareRootEndpoint R :=
    squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR1
  unfold RHLean.Analysis.squarePrefixMertens
  rw [hend, ← mertensSummatoryInt_cast (squareRootEndpoint R)]
  have hcast :
      ((((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) : ℂ)) =
        ((mertensSummatoryInt (squareRootEndpoint R) : ℂ) - 1) := by
    push_cast
    ring
  exact hcast

/-- Projecting the complex terminal bridge back to `ℝ` recovers the arithmetic
root-smooth state.  The real embedding remains the analytic coordinate used by
the Gram; the complex equality is simply the stronger reconstruction theorem. -/
theorem squareRootPrimeSmoothState_eq_shiftedSquarePrefixMertens_re
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeRootReal R + squareRootSmoothMassReal R =
      (RHLean.Analysis.squarePrefixMertens (R - 1)).re - 1 := by
  have h := congrArg Complex.re
    (squareRootPrimeSmoothState_cast_eq_shiftedSquarePrefixMertens R hR)
  simpa using h

/-- Consequently `D_R + 2 O_R` is literally the shifted square-prefix Mertens
energy.  This is the exact root-smooth Gram requested by the empirical
anti-alignment diagnostic. -/
theorem squareRootPrimeSmoothCrossRegionGram_eq_shiftedSquarePrefixMertens_norm_sq
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimeSmoothCrossRegionGram R =
      ‖RHLean.Analysis.squarePrefixMertens (R - 1) - 1‖ ^ 2 := by
  rw [squareRootPrimeSmoothCrossRegionGram_eq_residual_sq,
    squareRootPrimeSmoothState_eq_mertensInt_sub_one R hR]
  have hR1 : 1 ≤ R := by omega
  have hend :
      RHLean.Analysis.squarePrefixEndpoint (R - 1) = squareRootEndpoint R :=
    squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR1
  unfold RHLean.Analysis.squarePrefixMertens
  rw [hend, ← mertensSummatoryInt_cast (squareRootEndpoint R)]
  have hcast :
      ((mertensSummatoryInt (squareRootEndpoint R) : ℂ) - 1) =
        ((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_intCast]
  exact (sq_abs (((mertensSummatoryInt
    (squareRootEndpoint R) - 1 : ℤ) : ℝ))).symm

/-- Direct RH-scale endpoint target for the exact signed root-smooth Gram.  This
is a proposition only: no analytic estimate is asserted here. -/
def SquareRootPrimeSmoothCrossRegionGramBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        squareRootPrimeSmoothCrossRegionGram R ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- The direct cross-term form at one scale.  It says that the anti-alignment
between the prime-root transform and the complete smooth ancestry mass absorbs
both diagonal energies up to the permitted lower-envelope budget. -/
def SquareRootPrimeSmoothAntiAlignmentAt
    (A K : ℝ) (R : ℕ) : Prop :=
  squareRootPrimeRootReal R ^ 2 + squareRootSmoothMassReal R ^ 2 -
      A * (R : ℝ) ^ 2 * K ≤
    -2 * squareRootPrimeRootReal R * squareRootSmoothMassReal R

/-- Direct arithmetic form of the open theorem. -/
def SquareRootPrimeSmoothAntiAlignmentStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      SquareRootPrimeSmoothAntiAlignmentAt A K R

/-- The legal root-successor Gram amplification theorem is exactly the direct
prime-root versus smooth-mass anti-alignment theorem.  This is the proof target:
all signed cancellation is concentrated in the single cross term. -/
theorem squareRootLegalAncestryGramAmplification_iff_primeSmoothAntiAlignment :
    SquareRootLegalAncestryGramAmplificationStatement ↔
      SquareRootPrimeSmoothAntiAlignmentStatement := by
  constructor
  · rintro ⟨A, hA, hbound⟩
    refine ⟨A, hA, ?_⟩
    intro R K hR hK
    let B := squareRootEndpoint R
    have hB : squareRootEndpoint R ≤ B := by simp [B]
    have hgram := hbound R K B hR hK hB
    rw [squareRootLegalAncestryGramDefect_eq_prime_add_smooth_sq hR hB] at hgram
    unfold SquareRootPrimeSmoothAntiAlignmentAt
    unfold squareRootPrimeRootReal squareRootSmoothMassReal
    nlinarith
  · rintro ⟨A, hA, hanti⟩
    refine ⟨A, hA, ?_⟩
    intro R K B hR hK hB
    have ha := hanti R K hR hK
    rw [squareRootLegalAncestryGramDefect_eq_prime_add_smooth_sq hR hB]
    unfold SquareRootPrimeSmoothAntiAlignmentAt at ha
    unfold squareRootPrimeRootReal squareRootSmoothMassReal at ha
    nlinarith

end RHLean.Proof
