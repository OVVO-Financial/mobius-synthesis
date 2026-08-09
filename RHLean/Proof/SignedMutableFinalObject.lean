import Mathlib
import RHLean.Proof.MutableSupportBound
import RHLean.Analysis.ConcreteSquarePrefixGeometry

/-!
# Signed mutable prefix as the terminal arithmetic object

The terminal object is not the cardinality of the mutable support and not an
independent packet-Gram premise. It is the signed Möbius mass carried by the
mutable support in each square block, accumulated from the common origin.

When the settled complement has zero Möbius mass, this signed mutable block
sum is exactly the complete square-block increment. Consequently its prefix
is exactly the square-prefix Mertens sequence once the existing exact
identification is supplied.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Signed Möbius mass carried by the mutable support in square block `n`. -/
def signedMutableBlockSum (U : ℕ → Finset ℕ) (n : ℕ) : ℂ :=
  ((∑ m ∈ U n, μ m : ℤ) : ℂ)

/-- Cumulative signed mutable mass from the common square-block origin. -/
def signedMutablePrefix (U : ℕ → Finset ℕ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), signedMutableBlockSum U k

/-- The signed mutable block sum is exactly the complete block discrepancy
whenever the settled complement has zero Möbius mass. -/
theorem signedMutableBlockSum_eq_squareBlockMoebius
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (n : ℕ) :
    signedMutableBlockSum U n = (squareBlockMoebius n : ℂ) := by
  unfold signedMutableBlockSum
  rw [squareBlockMoebius_eq_sum_mutable (hU n) (hinterior n)]

/-- Exact cumulative version: the signed mutable prefix is the prefix of the
complete square-block discrepancies. -/
theorem signedMutablePrefix_eq_squareBlockMoebiusPrefix
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (n : ℕ) :
    signedMutablePrefix U n =
      ∑ k ∈ Finset.range (n + 1), (squareBlockMoebius k : ℂ) := by
  unfold signedMutablePrefix
  apply Finset.sum_congr rfl
  intro k hk
  exact signedMutableBlockSum_eq_squareBlockMoebius U hU hinterior k

/-- RH-scale translated-window energy control for the cumulative signed mutable
sum. This is the final analytic object suggested by the experiments. -/
def SignedMutableUniformLocalBoundedStatement
    (U : ℕ → Finset ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy (signedMutablePrefix U) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- Once the exact identification with the square-prefix Mertens sequence is
supplied, the signed mutable local-energy statement is literally the
repository's protected square-prefix criterion. -/
theorem signedMutableUniformLocalBounded_implies_squarePrefixUniformLocal
    (U : ℕ → Finset ℕ)
    (hidentify : ∀ n, signedMutablePrefix U n =
      RHLean.Analysis.squarePrefixMertens n)
    (hbound : SignedMutableUniformLocalBoundedStatement U) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  intro ε hε
  rcases hbound ε hε with ⟨C, hC, hlocal⟩
  refine ⟨C, hC, ?_⟩
  intro N H hH hHN
  simpa [RHLean.Analysis.localSequenceEnergy, hidentify] using
    hlocal N H hH hHN

/-- Conditional RH closure with the cumulative signed mutable sum as the sole
final analytic object. All subsequent arrows are existing repository bridges. -/
theorem riemannHypothesis_of_signedMutableUniformLocalBounded
    (U : ℕ → Finset ℕ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hidentify : ∀ n, signedMutablePrefix U n =
      RHLean.Analysis.squarePrefixMertens n)
    (hbound : SignedMutableUniformLocalBoundedStatement U) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  apply criterion.iff_riemannHypothesis.mp
  apply RHLean.Analysis.squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded.mp
  exact signedMutableUniformLocalBounded_implies_squarePrefixUniformLocal
    U hidentify hbound

end RHLean.Proof
