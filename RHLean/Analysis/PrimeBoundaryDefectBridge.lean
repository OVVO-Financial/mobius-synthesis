import Mathlib
import RHLean.Arithmetic.FullPrimeFactorizationState
import RHLean.Arithmetic.PrimeSquareCollisionPairingFrontier
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Proof.RealSquareBlockIncrements

/-!
# Prime-coordinate boundary defects

This module keeps two exact coordinate systems for a square-block Möbius
increment separate:

* canonical terminal-prime channels provide a unique arithmetic decomposition;
* fixed-prime Boolean matchings provide cancellation coordinates.

The second representation is redundant: every complete prime coordinate equals
the same increment.  Consequently raw summation over prime coordinates
multiplies the increment by the number of coordinates, while normalized
averaging preserves it.  The redundancy is useful because its second moment is
exactly the coordinate count times the square of the block increment.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- Integer-valued indicator of a finite arithmetic window. -/
def windowIndicator (W : Finset ℕ) (n : ℕ) : ℤ :=
  if n ∈ W then 1 else 0

/-- Boundary term contributed by one fresh parent-child transport edge. -/
def primePairBoundaryTerm (W : Finset ℕ) (e : PrimeTransportEdge) : ℤ :=
  μ e.parent * (windowIndicator W e.parent - windowIndicator W e.child)

/-- A fresh prime-extension pair contributes only when the window separates its
parent and child.  If both lie inside, or both lie outside, the contribution is
zero. -/
theorem freshPrime_pair_eq_boundaryTerm
    (W : Finset ℕ) (e : PrimeTransportEdge)
    (hfresh : ¬ e.terminal ∣ e.parent) :
    μ e.parent * windowIndicator W e.parent +
        μ e.child * windowIndicator W e.child =
      primePairBoundaryTerm W e := by
  rw [PrimeTransportEdge.moebius_child_eq_neg_parent e hfresh]
  unfold primePairBoundaryTerm
  ring

/-- If both endpoints of a fresh edge lie in the window, their Möbius
contributions cancel exactly. -/
theorem freshPrime_pair_cancel_of_both_mem
    (W : Finset ℕ) (e : PrimeTransportEdge)
    (hfresh : ¬ e.terminal ∣ e.parent)
    (_hparent : e.parent ∈ W) (_hchild : e.child ∈ W) :
    μ e.parent + μ e.child = 0 := by
  rw [PrimeTransportEdge.moebius_child_eq_neg_parent e hfresh]
  ring

/-- If neither endpoint lies in the window, its boundary term vanishes. -/
theorem primePairBoundaryTerm_eq_zero_of_neither_mem
    (W : Finset ℕ) (e : PrimeTransportEdge)
    (hparent : e.parent ∉ W) (hchild : e.child ∉ W) :
    primePairBoundaryTerm W e = 0 := by
  simp [primePairBoundaryTerm, windowIndicator, hparent, hchild]

/-- If both endpoints lie in the window, its boundary term also vanishes. -/
theorem primePairBoundaryTerm_eq_zero_of_both_mem
    (W : Finset ℕ) (e : PrimeTransportEdge)
    (hparent : e.parent ∈ W) (hchild : e.child ∈ W) :
    primePairBoundaryTerm W e = 0 := by
  simp [primePairBoundaryTerm, windowIndicator, hparent, hchild]

/-- Abstract data for a finite family of exact fixed-prime representations of
one increment.  Concrete arithmetic modules supply `defect`; this structure
records the exact fact that every represented prime coordinate equals the same
window sum. -/
structure ExactPrimeBoundaryFamily (P : Finset ℕ) (increment : ℤ) where
  defect : ℕ → ℤ
  exact_on_primes : ∀ q ∈ P, q.Prime ∧ defect q = increment

namespace ExactPrimeBoundaryFamily

variable {P : Finset ℕ} {increment : ℤ}

/-- Raw summation over exact prime coordinates duplicates the increment once
per coordinate. -/
theorem sum_defect_eq_card_mul
    (F : ExactPrimeBoundaryFamily P increment) :
    ∑ q ∈ P, F.defect q = (P.card : ℤ) * increment := by
  calc
    (∑ q ∈ P, F.defect q) = ∑ _q ∈ P, increment := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (F.exact_on_primes q hq).2
    _ = (P.card : ℤ) * increment := by simp

/-- The averaged identity in division-free form.  This is the preferred exact
statement over integers: the sum of all coordinates is the coordinate count
times the original increment. -/
theorem averaged_defect_crossMultiplied
    (F : ExactPrimeBoundaryFamily P increment) :
    ∑ q ∈ P, F.defect q = (P.card : ℤ) * increment :=
  F.sum_defect_eq_card_mul

/-- Exact second-moment rigidity: because every coordinate represents the same
increment, the coordinate energy is the number of coordinates times the square
of that increment. -/
theorem sum_sq_defect_eq_card_mul_sq
    (F : ExactPrimeBoundaryFamily P increment) :
    ∑ q ∈ P, (F.defect q) ^ 2 = (P.card : ℤ) * increment ^ 2 := by
  calc
    (∑ q ∈ P, (F.defect q) ^ 2) = ∑ _q ∈ P, increment ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(F.exact_on_primes q hq).2]
    _ = (P.card : ℤ) * increment ^ 2 := by simp

/-- Any two represented prime directions give the same boundary defect. -/
theorem defect_eq_defect
    (F : ExactPrimeBoundaryFamily P increment)
    {q r : ℕ} (hq : q ∈ P) (hr : r ∈ P) :
    F.defect q = F.defect r := by
  rw [(F.exact_on_primes q hq).2, (F.exact_on_primes r hr).2]

end ExactPrimeBoundaryFamily

/-- A unique canonical decomposition and a redundant fixed-prime family are
bridged by their common increment.  This structure deliberately does not
identify the two coordinate systems term by term. -/
structure CanonicalAndBoundaryBridge (P : Finset ℕ) where
  increment : ℤ
  canonicalContribution : ℤ
  canonical_eq_increment : canonicalContribution = increment
  boundaryFamily : ExactPrimeBoundaryFamily P increment

namespace CanonicalAndBoundaryBridge

variable {P : Finset ℕ}

/-- The canonical terminal-prime total equals every represented fixed-prime
boundary coordinate. -/
theorem canonical_eq_boundary
    (B : CanonicalAndBoundaryBridge P)
    {q : ℕ} (hq : q ∈ P) :
    B.canonicalContribution = B.boundaryFamily.defect q := by
  rw [B.canonical_eq_increment,
    (B.boundaryFamily.exact_on_primes q hq).2]

/-- The canonical total also equals the normalized prime average in exact
cross-multiplied form. -/
theorem card_mul_canonical_eq_sum_boundary
    (B : CanonicalAndBoundaryBridge P) :
    (P.card : ℤ) * B.canonicalContribution =
      ∑ q ∈ P, B.boundaryFamily.defect q := by
  rw [B.canonical_eq_increment,
    B.boundaryFamily.sum_defect_eq_card_mul]

end CanonicalAndBoundaryBridge

/-- Every product entering the concrete block `[100,121)` through a nontrivial
terminal factor has parent at most `60`. -/
theorem parent_le_sixty_of_mem_block_100_121
    {c q n : ℕ} (hq : 2 ≤ q) (hprod : c * q = n)
    (hn : n < 121) :
    c ≤ 60 := by
  have htwo : c * 2 ≤ c * q := Nat.mul_le_mul_left c hq
  rw [hprod] at htwo
  omega

/-- Therefore every such parent lies in the completed square prefix `[1,64)`.
This is the exact `60 < 8²` frontier used by the block schedule. -/
theorem parent_lt_sixtyFour_of_mem_block_100_121
    {c q n : ℕ} (hq : 2 ≤ q) (hprod : c * q = n)
    (hn : n < 121) :
    c < 64 := by
  have hc := parent_le_sixty_of_mem_block_100_121 hq hprod hn
  omega

/-! ## A finite collision-defect criterion at the RH scale

The nine-class collision involution proved in the arithmetic layer has only
three possible stranded labels in any finite frontier.  The structure below
isolates the remaining global arithmetic theorem needed to turn that local
fact into a square-prefix Mertens estimate.

For the square endpoint `(n+1)^2 - 1`, a chain consists of at most `n+1`
fresh-prime steps.  Each step contributes one finite collision defect with
unit-bounded signed weights, and the sum of those defects must equal the exact
square-prefix Mertens value.  No asymptotic estimate is stored in the
structure: only a finite identity and finite support conditions.

Once such a chain is constructed, the local three-label theorem gives

`|M((n+1)^2 - 1)| <= 3 (n+1)`

and hence squared energy at most `9 (n+1)^2`, already at the critical RH scale
before any epsilon loss.
-/

/-- Exact finite data expressing one square-prefix Mertens value as a chain of
nine-class collision-frontier defects.  The key construction problem is the
`represents` field; the remaining fields make the global charge multiplicity
explicit and bounded. -/
structure SquarePrefixCollisionDefectChain (n : ℕ) where
  steps : Finset ℕ
  steps_bounded : steps ⊆ Finset.range (n + 1)
  frontier : ℕ → Finset TwoPrimeCollisionState
  weight : ℕ → TwoPrimeCollisionState → ℤ
  unit_weight : ∀ t ∈ steps,
    ∀ s ∈ collisionInvolutionDefectPart (frontier t), |weight t s| ≤ 1
  represents :
    squarePrefixMertens n =
      ((∑ t ∈ steps,
          ∑ s ∈ collisionInvolutionDefectPart (frontier t), weight t s : ℤ) : ℂ)

namespace SquarePrefixCollisionDefectChain

variable {n : ℕ}

/-- Total signed mass carried by the chain. -/
def mass (C : SquarePrefixCollisionDefectChain n) : ℤ :=
  ∑ t ∈ C.steps,
    ∑ s ∈ collisionInvolutionDefectPart (C.frontier t), C.weight t s

/-- The representation field rewritten through the named chain mass. -/
theorem represents_mass (C : SquarePrefixCollisionDefectChain n) :
    squarePrefixMertens n = ((C.mass : ℤ) : ℂ) := by
  exact C.represents

/-- Each chain step contributes absolute mass at most three, so the total chain
mass is at most three times the number of charged steps. -/
theorem abs_mass_le_three_mul_card
    (C : SquarePrefixCollisionDefectChain n) :
    |C.mass| ≤ 3 * (C.steps.card : ℤ) := by
  unfold mass
  calc
    |∑ t ∈ C.steps,
        ∑ s ∈ collisionInvolutionDefectPart (C.frontier t), C.weight t s| ≤
      ∑ t ∈ C.steps,
        |∑ s ∈ collisionInvolutionDefectPart (C.frontier t), C.weight t s| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ C.steps, (3 : ℤ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact abs_sum_collisionInvolutionDefectPart_le_three
        (C.frontier t) (C.weight t) (C.unit_weight t ht)
    _ = 3 * (C.steps.card : ℤ) := by
      simp [mul_comm]

/-- The chain has at most `n+1` charged steps. -/
theorem steps_card_le_succ
    (C : SquarePrefixCollisionDefectChain n) :
    C.steps.card ≤ n + 1 := by
  calc
    C.steps.card ≤ (Finset.range (n + 1)).card :=
      Finset.card_le_card C.steps_bounded
    _ = n + 1 := by simp

/-- Critical linear Mertens bound supplied by any exact collision-defect chain. -/
theorem abs_mass_le_three_mul_succ
    (C : SquarePrefixCollisionDefectChain n) :
    |C.mass| ≤ 3 * (((n + 1 : ℕ) : ℤ)) := by
  have hcard : (C.steps.card : ℤ) ≤ (((n + 1 : ℕ) : ℤ)) := by
    exact_mod_cast C.steps_card_le_succ
  exact C.abs_mass_le_three_mul_card.trans
    (mul_le_mul_of_nonneg_left hcard (by norm_num))

private theorem norm_intCast_complex_sq (z : ℤ) :
    ‖((z : ℤ) : ℂ)‖ ^ 2 = ((z * z : ℤ) : ℝ) := by
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply]

/-- A collision-defect chain gives the epsilon-free critical square-prefix
energy bound with constant `9`. -/
theorem norm_sq_squarePrefixMertens_le_nine_mul_sq
    (C : SquarePrefixCollisionDefectChain n) :
    ‖squarePrefixMertens n‖ ^ 2 ≤
      9 * (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have habsInt := C.abs_mass_le_three_mul_succ
  have habsReal :
      |((C.mass : ℤ) : ℝ)| ≤ 3 * (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast habsInt
  have hbounds := (abs_le.mp habsReal)
  have hprod :
      0 ≤
        (3 * (((n + 1 : ℕ) : ℝ)) - ((C.mass : ℤ) : ℝ)) *
          (3 * (((n + 1 : ℕ) : ℝ)) + ((C.mass : ℤ) : ℝ)) := by
    exact mul_nonneg
      (sub_nonneg.mpr hbounds.2)
      (by linarith [hbounds.1])
  have hsq :
      (((C.mass : ℤ) : ℝ)) ^ 2 ≤
        (3 * (((n + 1 : ℕ) : ℝ))) ^ 2 := by
    nlinarith [hprod]
  rw [C.represents_mass, norm_intCast_complex_sq]
  calc
    (((C.mass * C.mass : ℤ) : ℝ)) = (((C.mass : ℤ) : ℝ)) ^ 2 := by
      push_cast
      ring
    _ ≤ (3 * (((n + 1 : ℕ) : ℝ))) ^ 2 := hsq
    _ = 9 * (((n + 1 : ℕ) : ℝ) ^ 2) := by ring

end SquarePrefixCollisionDefectChain

/-- Global arithmetic target: construct one exact bounded collision-defect chain
for every square-prefix endpoint. -/
def SquarePrefixCollisionDefectChainStatement : Prop :=
  ∀ n : ℕ, Nonempty (SquarePrefixCollisionDefectChain n)

/-- The finite chain statement implies the repository's exact square-prefix
energy criterion with constant `9`; the epsilon slack is needed only to match
the conventional statement. -/
theorem squarePrefixEnergyBounded_of_collisionDefectChainStatement
    (hchain : SquarePrefixCollisionDefectChainStatement) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  refine ⟨9, by norm_num, ?_⟩
  intro n
  rcases hchain n with ⟨C⟩
  have hcritical :=
    C.norm_sq_squarePrefixMertens_le_nine_mul_sq
  have hbase : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hexponent : (2 : ℝ) ≤ 2 + ε := by
    linarith
  have hpow :
      (((n + 1 : ℕ) : ℝ)) ^ 2 ≤
        Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + ε) := by
    rw [← Real.rpow_natCast]
    exact (Real.monotone_rpow_of_base_ge_one hbase) hexponent
  exact hcritical.trans
    (mul_le_mul_of_nonneg_left hpow (by norm_num))

/-- Therefore the same finite chain statement implies the full Mertens energy
criterion through the already-formalized square-prefix interpolation. -/
theorem mertensEnergyBounded_of_collisionDefectChainStatement
    (hchain : SquarePrefixCollisionDefectChainStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_squarePrefixEnergyBounded
    (squarePrefixEnergyBounded_of_collisionDefectChainStatement hchain)

/-- With the classical forward Mertens-to-RH implication supplied explicitly,
the finite collision-defect chain statement proves the formal Riemann
Hypothesis statement.  No reverse RH-to-Mertens implication is used. -/
theorem riemannHypothesis_of_collisionDefectChainStatement
    (forward : MertensEnergyBoundedStatement → RiemannHypothesisStatement)
    (hchain : SquarePrefixCollisionDefectChainStatement) :
    RiemannHypothesisStatement :=
  forward (mertensEnergyBounded_of_collisionDefectChainStatement hchain)

end RHLean.Analysis
