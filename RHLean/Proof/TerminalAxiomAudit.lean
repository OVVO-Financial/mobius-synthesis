import RHLean.Analysis.NativePNTAxer
import RHLean.Analysis.PrimeDilateCofactorPrimeWindows
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Proof.CanonicalGapAncestryQuadraticClosure
import RHLean.Proof.LowPrimeCombinedBornHighFirstFailure
import RHLean.Proof.LowPrimeCombinedBornHighTransition
import RHLean.Proof.LowPrimeCompletedPartnerWindowFold
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction
import RHLean.Proof.SquareRootAncestryParentFibres
import RHLean.Proof.SquareRootBornPostTailLowPrimeCollapse
import RHLean.Proof.SquareRootBornPostTailLowPrimeRemainder
import RHLean.Proof.SquareRootLowPrimeSequentialDissipation
import RHLean.Proof.SquareRootLowPrimeTerminalHighPrimeIntegration
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling
import RHLean.Proof.SquareRootLowPrimeMatchedCoreMertensObstruction
import RHLean.Proof.SquareRootMertensMiddleTracking
import RHLean.Proof.SquareRootMertensPositiveTracking
import RHLean.Proof.TerminalMertensForward
import RHLean.Proof.TerminalMertensReduction

/-!
# Axiom footprint of the terminal reduction

`scripts/audit_assumptions.sh` greps the sources for unfinished-proof placeholders and
for declared opaque constants. That is necessary but not sufficient: it inspects text,
not the kernel's record of what a proof actually depends on, and it cannot see anything
inherited through an import.

This module closes that gap for the theorems that carry the reduction to RH. Each
`#print axioms` below asks the kernel directly, while `#guard_msgs` makes the expected
answer part of the build.  The expected answer is exactly

```text
[propext, Classical.choice, Quot.sound]
```

the three standard axioms of Lean's logic used throughout Mathlib. Any other name in
these lists -- in particular `sorryAx`, which is what an unfinished proof compiles to,
or any project-declared axiom -- fails this module and invalidates the corresponding
reduction claim.

A clean axiom list is necessary but does not by itself certify that a theorem has no
ordinary hypothesis representing an external criterion.  The historical equivalences
below still accept `ClassicalMertensRHCriterion` as an ordinary theorem argument, so
that conditionality remains visible in their signatures even though it is absent from
`#print axioms`.  The new guarded theorem
`TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy` is different: its only
hypothesis is the square-prefix energy estimate itself.  The forward Mertens-to-RH
criterion is constructed internally by `MertensEnergyRHForward`, so this is the terminal
unconditional analytic consumer for the arithmetic project.

The square-root legal-ancestry Gram reduction is imported here as well so the ordinary
root build type-checks its exact endpoint and parent-fibre identities. Its new analytic
amplification statement remains an explicitly open proposition and is not added to the
axiom guards below.

The terminal high-prime integration is imported here for the same reason: the ordinary
root build type-checks the exact high-prime splice on the canonical processed
terminal frontier.

The smooth/transport recoupling is also imported here.  It proves that the terminal
running imbalance is the historical matched born-smooth/transport residual minus only
the partial crossing packet and the near-root rectangle, whose combined norm is at
most `R + K`.  It also proves that a `3 R sqrt(K)` bound for that matched residual
implies the exact `25 R^2 K` terminal-square bound and hence the signed response-child
energy decrement through the pre-existing exact telescope.  The `3 R sqrt(K)` matched
bound itself is not proved here: that signed `BornSmooth - Transport` / `A - T`
correlation is the remaining arithmetic input.  In particular, no independent
low-prime frontier estimate is introduced as a new analytic obligation.

The final low-prime branch now exposes the same arithmetic input in two exact Mertens
tracking coordinates.  First, the matched core is `M(R^2-1)` minus one literal
positive-orientation middle source mass.  Second, and more economically,
`M(R^2-1) - PositiveSmooth(R)` is exactly the matched channel itself.  The corresponding
`O(R)` tracking estimates remain explicit theorem hypotheses.  The guards below certify
that the exact identities and the implications *from* those hypotheses have no hidden
project axiom.

The later sections also host the exact first-jump coordinate bridges.  They introduce
no analytic estimate: every statement is finite Euler arithmetic before any norm is
taken.

The final section is different in kind.  Every guard above certifies an implication or
an identity, so a clean axiom list there says only that no hidden project axiom is used;
the open analytic content still sits in an ordinary hypothesis, and a clean list alone
establishes nothing about `M`.  The last two theorems have no hypotheses at all, so for
them the kernel's answer is the whole story: they are finished, unconditional
mathematics.
-/

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

namespace TerminalAxiomAudit

-- The direct terminal arithmetic-to-RH consumer.  Unlike the historical
-- equivalences below, its only ordinary hypothesis is the square-prefix energy bound.
/--
info: 'RHLean.Proof.TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy

-- The terminal equivalence: the projected-renewal quadratic bound is RH, given the
-- classical Mertens criterion.
/--
info: 'RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_riemannHypothesis

-- The algebraic half of the chain: the projected-renewal bound is exactly canonical
-- (HS). This one is unconditional.
/--
info: 'RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh

-- The analytic half: canonical (HS) is RH, given the criterion.
/--
info: 'RHLean.Proof.canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized

-- Exact source-form obstruction: no estimate is used here.
/--
info: 'RHLean.Proof.squareRootLowPrimeMatchedCore_eq_mertens_sub_middleSourceMass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.squareRootLowPrimeMatchedCore_eq_mertens_sub_middleSourceMass

-- Conditional terminal implication from the explicit Mertens/middle tracking
-- proposition.  The tracking proposition is an ordinary theorem argument, not an axiom.
/--
info: 'RHLean.Proof.abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensMiddleTracking' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensMiddleTracking

-- Shortest conditional endpoint: M(R^2-1) - PositiveSmooth(R) is exactly the matched
-- channel, so this route incurs no seven-strip loss.
/--
info: 'RHLean.Proof.abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensPositiveTracking' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensPositiveTracking

/-! ## Unconditional results

The two theorems below take no arguments.  They are restated here under explicit names,
with their statements written out, so that the guard records exactly what is claimed and
so that a later change to the underlying definitions breaks this module rather than
silently weakening the claim. -/

/-- **Native Chebyshev prime number theorem, unconditional.**  `psi(N)/N -> 1`, with no
hypothesis.  The underlying contraction is this repository's own elementary argument:
`NativePNTErdosContraction` imports Mathlib and one project file, so this does not route
through the vendored StrongPNT port. -/
theorem nativeChebyshevPrimeNumberTheorem_unconditional :
    Filter.Tendsto (fun N : ℕ => RHLean.Analysis.nativePsi N / (N : ℝ))
      Filter.atTop (nhds 1) :=
  RHLean.Analysis.nativePsi_div_atTop_one

/--
info: 'RHLean.Proof.TerminalAxiomAudit.nativeChebyshevPrimeNumberTheorem_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RHLean.Proof.TerminalAxiomAudit.nativeChebyshevPrimeNumberTheorem_unconditional

/-- **Mertens cancellation, unconditional.**  `M(N)/N -> 0`, that is `M(x) = o(x)`, with
no hypothesis, via the Axer bridge applied to the native PNT above.

This is exactly prime-number-theorem strength and no more.  It is *not* the RH-scale
bound `M(x) << x^(1/2+eps)`, which is equivalent to the Riemann hypothesis and remains
open; that bound is the content of `SquarePrefixEnergyBoundedStatement` and of the other
`...BoundedStatement` premises in this development, none of which is discharged here. -/
theorem nativeMertensSummatoryCancellation_unconditional :
    Filter.Tendsto (fun N : ℕ => RHLean.Analysis.nativeMertensSummatory N / (N : ℝ))
      Filter.atTop (nhds 0) :=
  RHLean.Analysis.nativeMertens_div_atTop_zero

/--
info: 'RHLean.Proof.TerminalAxiomAudit.nativeMertensSummatoryCancellation_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RHLean.Proof.TerminalAxiomAudit.nativeMertensSummatoryCancellation_unconditional

end TerminalAxiomAudit

open RHLean.Analysis
open RHLean.Arithmetic

/-! ## First-jump residual in canonical prime-sieve coordinates -/

/-- Literal Mertens column carried by primes in the frozen band `(s,K]`. -/
noncomputable def firstJumpPrimeSieveMertensBand (s K X : ℕ) : ℂ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
    mertensSummatory (X / p)

/-- The frozen high-prime band is exactly the prime-filtered integer interval. -/
theorem frozenPrimeUniverseHighPrimeSet_eq_Ioc_filter_prime
    (s K : ℕ) :
    frozenPrimeUniverseHighPrimeSet s K =
      (Finset.Ioc s K).filter Nat.Prime := by
  ext p
  simp [mem_frozenPrimeUniverseHighPrimeSet, and_comm, and_assoc]

/-- Interval form of the literal Mertens band. -/
theorem firstJumpPrimeSieveMertensBand_eq_Ioc
    (s K X : ℕ) :
    firstJumpPrimeSieveMertensBand s K X =
      ∑ p ∈ Finset.Ioc s K,
        if p.Prime then mertensSummatory (X / p) else 0 := by
  unfold firstJumpPrimeSieveMertensBand
  rw [frozenPrimeUniverseHighPrimeSet_eq_Ioc_filter_prime]
  rw [Finset.sum_filter]

/-- **Prime band = difference of repository prime tails.**
This includes `K > X`; primes beyond `X` have quotient zero and vanish. -/
theorem firstJumpPrimeSieveMertensBand_eq_tail_sub_tail
    {s K X : ℕ} (hsK : s ≤ K) :
    firstJumpPrimeSieveMertensBand s K X =
      primeSieveMertensPrimeTail s X -
        primeSieveMertensPrimeTail K X := by
  rw [firstJumpPrimeSieveMertensBand_eq_Ioc]
  unfold primeSieveMertensPrimeTail
  let f : ℕ → ℂ := fun p =>
    if p.Prime then mertensSummatory (X / p) else 0
  change (∑ p ∈ Finset.Ioc s K, f p) =
    (∑ p ∈ Finset.Ioc s X, f p) -
      ∑ p ∈ Finset.Ioc K X, f p
  by_cases hKX : K ≤ X
  · have hsplit := Finset.sum_Ioc_consecutive (f := f) hsK hKX
    exact (eq_sub_iff_add_eq).2 hsplit
  · have hXK : X < K := Nat.lt_of_not_ge hKX
    have htailK : (∑ p ∈ Finset.Ioc K X, f p) = 0 := by
      rw [Finset.Ioc_eq_empty_of_le hXK.le]
      simp
    by_cases hsX : s ≤ X
    · have hsplit := Finset.sum_Ioc_consecutive (f := f) hsX hXK.le
      have hzero : (∑ p ∈ Finset.Ioc X K, f p) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hXp : X < p := (Finset.mem_Ioc.mp hp).1
        have hdiv : X / p = 0 := Nat.div_eq_of_lt hXp
        simp [f, hdiv]
      rw [hzero, add_zero] at hsplit
      rw [htailK, sub_zero]
      exact hsplit.symm
    · have hXs : X < s := Nat.lt_of_not_ge hsX
      have hband : (∑ p ∈ Finset.Ioc s K, f p) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hsp : s < p := (Finset.mem_Ioc.mp hp).1
        have hXp : X < p := hXs.trans hsp
        have hdiv : X / p = 0 := Nat.div_eq_of_lt hXp
        simp [f, hdiv]
      have htailS : (∑ p ∈ Finset.Ioc s X, f p) = 0 := by
        rw [Finset.Ioc_eq_empty_of_le hXs.le]
        simp
      rw [hband, htailS, htailK, sub_zero]

/-- The same prime band in the quotient-reindexed reciprocal prime-count
coordinate.  No strict square-root assumption is needed for this finite Fubini
identity. -/
theorem firstJumpPrimeSieveMertensBand_eq_reciprocalSignedSum_sub
    {s K X : ℕ} (hsK : s ≤ K) :
    firstJumpPrimeSieveMertensBand s K X =
      primeSieveReciprocalMertensSignedSum s X -
        primeSieveReciprocalMertensSignedSum K X := by
  rw [firstJumpPrimeSieveMertensBand_eq_tail_sub_tail hsK]
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail,
    primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail]

/-- Cast the integer first-jump residual without changing its signed structure. -/
theorem sqrtFirstJumpResidual_cast_eq_band_sub_band
    {R q A B : ℕ}
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ) =
      firstJumpPrimeSieveMertensBand (Nat.sqrt R) (q - 1) A -
        firstJumpPrimeSieveMertensBand (Nat.sqrt R) (q - 1) B := by
  have hJ := sqrtFirstJumpResidual_eq_neg_sum_mertensGaps
    hqroot hBR hAB
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) hJ
  push_cast at hcast
  simp only [mertensSummatoryInt_cast] at hcast
  rw [Finset.sum_sub_distrib] at hcast
  unfold firstJumpPrimeSieveMertensBand
  simpa only [neg_sub] using hcast

/-- The exact signed reciprocal-Mertens object left after the geometric
contractions.  No norm is built into this definition. -/
noncomputable def firstJumpReciprocalMertensDifference
    (s K A B : ℕ) : ℂ :=
  (primeSieveReciprocalMertensSignedSum s A -
      primeSieveReciprocalMertensSignedSum K A) -
    (primeSieveReciprocalMertensSignedSum s B -
      primeSieveReciprocalMertensSignedSum K B)

/-- **First-jump residual -> reciprocal-prime-count/Mertens coordinate.** -/
theorem sqrtFirstJumpResidual_cast_eq_reciprocalMertensDifference
    {R q A B : ℕ}
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ) =
      firstJumpReciprocalMertensDifference
        (Nat.sqrt R) (q - 1) A B := by
  have hsK : Nat.sqrt R ≤ q - 1 := by omega
  rw [sqrtFirstJumpResidual_cast_eq_band_sub_band hqroot hBR hAB]
  unfold firstJumpReciprocalMertensDifference
  rw [firstJumpPrimeSieveMertensBand_eq_reciprocalSignedSum_sub hsK,
    firstJumpPrimeSieveMertensBand_eq_reciprocalSignedSum_sub hsK]

/-- Endpoints `X <= R` have no larger square root. -/
theorem sqrt_le_root_of_endpoint_le
    {R X : ℕ} (hXR : X ≤ R) :
    Nat.sqrt X ≤ Nat.sqrt R :=
  Nat.sqrt_le_sqrt hXR

/-- The strict/equality root edge is explicit. -/
theorem sqrt_endpoint_root_boundary_dichotomy
    {R X : ℕ} (hXR : X ≤ R) :
    Nat.sqrt X < Nat.sqrt R ∨ Nat.sqrt X = Nat.sqrt R := by
  have hle := sqrt_le_root_of_endpoint_le hXR
  omega

/-! ## Low-cofactor prime-window form of the first-jump residual -/

/-- Zero-extended cofactor response of the high-prime band `(sqrt R,K]` at
endpoint `X`.  This is a response field, not a covariance object. -/
noncomputable def firstJumpHighPrimeCofactorResponse
    (p R K X c : ℕ) : ℂ :=
  if c ∈ primeDilateCofactorSupport p X then
    primeDilateCofactorWindowPrimeCount p (Nat.sqrt R) X c -
      primeDilateCofactorWindowPrimeCount p K X c
  else
    0

/-- The actual active cofactor support after the square-root contraction. -/
def firstJumpHighPrimeCofactorSupport
    (p R X : ℕ) : Finset ℕ :=
  primeDilateCofactorSupport p X ∩ Finset.Icc 1 (Nat.sqrt R)

/-- Every active cofactor lies on the low side of the square-root cut. -/
theorem firstJumpHighPrimeCofactorSupport_le_sqrt
    {p R X c : ℕ}
    (hc : c ∈ firstJumpHighPrimeCofactorSupport p R X) :
    c ≤ Nat.sqrt R := by
  exact (Finset.mem_Icc.mp (Finset.mem_inter.mp hc).2).2

/-- Above the square-root cofactor cut every prime-dilate window with cutoff at
least `sqrt R` is empty at every physical endpoint `X <= R`. -/
theorem primeDilateCofactorWindowPrimeCount_eq_zero_of_sqrt_lt_cofactor
    {p R X y c : ℕ}
    (hXR : X ≤ R) (hcs : Nat.sqrt R < c)
    (hsy : Nat.sqrt R ≤ y) :
    primeDilateCofactorWindowPrimeCount p y X c = 0 := by
  have hcpos : 0 < c := by omega
  have hclock : R < (Nat.sqrt R + 1) ^ 2 := Nat.lt_succ_sqrt' R
  have hsc : Nat.sqrt R + 1 ≤ c := by omega
  have hmul :
      (Nat.sqrt R + 1) ^ 2 ≤ (Nat.sqrt R + 1) * c := by
    simpa [pow_two] using
      Nat.mul_le_mul_left (Nat.sqrt R + 1) hsc
  have hXlt : X < (Nat.sqrt R + 1) * c :=
    hXR.trans_lt (hclock.trans_le hmul)
  have hdivlt : X / c < Nat.sqrt R + 1 :=
    (Nat.div_lt_iff_lt_mul hcpos).2 hXlt
  have hupper : X / c ≤ Nat.sqrt R := by omega
  have hle :
      primeDilateCofactorWindowUpper X c ≤
        primeDilateCofactorWindowLower p y X c := by
    unfold primeDilateCofactorWindowUpper primeDilateCofactorWindowLower
    exact hupper.trans (hsy.trans (le_max_left _ _))
  unfold primeDilateCofactorWindowPrimeCount primeDilateCofactorWindow
  rw [Finset.Ioc_eq_empty_of_le hle]
  simp

/-- The zero-extended high-prime response itself vanishes above `sqrt R`. -/
theorem firstJumpHighPrimeCofactorResponse_eq_zero_of_sqrt_lt_cofactor
    {p R K X c : ℕ}
    (hXR : X ≤ R) (hsK : Nat.sqrt R ≤ K)
    (hcs : Nat.sqrt R < c) :
    firstJumpHighPrimeCofactorResponse p R K X c = 0 := by
  unfold firstJumpHighPrimeCofactorResponse
  by_cases hc : c ∈ primeDilateCofactorSupport p X
  · simp only [hc, if_true]
    rw [primeDilateCofactorWindowPrimeCount_eq_zero_of_sqrt_lt_cofactor
      hXR hcs (le_refl _),
      primeDilateCofactorWindowPrimeCount_eq_zero_of_sqrt_lt_cofactor
        hXR hcs hsK]
    ring
  · simp [hc]

/-- **High-prime band -> low-cofactor prime-window transform.**

The Mertens band is exactly Möbius parity paired with a zero-extended
cofactor response on the fixed carrier `1 <= c <= sqrt R`.  Cofactors above the
root cut have already vanished before this equality; no norm is taken. -/
theorem highPrimeBand_windowTransform
    {p R K X : ℕ} (hp : p.Prime)
    (hXR : X ≤ R) (hsK : Nat.sqrt R ≤ K) :
    firstJumpPrimeSieveMertensBand (Nat.sqrt R) K X =
      ∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight c *
          firstJumpHighPrimeCofactorResponse p R K X c := by
  have hfull :
      firstJumpPrimeSieveMertensBand (Nat.sqrt R) K X =
        ∑ c ∈ primeDilateCofactorSupport p X,
          firstJumpHighPrimeCofactorResponse p R K X c *
            canonicalMoebiusWeight c := by
    rw [firstJumpPrimeSieveMertensBand_eq_tail_sub_tail hsK,
      primeSieveMertensPrimeTail_eq_primeDilateCofactorPrimeCountTransform
        p (Nat.sqrt R) X hp,
      primeSieveMertensPrimeTail_eq_primeDilateCofactorPrimeCountTransform
        p K X hp]
    unfold primeDilateCofactorPrimeCountTransform
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    simp [firstJumpHighPrimeCofactorResponse, hc]
    ring
  have hrestricted :
      firstJumpPrimeSieveMertensBand (Nat.sqrt R) K X =
        ∑ c ∈ firstJumpHighPrimeCofactorSupport p R X,
          firstJumpHighPrimeCofactorResponse p R K X c *
            canonicalMoebiusWeight c := by
    rw [hfull]
    symm
    refine Finset.sum_subset Finset.inter_subset_left ?_
    intro c hcFull hcNotLow
    have hc1 : 1 ≤ c :=
      (mem_primeDilateCofactorSupport.mp hcFull).1
    have hcNotRoot : c ∉ Finset.Icc 1 (Nat.sqrt R) := by
      intro hcRoot
      exact hcNotLow (Finset.mem_inter.mpr ⟨hcFull, hcRoot⟩)
    have hcs : Nat.sqrt R < c := by
      by_contra hnot
      have hcle : c ≤ Nat.sqrt R := Nat.le_of_not_gt hnot
      exact hcNotRoot (Finset.mem_Icc.mpr ⟨hc1, hcle⟩)
    rw [firstJumpHighPrimeCofactorResponse_eq_zero_of_sqrt_lt_cofactor
      hXR hsK hcs]
    simp
  calc
    firstJumpPrimeSieveMertensBand (Nat.sqrt R) K X =
        ∑ c ∈ firstJumpHighPrimeCofactorSupport p R X,
          firstJumpHighPrimeCofactorResponse p R K X c *
            canonicalMoebiusWeight c := hrestricted
    _ = ∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
          firstJumpHighPrimeCofactorResponse p R K X c *
            canonicalMoebiusWeight c := by
      refine Finset.sum_subset Finset.inter_subset_right ?_
      intro c hcRoot hcNotActive
      have hcNotSupport : c ∉ primeDilateCofactorSupport p X := by
        intro hcSupport
        exact hcNotActive (Finset.mem_inter.mpr ⟨hcSupport, hcRoot⟩)
      simp [firstJumpHighPrimeCofactorResponse, hcNotSupport]
    _ = ∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
          canonicalMoebiusWeight c *
            firstJumpHighPrimeCofactorResponse p R K X c := by
      apply Finset.sum_congr rfl
      intro c _hc
      ring

/-- **Endpoint difference on one fixed low-cofactor carrier.**

This is the requested exact identity

`J = sum_{c <= sqrt R} mu(c) * Delta N(c)`

with inactive cofactors zero-extended. -/
theorem sqrtFirstJumpResidual_cast_eq_cofactorWindowDifference
    {p R q A B : ℕ} (hp : p.Prime)
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ) =
      ∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight c *
          (firstJumpHighPrimeCofactorResponse p R (q - 1) A c -
            firstJumpHighPrimeCofactorResponse p R (q - 1) B c) := by
  have hAR : A ≤ R := hAB.trans hBR
  have hsK : Nat.sqrt R ≤ q - 1 := by omega
  rw [sqrtFirstJumpResidual_cast_eq_band_sub_band hqroot hBR hAB,
    highPrimeBand_windowTransform hp hAR hsK,
    highPrimeBand_windowTransform hp hBR hsK,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  ring

/-- Increasing the prime cutoff only removes points from a fixed prime-dilate
window. -/
theorem primeDilateCofactorWindow_mono_cutoff
    {p s K X c : ℕ} (hsK : s ≤ K) :
    primeDilateCofactorWindow p K X c ⊆
      primeDilateCofactorWindow p s X c := by
  intro q hq
  rcases mem_primeDilateCofactorWindow.mp hq with ⟨hlo, hup⟩
  apply mem_primeDilateCofactorWindow.mpr
  refine ⟨?_, hup⟩
  unfold primeDilateCofactorWindowLower at hlo ⊢
  have hmax :
      max s (X / (p * c)) ≤ max K (X / (p * c)) := by
    exact max_le
      (hsK.trans (le_max_left _ _))
      (le_max_right _ _)
  exact hmax.trans_lt hlo

/-- Literal prime support of one cofactor's high-prime band. -/
def firstJumpHighPrimeCofactorWindowSet
    (p R K X c : ℕ) : Finset ℕ :=
  (primeDilateCofactorWindow p (Nat.sqrt R) X c \
      primeDilateCofactorWindow p K X c).filter Nat.Prime

/-- Prime-indicator mass of that literal support. -/
noncomputable def firstJumpHighPrimeCofactorWindowMass
    (p R K X c : ℕ) : ℂ :=
  ∑ q ∈ primeDilateCofactorWindow p (Nat.sqrt R) X c \
      primeDilateCofactorWindow p K X c,
    primeSievePrimeIndicator q

/-- On an active cofactor the response is exactly the set-difference window
mass. -/
theorem firstJumpHighPrimeCofactorResponse_eq_windowMass
    {p R K X c : ℕ}
    (hsK : Nat.sqrt R ≤ K)
    (hc : c ∈ primeDilateCofactorSupport p X) :
    firstJumpHighPrimeCofactorResponse p R K X c =
      firstJumpHighPrimeCofactorWindowMass p R K X c := by
  unfold firstJumpHighPrimeCofactorResponse
  simp only [hc, if_true]
  unfold firstJumpHighPrimeCofactorWindowMass
    primeDilateCofactorWindowPrimeCount
  have hsub :
      primeDilateCofactorWindow p K X c ⊆
        primeDilateCofactorWindow p (Nat.sqrt R) X c :=
    primeDilateCofactorWindow_mono_cutoff hsK
  have hs := Finset.sum_sdiff hsub (f := primeSievePrimeIndicator)
  rw [sub_eq_iff_eq_add]
  exact hs.symm

/-- The window mass is literally the cardinality of its prime support. -/
theorem firstJumpHighPrimeCofactorWindowMass_eq_card
    (p R K X c : ℕ) :
    firstJumpHighPrimeCofactorWindowMass p R K X c =
      (((firstJumpHighPrimeCofactorWindowSet p R K X c).card : ℕ) : ℂ) := by
  unfold firstJumpHighPrimeCofactorWindowMass
    firstJumpHighPrimeCofactorWindowSet
  simp [primeSievePrimeIndicator, Finset.sum_boole]

/-- Zero-extended literal prime support, matching the zero extension in the
cofactor response. -/
def firstJumpHighPrimeCofactorActiveWindowSet
    (p R K X c : ℕ) : Finset ℕ :=
  if c ∈ primeDilateCofactorSupport p X then
    firstJumpHighPrimeCofactorWindowSet p R K X c
  else
    ∅

/-- For every cofactor, active or absent, the response is exactly the cardinality
of its zero-extended literal prime support. -/
theorem firstJumpHighPrimeCofactorResponse_eq_activeWindowSet_card
    {p R K X c : ℕ} (hsK : Nat.sqrt R ≤ K) :
    firstJumpHighPrimeCofactorResponse p R K X c =
      (((firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card : ℕ) : ℂ) := by
  by_cases hc : c ∈ primeDilateCofactorSupport p X
  · rw [firstJumpHighPrimeCofactorResponse_eq_windowMass hsK hc,
      firstJumpHighPrimeCofactorWindowMass_eq_card]
    simp [firstJumpHighPrimeCofactorActiveWindowSet, hc]
  · simp [firstJumpHighPrimeCofactorResponse,
      firstJumpHighPrimeCofactorActiveWindowSet, hc]

/-- The endpoint identity with `Delta N(c)` literally displayed as a difference
of two prime-set cardinalities. -/
theorem sqrtFirstJumpResidual_cast_eq_cofactorWindowCardDifference
    {p R q A B : ℕ} (hp : p.Prime)
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ) =
      ∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight c *
          ((((firstJumpHighPrimeCofactorActiveWindowSet
              p R (q - 1) A c).card : ℕ) : ℂ) -
            (((firstJumpHighPrimeCofactorActiveWindowSet
              p R (q - 1) B c).card : ℕ) : ℂ)) := by
  rw [sqrtFirstJumpResidual_cast_eq_cofactorWindowDifference
    hp hqroot hBR hAB]
  have hsK : Nat.sqrt R ≤ q - 1 := by omega
  apply Finset.sum_congr rfl
  intro c _hc
  rw [firstJumpHighPrimeCofactorResponse_eq_activeWindowSet_card hsK,
    firstJumpHighPrimeCofactorResponse_eq_activeWindowSet_card hsK]

/-! ## Local first-jump packing -/

/-- Every active window point carries a prime strictly above the square-root
cut and its cofactor product stays below the physical endpoint. -/
theorem firstJumpHighPrimeCofactorActiveWindowSet_data
    {p R K X c q : ℕ}
    (hcRoot : c ∈ Finset.Icc 1 (Nat.sqrt R))
    (hq : q ∈ firstJumpHighPrimeCofactorActiveWindowSet p R K X c) :
    q.Prime ∧ Nat.sqrt R < q ∧ c * q ≤ X := by
  by_cases hcSupport : c ∈ primeDilateCofactorSupport p X
  · have hq' : q ∈ firstJumpHighPrimeCofactorWindowSet p R K X c := by
      simpa [firstJumpHighPrimeCofactorActiveWindowSet, hcSupport] using hq
    rcases Finset.mem_filter.mp hq' with ⟨hqDiff, hqPrime⟩
    have hqWindow := (Finset.mem_sdiff.mp hqDiff).1
    rcases mem_primeDilateCofactorWindow.mp hqWindow with ⟨hlo, hup⟩
    have hsltq : Nat.sqrt R < q := by
      have hsle :
          Nat.sqrt R ≤
            primeDilateCofactorWindowLower p (Nat.sqrt R) X c := by
        unfold primeDilateCofactorWindowLower
        exact le_max_left _ _
      exact hsle.trans_lt hlo
    have hcpos : 0 < c := by
      have hc1 := (Finset.mem_Icc.mp hcRoot).1
      omega
    unfold primeDilateCofactorWindowUpper at hup
    have hqcX : q * c ≤ X :=
      (Nat.le_div_iff_mul_le hcpos).1 hup
    exact ⟨hqPrime, hsltq, by simpa [Nat.mul_comm] using hqcX⟩
  · simp [firstJumpHighPrimeCofactorActiveWindowSet, hcSupport] at hq

/-- Product image of one active cofactor window. -/
def firstJumpHighPrimeCofactorProductSet
    (p R K X c : ℕ) : Finset ℕ :=
  (firstJumpHighPrimeCofactorActiveWindowSet p R K X c).image
    (fun q => c * q)

/-- Multiplication by a positive cofactor preserves the active-window
cardinality. -/
theorem firstJumpHighPrimeCofactorProductSet_card
    {p R K X c : ℕ} (hcpos : 0 < c) :
    (firstJumpHighPrimeCofactorProductSet p R K X c).card =
      (firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card := by
  unfold firstJumpHighPrimeCofactorProductSet
  rw [Finset.card_image_of_injective _
    (fun a b hab => Nat.eq_of_mul_eq_mul_left hcpos hab)]

/-- Distinct low cofactors have disjoint product images.  The reason is
canonical rather than probabilistic: if `c <= sqrt R < q`, then `q` is the
canonical largest prime factor of `c*q`, so the product itself recovers both
`q` and then `c`. -/
theorem firstJumpHighPrimeCofactorProductSet_pairwiseDisjoint
    (p R K X : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 (Nat.sqrt R)))
      (firstJumpHighPrimeCofactorProductSet p R K X) := by
  intro c hc d hd hcd
  have hcRoot : c ∈ Finset.Icc 1 (Nat.sqrt R) := by simpa using hc
  have hdRoot : d ∈ Finset.Icc 1 (Nat.sqrt R) := by simpa using hd
  change Disjoint
    (firstJumpHighPrimeCofactorProductSet p R K X c)
    (firstJumpHighPrimeCofactorProductSet p R K X d)
  rw [Finset.disjoint_left]
  intro n hnc hnd
  rcases Finset.mem_image.mp hnc with ⟨q, hq, hcq⟩
  rcases Finset.mem_image.mp hnd with ⟨r, hr, hdr⟩
  rcases firstJumpHighPrimeCofactorActiveWindowSet_data hcRoot hq with
    ⟨hqPrime, hsq, _hcqX⟩
  rcases firstJumpHighPrimeCofactorActiveWindowSet_data hdRoot hr with
    ⟨hrPrime, hsr, _hdrX⟩
  have hcData := Finset.mem_Icc.mp hcRoot
  have hdData := Finset.mem_Icc.mp hdRoot
  have hcpos : 0 < c := by omega
  have hdpos : 0 < d := by omega
  have hcLtq : c < q := hcData.2.trans_lt hsq
  have hdLtr : d < r := hdData.2.trans_lt hsr
  have hqTop : canonicalLargestPrimeFactor (c * q) = q :=
    canonicalLargestPrimeFactor_mul_prime_eq hcpos hcLtq hqPrime
  have hrTop : canonicalLargestPrimeFactor (d * r) = r :=
    canonicalLargestPrimeFactor_mul_prime_eq hdpos hdLtr hrPrime
  have hprod : c * q = d * r := hcq.trans hdr.symm
  have hqr : q = r := by
    calc
      q = canonicalLargestPrimeFactor (c * q) := hqTop.symm
      _ = canonicalLargestPrimeFactor (d * r) := by rw [hprod]
      _ = r := hrTop
  subst r
  have hcdEq : c = d :=
    Nat.eq_of_mul_eq_mul_right hqPrime.pos hprod
  exact hcd hcdEq

/-- Every packed product lies in the ordinary positive prefix through `X`. -/
theorem firstJumpHighPrimeCofactorProductSet_subset_Icc
    {p R K X c : ℕ}
    (hcRoot : c ∈ Finset.Icc 1 (Nat.sqrt R)) :
    firstJumpHighPrimeCofactorProductSet p R K X c ⊆
      Finset.Icc 1 X := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
  rcases firstJumpHighPrimeCofactorActiveWindowSet_data hcRoot hq with
    ⟨hqPrime, _hsq, hcqX⟩
  have hc1 := (Finset.mem_Icc.mp hcRoot).1
  have hcpos : 0 < c := by omega
  have hprodpos : 0 < c * q := Nat.mul_pos hcpos hqPrime.pos
  exact Finset.mem_Icc.mpr ⟨by omega, hcqX⟩

/-- The union of all packed low-cofactor windows is contained in `[1,X]`. -/
theorem firstJumpHighPrimeCofactorProductUnion_subset_Icc
    (p R K X : ℕ) :
    (Finset.Icc 1 (Nat.sqrt R)).biUnion
        (firstJumpHighPrimeCofactorProductSet p R K X) ⊆
      Finset.Icc 1 X := by
  intro n hn
  rcases Finset.mem_biUnion.mp hn with ⟨c, hc, hnc⟩
  exact firstJumpHighPrimeCofactorProductSet_subset_Icc hc hnc

/-- **Local packing bound.**  Across all `c <= sqrt R`, the active high-prime
windows inject into the ordinary integers through `q |-> c*q`.  Hence their
total cardinality is at most the endpoint `X`. -/
theorem sum_firstJumpHighPrimeCofactorActiveWindowSet_card_le_endpoint
    (p R K X : ℕ) :
    (∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        (firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card) ≤ X := by
  let S := Finset.Icc 1 (Nat.sqrt R)
  let F := firstJumpHighPrimeCofactorProductSet p R K X
  have hpair : Set.PairwiseDisjoint (↑S) F := by
    simpa [S, F] using
      firstJumpHighPrimeCofactorProductSet_pairwiseDisjoint p R K X
  have hunion :
      (S.biUnion F).card = ∑ c ∈ S, (F c).card := by
    have h := Finset.sum_biUnion hpair (f := fun _ : ℕ => (1 : ℕ))
    simpa using h
  have hsubset : S.biUnion F ⊆ Finset.Icc 1 X := by
    simpa [S, F] using
      firstJumpHighPrimeCofactorProductUnion_subset_Icc p R K X
  calc
    (∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        (firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card) =
      ∑ c ∈ S, (F c).card := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcpos : 0 < c := by
          have hc1 := (Finset.mem_Icc.mp (by simpa [S] using hc)).1
          omega
        symm
        exact firstJumpHighPrimeCofactorProductSet_card hcpos
    _ = (S.biUnion F).card := hunion.symm
    _ ≤ (Finset.Icc 1 X).card := Finset.card_le_card hsubset
    _ = X := by
      rw [Nat.card_Icc]
      omega

/-- One high-prime Mertens band is itself bounded by its physical endpoint.
This is a consequence of the packing theorem, not cancellation between
cofactors. -/
theorem norm_firstJumpPrimeSieveMertensBand_le_endpoint
    {p R K X : ℕ} (hp : p.Prime)
    (hXR : X ≤ R) (hsK : Nat.sqrt R ≤ K) :
    ‖firstJumpPrimeSieveMertensBand (Nat.sqrt R) K X‖ ≤ (X : ℝ) := by
  rw [highPrimeBand_windowTransform hp hXR hsK]
  simp_rw [firstJumpHighPrimeCofactorResponse_eq_activeWindowSet_card hsK]
  have hpack :=
    sum_firstJumpHighPrimeCofactorActiveWindowSet_card_le_endpoint p R K X
  have hpackR :
      (∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        ((firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card : ℝ)) ≤
        (X : ℝ) := by
    exact_mod_cast hpack
  calc
    ‖∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight c *
          (((firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card : ℕ) : ℂ)‖ ≤
      ∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        ‖canonicalMoebiusWeight c *
          (((firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card : ℕ) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c ∈ Finset.Icc 1 (Nat.sqrt R),
        ((firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card : ℝ) := by
      apply Finset.sum_le_sum
      intro c _hc
      rw [norm_mul]
      have hmu : ‖canonicalMoebiusWeight c‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or c with h | h | h <;>
          simp [canonicalMoebiusWeight, h]
      have hcardnorm :
          ‖(((firstJumpHighPrimeCofactorActiveWindowSet
              p R K X c).card : ℕ) : ℂ)‖ =
            ((firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card : ℝ) := by
        simp
      rw [hcardnorm]
      have hcardNonneg :
          (0 : ℝ) ≤
            ((firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card : ℝ) := by
        exact_mod_cast (Nat.zero_le
          (firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card)
      simpa using mul_le_mul_of_nonneg_right hmu hcardNonneg
    _ ≤ (X : ℝ) := hpackR

/-- **Local first-jump residual is linear.**  The complete signed residual of
one frozen state costs at most `2R`; this is stronger than the RH-scale epsilon
bound and uses no prime-distribution estimate. -/
theorem norm_sqrtFirstJumpResidual_cast_le_two_mul_root
    {R q A B : ℕ}
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ‖((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ)‖ ≤
      2 * (R : ℝ) := by
  have hAR : A ≤ R := hAB.trans hBR
  have hsK : Nat.sqrt R ≤ q - 1 := by omega
  rw [sqrtFirstJumpResidual_cast_eq_band_sub_band hqroot hBR hAB]
  calc
    ‖firstJumpPrimeSieveMertensBand (Nat.sqrt R) (q - 1) A -
        firstJumpPrimeSieveMertensBand (Nat.sqrt R) (q - 1) B‖ ≤
      ‖firstJumpPrimeSieveMertensBand (Nat.sqrt R) (q - 1) A‖ +
        ‖firstJumpPrimeSieveMertensBand (Nat.sqrt R) (q - 1) B‖ :=
      norm_sub_le _ _
    _ ≤ (A : ℝ) + (B : ℝ) :=
      add_le_add
        (norm_firstJumpPrimeSieveMertensBand_le_endpoint
          Nat.prime_two hAR hsK)
        (norm_firstJumpPrimeSieveMertensBand_le_endpoint
          Nat.prime_two hBR hsK)
    _ ≤ 2 * (R : ℝ) := by
      have hsum : A + B ≤ 2 * R := by omega
      exact_mod_cast hsum

/-! ## Signed lift to the global oriented state carrier -/

open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

/-- The dense side of one state after square-root contraction.  High-owner
states are replaced by the complete `primesUpTo (sqrt R)` frozen cube; states
whose owner is not above the contraction wall are left unchanged. -/
noncomputable def lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
      Nat.sqrt R < lowWheelCanonicalDowncrossPivot x then
    canonicalMoebiusWeight x.1 *
      ((frozenPrimeUniverseWindowMass
        (primesUpTo (Nat.sqrt R))
        (R / x.2)
        (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2) : ℤ) : ℂ)
  else
    lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x

/-- The signed first-jump component of one state.  It is zero unless the
canonical owner lies above the square-root contraction wall. -/
noncomputable def lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
      Nat.sqrt R < lowWheelCanonicalDowncrossPivot x then
    canonicalMoebiusWeight x.1 *
      ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R)
        (primesUpTo (lowWheelCanonicalDowncrossPivot x - 1))
        (R / x.2)
        (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2) : ℤ) : ℂ)
  else
    0

/-- **Statewise square-root contraction with signs intact.** -/
theorem lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_sqrtDense_add_firstJump
    (R : ℕ) (x : LowWheelCofactorQuotientState) :
    lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x =
      lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre R x +
        lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x := by
  by_cases h : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
      Nat.sqrt R < lowWheelCanonicalDowncrossPivot x
  · rcases x with ⟨c, k⟩
    have hne := h.1
    have hqroot := h.2
    have hupper : lowWheelCanonicalDowncrossOwnershipUpper R c k ≤ R := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_left _ _).trans (Nat.div_le_self _ _)
    have hsplit :=
      frozenPrimeUniverseWindowMass_eq_sqrtContraction_add_firstJump
        R (lowWheelCanonicalDowncrossPivot (c, k))
        (R / k) (lowWheelCanonicalDowncrossOwnershipUpper R c k)
        hqroot hupper
    have hcast := congrArg (fun z : ℤ => (z : ℂ)) hsplit
    push_cast at hcast
    unfold lowWheelCanonicalDowncrossOrientedFrozenStateFibre
      lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre
      lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre
    rw [if_pos hne, if_pos h, if_pos h]
    rw [hcast]
    ring
  · simp [lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre,
      lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre, h]

/-- The complete oriented ledger is the signed dense aggregate plus the signed
first-jump aggregate.  No norm is taken over the state carrier. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sqrtDense_add_firstJump
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre R x) +
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x := by
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_frozenStateFibres]
  calc
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        (lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre R x +
          lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_sqrtDense_add_firstJump]
    _ = _ := by rw [Finset.sum_add_distrib]

/-- **True global run object after local contraction.**  Both endpoint ledgers
live on the same canonical physical-state carrier.  The RH-hard quantity is the
outer signed aggregation of the dense differences and first-jump differences;
no local `O(R)` estimate has been summed by triangle inequality. -/
theorem canonicalOrientedRunDifference_eq_sqrtDenseDifference_add_firstJumpDifference
    (a b : ℕ) :
    canonicalOrientedRunDifference a b =
      (∑ x ∈ canonicalOrientedRunStateCarrier a b,
        (lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre (b + 1) x -
          lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre a x)) +
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        (lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre (b + 1) x -
          lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre a x) := by
  rw [canonicalOrientedRunDifference_eq_sum_frozenStateFibreDifferences]
  calc
    (∑ x ∈ canonicalOrientedRunStateCarrier a b,
        (lowWheelCanonicalDowncrossOrientedFrozenStateFibre (b + 1) x -
          lowWheelCanonicalDowncrossOrientedFrozenStateFibre a x)) =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        ((lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre (b + 1) x -
            lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre a x) +
          (lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre (b + 1) x -
            lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre a x)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_sqrtDense_add_firstJump,
          lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_sqrtDense_add_firstJump]
        ring
    _ = _ := by rw [Finset.sum_add_distrib]

/-- **Comparison with the existing canonical rough-prime carrier.**

At `X <= R`, every prime in an active first-jump cofactor window is already a
canonical rough-prime partner at the next complete-square root `sqrt R + 1`.
The new response is therefore a windowed subcarrier of the existing rough
response field, not a new covariance object. -/
theorem firstJumpHighPrimeCofactorWindowSet_subset_canonicalRoughPrimePartnerSet
    {p R K X c : ℕ} (hR : 0 < R) (hXR : X ≤ R)
    (hc : c ∈ firstJumpHighPrimeCofactorSupport p R X) :
    firstJumpHighPrimeCofactorWindowSet p R K X c ⊆
      squareRootCanonicalRoughPrimePartnerSet (Nat.sqrt R + 1) c := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqDiff, hqPrime⟩
  have hqWindow := (Finset.mem_sdiff.mp hqDiff).1
  rcases mem_primeDilateCofactorWindow.mp hqWindow with ⟨hlo, hup⟩
  rcases Finset.mem_inter.mp hc with ⟨hcSupport, hcRoot⟩
  rcases mem_primeDilateCofactorSupport.mp hcSupport with
    ⟨hc1, _hcX, _hfree⟩
  have hcpos : 0 < c := by omega
  have hcle : c ≤ Nat.sqrt R :=
    (Finset.mem_Icc.mp hcRoot).2
  have hsltq : Nat.sqrt R < q := by
    have hsLower :
        Nat.sqrt R ≤
          primeDilateCofactorWindowLower p (Nat.sqrt R) X c := by
      unfold primeDilateCofactorWindowLower
      exact le_max_left _ _
    exact hsLower.trans_lt hlo
  have hrough : canonicalLargestPrimeFactor c < q := by
    by_cases hcEq : c = 1
    · subst c
      simpa [canonicalLargestPrimeFactor] using hqPrime.one_lt
    · have hcgt : 1 < c := by omega
      exact
        (Nat.le_of_dvd (by omega) (canonicalLargestPrimeFactor_dvd hcgt)).trans_lt
          (hcle.trans_lt hsltq)
  unfold primeDilateCofactorWindowUpper at hup
  have hqcX : q * c ≤ X :=
    (Nat.le_div_iff_mul_le hcpos).1 hup
  have hcqX : c * q ≤ X := by
    simpa [Nat.mul_comm] using hqcX
  have hqRoot : Nat.sqrt R + 1 ≤ q := by omega
  have hrootProduct : Nat.sqrt R + 1 ≤ c * q := by
    have hqle : q ≤ c * q := by
      simpa using Nat.mul_le_mul_right q hc1
    exact hqRoot.trans hqle
  have hclock : R < (Nat.sqrt R + 1) ^ 2 := Nat.lt_succ_sqrt' R
  have hRupper : R ≤ squareRootEndpoint (Nat.sqrt R + 1) := by
    unfold squareRootEndpoint
    omega
  have hcqUpper : c * q ≤ squareRootEndpoint (Nat.sqrt R + 1) :=
    hcqX.trans (hXR.trans hRupper)
  have hspos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 hR
  have hrootTwo : 2 ≤ Nat.sqrt R + 1 := by omega
  exact
    (mem_squareRootCanonicalRoughPrimePartnerSet_iff hrootTwo hcpos).2
      ⟨hqPrime, hrough, hrootProduct, hcqUpper⟩

/-- The zero-extended window of every cofactor in the signed `c <= sqrt R`
carrier is a subcarrier of the already-existing canonical rough response. -/
theorem firstJumpHighPrimeCofactorActiveWindowSet_subset_canonicalRoughPrimePartnerSet
    {p R K X c : ℕ} (hR : 0 < R) (hXR : X ≤ R)
    (hcRoot : c ∈ Finset.Icc 1 (Nat.sqrt R)) :
    firstJumpHighPrimeCofactorActiveWindowSet p R K X c ⊆
      squareRootCanonicalRoughPrimePartnerSet (Nat.sqrt R + 1) c := by
  by_cases hcSupport : c ∈ primeDilateCofactorSupport p X
  · have hcActive : c ∈ firstJumpHighPrimeCofactorSupport p R X :=
      Finset.mem_inter.mpr ⟨hcSupport, hcRoot⟩
    simpa [firstJumpHighPrimeCofactorActiveWindowSet, hcSupport] using
      (firstJumpHighPrimeCofactorWindowSet_subset_canonicalRoughPrimePartnerSet
        hR hXR hcActive)
  · simp [firstJumpHighPrimeCofactorActiveWindowSet, hcSupport]

/-- Cardinality comparison with the existing canonical rough-prime partner
response.  Exact equality is not asserted: the first-jump object retains the
extra high-prime-band and prime-dilate child-outside walls. -/
theorem firstJumpHighPrimeCofactorActiveWindowSet_card_le_canonicalRoughPrimePartnerSet
    {p R K X c : ℕ} (hR : 0 < R) (hXR : X ≤ R)
    (hcRoot : c ∈ Finset.Icc 1 (Nat.sqrt R)) :
    (firstJumpHighPrimeCofactorActiveWindowSet p R K X c).card ≤
      (squareRootCanonicalRoughPrimePartnerSet (Nat.sqrt R + 1) c).card :=
  Finset.card_le_card
    (firstJumpHighPrimeCofactorActiveWindowSet_subset_canonicalRoughPrimePartnerSet
      hR hXR hcRoot)

end RHLean.Proof