import Mathlib
import RHLean.Proof.CanonicalRoughQuantitativeContraction

/-!
# Critical correlation contraction and exact Abel return

The centered reciprocal covariance coordinate is useful for exposing the local
Euler contraction, but the protected RH-critical object is the *uncentered*
canonical rough correlation

`Corr_R = sum_c mu(c) * Response_R(c)`.

The repository already proves

`Corr_R = M(R - 1) - M(X_R)`

and that critical control of `Corr_R` is equivalent to the square-prefix
Mertens energy criterion.  Consequently the zero mode must be recoupled before
the quantitative return.

This file performs that recoupling without changing the physical defect.  The
reciprocal parity zero mode `mu(c)/c` obeys the same pure Euler factor as the
centered response coordinate, with no defect.  Adding back the response mean
therefore gives the uncentered reciprocal correlation coordinate with exactly
the same threshold/top-escape/birth defect law.

The file then iterates the one-prime carrier theorem on the *actual compressed
parent carriers*.  Unpaired states are retained in an explicit transported
survivor ledger.  Thus the many-prime theorem does not pretend that an
arbitrary carrier is uniformly multiplied by the Euler product.

Finally finite Abel summation returns the uncentered reciprocal-prefix profile
directly to `squareRootCanonicalRoughCorrelation`, and a large critical
correlation is shown to force a large reciprocal prefix.  This is the exact
PNT-style excursion trigger needed for a subsequent arithmetic defect/survivor
estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-! ## Recouple the parity zero mode -/

/-- Reciprocal Möbius parity coordinate. -/
def squareRootCanonicalRoughParityReciprocalSummand (c : ℕ) : ℂ :=
  canonicalMoebiusWeight c / (c : ℂ)

/-- The RH-critical reciprocal correlation coordinate.  It is deliberately
defined by adding the parity zero mode back to the centered coordinate. -/
def squareRootCanonicalRoughCorrelationReciprocalSummand
    (R c : ℕ) : ℂ :=
  squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
    squareRootCanonicalRoughResponseMean R *
      squareRootCanonicalRoughParityReciprocalSummand c

/-- The recoupled reciprocal coordinate is literally the uncentered
Möbius-response summand divided by its cofactor. -/
theorem squareRootCanonicalRoughCorrelationReciprocalSummand_eq_weighted_response_div
    (R : ℕ) {c : ℕ} (hc : 0 < c) :
    squareRootCanonicalRoughCorrelationReciprocalSummand R c =
      (canonicalMoebiusWeight c *
        squareRootCanonicalRoughCofactorResponse R c) / (c : ℂ) := by
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hc)
  unfold squareRootCanonicalRoughCorrelationReciprocalSummand
    squareRootCanonicalRoughResponseCenteredReciprocalSummand
    squareRootCanonicalRoughResponseCenteredSummand
    squareRootCanonicalRoughParityReciprocalSummand
  field_simp [hc0]
  ring

/-- The reciprocal parity zero mode has the pure native-PNT Euler contraction
and introduces no physical defect. -/
theorem squareRootCanonicalRoughParityReciprocalSummand_add_mul_freshPrime
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughParityReciprocalSummand c +
        squareRootCanonicalRoughParityReciprocalSummand (c * p) =
      (1 - 1 / (p : ℂ)) *
        squareRootCanonicalRoughParityReciprocalSummand c := by
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hc)
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  unfold squareRootCanonicalRoughParityReciprocalSummand
  rw [canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hp hfresh]
  push_cast
  field_simp [hc0, hp0]
  ring

/-- Real Euler factor cast to the complex scalar used by the carrier sums. -/
theorem canonicalRoughEulerFactor_cast_complex (p : ℕ) :
    ((canonicalRoughEulerFactor p : ℝ) : ℂ) =
      1 - 1 / (p : ℂ) := by
  simp [canonicalRoughEulerFactor]

/-- **Exact fresh-prime Euler law on the RH-critical uncentered correlation.**
The parity mean recouples with the centered coordinate and disappears into the
same Euler factor.  The physical defect is exactly the one already formalized
in an earlier layer. -/
theorem squareRootCanonicalRoughCorrelationReciprocalSummand_add_mul_freshPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughCorrelationReciprocalSummand R c +
        squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) =
      (canonicalRoughEulerFactor p : ℂ) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R c +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p := by
  unfold squareRootCanonicalRoughCorrelationReciprocalSummand
  have hcenter :=
    squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime
      hR hc hp hfresh
  have hparity :=
    squareRootCanonicalRoughParityReciprocalSummand_add_mul_freshPrime
      hc hp hfresh
  rw [canonicalRoughEulerFactor_cast_complex]
  calc
    squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
          squareRootCanonicalRoughResponseMean R *
            squareRootCanonicalRoughParityReciprocalSummand c +
        (squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p) +
          squareRootCanonicalRoughResponseMean R *
            squareRootCanonicalRoughParityReciprocalSummand (c * p)) =
      (squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p)) +
        squareRootCanonicalRoughResponseMean R *
          (squareRootCanonicalRoughParityReciprocalSummand c +
            squareRootCanonicalRoughParityReciprocalSummand (c * p)) := by ring
    _ = ((1 - 1 / (p : ℂ)) *
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) +
        squareRootCanonicalRoughResponseMean R *
          ((1 - 1 / (p : ℂ)) *
            squareRootCanonicalRoughParityReciprocalSummand c) := by
      rw [hcenter, hparity]
    _ = (1 - 1 / (p : ℂ)) *
          (squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
            squareRootCanonicalRoughResponseMean R *
              squareRootCanonicalRoughParityReciprocalSummand c) +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p := by ring

/-! ## One physical prime on the complete active carrier -/

/-- The complete paired population of the uncentered reciprocal correlation
compresses to the parent carrier plus the same signed physical defect mass. -/
theorem sum_squareRootCanonicalRoughFreshPrimePairedOn_correlationReciprocal
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      (canonicalRoughEulerFactor p : ℂ) *
        (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U := by
  unfold squareRootCanonicalRoughFreshPrimePairedOn
  rw [Finset.sum_union
    (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_childrenOn U hp)]
  unfold squareRootCanonicalRoughFreshPrimeChildrenOn
  rw [Finset.sum_image]
  · rw [← Finset.sum_add_distrib]
    calc
      (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          (squareRootCanonicalRoughCorrelationReciprocalSummand R c +
            squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p))) =
        ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          ((canonicalRoughEulerFactor p : ℂ) *
              squareRootCanonicalRoughCorrelationReciprocalSummand R c +
            squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) := by
        apply Finset.sum_congr rfl
        intro c hcParent
        rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
          ⟨_hcU, hcpos, hcrough, _hcchild⟩
        exact
          squareRootCanonicalRoughCorrelationReciprocalSummand_add_mul_freshPrime
            hR hcpos hp hcrough
      _ = (canonicalRoughEulerFactor p : ℂ) *
          (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U := by
        rw [Finset.sum_add_distrib]
        unfold squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass
        rw [Finset.mul_sum]
  · intro a _ha b _hb hab
    exact Nat.mul_right_cancel hp.pos hab

/-- **One exact physical compression step on the RH-critical reciprocal
correlation carrier.**  Unpaired states remain visible as a survivor mass. -/
theorem sum_squareRootCanonicalRoughCorrelationReciprocal_eq_compressed_add_defect_add_survivors
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ n ∈ U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      (canonicalRoughEulerFactor p : ℂ) *
        (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n := by
  have hsub := squareRootCanonicalRoughFreshPrimePairedOn_subset p U
  have hsplit :
      (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
        (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
        ∑ n ∈ U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n := by
    simpa [squareRootCanonicalRoughFreshPrimeSurvivorsOn] using
      (Finset.sum_sdiff hsub
        (f := squareRootCanonicalRoughCorrelationReciprocalSummand R))
  rw [sum_squareRootCanonicalRoughFreshPrimePairedOn_correlationReciprocal
    R U hR hp] at hsplit
  calc
    (∑ n ∈ U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
        ((canonicalRoughEulerFactor p : ℂ) *
          (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U) :=
      hsplit.symm
    _ = (canonicalRoughEulerFactor p : ℂ) *
        (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n := by ring

/-! ## Actual many-prime parent-carrier recursion -/

/-- Physical step list generated by repeatedly compressing onto the parent
carrier.  The active carrier stored in each step is exactly the carrier on
which that prime's signed physical defect is evaluated. -/
def squareRootCanonicalRoughCompressionRunSteps :
    List ℕ → Finset ℕ → List CanonicalRoughPhysicalEulerStep
  | [], _U => []
  | p :: ps, U =>
      (p, U) ::
        squareRootCanonicalRoughCompressionRunSteps ps
          (squareRootCanonicalRoughFreshPrimeParentsOn p U)

/-- Parent carrier remaining after all requested compression primes. -/
def squareRootCanonicalRoughCompressionFinalParents :
    List ℕ → Finset ℕ → Finset ℕ
  | [], U => U
  | p :: ps, U =>
      squareRootCanonicalRoughCompressionFinalParents ps
        (squareRootCanonicalRoughFreshPrimeParentsOn p U)

/-- Survivor mass created along the actual parent-carrier recursion, transported
by all earlier/larger Euler factors. -/
def squareRootCanonicalRoughCorrelationTransportedSurvivorLedger
    (R : ℕ) : List ℕ → Finset ℕ → ℂ
  | [], _U => 0
  | p :: ps, U =>
      (canonicalRoughEulerFactor p : ℂ) *
        squareRootCanonicalRoughCorrelationTransportedSurvivorLedger
          R ps (squareRootCanonicalRoughFreshPrimeParentsOn p U) +
      ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n

/-- Every step in the actual compression run inherits primality from the input
prime list. -/
theorem squareRootCanonicalRoughCompressionRunSteps_prime
    (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    ∀ step ∈ squareRootCanonicalRoughCompressionRunSteps ps U,
      step.1.Prime := by
  induction ps generalizing U with
  | nil => simp [squareRootCanonicalRoughCompressionRunSteps]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      intro step hstep
      simp only [squareRootCanonicalRoughCompressionRunSteps,
        List.mem_cons] at hstep
      rcases hstep with hhead | htail
      · subst step
        exact hp
      · exact ih (squareRootCanonicalRoughFreshPrimeParentsOn p U) hps
          step htail

/-- **Exact many-prime compression on the actual RH-critical carrier.**

The initial reciprocal correlation mass is the Euler-product-scaled mass on the
final compressed parent carrier, plus the transported signed physical defect
ledger, plus the transported survivor ledger.  No survivor is silently assigned
an Euler factor it did not receive. -/
theorem sum_squareRootCanonicalRoughCorrelationReciprocal_eq_manyPrimeCompression
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      (canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps U) : ℂ) *
        (∑ n ∈ squareRootCanonicalRoughCompressionFinalParents ps U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
      squareRootCanonicalRoughTransportedDefectLedger R
        (squareRootCanonicalRoughCompressionRunSteps ps U) +
      squareRootCanonicalRoughCorrelationTransportedSurvivorLedger R ps U := by
  induction ps generalizing U with
  | nil =>
      simp [squareRootCanonicalRoughCompressionRunSteps,
        squareRootCanonicalRoughCompressionFinalParents,
        canonicalRoughEulerProduct,
        squareRootCanonicalRoughTransportedDefectLedger,
        squareRootCanonicalRoughCorrelationTransportedSurvivorLedger]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      rw [sum_squareRootCanonicalRoughCorrelationReciprocal_eq_compressed_add_defect_add_survivors
        R U hR hp]
      rw [ih (U := squareRootCanonicalRoughFreshPrimeParentsOn p U) hps]
      simp only [squareRootCanonicalRoughCompressionRunSteps,
        squareRootCanonicalRoughCompressionFinalParents,
        canonicalRoughEulerProduct,
        squareRootCanonicalRoughTransportedDefectLedger,
        squareRootCanonicalRoughPhysicalStepDefect,
        squareRootCanonicalRoughCorrelationTransportedSurvivorLedger]
      push_cast
      ring

/-- **Quantitative many-prime carrier contraction.**  The exact decomposition
above, together with the Euler telescope from `CanonicalRoughQuantitativeContraction`,
bounds the initial reciprocal correlation profile by three honest terms:
contracted final parents, the scaled signed physical defect floor, and the
transported unpaired survivor ledger. -/
theorem norm_sum_squareRootCanonicalRoughCorrelationReciprocal_le_manyPrimeCompression
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    ‖∑ n ∈ U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n‖ ≤
      canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps U) *
        ‖∑ n ∈ squareRootCanonicalRoughCompressionFinalParents ps U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n‖ +
      (1 - canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps U)) *
        squareRootCanonicalRoughScaledSignedDefectFloor R
          (squareRootCanonicalRoughCompressionRunSteps ps U) +
      ‖squareRootCanonicalRoughCorrelationTransportedSurvivorLedger R ps U‖ := by
  have hrunPrime :=
    squareRootCanonicalRoughCompressionRunSteps_prime ps U hprime
  have hP0 := canonicalRoughEulerProduct_nonneg
    (squareRootCanonicalRoughCompressionRunSteps ps U) hrunPrime
  have hledger := squareRootCanonicalRoughTransportedDefectLedger_norm_le
    R (squareRootCanonicalRoughCompressionRunSteps ps U) hrunPrime
  rw [sum_squareRootCanonicalRoughCorrelationReciprocal_eq_manyPrimeCompression
    R hR ps U hprime]
  calc
    ‖(canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps U) : ℂ) *
          (∑ n ∈ squareRootCanonicalRoughCompressionFinalParents ps U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
        squareRootCanonicalRoughTransportedDefectLedger R
          (squareRootCanonicalRoughCompressionRunSteps ps U) +
        squareRootCanonicalRoughCorrelationTransportedSurvivorLedger R ps U‖ ≤
      ‖(canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps U) : ℂ) *
          (∑ n ∈ squareRootCanonicalRoughCompressionFinalParents ps U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R n)‖ +
        ‖squareRootCanonicalRoughTransportedDefectLedger R
          (squareRootCanonicalRoughCompressionRunSteps ps U)‖ +
        ‖squareRootCanonicalRoughCorrelationTransportedSurvivorLedger R ps U‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_right (norm_add_le _ _) _)
    _ = canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps U) *
          ‖∑ n ∈ squareRootCanonicalRoughCompressionFinalParents ps U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R n‖ +
        ‖squareRootCanonicalRoughTransportedDefectLedger R
          (squareRootCanonicalRoughCompressionRunSteps ps U)‖ +
        ‖squareRootCanonicalRoughCorrelationTransportedSurvivorLedger R ps U‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP0]
    _ ≤ canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps U) *
          ‖∑ n ∈ squareRootCanonicalRoughCompressionFinalParents ps U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R n‖ +
        (1 - canonicalRoughEulerProduct
          (squareRootCanonicalRoughCompressionRunSteps ps U)) *
          squareRootCanonicalRoughScaledSignedDefectFloor R
            (squareRootCanonicalRoughCompressionRunSteps ps U) +
        ‖squareRootCanonicalRoughCorrelationTransportedSurvivorLedger R ps U‖ := by
      exact add_le_add_right (add_le_add_left hledger _) _

/-! ## Finite Abel return directly to the RH-equivalent correlation -/

/-- Reciprocal prefix of the uncentered canonical rough correlation. -/
def squareRootCanonicalRoughCorrelationReciprocalPrefix
    (R n : ℕ) : ℂ :=
  inclusivePrefix
    (fun c => squareRootCanonicalRoughCorrelationReciprocalSummand R c) n

/-- Recover one positive unweighted correlation summand. -/
theorem natCast_mul_squareRootCanonicalRoughCorrelationReciprocalSummand
    (R : ℕ) {c : ℕ} (hc : 0 < c) :
    (c : ℂ) * squareRootCanonicalRoughCorrelationReciprocalSummand R c =
      canonicalMoebiusWeight c *
        squareRootCanonicalRoughCofactorResponse R c := by
  rw [squareRootCanonicalRoughCorrelationReciprocalSummand_eq_weighted_response_div
    R hc]
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hc)
  field_simp [hc0]

/-- Exact Abel reconstruction of the uncentered correlation prefix. -/
theorem sum_squareRootCanonicalRoughCorrelation_eq_abel_reciprocalPrefix
    (R n : ℕ) :
    (∑ c ∈ Finset.Icc 1 n,
        canonicalMoebiusWeight c *
          squareRootCanonicalRoughCofactorResponse R c) =
      (n : ℂ) * squareRootCanonicalRoughCorrelationReciprocalPrefix R n -
        ∑ k ∈ Finset.range n,
          squareRootCanonicalRoughCorrelationReciprocalPrefix R k := by
  let v : ℕ → ℂ :=
    fun c => squareRootCanonicalRoughCorrelationReciprocalSummand R c
  have habel := finite_abel_identity v (fun k : ℕ => (k : ℂ)) n
  have hleft :
      (∑ c ∈ Finset.Icc 1 n,
          canonicalMoebiusWeight c *
            squareRootCanonicalRoughCofactorResponse R c) =
        ∑ c ∈ Finset.range (n + 1), v c * (c : ℂ) := by
    have hset : Finset.Icc 1 n = Finset.range (n + 1) \ {0} := by
      ext c
      simp
      omega
    rw [hset]
    have hsub : ({0} : Finset ℕ) ⊆ Finset.range (n + 1) := by
      intro c hc
      simp at hc
      subst c
      simp
    have hsplit :=
      Finset.sum_sdiff hsub (f := fun c => v c * (c : ℂ))
    have hweighted :
        (∑ c ∈ Finset.range (n + 1) \ {0}, v c * (c : ℂ)) =
          ∑ c ∈ Finset.range (n + 1) \ {0},
            canonicalMoebiusWeight c *
              squareRootCanonicalRoughCofactorResponse R c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hc0 : c ≠ 0 := by
        have hcnot : c ∉ ({0} : Finset ℕ) := (Finset.mem_sdiff.mp hc).2
        simpa using hcnot
      rw [← natCast_mul_squareRootCanonicalRoughCorrelationReciprocalSummand
        R (Nat.pos_of_ne_zero hc0)]
      ring
    rw [hweighted] at hsplit
    simpa [v] using hsplit
  rw [hleft]
  rw [habel]
  unfold squareRootCanonicalRoughCorrelationReciprocalPrefix
  simp only [inclusivePrefix]
  have hdiff : ∀ k : ℕ, (k : ℂ) - ((k + 1 : ℕ) : ℂ) = -1 := by
    intro k
    push_cast
    ring
  simp_rw [hdiff, mul_neg_one]
  rw [Finset.sum_neg_distrib]
  ring

/-- Sharp Abel budget for the RH-critical uncentered correlation profile. -/
def squareRootCanonicalRoughCorrelationReciprocalAbelBudget
    (R n : ℕ) : ℝ :=
  (n : ℝ) * ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R n‖ +
    ∑ k ∈ Finset.range n,
      ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖

/-- The complete square-endpoint correlation is bounded by its reciprocal-prefix
Abel profile. -/
theorem squareRootCanonicalRoughCorrelation_norm_le_abelBudget
    (R : ℕ) :
    ‖squareRootCanonicalRoughCorrelation R‖ ≤
      squareRootCanonicalRoughCorrelationReciprocalAbelBudget
        R (squareRootEndpoint R) := by
  unfold squareRootCanonicalRoughCorrelation
  rw [sum_squareRootCanonicalRoughCorrelation_eq_abel_reciprocalPrefix]
  unfold squareRootCanonicalRoughCorrelationReciprocalAbelBudget
  calc
    ‖(squareRootEndpoint R : ℂ) *
          squareRootCanonicalRoughCorrelationReciprocalPrefix R
            (squareRootEndpoint R) -
        ∑ k ∈ Finset.range (squareRootEndpoint R),
          squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ ≤
      ‖(squareRootEndpoint R : ℂ) *
          squareRootCanonicalRoughCorrelationReciprocalPrefix R
            (squareRootEndpoint R)‖ +
        ‖∑ k ∈ Finset.range (squareRootEndpoint R),
          squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ :=
      norm_sub_le _ _
    _ ≤ (squareRootEndpoint R : ℝ) *
          ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R
            (squareRootEndpoint R)‖ +
        ∑ k ∈ Finset.range (squareRootEndpoint R),
          ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ := by
      apply add_le_add
      · rw [norm_mul]
        simp
      · exact norm_sum_le _ _

/-- Uniform-prefix coarse form of the critical Abel return. -/
theorem squareRootCanonicalRoughCorrelation_norm_le_two_endpoint_mul
    (R : ℕ) (A : ℝ)
    (hprefix : ∀ k ≤ squareRootEndpoint R,
      ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ ≤ A) :
    ‖squareRootCanonicalRoughCorrelation R‖ ≤
      2 * (squareRootEndpoint R : ℝ) * A := by
  have hprofile := squareRootCanonicalRoughCorrelation_norm_le_abelBudget R
  exact hprofile.trans <| by
    unfold squareRootCanonicalRoughCorrelationReciprocalAbelBudget
    have hend := hprefix (squareRootEndpoint R) le_rfl
    have hsum :
        (∑ k ∈ Finset.range (squareRootEndpoint R),
          ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖) ≤
          (squareRootEndpoint R : ℝ) * A := by
      calc
        (∑ k ∈ Finset.range (squareRootEndpoint R),
            ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖) ≤
          ∑ _k ∈ Finset.range (squareRootEndpoint R), A := by
            apply Finset.sum_le_sum
            intro k hk
            exact hprefix k (Nat.le_of_lt (Finset.mem_range.mp hk))
        _ = (squareRootEndpoint R : ℝ) * A := by simp
    calc
      (squareRootEndpoint R : ℝ) *
            ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R
              (squareRootEndpoint R)‖ +
          ∑ k ∈ Finset.range (squareRootEndpoint R),
            ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ ≤
        (squareRootEndpoint R : ℝ) * A +
          (squareRootEndpoint R : ℝ) * A :=
        add_le_add
          (mul_le_mul_of_nonneg_left hend (by positivity)) hsum
      _ = 2 * (squareRootEndpoint R : ℝ) * A := by ring

/-- **Critical excursion trigger.**  A correlation larger than the Abel return
at height `A` forces at least one reciprocal prefix above `A`.  Since the
correlation is exactly `M(R-1)-M(X_R)`, this is the direct analogue of the
native-PNT step `large endpoint error -> reciprocal spike on which Euler
contraction acts`. -/
theorem squareRootCanonicalRoughCorrelation_large_forces_reciprocalPrefix
    (R : ℕ) (A : ℝ)
    (hlarge :
      2 * (squareRootEndpoint R : ℝ) * A <
        ‖squareRootCanonicalRoughCorrelation R‖) :
    ∃ k : ℕ, k ≤ squareRootEndpoint R ∧
      A < ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ := by
  by_contra hnone
  have hprefix : ∀ k ≤ squareRootEndpoint R,
      ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ ≤ A := by
    intro k hk
    apply le_of_not_gt
    intro hkLarge
    apply hnone
    exact ⟨k, hk, hkLarge⟩
  have hbound :=
    squareRootCanonicalRoughCorrelation_norm_le_two_endpoint_mul R A hprefix
  exact (not_lt_of_ge hbound) hlarge

end RHLean.Proof
