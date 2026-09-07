import Mathlib
import RHLean.Analysis.LargePrimeTTransport
import RHLean.Analysis.PrimeAveragedCubeEnergy
import RHLean.Analysis.SquareRootTransportTopFibreNoGo
import RHLean.Proof.LargePrimeTerminalFlipLayers
import RHLean.Proof.SquareRootPredecessorPrimeCells

/-!
# Exact middle-prime fibre collapse

At the square endpoint `X_R = R^2 - 1`, every prime in the middle range

`R < q <= X_R / 2`

has reciprocal quotient in `[2,R)`.  Hence every cofactor
`1 <= c <= floor(X_R/q)` lies strictly below `R < q`.  The fresh prime `q`
is therefore coprime to `c`, so adjoining it flips the Möbius sign exactly:

`mu(c*q) = -mu(c)`.

This module keeps that pointwise sign law intact and performs only finite exact
regrouping.  It proves:

* each middle prime fibre is `-M(floor(X_R/q))`;
* grouping middle primes by the reciprocal quotient `k` gives the finite shell
  sum `- sum_{2 <= k < R} N_R(k) M(k)`;
* the separate quotient-one top block is deterministic: every top prime
  contributes exactly `-1` to the final Möbius fibre.

The final section adds the multi-prime **hierarchical covariance exhaustion**
coordinate.  The prime-2 face is isolated as the exact middle-minus-top prime
population gap, while every remaining face is a deeper reciprocal layer
`d >= 3` weighted by the already-complete lower-scale value `M(d)`.  Later
prime injections inspect only the smaller child cutoff `floor(k/p)`, complete
old Boolean cubes vanish exactly, and nonsquarefree cofactors remain exact
Möbius zeros.  No probabilistic independence or density hypothesis is used.

No absolute value, Cauchy--Schwarz inequality, prime-count estimate, Mertens
bound, density statement, RH input, or dissipation claim is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic

/-- Integer-valued Möbius prefix through `N`.  This is the exact finite object
used in the middle fibres; no estimate is attached to it here. -/
def nativeMertens (N : ℕ) : ℤ :=
  ∑ c ∈ Finset.Icc 1 N, ArithmeticFunction.moebius c

/-- The middle prime range `R < q <= (R^2-1)/2`. -/
def middlePrimeSet (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R / 2)).filter Nat.Prime

@[simp] theorem mem_middlePrimeSet
    {R q : ℕ} :
    q ∈ middlePrimeSet R ↔
      R < q ∧ q ≤ squareRootEndpoint R / 2 ∧ q.Prime := by
  unfold middlePrimeSet
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hRq, hqle⟩
    exact ⟨hRq, hqle, hqPrime⟩
  · rintro ⟨hRq, hqle, hqPrime⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hRq, hqle⟩, hqPrime⟩

/-- The assumptions describing a middle prime force a positive root cutoff. -/
private theorem one_le_root_of_middlePrime
    {R q : ℕ} (hq : q.Prime)
    (hqle : q ≤ squareRootEndpoint R / 2) :
    1 ≤ R := by
  by_contra hR
  have hR0 : R = 0 := by omega
  subst R
  have hqpos : 0 < q := hq.pos
  unfold squareRootEndpoint at hqle
  norm_num at hqle
  omega

/-- Every middle reciprocal quotient lies in the exact finite shell range
`2 <= floor(X_R/q) < R`. -/
theorem middlePrime_quotient_mem_Ico
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) :
    squareRootEndpoint R / q ∈ Finset.Ico 2 R := by
  rcases mem_middlePrimeSet.mp hqmem with ⟨hRq, hqle, hqPrime⟩
  have hR : 1 ≤ R := one_le_root_of_middlePrime hqPrime hqle
  have hqIoc : q ∈ Finset.Ioc R (squareRootEndpoint R / 2) :=
    Finset.mem_Ioc.mpr ⟨hRq, hqle⟩
  exact Finset.mem_Ico.mpr (squareRootMiddleQuotient_range hR hqIoc)

/-- **Fibrewise middle-prime collapse.**

For a prime `q` above `R`, every admitted cofactor is below `R`, hence below
`q`.  The large-prime transport law gives `mu(c*q) = -mu(c)` pointwise, and the
whole fibre is therefore the negative Möbius prefix at the reciprocal quotient.
-/
theorem middlePrimeFibre_sum_moebius_eq_neg_mertens
    (R q : ℕ)
    (hq : q.Prime)
    (hRq : R < q)
    (hqle : q ≤ squareRootEndpoint R / 2) :
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        ArithmeticFunction.moebius (c * q) : ℤ) =
      - (nativeMertens (squareRootEndpoint R / q) : ℤ) := by
  have hR : 1 ≤ R := one_le_root_of_middlePrime hq hqle
  have hqIoc : q ∈ Finset.Ioc R (squareRootEndpoint R / 2) :=
    Finset.mem_Ioc.mpr ⟨hRq, hqle⟩
  have hquotR : squareRootEndpoint R / q < R :=
    squareRootEndpoint_div_lt_root_of_middle hR hqIoc
  unfold nativeMertens
  calc
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        ArithmeticFunction.moebius (c * q) : ℤ) =
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        -(ArithmeticFunction.moebius c : ℤ) := by
          apply Finset.sum_congr rfl
          intro c hc
          rcases Finset.mem_Icc.mp hc with ⟨hc1, hcUpper⟩
          have hcR : c < R := hcUpper.trans_lt hquotR
          let D : LargePrimeTransportData R c q :=
            { c_pos := hc1
              c_lt_cutoff := hcR
              q_prime := hq
              cutoff_lt_q := hRq }
          have hflip := LargePrimeTransportData.moebius_mul_eq_neg D
          simpa [Nat.mul_comm] using hflip
    _ = -(∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        ArithmeticFunction.moebius c : ℤ) := by
          rw [Finset.sum_neg_distrib]

/-- The signed final Möbius residual carried by one reciprocal prime fibre. -/
def middlePrimeFibreResidual (R q : ℕ) : ℤ :=
  ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
    ArithmeticFunction.moebius (c * q)

/-- Fibrewise collapse in residual notation. -/
theorem middlePrimeFibreResidual_eq_neg_mertens
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) :
    middlePrimeFibreResidual R q =
      -nativeMertens (squareRootEndpoint R / q) := by
  rcases mem_middlePrimeSet.mp hqmem with ⟨hRq, hqle, hqPrime⟩
  unfold middlePrimeFibreResidual
  exact middlePrimeFibre_sum_moebius_eq_neg_mertens
    R q hqPrime hRq hqle

/-- Middle primes with one fixed reciprocal quotient `k`. -/
def middlePrimeReciprocalShell (R k : ℕ) : Finset ℕ :=
  (middlePrimeSet R).filter fun q =>
    squareRootEndpoint R / q = k

/-- The quotient-shell multiplicity `N_R(k)`. -/
def middlePrimeReciprocalCount (R k : ℕ) : ℕ :=
  (middlePrimeReciprocalShell R k).card

@[simp] theorem mem_middlePrimeReciprocalShell
    {R k q : ℕ} :
    q ∈ middlePrimeReciprocalShell R k ↔
      q ∈ middlePrimeSet R ∧ squareRootEndpoint R / q = k := by
  simp [middlePrimeReciprocalShell]

/-- Finite Fubini regrouping of the reciprocal Mertens arguments by their exact
quotient fibres.  No estimate is used between shells. -/
theorem middlePrime_mertens_sum_eq_count_mul_mertens
    (R : ℕ) :
    (∑ q ∈ middlePrimeSet R,
        nativeMertens (squareRootEndpoint R / q) : ℤ) =
      ∑ k ∈ Finset.Ico 2 R,
        (middlePrimeReciprocalCount R k : ℤ) * nativeMertens k := by
  classical
  have hmaps :
      ∀ q ∈ middlePrimeSet R,
        squareRootEndpoint R / q ∈ Finset.Ico 2 R := by
    intro q hq
    exact middlePrime_quotient_mem_Ico hq
  unfold middlePrimeReciprocalCount middlePrimeReciprocalShell
  calc
    (∑ q ∈ middlePrimeSet R,
        nativeMertens (squareRootEndpoint R / q) : ℤ) =
      ∑ k ∈ Finset.Ico 2 R,
        ∑ _q ∈ middlePrimeSet R with
            squareRootEndpoint R / _q = k,
          nativeMertens k := by
            symm
            simpa using
              (Finset.sum_fiberwise_of_maps_to'
                (s := middlePrimeSet R)
                (t := Finset.Ico 2 R)
                (g := fun q => squareRootEndpoint R / q)
                hmaps
                (fun k : ℕ => nativeMertens k))
    _ = ∑ k ∈ Finset.Ico 2 R,
        (((middlePrimeSet R).filter fun q =>
            squareRootEndpoint R / q = k).card : ℤ) * nativeMertens k := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp

/-- **Exact quotient-shell identity for the whole middle block.**

The only operation after the fibrewise sign flip is finite regrouping by
`k = floor(X_R/q)`.  In particular no absolute values are inserted between the
`k`-shells. -/
theorem middlePrimeShell_sum_eq_neg_count_mul_mertens
    (R : ℕ) :
    (∑ q ∈ middlePrimeSet R,
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
          ArithmeticFunction.moebius (c * q) : ℤ) =
      - (∑ k ∈ Finset.Ico 2 R,
          (middlePrimeReciprocalCount R k : ℤ) *
            (nativeMertens k : ℤ)) := by
  classical
  calc
    (∑ q ∈ middlePrimeSet R,
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
          ArithmeticFunction.moebius (c * q) : ℤ) =
      ∑ q ∈ middlePrimeSet R,
        -nativeMertens (squareRootEndpoint R / q) := by
          apply Finset.sum_congr rfl
          intro q hq
          simpa [middlePrimeFibreResidual] using
            (middlePrimeFibreResidual_eq_neg_mertens hq)
    _ = -(∑ q ∈ middlePrimeSet R,
        nativeMertens (squareRootEndpoint R / q) : ℤ) := by
          rw [Finset.sum_neg_distrib]
    _ = - (∑ k ∈ Finset.Ico 2 R,
          (middlePrimeReciprocalCount R k : ℤ) *
            (nativeMertens k : ℤ)) := by
          rw [middlePrime_mertens_sum_eq_count_mul_mertens]

/-- The exact total middle residual. -/
def middlePrimeTotal (R : ℕ) : ℤ :=
  ∑ q ∈ middlePrimeSet R, middlePrimeFibreResidual R q

/-- The total middle residual is precisely the quotient-shell compression. -/
theorem middlePrimeTotal_eq_neg_count_mul_mertens
    (R : ℕ) :
    middlePrimeTotal R =
      - (∑ k ∈ Finset.Ico 2 R,
          (middlePrimeReciprocalCount R k : ℤ) *
            (nativeMertens k : ℤ)) := by
  unfold middlePrimeTotal middlePrimeFibreResidual
  exact middlePrimeShell_sum_eq_neg_count_mul_mertens R

/-! ## The separate quotient-one top block -/

/-- Every prime in the top half `(X_R/2,X_R]` has reciprocal quotient exactly
`1`. -/
theorem middlePrimeTop_quotient_eq_one
    {R q : ℕ} (hqmem : q ∈ squareRootTopFibrePrimes R) :
    squareRootEndpoint R / q = 1 := by
  rcases Finset.mem_filter.mp hqmem with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hlow, hhigh⟩
  have hXlt : squareRootEndpoint R < 2 * q := by
    have h :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hlow
    simpa [Nat.mul_comm] using h
  exact squareRootEndpoint_div_eq_one_of_top_fibre
    hqPrime.pos hXlt hhigh

/-- A quotient-one top prime has only `c=1` in its final Möbius fibre, so it
contributes exactly `-1`. -/
theorem middlePrimeTopFibreResidual_eq_neg_one
    {R q : ℕ} (hqmem : q ∈ squareRootTopFibrePrimes R) :
    middlePrimeFibreResidual R q = -1 := by
  have hqPrime : q.Prime := (Finset.mem_filter.mp hqmem).2
  have hdiv := middlePrimeTop_quotient_eq_one hqmem
  unfold middlePrimeFibreResidual
  rw [hdiv]
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  simp [ArithmeticFunction.moebius_apply_prime hqPrime]

/-- Deterministic signed baseline of the quotient-one top block. -/
def middlePrimeTopDeterministicBaseline (R : ℕ) : ℤ :=
  -((squareRootTopFibrePrimes R).card : ℤ)

/-- **The `k=1` top block is exactly the deterministic prime baseline.**
Every top prime contributes one final Möbius value `-1`; no cancellation or
prime-count estimate is involved. -/
theorem middlePrimeTopBlock_sum_eq_deterministicBaseline
    (R : ℕ) :
    (∑ q ∈ squareRootTopFibrePrimes R,
        middlePrimeFibreResidual R q : ℤ) =
      middlePrimeTopDeterministicBaseline R := by
  classical
  unfold middlePrimeTopDeterministicBaseline
  calc
    (∑ q ∈ squareRootTopFibrePrimes R,
        middlePrimeFibreResidual R q : ℤ) =
      ∑ _q ∈ squareRootTopFibrePrimes R, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact middlePrimeTopFibreResidual_eq_neg_one hq
    _ = -((squareRootTopFibrePrimes R).card : ℤ) := by
      simp

/-! ## Hierarchical covariance exhaustion -/

/-- The signed terminal-correction channel: genuine middle cofactor flips
(`c >= 2`) together with the untouched top-prime seats (`c = 1`).  The middle
bare-prime seats are deliberately not included here: prime 2 is the first
injection that cancels those seats whenever `2q <= X_R`. -/
def squareRootHierarchicalTerminalCorrectionMass (R : ℕ) : ℂ :=
  squareRootMiddleTerminalFlipMass R -
    ((squareRootTopFibrePrimes R).card : ℂ)

private theorem hierarchical_mertensSummatory_two : mertensSummatory 2 = 0 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  unfold cofactorMobiusPrefixMass
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
  simp [canonicalMoebiusWeight,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- **Hierarchical covariance exhaustion.**  After the bare middle-prime seats
are paired with their prime-2 children, the first surviving face is exactly the
middle-minus-top prime population gap.  Every remaining correction is already
a deeper reciprocal Euler layer `d >= 3`, weighted by the complete lower-scale
Mertens state `M(d)`.

In particular, even the worst same-sign coherence of the first middle face is
not an independent quadratic obstruction: before any norm is taken it enters
only through the *difference* of the middle and top prime populations.  The
`d = 2` layer is absent exactly because `M(2)=0`. -/
theorem squareRootHierarchicalCovarianceExhaustion
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootHierarchicalTerminalCorrectionMass R =
      squareRootMiddleTopPrimeCountGapMass R -
        ∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d := by
  have hset :
      Finset.Icc 2 (R - 1) =
        ({2} : Finset ℕ) ∪ Finset.Icc 3 (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({2} : Finset ℕ) (Finset.Icc 3 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd2 hd3
    rw [Finset.mem_singleton] at hd2
    subst d
    simp at hd3
  unfold squareRootHierarchicalTerminalCorrectionMass
    squareRootMiddleTerminalFlipMass
    squareRootMiddleTopPrimeCountGapMass
  rw [squareRootMiddleMertensTail_eq_reciprocalPrimeLayers R hR,
    hset, Finset.sum_union hdisj, Finset.sum_singleton,
    hierarchical_mertensSummatory_two]
  ring

/-- The same exhaustion with the first face written as the literal difference
of prime counts in the middle and top sections. -/
theorem squareRootHierarchicalCovarianceExhaustion_primeCounting
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootHierarchicalTerminalCorrectionMass R =
      (2 * (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) -
          (Nat.primeCounting (squareRootEndpoint R) : ℂ) -
          (Nat.primeCounting R : ℂ)) -
        ∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d := by
  rw [squareRootHierarchicalCovarianceExhaustion R hR]
  have hgap :
      squareRootMiddleTopPrimeCountGapMass R =
        ((squareRootMiddleTopPrimeCountGap R : ℤ) : ℂ) := by
    unfold squareRootMiddleTopPrimeCountGapMass
    rw [squareRootMiddleTopPrimeCountGap_eq_card_sub R hR]
    push_cast
    rfl
  rw [hgap]
  unfold squareRootMiddleTopPrimeCountGap
  push_cast
  ring

/-- **Later prime injections inspect smaller child cutoffs.**  If `p <= q`,
then the predecessor state sampled by `q` lies no deeper than the predecessor
state sampled by `p`.  This is the exact support contraction; it deliberately
does not assert monotonicity of the signed masses themselves. -/
theorem hierarchicalChildCutoff_antitone
    {p q k : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    k / q ≤ k / p := by
  apply (Nat.le_div_iff_mul_le hp).2
  calc
    (k / q) * p ≤ (k / q) * q := Nat.mul_le_mul_left (k / q) hpq
    _ ≤ k := Nat.div_mul_le_self k q

/-- **Complete predecessor cubes are exhausted exactly.**  Once all old
Boolean faces below a fresh prime `p` fit into its child cutoff, its signed
predecessor correction vanishes identically. -/
theorem hierarchicalPredecessorMass_eq_zero_of_complete_old_cube
    {p k : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hfit : p * primeFaceProduct (primesUpTo (p - 1)) ≤ k) :
    predecessorPrimeMass p k = 0 :=
  predecessorPrimeMass_eq_zero_of_predPrimeCube_complete hp hp2 hfit

/-- **Möbius-zero seats are removed pointwise.**  A nonsquarefree lower
cofactor remains zero after adjoining a fresh large prime.  This exact
construction-level statement is what matters here; no asymptotic zero-density
input is required. -/
theorem hierarchicalTerminalFlip_eq_zero_of_cofactor_not_squarefree
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hcpos : 0 < c) (hcqX : c * q ≤ X)
    (hnsq : ¬ Squarefree c) :
    μ (c * q) = 0 :=
  moebius_mul_largePrime_eq_zero_of_cofactor_not_squarefree
    hq hqRoot hcpos hcqX hnsq

/-! ## Maximum covariance surviving the remaining Euler faces

The hierarchy above preserves every signed cancellation until the lower-scale
Mertens states `M(d)` are complete.  At that point we may expose *any* prime
coordinate of the finite Boolean cube.  Exact parent/child pairing leaves only
the corresponding first-failure frontier.  Consequently no matter how the
signs oscillated while the primes were inserted, the completed scalar can carry
at most one unit of signed mass per frontier face.

This gives a deterministic covariance capacity.  No monotonicity of the signed
states is asserted: the pivot may be chosen independently in every reciprocal
layer, and the bound holds for every such choice. -/

/-- Number of first-failure faces left after exact pairing at Euler coordinate
`ell` in the complete prime cube through `X`.  Every such face is squarefree,
so this count already excludes all Möbius-zero seats. -/
def primeProductFrontierCard (X ell : ℕ) : ℕ :=
  (primeProductFirstFailureBoundary (primesUpTo X) X ell).card

/-- **One Euler face bounds every possible completed sign history.**  The
complete Mertens state equals the signed first-failure frontier at any prime
coordinate `ell <= X`; taking a norm only after this exact pairing gives the
sharp support-only bound by the surviving frontier cardinality. -/
theorem norm_mertensSummatory_le_primeProductFrontierCard
    {X ell : ℕ} (hell : ell ∈ primesUpTo X) :
    ‖mertensSummatory X‖ ≤ (primeProductFrontierCard X ell : ℝ) := by
  rw [← primeProductFrontierMobiusMass_eq_mertensSummatory hell]
  unfold primeProductFrontierMobiusMass primeProductFrontierCard
  calc
    ‖∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
        (((μ (primeFaceProduct t) : ℤ) : ℂ))‖ ≤
      ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
        ‖(((μ (primeFaceProduct t) : ℤ) : ℂ))‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ _t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
        (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t _ht
          rcases ArithmeticFunction.moebius_eq_or (primeFaceProduct t) with
            h | h | h <;> simp [h]
    _ = ((primeProductFirstFailureBoundary
          (primesUpTo X) X ell).card : ℝ) := by
            simp

/-- Order-free off-diagonal covariance carried by one exposed Euler frontier.
The diagonal is its unit-atom capacity `F`; thus this is `(energy-F)/2`.
Intermediate prime additions may oscillate arbitrarily. -/
def primeProductFrontierSurvivingCovariance (X ell : ℕ) : ℝ :=
  (‖mertensSummatory X‖ ^ 2 - (primeProductFrontierCard X ell : ℝ)) / 2

/-- Maximum possible covariance on a frontier of `F` unit atoms: every
surviving sign aligned. -/
def primeProductFrontierMaximumCovariance (X ell : ℕ) : ℝ :=
  ((primeProductFrontierCard X ell : ℝ) *
    ((primeProductFrontierCard X ell : ℝ) - 1)) / 2

/-- **Maximum covariance surviving one Euler face.**  Since exact pairing has
already removed every completed parent/child pair, arbitrary earlier sign
oscillation cannot produce more covariance than complete alignment of the
remaining first-failure atoms. -/
theorem primeProductFrontierSurvivingCovariance_le_maximum
    {X ell : ℕ} (hell : ell ∈ primesUpTo X) :
    primeProductFrontierSurvivingCovariance X ell ≤
      primeProductFrontierMaximumCovariance X ell := by
  have hnorm := norm_mertensSummatory_le_primeProductFrontierCard hell
  have hcard0 : 0 ≤ (primeProductFrontierCard X ell : ℝ) := by positivity
  have hsq :
      ‖mertensSummatory X‖ ^ 2 ≤
        (primeProductFrontierCard X ell : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hcard0).2 hnorm
  unfold primeProductFrontierSurvivingCovariance
    primeProductFrontierMaximumCovariance
  nlinarith

/-- A choice of one exposed Euler coordinate in every still-present reciprocal
layer.  The theorem below is uniform in this choice; hence one may choose the
smallest frontier separately in every layer without making any sign assumption. -/
def SquareRootHierarchicalEulerPivotAdmissible
    (R : ℕ) (pivot : ℕ → ℕ) : Prop :=
  ∀ d ∈ Finset.Icc 3 (R - 1), pivot d ∈ primesUpTo d

/-- The number of deeper unit frontier atoms still available after the chosen
Euler face is exposed separately in every reciprocal layer. -/
def squareRootHierarchicalEulerDeepAtomCapacity
    (R : ℕ) (pivot : ℕ → ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 3 (R - 1),
    ((((primeSieveReciprocalInterval R (squareRootEndpoint R) d).filter
        Nat.Prime).card : ℝ) *
      (primeProductFrontierCard d (pivot d) : ℝ))

/-- Unit-atom support capacity left after the middle/top opposition and after exposing the selected
Euler face in each completed lower-scale `M(d)`.  The first term counts the
literal middle and top prime seats.  In each deeper layer the reciprocal prime
multiplicity is expanded into literal copies of the surviving frontier atoms. -/
def squareRootHierarchicalEulerAtomCapacity
    (R : ℕ) (pivot : ℕ → ℕ) : ℝ :=
  (((squareRootMiddleFibrePrimes R).card : ℝ) +
      ((squareRootTopFibrePrimes R).card : ℝ)) +
    squareRootHierarchicalEulerDeepAtomCapacity R pivot

/-- The signed middle-minus-top first face is bounded by the total number of
its literal unit prime seats. -/
theorem norm_squareRootMiddleTopPrimeCountGapMass_le_atomCard
    (R : ℕ) :
    ‖squareRootMiddleTopPrimeCountGapMass R‖ ≤
      ((squareRootMiddleFibrePrimes R).card : ℝ) +
        ((squareRootTopFibrePrimes R).card : ℝ) := by
  unfold squareRootMiddleTopPrimeCountGapMass
  calc
    ‖((squareRootMiddleFibrePrimes R).card : ℂ) -
        ((squareRootTopFibrePrimes R).card : ℂ)‖ ≤
      ‖((squareRootMiddleFibrePrimes R).card : ℂ)‖ +
        ‖((squareRootTopFibrePrimes R).card : ℂ)‖ :=
          norm_sub_le _ _
    _ = ((squareRootMiddleFibrePrimes R).card : ℝ) +
        ((squareRootTopFibrePrimes R).card : ℝ) := by simp

/-- **All-face support-capacity bound for the hierarchy.**  The pivot in
each lower reciprocal layer is arbitrary.  Thus the estimate is valid after
any chosen remaining Euler face, and in particular after choosing the tightest
available frontier layer-by-layer.  No monotonicity of the signed corrections
is used. -/
theorem norm_squareRootHierarchicalTerminalCorrectionMass_le_eulerAtomCapacity
    (R : ℕ) (pivot : ℕ → ℕ) (hR : 3 ≤ R)
    (hpivot : SquareRootHierarchicalEulerPivotAdmissible R pivot) :
    ‖squareRootHierarchicalTerminalCorrectionMass R‖ ≤
      squareRootHierarchicalEulerAtomCapacity R pivot := by
  rw [squareRootHierarchicalCovarianceExhaustion R hR]
  have hsum :
      ‖∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ ≤
        squareRootHierarchicalEulerDeepAtomCapacity R pivot := by
    unfold squareRootHierarchicalEulerDeepAtomCapacity
    calc
      ‖∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ ≤
        ∑ d ∈ Finset.Icc 3 (R - 1),
          ‖primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 3 (R - 1),
          ((((primeSieveReciprocalInterval R (squareRootEndpoint R) d).filter
              Nat.Prime).card : ℝ) *
            (primeProductFrontierCard d (pivot d) : ℝ)) := by
              apply Finset.sum_le_sum
              intro d hd
              have hM :=
                norm_mertensSummatory_le_primeProductFrontierCard
                  (hpivot d hd)
              have hcount :
                  ‖primeSieveReciprocalPrimeCount R
                      (squareRootEndpoint R) d‖ =
                    (((primeSieveReciprocalInterval R
                        (squareRootEndpoint R) d).filter Nat.Prime).card : ℝ) := by
                rw [primeSieveReciprocalPrimeCount_eq_card]
                simp
              rw [norm_mul, hcount]
              exact mul_le_mul_of_nonneg_left hM (by positivity)
  have hgap := norm_squareRootMiddleTopPrimeCountGapMass_le_atomCard R
  calc
    ‖squareRootMiddleTopPrimeCountGapMass R -
        ∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ ≤
      ‖squareRootMiddleTopPrimeCountGapMass R‖ +
        ‖∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ := norm_sub_le _ _
    _ ≤ (((squareRootMiddleFibrePrimes R).card : ℝ) +
          ((squareRootTopFibrePrimes R).card : ℝ)) +
        squareRootHierarchicalEulerDeepAtomCapacity R pivot :=
      add_le_add hgap hsum
    _ = squareRootHierarchicalEulerAtomCapacity R pivot := rfl

/-- Forced-sign amplitude capacity.  Unlike the coarse atom capacity, the
middle and top prime populations are not allowed to align: their contribution
is the exact norm of their already-opposite signed difference.  Only the deeper
frontier atoms are allowed arbitrary worst-case alignment. -/
def squareRootHierarchicalEulerForcedSignCapacity
    (R : ℕ) (pivot : ℕ → ℕ) : ℝ :=
  ‖squareRootMiddleTopPrimeCountGapMass R‖ +
    squareRootHierarchicalEulerDeepAtomCapacity R pivot

/-- **Sharp support-only amplitude bound preserving the middle/top offset.**
All deeper Euler layers may oscillate arbitrarily and may finally align in the
worst possible direction; the first prime-2 face nevertheless enters only by
its exact middle-minus-top population difference. -/
theorem norm_squareRootHierarchicalTerminalCorrectionMass_le_eulerForcedSignCapacity
    (R : ℕ) (pivot : ℕ → ℕ) (hR : 3 ≤ R)
    (hpivot : SquareRootHierarchicalEulerPivotAdmissible R pivot) :
    ‖squareRootHierarchicalTerminalCorrectionMass R‖ ≤
      squareRootHierarchicalEulerForcedSignCapacity R pivot := by
  rw [squareRootHierarchicalCovarianceExhaustion R hR]
  have hsum :
      ‖∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ ≤
        squareRootHierarchicalEulerDeepAtomCapacity R pivot := by
    unfold squareRootHierarchicalEulerDeepAtomCapacity
    calc
      ‖∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ ≤
        ∑ d ∈ Finset.Icc 3 (R - 1),
          ‖primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 3 (R - 1),
          ((((primeSieveReciprocalInterval R (squareRootEndpoint R) d).filter
              Nat.Prime).card : ℝ) *
            (primeProductFrontierCard d (pivot d) : ℝ)) := by
              apply Finset.sum_le_sum
              intro d hd
              have hM :=
                norm_mertensSummatory_le_primeProductFrontierCard
                  (hpivot d hd)
              have hcount :
                  ‖primeSieveReciprocalPrimeCount R
                      (squareRootEndpoint R) d‖ =
                    (((primeSieveReciprocalInterval R
                        (squareRootEndpoint R) d).filter Nat.Prime).card : ℝ) := by
                rw [primeSieveReciprocalPrimeCount_eq_card]
                simp
              rw [norm_mul, hcount]
              exact mul_le_mul_of_nonneg_left hM (by positivity)
  calc
    ‖squareRootMiddleTopPrimeCountGapMass R -
        ∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ ≤
      ‖squareRootMiddleTopPrimeCountGapMass R‖ +
        ‖∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d‖ := norm_sub_le _ _
    _ ≤ ‖squareRootMiddleTopPrimeCountGapMass R‖ +
        squareRootHierarchicalEulerDeepAtomCapacity R pivot :=
      add_le_add_left hsum _
    _ = squareRootHierarchicalEulerForcedSignCapacity R pivot := rfl

/-- Algebraic off-diagonal covariance left after the exact hierarchy and the
selected remaining Euler faces.  The diagonal is the expanded unit-atom
capacity; this definition is order-free. -/
def squareRootHierarchicalSurvivingCovariance
    (R : ℕ) (pivot : ℕ → ℕ) : ℝ :=
  (‖squareRootHierarchicalTerminalCorrectionMass R‖ ^ 2 -
    squareRootHierarchicalEulerAtomCapacity R pivot) / 2

/-- Coarse absolute worst case: every literal unit atom, including the already
opposite middle/top populations, is allowed to have the same sign. -/
def squareRootHierarchicalMaximumCovariance
    (R : ℕ) (pivot : ℕ → ℕ) : ℝ :=
  (squareRootHierarchicalEulerAtomCapacity R pivot *
    (squareRootHierarchicalEulerAtomCapacity R pivot - 1)) / 2

/-- **Coarse maximum covariance after the remaining Euler faces.** -/
theorem squareRootHierarchicalSurvivingCovariance_le_maximum
    (R : ℕ) (pivot : ℕ → ℕ) (hR : 3 ≤ R)
    (hpivot : SquareRootHierarchicalEulerPivotAdmissible R pivot) :
    squareRootHierarchicalSurvivingCovariance R pivot ≤
      squareRootHierarchicalMaximumCovariance R pivot := by
  have hnorm :=
    norm_squareRootHierarchicalTerminalCorrectionMass_le_eulerAtomCapacity
      R pivot hR hpivot
  have hcap0 : 0 ≤ squareRootHierarchicalEulerAtomCapacity R pivot := by
    unfold squareRootHierarchicalEulerAtomCapacity
      squareRootHierarchicalEulerDeepAtomCapacity
    positivity
  have hsq :
      ‖squareRootHierarchicalTerminalCorrectionMass R‖ ^ 2 ≤
        squareRootHierarchicalEulerAtomCapacity R pivot ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hcap0).2 hnorm
  unfold squareRootHierarchicalSurvivingCovariance
    squareRootHierarchicalMaximumCovariance
  nlinarith

/-- **Forced-sign maximum covariance.**  This is the sharper worst case that
respects the exact prime-2 middle/top opposition from an earlier layer.  Deeper Euler faces
may oscillate arbitrarily and then align adversarially; the first face cannot
undo its already-forced population difference. -/
def squareRootHierarchicalForcedSignMaximumCovariance
    (R : ℕ) (pivot : ℕ → ℕ) : ℝ :=
  (squareRootHierarchicalEulerForcedSignCapacity R pivot ^ 2 -
    squareRootHierarchicalEulerAtomCapacity R pivot) / 2

/-- **Maximum covariance that can survive all selected remaining Euler faces,
with arbitrary sign oscillation at every deeper stage.**  The diagonal uses all
literal surviving unit atoms, while the amplitude retains the exact
middle-minus-top signed difference. -/
theorem squareRootHierarchicalSurvivingCovariance_le_forcedSignMaximum
    (R : ℕ) (pivot : ℕ → ℕ) (hR : 3 ≤ R)
    (hpivot : SquareRootHierarchicalEulerPivotAdmissible R pivot) :
    squareRootHierarchicalSurvivingCovariance R pivot ≤
      squareRootHierarchicalForcedSignMaximumCovariance R pivot := by
  have hnorm :=
    norm_squareRootHierarchicalTerminalCorrectionMass_le_eulerForcedSignCapacity
      R pivot hR hpivot
  have hforced0 :
      0 ≤ squareRootHierarchicalEulerForcedSignCapacity R pivot := by
    unfold squareRootHierarchicalEulerForcedSignCapacity
      squareRootHierarchicalEulerDeepAtomCapacity
    positivity
  have hsq :
      ‖squareRootHierarchicalTerminalCorrectionMass R‖ ^ 2 ≤
        squareRootHierarchicalEulerForcedSignCapacity R pivot ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hforced0).2 hnorm
  unfold squareRootHierarchicalSurvivingCovariance
    squareRootHierarchicalForcedSignMaximumCovariance
  linarith

/-- Concrete admissible choice: prime `2` is available in every lower layer
`d >= 3`.  This is not a monotonicity statement; it is simply one simultaneous
family of exact Euler pairings. -/
def squareRootHierarchicalPrimeTwoEulerAtomCapacity (R : ℕ) : ℝ :=
  squareRootHierarchicalEulerAtomCapacity R (fun _ => 2)

/-- Concrete support bound obtained by exposing the prime-2 face inside every
completed lower reciprocal Mertens layer. -/
theorem norm_squareRootHierarchicalTerminalCorrectionMass_le_primeTwoEulerAtomCapacity
    (R : ℕ) (hR : 3 ≤ R) :
    ‖squareRootHierarchicalTerminalCorrectionMass R‖ ≤
      squareRootHierarchicalPrimeTwoEulerAtomCapacity R := by
  unfold squareRootHierarchicalPrimeTwoEulerAtomCapacity
  apply norm_squareRootHierarchicalTerminalCorrectionMass_le_eulerAtomCapacity
    R (fun _ => 2) hR
  intro d hd
  exact mem_primesUpTo.mpr ⟨Nat.prime_two, by
    have hd3 : 3 ≤ d := (Finset.mem_Icc.mp hd).1
    simpa using (show 2 ≤ d by omega)⟩

end RHLean.Proof
