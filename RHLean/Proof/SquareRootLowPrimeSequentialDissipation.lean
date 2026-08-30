import Mathlib
import RHLean.Proof.LowPrimeFreshLayerBridge

/-!
# One-sided low-prime sequential dissipation

The running BornPostTail response is already split into exact fresh
largest-prime-factor layers.  This module turns one complete fresh layer into a
genuine one-sided decomposition before any estimate.

The born and high responses are first kept together at each cofactor.  The high
response is included on its honest cutoff `c <= R - 1`; outside that cutoff the
combined response is just the born response.  The resulting response is a
natural number.

The fresh layer is then partitioned by its already-final Möbius orientation:

* cofactors with `mu(c) = -1` form the deletion mass `D_p`;
* cofactors with `mu(c) = 1` form the bad/frontier mass `F_p`;
* cofactors with `mu(c) = 0` contribute nothing.

Hence the actual running increment has the exact one-sided form

`Delta_p^born + Delta_p^high = -D_p + F_p`,

with both `D_p` and `F_p` natural and therefore nonnegative.  The bad support is
not copied into an independent error term for every prime: membership records
`P+(c) = p`, so bad supports for distinct fresh primes are disjoint.  The
earlier empty-parent atom `c = p` remains visible as one forced negative term
inside the full deletion mass.

No absolute value, Cauchy--Schwarz estimate, PNT, Mertens bound, covariance
normalization, endpoint reconstruction, or RH-equivalent statement appears.
The next quantitative obligation is now the globally assigned positive
Möbius-orientation mass, rather than the original signed fresh layer.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Cofactors in the born part of the fresh largest-prime layer. -/
def squareRootLowPrimeBornFreshCofactors
    (R p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun c =>
    canonicalLargestPrimeFactor c = p

/-- Cofactors in the high part of the fresh largest-prime layer. -/
def squareRootLowPrimeHighFreshCofactors
    (R p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R - 1)).filter fun c =>
    canonicalLargestPrimeFactor c = p

/-- Proper-parent born cofactors: remove the empty-parent atom `c = p`. -/
def squareRootLowPrimeProperBornCofactors
    (R p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeBornFreshCofactors R p).erase p

/-- Proper-parent high cofactors: remove the empty-parent atom `c = p`. -/
def squareRootLowPrimeProperHighCofactors
    (R p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeHighFreshCofactors R p).erase p

/-- Born component of the actual fresh running increment. -/
def squareRootLowPrimeBornFreshIncrement
    (R p : ℕ) : ℂ :=
  ∑ c ∈ squareRootLowPrimeBornFreshCofactors R p,
    canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)

/-- High component of the actual fresh running increment. -/
def squareRootLowPrimeHighFreshIncrement
    (R K j p : ℕ) : ℂ :=
  ∑ c ∈ squareRootLowPrimeHighFreshCofactors R p,
    canonicalMoebiusWeight c *
      (squareRootBornPostTailHighResponse R K j c : ℂ)

/-- The actual fresh increment, with born and high retained together. -/
def squareRootLowPrimeFreshIncrement
    (R K j p : ℕ) : ℂ :=
  squareRootLowPrimeBornFreshIncrement R p +
    squareRootLowPrimeHighFreshIncrement R K j p

/-- Running imbalance used in the sequential energy diagnostic. -/
def squareRootLowPrimeRunningImbalance
    (R K j p : ℕ) : ℂ :=
  1 - squareRootBornPostTailRunningLowPrimeResponse R K j p

/-- Forced deletion carried by the empty-parent fresh child `c = p`. -/
def squareRootLowPrimePrimeDeletionCount
    (R K j p : ℕ) : ℕ :=
  squareRootBornPostTailHighResponse R K j p

/-- All proper-parent terms at one fresh prime, with the born and high channels
kept signed together.  This preliminary signed remainder is refined below into
its full negative and positive Möbius orientations. -/
def squareRootLowPrimeProperParentBadMass
    (R K j p : ℕ) : ℂ :=
  (∑ c ∈ squareRootLowPrimeProperBornCofactors R p,
      canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)) +
    ∑ c ∈ squareRootLowPrimeProperHighCofactors R p,
      canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)

/-- Global proper-parent signed mass on a prime interval. -/
def squareRootLowPrimeGlobalProperParentBadMass
    (R K j L U : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
    squareRootLowPrimeProperParentBadMass R K j p

private theorem canonicalLargestPrimeFactor_eq_prime
    {p : ℕ} (hp : p.Prime) :
    canonicalLargestPrimeFactor p = p := by
  have hlpfPrime : (canonicalLargestPrimeFactor p).Prime :=
    canonicalLargestPrimeFactor_prime hp.one_lt
  have hlpfDvd : canonicalLargestPrimeFactor p ∣ p :=
    canonicalLargestPrimeFactor_dvd hp.one_lt
  exact (Nat.prime_dvd_prime_iff_eq hlpfPrime hp).mp hlpfDvd

private theorem canonicalMoebiusWeight_prime_eq_neg_one
    {p : ℕ} (hp : p.Prime) :
    canonicalMoebiusWeight p = -1 := by
  unfold canonicalMoebiusWeight
  rw [ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- A prime cofactor has no born partner: the defining interval would require
simultaneously `p < q` and `q ≤ p`. -/
theorem squareRootBornPartnerCount_prime_eq_zero
    (R : ℕ) {p : ℕ} (hp : p.Prime) :
    squareRootBornPartnerCount R p = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rw [squareRootBornPartnerSet, Finset.mem_filter] at hq
  rcases hq with ⟨_hqRange, _hqPrime, hrough, hqp, _hproduct⟩
  rw [canonicalLargestPrimeFactor_eq_prime hp] at hrough
  omega

private theorem prime_mem_squareRootLowPrimeBornFreshCofactors
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    p ∈ squareRootLowPrimeBornFreshCofactors R p := by
  have hRX : R ≤ squareRootEndpoint R := by
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  unfold squareRootLowPrimeBornFreshCofactors
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr
        ⟨hp.one_le, (Nat.le_of_lt hpR).trans hRX⟩,
      canonicalLargestPrimeFactor_eq_prime hp⟩

private theorem prime_mem_squareRootLowPrimeHighFreshCofactors
    {R p : ℕ} (hp : p.Prime) (hpR : p < R) :
    p ∈ squareRootLowPrimeHighFreshCofactors R p := by
  unfold squareRootLowPrimeHighFreshCofactors
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hp.one_le, by omega⟩,
      canonicalLargestPrimeFactor_eq_prime hp⟩

/-- The split fresh increment is exactly the existing kernel-checked fresh
cofactor layer. -/
theorem squareRootBornPostTailFreshCofactorLayer_eq_lowPrimeFreshIncrement
    (R K j p : ℕ) :
    squareRootBornPostTailFreshCofactorLayer R K j p =
      squareRootLowPrimeFreshIncrement R K j p := by
  unfold squareRootBornPostTailFreshCofactorLayer
    squareRootLowPrimeFreshIncrement
    squareRootLowPrimeBornFreshIncrement
    squareRootLowPrimeHighFreshIncrement
    squareRootLowPrimeBornFreshCofactors
    squareRootLowPrimeHighFreshCofactors
  rw [Finset.sum_filter, Finset.sum_filter]

/-- The running-state step is the split born-plus-high fresh increment. -/
theorem squareRootBornPostTailRunningLowPrimeResponse_step_eq_lowPrimeFreshIncrement
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) =
      squareRootLowPrimeFreshIncrement R K j p := by
  rw [squareRootBornPostTailRunningLowPrimeResponse_step_eq_freshCofactorLayer
      R K j p hp,
    squareRootBornPostTailFreshCofactorLayer_eq_lowPrimeFreshIncrement]

/-- Removing the empty-parent prime atom leaves the entire born increment,
because that atom's born response is zero. -/
theorem squareRootLowPrimeBornFreshIncrement_eq_properParent
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    squareRootLowPrimeBornFreshIncrement R p =
      ∑ c ∈ squareRootLowPrimeProperBornCofactors R p,
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ) := by
  have hpMem :=
    prime_mem_squareRootLowPrimeBornFreshCofactors hR hp hpR
  unfold squareRootLowPrimeBornFreshIncrement
    squareRootLowPrimeProperBornCofactors
  rw [← Finset.add_sum_erase _
      (fun c => canonicalMoebiusWeight c *
        (squareRootBornPartnerCount R c : ℂ)) hpMem,
    squareRootBornPartnerCount_prime_eq_zero R hp]
  simp

/-- The empty-parent atom contributes exactly the negative natural deletion
count to the high increment. -/
theorem squareRootLowPrimeHighFreshIncrement_eq_neg_deletion_add_properParent
    {R K j p : ℕ} (hp : p.Prime) (hpR : p < R) :
    squareRootLowPrimeHighFreshIncrement R K j p =
      -((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
        ∑ c ∈ squareRootLowPrimeProperHighCofactors R p,
          canonicalMoebiusWeight c *
            (squareRootBornPostTailHighResponse R K j c : ℂ) := by
  have hpMem := prime_mem_squareRootLowPrimeHighFreshCofactors hp hpR
  unfold squareRootLowPrimeHighFreshIncrement
    squareRootLowPrimeProperHighCofactors
    squareRootLowPrimePrimeDeletionCount
  rw [← Finset.add_sum_erase _
      (fun c => canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)) hpMem,
    canonicalMoebiusWeight_prime_eq_neg_one hp]
  ring

/-- Preliminary prime-atom split.  The full one-sided decomposition below also
splits every proper-parent term by its Möbius orientation. -/
theorem squareRootLowPrimeFreshIncrement_eq_neg_primeDeletion_add_properMass
    {R K j p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    squareRootLowPrimeFreshIncrement R K j p =
      -((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
        squareRootLowPrimeProperParentBadMass R K j p := by
  unfold squareRootLowPrimeFreshIncrement
    squareRootLowPrimeProperParentBadMass
  rw [squareRootLowPrimeBornFreshIncrement_eq_properParent hR hp hpR,
    squareRootLowPrimeHighFreshIncrement_eq_neg_deletion_add_properParent
      hp hpR]
  ring

/-- The prime atom is a genuine nonnegative quantity. -/
theorem squareRootLowPrimePrimeDeletionCount_nonneg
    (R K j p : ℕ) :
    (0 : ℤ) ≤ (squareRootLowPrimePrimeDeletionCount R K j p : ℤ) := by
  positivity

/-- Beyond the shallow cutoff, the forced prime-atom deletion is exactly the
post-root prime-prefix cardinality at the fresh prime. -/
theorem squareRootLowPrimePrimeDeletionCount_eq_postRootPrefix
    {R K j p : ℕ} (hKp : K < p) :
    squareRootLowPrimePrimeDeletionCount R K j p =
      squareRootPostRootPrimePrefixCard R p := by
  unfold squareRootLowPrimePrimeDeletionCount
    squareRootBornPostTailHighResponse
  rw [if_neg (by omega : ¬ p ≤ K)]

/-- Later prime-atom deletions have no larger geometric post-root prefix than
earlier ones. -/
theorem squareRootLowPrimePrimeDeletionCount_antitone
    {R K j p q : ℕ} (hp : 0 < p) (hpq : p ≤ q)
    (hKp : K < p) (hKq : K < q) :
    squareRootLowPrimePrimeDeletionCount R K j q ≤
      squareRootLowPrimePrimeDeletionCount R K j p := by
  rw [squareRootLowPrimePrimeDeletionCount_eq_postRootPrefix hKq,
    squareRootLowPrimePrimeDeletionCount_eq_postRootPrefix hKp]
  unfold squareRootPostRootPrimePrefixCard
  apply Finset.card_le_card
  intro r hr
  rcases Finset.mem_filter.mp hr with ⟨hrIoc, hrPrime⟩
  rcases Finset.mem_Ioc.mp hrIoc with ⟨hRr, hrq⟩
  have hdiv : squareRootEndpoint R / q ≤ squareRootEndpoint R / p :=
    Nat.div_le_div_left hpq hp
  have hmax :
      max R (squareRootEndpoint R / q) ≤
        max R (squareRootEndpoint R / p) :=
    max_le_max_left R hdiv
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hRr, hrq.trans hmax⟩, hrPrime⟩

private theorem lpf_eq_of_mem_properBorn
    {R p c : ℕ} (hc : c ∈ squareRootLowPrimeProperBornCofactors R p) :
    canonicalLargestPrimeFactor c = p := by
  exact (Finset.mem_filter.mp (Finset.mem_erase.mp hc).2).2

private theorem lpf_eq_of_mem_properHigh
    {R p c : ℕ} (hc : c ∈ squareRootLowPrimeProperHighCofactors R p) :
    canonicalLargestPrimeFactor c = p := by
  exact (Finset.mem_filter.mp (Finset.mem_erase.mp hc).2).2

/-- Proper-parent born supports for distinct fresh primes are disjoint. -/
theorem squareRootLowPrimeProperBornCofactors_disjoint
    {R p q : ℕ} (hpq : p ≠ q) :
    Disjoint (squareRootLowPrimeProperBornCofactors R p)
      (squareRootLowPrimeProperBornCofactors R q) := by
  rw [Finset.disjoint_left]
  intro c hcp hcq
  exact hpq ((lpf_eq_of_mem_properBorn hcp).symm.trans
    (lpf_eq_of_mem_properBorn hcq))

/-- Proper-parent high supports for distinct fresh primes are disjoint. -/
theorem squareRootLowPrimeProperHighCofactors_disjoint
    {R p q : ℕ} (hpq : p ≠ q) :
    Disjoint (squareRootLowPrimeProperHighCofactors R p)
      (squareRootLowPrimeProperHighCofactors R q) := by
  rw [Finset.disjoint_left]
  intro c hcp hcq
  exact hpq ((lpf_eq_of_mem_properHigh hcp).symm.trans
    (lpf_eq_of_mem_properHigh hcq))

/-- A proper-parent cofactor can be assigned to only one fresh prime even when
it contributes to both response channels. -/
theorem squareRootLowPrimeProperParent_support_unique
    {R p q c : ℕ}
    (hcp : c ∈ squareRootLowPrimeProperBornCofactors R p ∨
      c ∈ squareRootLowPrimeProperHighCofactors R p)
    (hcq : c ∈ squareRootLowPrimeProperBornCofactors R q ∨
      c ∈ squareRootLowPrimeProperHighCofactors R q) :
    p = q := by
  have hp : canonicalLargestPrimeFactor c = p := by
    rcases hcp with hcp | hcp
    · exact lpf_eq_of_mem_properBorn hcp
    · exact lpf_eq_of_mem_properHigh hcp
  have hq : canonicalLargestPrimeFactor c = q := by
    rcases hcq with hcq | hcq
    · exact lpf_eq_of_mem_properBorn hcq
    · exact lpf_eq_of_mem_properHigh hcq
  exact hp.symm.trans hq

/-! ## Full sign-oriented dissipation split -/

/-- The complete natural response at one fresh cofactor.  Born and high are
added before the Möbius sign is used; the high term is present exactly on its
honest cutoff. -/
def squareRootLowPrimeCombinedFreshResponse
    (R K j c : ℕ) : ℕ :=
  squareRootBornPartnerCount R c +
    if c ≤ R - 1 then
      squareRootBornPostTailHighResponse R K j c
    else
      0

/-- Fresh cofactors whose already-final Möbius orientation is negative. -/
def squareRootLowPrimeDeletionCofactors
    (R p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeBornFreshCofactors R p).filter fun c =>
    μ c = -1

/-- Fresh cofactors whose already-final Möbius orientation is positive. -/
def squareRootLowPrimeBadCofactors
    (R p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeBornFreshCofactors R p).filter fun c =>
    μ c = 1

/-- Total negative-orientation response in one fresh layer. -/
def squareRootLowPrimeDeletionMass
    (R K j p : ℕ) : ℕ :=
  ∑ c ∈ squareRootLowPrimeDeletionCofactors R p,
    squareRootLowPrimeCombinedFreshResponse R K j c

/-- Total positive-orientation response in one fresh layer.  This is the
bad/frontier mass left for the global quantitative estimate. -/
def squareRootLowPrimeBadMass
    (R K j p : ℕ) : ℕ :=
  ∑ c ∈ squareRootLowPrimeBadCofactors R p,
    squareRootLowPrimeCombinedFreshResponse R K j c

/-- Globally assigned bad mass on a prime interval. -/
def squareRootLowPrimeGlobalBadMass
    (R K j L U : ℕ) : ℕ :=
  ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
    squareRootLowPrimeBadMass R K j p

/-- The honest high support is exactly the part of the born support below `R`.
This lets the two channels be added at each cofactor before splitting signs. -/
theorem squareRootLowPrimeHighFreshCofactors_eq_bornFresh_filter
    {R p : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeHighFreshCofactors R p =
      (squareRootLowPrimeBornFreshCofactors R p).filter fun c =>
        c ≤ R - 1 := by
  have hpredX : R - 1 ≤ squareRootEndpoint R := by
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  ext c
  simp only [squareRootLowPrimeHighFreshCofactors,
    squareRootLowPrimeBornFreshCofactors, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hc1, hcR⟩, hlpf⟩
    exact ⟨⟨⟨hc1, hcR.trans hpredX⟩, hlpf⟩, hcR⟩
  · rintro ⟨⟨⟨hc1, _hcX⟩, hlpf⟩, hcR⟩
    exact ⟨⟨hc1, hcR⟩, hlpf⟩

/-- The actual born-plus-high increment is one cofactor sum of natural responses
with Möbius signs outside. -/
theorem squareRootLowPrimeFreshIncrement_eq_combinedCofactorSum
    {R K j p : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeFreshIncrement R K j p =
      ∑ c ∈ squareRootLowPrimeBornFreshCofactors R p,
        canonicalMoebiusWeight c *
          (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ) := by
  unfold squareRootLowPrimeFreshIncrement
    squareRootLowPrimeBornFreshIncrement
    squareRootLowPrimeHighFreshIncrement
  rw [squareRootLowPrimeHighFreshCofactors_eq_bornFresh_filter hR,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hcR : c ≤ R - 1
  · simp [squareRootLowPrimeCombinedFreshResponse, hcR]
    ring
  · simp [squareRootLowPrimeCombinedFreshResponse, hcR]

private theorem canonicalMoebiusWeight_mul_natCast_eq_signSplit
    (c n : ℕ) :
    canonicalMoebiusWeight c * (n : ℂ) =
      -(if μ c = -1 then (n : ℂ) else 0) +
        (if μ c = 1 then (n : ℂ) else 0) := by
  have hbound := ArithmeticFunction.abs_moebius_le_one (n := c)
  rw [abs_le] at hbound
  have hcases : μ c = -1 ∨ μ c = 0 ∨ μ c = 1 := by omega
  rcases hcases with hneg | hzero | hpos
  · simp [canonicalMoebiusWeight, hneg]
  · simp [canonicalMoebiusWeight, hzero]
  · simp [canonicalMoebiusWeight, hpos]

/-- **Full one-sided fresh-layer decomposition.**  Every negative Möbius
orientation contributes to one natural deletion mass and every positive
orientation contributes to one natural bad mass. -/
theorem squareRootLowPrimeFreshIncrement_eq_neg_deletionMass_add_badMass
    {R K j p : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeFreshIncrement R K j p =
      -((squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ) +
        ((squareRootLowPrimeBadMass R K j p : ℕ) : ℂ) := by
  rw [squareRootLowPrimeFreshIncrement_eq_combinedCofactorSum hR]
  have hDcast :
      ((squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ) =
        ∑ c ∈ squareRootLowPrimeDeletionCofactors R p,
          (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ) := by
    unfold squareRootLowPrimeDeletionMass
    push_cast
    rfl
  have hFcast :
      ((squareRootLowPrimeBadMass R K j p : ℕ) : ℂ) =
        ∑ c ∈ squareRootLowPrimeBadCofactors R p,
          (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ) := by
    unfold squareRootLowPrimeBadMass
    push_cast
    rfl
  calc
    (∑ c ∈ squareRootLowPrimeBornFreshCofactors R p,
        canonicalMoebiusWeight c *
          (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ)) =
      ∑ c ∈ squareRootLowPrimeBornFreshCofactors R p,
        (-(if μ c = -1 then
              (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ)
            else 0) +
          (if μ c = 1 then
              (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ)
            else 0)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact canonicalMoebiusWeight_mul_natCast_eq_signSplit c
        (squareRootLowPrimeCombinedFreshResponse R K j c)
    _ = -(∑ c ∈ squareRootLowPrimeBornFreshCofactors R p,
          if μ c = -1 then
            (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ)
          else 0) +
        ∑ c ∈ squareRootLowPrimeBornFreshCofactors R p,
          if μ c = 1 then
            (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ)
          else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = -(∑ c ∈ squareRootLowPrimeDeletionCofactors R p,
          (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ)) +
        ∑ c ∈ squareRootLowPrimeBadCofactors R p,
          (squareRootLowPrimeCombinedFreshResponse R K j c : ℂ) := by
      unfold squareRootLowPrimeDeletionCofactors
        squareRootLowPrimeBadCofactors
      rw [Finset.sum_filter, Finset.sum_filter]
    _ = -((squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ) +
        ((squareRootLowPrimeBadMass R K j p : ℕ) : ℂ) := by
      rw [hDcast, hFcast]

/-- Both sides of the one-sided split are honest nonnegative natural masses. -/
theorem squareRootLowPrimeDeletionMass_nonneg
    (R K j p : ℕ) :
    (0 : ℤ) ≤ (squareRootLowPrimeDeletionMass R K j p : ℤ) := by
  positivity

/-- The globally problematic orientation is also an honest nonnegative natural
mass, ready for a single global estimate. -/
theorem squareRootLowPrimeBadMass_nonneg
    (R K j p : ℕ) :
    (0 : ℤ) ≤ (squareRootLowPrimeBadMass R K j p : ℤ) := by
  positivity

private theorem lpf_eq_of_mem_badCofactors
    {R p c : ℕ} (hc : c ∈ squareRootLowPrimeBadCofactors R p) :
    canonicalLargestPrimeFactor c = p := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2

/-- Bad supports for distinct fresh primes are disjoint.  Thus the global bad
mass is assigned once by the canonical largest prime, not charged once per
prime coordinate. -/
theorem squareRootLowPrimeBadCofactors_disjoint
    {R p q : ℕ} (hpq : p ≠ q) :
    Disjoint (squareRootLowPrimeBadCofactors R p)
      (squareRootLowPrimeBadCofactors R q) := by
  rw [Finset.disjoint_left]
  intro c hcp hcq
  exact hpq ((lpf_eq_of_mem_badCofactors hcp).symm.trans
    (lpf_eq_of_mem_badCofactors hcq))

/-- The empty-parent prime atom lies inside the full deletion support. -/
theorem prime_mem_squareRootLowPrimeDeletionCofactors
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    p ∈ squareRootLowPrimeDeletionCofactors R p := by
  unfold squareRootLowPrimeDeletionCofactors
  exact Finset.mem_filter.mpr
    ⟨prime_mem_squareRootLowPrimeBornFreshCofactors hR hp hpR,
      by rw [ArithmeticFunction.moebius_apply_prime hp]⟩

/-- Preliminary empty-parent split retained as a local diagnostic. -/
theorem squareRootLowPrimePrimeAtomDecomposition
    {R K j p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    (squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) =
      -((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
        squareRootLowPrimeProperParentBadMass R K j p) ∧
      (0 : ℤ) ≤ (squareRootLowPrimePrimeDeletionCount R K j p : ℤ) := by
  constructor
  · rw [squareRootBornPostTailRunningLowPrimeResponse_step_eq_lowPrimeFreshIncrement
      R K j p hp]
    exact squareRootLowPrimeFreshIncrement_eq_neg_primeDeletion_add_properMass
      hR hp hpR
  · exact squareRootLowPrimePrimeDeletionCount_nonneg R K j p

/-- **SquareRootLowPrimeSequentialDissipation.**  The actual running fresh-prime
step is the difference of two nonnegative natural masses.  The positive
bad/frontier support is globally disjoint across fresh primes. -/
theorem squareRootLowPrimeSequentialDissipation
    {R K j p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (_hpR : p < R) :
    (squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) =
      -((squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ) +
        ((squareRootLowPrimeBadMass R K j p : ℕ) : ℂ)) ∧
      (0 : ℤ) ≤ (squareRootLowPrimeDeletionMass R K j p : ℤ) ∧
      (0 : ℤ) ≤ (squareRootLowPrimeBadMass R K j p : ℤ) := by
  constructor
  · rw [squareRootBornPostTailRunningLowPrimeResponse_step_eq_lowPrimeFreshIncrement
      R K j p hp]
    exact squareRootLowPrimeFreshIncrement_eq_neg_deletionMass_add_badMass hR
  · exact ⟨squareRootLowPrimeDeletionMass_nonneg R K j p,
      squareRootLowPrimeBadMass_nonneg R K j p⟩

end RHLean.Proof
