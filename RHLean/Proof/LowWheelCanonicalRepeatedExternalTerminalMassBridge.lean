import Mathlib
import RHLean.Analysis.MertensCovarianceDescent
import RHLean.Analysis.SquareRootTransportTopFibreNoGo
import RHLean.Analysis.SquareRootCanonicalRoughCovariance

/-!
# Prime-deletion Hall obstruction and rough-partner fresh-prime difference

The canonically oriented downcross carrier invites a graph-theoretic pairing:
connect opposite Mobius signs when one tail integer is obtained from the other
by adding or deleting one prime.  The actual crossing-prime deletion graph is a
subgraph of this more generous one-prime graph.

The first section records the obstruction before attempting any Hall estimate.
Every prime in the inert top half `(X_R / 2, X_R]`, where `X_R = R^2 - 1`, is
an isolated negative vertex even in the enlarged graph.  Hence every
crossing-prime deletion graph has Hall defect at least the cardinality of the
complete top prime fibre.

The second section attacks the remaining Othello/Euler question directly: how
the canonical rough-prime partner multiplicity changes under a fresh-prime
extension `c -> c*p`.  The reciprocal-depth sum collapses exactly to one clipped
prime-count window.  A fresh-prime move changes both ends of that window, and
the signed parent/child contribution is exactly an upper prime-count boundary
minus a lower prime-count boundary.

The final sections put the centered numerical coordinate used by the covariance
experiments on this same packet API, then lift the fresh-prime law to the actual
centered covariance numerator.  The key normalization is one-sided: center the
rough response but not the Mobius parity field.  Globally this is exactly the
same centered covariance, while on every fresh-prime pair the common response
mean cancels because the two Mobius signs are opposite.  Thus one Euler-prime
step leaves only its two prime-count boundaries plus the still-unpaired carrier.
The construction is iterable along any list of primes and never takes an
absolute value.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

namespace CrossingPrimeDeletionGraph

/-- Negative nonzero-Mobius vertices in the square-root Mertens tail. -/
def squareRootTailNegativePart (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun n => μ n = -1

/-- Positive nonzero-Mobius vertices in the square-root Mertens tail. -/
def squareRootTailPositivePart (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun n => μ n = 1

/-- Enlarged one-prime adjacency on opposite signs in the Mertens tail. -/
def OnePrimeTailAdjacent (R n m : ℕ) : Prop :=
  n ∈ squareRootTailNegativePart R ∧
    m ∈ squareRootTailPositivePart R ∧
      ∃ p : ℕ, p.Prime ∧ (n = p * m ∨ m = p * n)

/-- Positive neighbors of a set of negative tail vertices. -/
def onePrimeTailNeighbors (R : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (squareRootTailPositivePart R).filter fun m =>
    ∃ n ∈ S, OnePrimeTailAdjacent R n m

/-- Hall deficiency of one negative subset. -/
def onePrimeTailHallDefectAt (R : ℕ) (S : Finset ℕ) : ℕ :=
  S.card - (onePrimeTailNeighbors R S).card

/-- Maximum Hall deficiency over all negative subsets. -/
noncomputable def onePrimeTailHallDefect (R : ℕ) : ℕ :=
  ((squareRootTailNegativePart R).powerset.image
      (onePrimeTailHallDefectAt R)).max'
    (by
      refine ⟨onePrimeTailHallDefectAt R ∅, ?_⟩
      exact Finset.mem_image.mpr
        ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), rfl⟩)

/-- Top-half primes are genuine negative vertices of the Mertens tail. -/
theorem squareRootTopFibrePrimes_subset_negative
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTopFibrePrimes R ⊆ squareRootTailNegativePart R := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hqHalf, hqX⟩
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    have hRR : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
    have hsq : squareRootEndpoint R = R * R - 1 := by
      unfold squareRootEndpoint
      rw [pow_two]
    rw [hsq]
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hmul
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨hhalf.trans_lt hqHalf, hqX⟩, ?_⟩
  simpa using ArithmeticFunction.moebius_apply_prime hqPrime

/-- **Top-prime isolation.**  A top-half prime has no opposite-sign neighbor
obtained by inserting or deleting one prime while remaining in the tail. -/
theorem squareRootTopFibrePrimes_neighbors_eq_empty
    (R : ℕ) (hR : 3 ≤ R) :
    onePrimeTailNeighbors R (squareRootTopFibrePrimes R) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmPos, hneighbor⟩
  rcases hneighbor with ⟨q, hqTop, hadj⟩
  rcases hadj with ⟨_hqNeg, _hmPos, p, hpPrime, hrel⟩
  have hmTail := (Finset.mem_filter.mp hmPos).1
  rcases Finset.mem_Ioc.mp hmTail with ⟨hRm, hmX⟩
  rcases Finset.mem_filter.mp hqTop with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hqHalf, _hqX⟩
  rcases hrel with hqeq | hmeq
  · have hmdvd : m ∣ q := by
      refine ⟨p, ?_⟩
      simpa [Nat.mul_comm] using hqeq
    rcases hqPrime.eq_one_or_self_of_dvd m hmdvd with hm1 | hmq
    · omega
    · subst m
      have hp2 : 2 ≤ p := hpPrime.two_le
      have hqpos : 0 < q := hqPrime.pos
      nlinarith
  · have hXlt2q : squareRootEndpoint R < 2 * q := by
      have h :=
        (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hqHalf
      simpa [Nat.mul_comm] using h
    have h2q_le_pq : 2 * q ≤ p * q := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hpPrime.two_le
    have hXltm : squareRootEndpoint R < m := by
      rw [hmeq]
      exact hXlt2q.trans_le h2q_le_pq
    omega

/-- The Hall deficiency witnessed by the top-prime set is exactly its full
cardinality. -/
theorem onePrimeTailHallDefectAt_topFibre
    (R : ℕ) (hR : 3 ≤ R) :
    onePrimeTailHallDefectAt R (squareRootTopFibrePrimes R) =
      (squareRootTopFibrePrimes R).card := by
  rw [onePrimeTailHallDefectAt,
    squareRootTopFibrePrimes_neighbors_eq_empty R hR]
  simp

/-- **Hall no-go.**  Even the enlarged one-prime graph has Hall defect at least
the entire inert top-prime population. -/
theorem squareRootTopFibrePrimes_card_le_onePrimeTailHallDefect
    (R : ℕ) (hR : 3 ≤ R) :
    (squareRootTopFibrePrimes R).card ≤ onePrimeTailHallDefect R := by
  rw [← onePrimeTailHallDefectAt_topFibre R hR]
  unfold onePrimeTailHallDefect
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨squareRootTopFibrePrimes R, ?_, rfl⟩
  exact Finset.mem_powerset.mpr
    (squareRootTopFibrePrimes_subset_negative R hR)

end CrossingPrimeDeletionGraph

namespace CanonicalRoughFreshPrimeDifference

/-- Prefix prime count clipped at the canonical roughness threshold. -/
private def clippedPrimePrefix (y x d : ℕ) : ℂ :=
  primeSievePrefixPrimeCount (max y (x / d))

/-- Every reciprocal prime layer is one forward difference of clipped prefix
prime counts.  This remains exact after the interval has clipped to empty. -/
theorem primeSieveReciprocalPrimeCount_eq_clippedPrefix_diff
    (y x d : ℕ) (hd : 1 ≤ d) :
    primeSieveReciprocalPrimeCount y x d =
      clippedPrimePrefix y x d - clippedPrimePrefix y x (d + 1) := by
  have hmono : x / (d + 1) ≤ x / d :=
    Nat.div_le_div_left (by omega) (by omega)
  by_cases hy : y ≤ x / d
  · have hle : primeSieveReciprocalLower y x d ≤
        primeSieveReciprocalUpper x d := by
      unfold primeSieveReciprocalLower primeSieveReciprocalUpper
      exact max_le hy hmono
    rw [primeSieveReciprocalPrimeCount_eq_sub y x d hle]
    unfold clippedPrimePrefix primeSieveReciprocalLower
      primeSieveReciprocalUpper
    rw [max_eq_right hy]
  · have hxy : x / d < y := Nat.lt_of_not_ge hy
    have hnext : x / (d + 1) < y := hmono.trans_lt hxy
    have hle : primeSieveReciprocalUpper x d ≤
        primeSieveReciprocalLower y x d := by
      unfold primeSieveReciprocalUpper primeSieveReciprocalLower
      exact hxy.le.trans (le_max_left _ _)
    unfold primeSieveReciprocalPrimeCount primeSieveReciprocalInterval
    rw [Finset.Ioc_eq_empty_of_le hle]
    simp [clippedPrimePrefix, max_eq_left hxy.le, max_eq_left hnext.le]

private theorem sum_Icc_forwardDifference
    (f : ℕ → ℂ) (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, (f d - f (d + 1))) =
      f 1 - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
      ring

/-- Lower endpoint of the complete canonical rough-prime partner window. -/
def squareRootCanonicalRoughPrimePartnerLower (R c : ℕ) : ℕ :=
  max (canonicalLargestPrimeFactor c)
    ((squareRootEndpoint R / c) / R)

/-- Upper endpoint of the complete canonical rough-prime partner window. -/
def squareRootCanonicalRoughPrimePartnerUpper (R c : ℕ) : ℕ :=
  max (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c)

/-- **Partner-window collapse.**  The sum over every positive reciprocal depth
below `R` telescopes to one clipped prime-count interval. -/
theorem squareRootCanonicalRoughPrimePartnerCount_eq_prefixWindow
    {R c : ℕ} (hR : 1 ≤ R) :
    squareRootCanonicalRoughPrimePartnerCount R c =
      primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerUpper R c) -
        primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerLower R c) := by
  unfold squareRootCanonicalRoughPrimePartnerCount
    squareRootCanonicalRoughPrimeMultiplicity
  calc
    (∑ z ∈ Finset.Icc 1 (R - 1),
        primeSieveReciprocalPrimeCount
          (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z) =
      ∑ z ∈ Finset.Icc 1 (R - 1),
        (clippedPrimePrefix (canonicalLargestPrimeFactor c)
            (squareRootEndpoint R / c) z -
          clippedPrimePrefix (canonicalLargestPrimeFactor c)
            (squareRootEndpoint R / c) (z + 1)) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hz1 : 1 ≤ z := (Finset.mem_Icc.mp hz).1
        rw [primeSieveReciprocalPrimeCount_eq_clippedPrefix_diff
          (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z hz1]
    _ = clippedPrimePrefix (canonicalLargestPrimeFactor c)
          (squareRootEndpoint R / c) 1 -
        clippedPrimePrefix (canonicalLargestPrimeFactor c)
          (squareRootEndpoint R / c) R := by
        have htel := sum_Icc_forwardDifference
          (clippedPrimePrefix (canonicalLargestPrimeFactor c)
            (squareRootEndpoint R / c)) (R - 1)
        rw [Nat.sub_add_cancel hR] at htel
        exact htel
    _ = primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerUpper R c) -
        primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerLower R c) := by
        simp [clippedPrimePrefix,
          squareRootCanonicalRoughPrimePartnerUpper,
          squareRootCanonicalRoughPrimePartnerLower]

/-- A fresh prime becomes the canonical largest prime factor of its arithmetic
child, giving an explicit upper endpoint. -/
theorem squareRootCanonicalRoughPrimePartnerUpper_mul_freshPrime
    {R c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughPrimePartnerUpper R (c * p) =
      max p (squareRootEndpoint R / (c * p)) := by
  unfold squareRootCanonicalRoughPrimePartnerUpper
  rw [canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hrough]

/-- Fresh extension gives the corresponding explicit lower endpoint. -/
theorem squareRootCanonicalRoughPrimePartnerLower_mul_freshPrime
    {R c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughPrimePartnerLower R (c * p) =
      max p ((squareRootEndpoint R / (c * p)) / R) := by
  unfold squareRootCanonicalRoughPrimePartnerLower
  rw [canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hrough]

/-- Prime-count mass lost at the upper endpoint under `c -> c*p`. -/
def squareRootCanonicalRoughFreshPrimeUpperBoundary
    (R c p : ℕ) : ℂ :=
  primeSievePrefixPrimeCount
      (squareRootCanonicalRoughPrimePartnerUpper R c) -
    primeSievePrefixPrimeCount
      (squareRootCanonicalRoughPrimePartnerUpper R (c * p))

/-- Signed displacement of the lower endpoint under `c -> c*p`. -/
def squareRootCanonicalRoughFreshPrimeLowerBoundary
    (R c p : ℕ) : ℂ :=
  primeSievePrefixPrimeCount
      (squareRootCanonicalRoughPrimePartnerLower R c) -
    primeSievePrefixPrimeCount
      (squareRootCanonicalRoughPrimePartnerLower R (c * p))

/-- **Exact fresh-prime finite difference.**  The response difference is an
upper prime-count boundary minus a lower prime-count boundary. -/
theorem squareRootCanonicalRoughPrimePartnerCount_sub_mul_eq_boundaries
    {R c p : ℕ} (hR : 1 ≤ R) :
    squareRootCanonicalRoughPrimePartnerCount R c -
        squareRootCanonicalRoughPrimePartnerCount R (c * p) =
      squareRootCanonicalRoughFreshPrimeUpperBoundary R c p -
        squareRootCanonicalRoughFreshPrimeLowerBoundary R c p := by
  rw [squareRootCanonicalRoughPrimePartnerCount_eq_prefixWindow hR,
    squareRootCanonicalRoughPrimePartnerCount_eq_prefixWindow hR]
  unfold squareRootCanonicalRoughFreshPrimeUpperBoundary
    squareRootCanonicalRoughFreshPrimeLowerBoundary
  ring

/-- Explicit fresh-prime form of the same two-boundary law. -/
theorem squareRootCanonicalRoughPrimePartnerCount_sub_mul_freshPrime
    {R c p : ℕ} (hR : 1 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughPrimePartnerCount R c -
        squareRootCanonicalRoughPrimePartnerCount R (c * p) =
      (primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerUpper R c) -
        primeSievePrefixPrimeCount
          (max p (squareRootEndpoint R / (c * p)))) -
      (primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerLower R c) -
        primeSievePrefixPrimeCount
          (max p ((squareRootEndpoint R / (c * p)) / R))) := by
  rw [squareRootCanonicalRoughPrimePartnerCount_sub_mul_eq_boundaries hR]
  unfold squareRootCanonicalRoughFreshPrimeUpperBoundary
    squareRootCanonicalRoughFreshPrimeLowerBoundary
  rw [squareRootCanonicalRoughPrimePartnerUpper_mul_freshPrime hc hp hrough,
    squareRootCanonicalRoughPrimePartnerLower_mul_freshPrime hc hp hrough]

/-- **Othello parent/child law at the actual terminal kernel.**  The fresh-prime
sign flip converts the two positive partner multiplicities into the signed
prime-count boundary difference above. -/
theorem canonicalMoebiusWeight_mul_primePartnerCount_pair_eq_boundaries
    {R c p : ℕ} (hR : 1 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    canonicalMoebiusWeight c * squareRootCanonicalRoughPrimePartnerCount R c +
        canonicalMoebiusWeight (c * p) *
          squareRootCanonicalRoughPrimePartnerCount R (c * p) =
      canonicalMoebiusWeight c *
        (squareRootCanonicalRoughFreshPrimeUpperBoundary R c p -
          squareRootCanonicalRoughFreshPrimeLowerBoundary R c p) := by
  rw [canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hp hrough]
  calc
    canonicalMoebiusWeight c * squareRootCanonicalRoughPrimePartnerCount R c +
        -canonicalMoebiusWeight c *
          squareRootCanonicalRoughPrimePartnerCount R (c * p) =
      canonicalMoebiusWeight c *
        (squareRootCanonicalRoughPrimePartnerCount R c -
          squareRootCanonicalRoughPrimePartnerCount R (c * p)) := by ring
    _ = canonicalMoebiusWeight c *
        (squareRootCanonicalRoughFreshPrimeUpperBoundary R c p -
          squareRootCanonicalRoughFreshPrimeLowerBoundary R c p) := by
      rw [squareRootCanonicalRoughPrimePartnerCount_sub_mul_eq_boundaries hR]

end CanonicalRoughFreshPrimeDifference

/-! ## The centered reciprocal partial is exactly the negative packet -/

/-- The signed cumulative coordinate used in the numerical depth scans.  It
keeps the deterministic top block, the complete smooth state, and every
reciprocal layer through `D` together before any norm is taken. -/
def squareRootCenteredReciprocalPartialResidual (R D : ℕ) : ℂ :=
  ((squareRootTopFibrePrimes R).card : ℂ) -
    squareRootSmoothMass (R - 1) +
    ∑ d ∈ Finset.Icc 2 D,
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
        mertensSummatory d

/-- **Centered-partial / packet identity.**  The cumulative depth coordinate is
literally the negative upper-middle packet after restoring the complete smooth
zero mode.  This is the exact coordinate equality used by the numerical scans. -/
theorem squareRootCenteredReciprocalPartialResidual_eq_neg_smooth_sub_packet
    (R D : ℕ) (hR : 3 ≤ R) (hD : 1 ≤ D) :
    squareRootCenteredReciprocalPartialResidual R D =
      -squareRootSmoothMass (R - 1) -
        squareRootTruncatedUpperMiddlePacket R D := by
  classical
  have hset :
      Finset.Icc 1 D = ({1} : Finset ℕ) ∪ Finset.Icc 2 D := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 D) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_singleton] at hd1
    subst d
    simp at hd2
  have hM1 : mertensSummatory 1 = 1 := by
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
    simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]
  unfold squareRootCenteredReciprocalPartialResidual
    squareRootTruncatedUpperMiddlePacket
  rw [hset, Finset.sum_union hdisj]
  simp only [Finset.sum_singleton]
  rw [squareRootReciprocalPrimeCount_one_eq_topCard R hR, hM1, mul_one]
  ring

/-- At full reciprocal depth the scanned partial is exactly the centered
middle-bias residual already identified with the global Mertens carrier. -/
theorem squareRootCenteredReciprocalPartialResidual_full_eq_middleBiasResidual
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootCenteredReciprocalPartialResidual R (R - 1) =
      squareRootMiddleBiasResidual R := by
  rw [RHLean.Analysis.squareRootMiddleBiasResidual_eq_top_sub_smooth_add_reciprocalLayers
    R hR]
  rfl

/-- Consequently the full centered partial is exactly negative square-prefix
Mertens. -/
theorem squareRootCenteredReciprocalPartialResidual_full_eq_neg_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootCenteredReciprocalPartialResidual R (R - 1) =
      -squarePrefixMertens (R - 1) := by
  rw [squareRootCenteredReciprocalPartialResidual_full_eq_middleBiasResidual R hR,
    squareRootMiddleBiasResidual_eq_neg_mertens R hR]

/-- Admitting one more complete reciprocal layer changes the centered partial by
exactly that signed lower-Mertens layer. -/
theorem squareRootCenteredReciprocalPartialResidual_succ_sub
    (R D : ℕ) (hD : 1 ≤ D) :
    squareRootCenteredReciprocalPartialResidual R (D + 1) -
        squareRootCenteredReciprocalPartialResidual R D =
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) (D + 1) *
        mertensSummatory (D + 1) := by
  unfold squareRootCenteredReciprocalPartialResidual
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ D + 1)]
  ring

/-! ## Canonical rough covariance: one Euler-prime descent step -/

namespace CanonicalRoughPrimeAdditionDescent

open CanonicalRoughFreshPrimeDifference

/-- One-sided centered covariance summand.  Centering only the response field is
globally equivalent to centering both fields, because the centered response has
zero total mass.  This normalization is adapted to fresh-prime pairing: the
response mean then cancels inside each opposite-sign pair. -/
def squareRootCanonicalRoughResponseCenteredSummand (R c : ℕ) : ℂ :=
  canonicalMoebiusWeight c *
    (squareRootCanonicalRoughCofactorResponse R c -
      squareRootCanonicalRoughResponseMean R)

/-- **One-sided covariance numerator.**  The canonical rough covariance times
its cofactor population is exactly the sum of the response-centered Mobius
summands.  No mean-zero hypothesis is introduced. -/
theorem squareRootCanonicalRoughCofactorCard_mul_covariance_eq_sum_responseCentered
    (R : ℕ) (hR : 2 ≤ R) :
    (squareRootCanonicalRoughCofactorCard R : ℂ) *
        squareRootCanonicalRoughCovariance R =
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        squareRootCanonicalRoughResponseCenteredSummand R c := by
  classical
  have hcardNat : squareRootCanonicalRoughCofactorCard R ≠ 0 :=
    Nat.ne_of_gt (squareRootCanonicalRoughCofactorCard_pos R hR)
  have hcard : (squareRootCanonicalRoughCofactorCard R : ℂ) ≠ 0 := by
    exact_mod_cast hcardNat
  have hsum :
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          squareRootCanonicalRoughResponseCenteredSummand R c) =
        squareRootCanonicalRoughCorrelation R -
          squareRootCanonicalRoughParitySum R *
            squareRootCanonicalRoughResponseMean R := by
    unfold squareRootCanonicalRoughResponseCenteredSummand
      squareRootCanonicalRoughCorrelation
      squareRootCanonicalRoughParitySum
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum]
  unfold squareRootCanonicalRoughCovariance
    squareRootCanonicalRoughResponseMean
  field_simp [hcard]

/-- **Fresh-prime covariance pair law.**  On one legal arithmetic pair
`c, c*p`, both the global response mean and the Mobius sign flip disappear.
The centered covariance pair is therefore exactly the same two prime-count
boundaries already exposed by the uncentered Othello law. -/
theorem squareRootCanonicalRoughResponseCenteredSummand_add_mul_freshPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughResponseCenteredSummand R c +
        squareRootCanonicalRoughResponseCenteredSummand R (c * p) =
      canonicalMoebiusWeight c *
        (squareRootCanonicalRoughFreshPrimeUpperBoundary R c p -
          squareRootCanonicalRoughFreshPrimeLowerBoundary R c p) := by
  unfold squareRootCanonicalRoughResponseCenteredSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR,
    squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R (c * p) hR,
    canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hp hrough]
  have hdiff :=
    squareRootCanonicalRoughPrimePartnerCount_sub_mul_eq_boundaries
      (R := R) (c := c) (p := p) (by omega : 1 ≤ R)
  calc
    canonicalMoebiusWeight c *
          (squareRootCanonicalRoughPrimePartnerCount R c -
            squareRootCanonicalRoughResponseMean R) +
        -canonicalMoebiusWeight c *
          (squareRootCanonicalRoughPrimePartnerCount R (c * p) -
            squareRootCanonicalRoughResponseMean R) =
      canonicalMoebiusWeight c *
        (squareRootCanonicalRoughPrimePartnerCount R c -
          squareRootCanonicalRoughPrimePartnerCount R (c * p)) := by ring
    _ = canonicalMoebiusWeight c *
        (squareRootCanonicalRoughFreshPrimeUpperBoundary R c p -
          squareRootCanonicalRoughFreshPrimeLowerBoundary R c p) := by
      rw [hdiff]

/-- Legal parents for one fresh-prime step on an arbitrary active carrier.  A
parent and its child must both still be active, and `p` must be genuinely fresh
relative to the parent's canonical largest prime. -/
def squareRootCanonicalRoughFreshPrimeParentsOn
    (p : ℕ) (U : Finset ℕ) : Finset ℕ :=
  U.filter fun c =>
    0 < c ∧ canonicalLargestPrimeFactor c < p ∧ c * p ∈ U

/-- Children paired off by this fresh-prime step. -/
def squareRootCanonicalRoughFreshPrimeChildrenOn
    (p : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (squareRootCanonicalRoughFreshPrimeParentsOn p U).image fun c => c * p

/-- Entire portion removed by one prime step. -/
def squareRootCanonicalRoughFreshPrimePairedOn
    (p : ℕ) (U : Finset ℕ) : Finset ℕ :=
  squareRootCanonicalRoughFreshPrimeParentsOn p U ∪
    squareRootCanonicalRoughFreshPrimeChildrenOn p U

/-- Carrier surviving one exact fresh-prime descent step. -/
def squareRootCanonicalRoughFreshPrimeSurvivorsOn
    (p : ℕ) (U : Finset ℕ) : Finset ℕ :=
  U \ squareRootCanonicalRoughFreshPrimePairedOn p U

@[simp] theorem mem_squareRootCanonicalRoughFreshPrimeParentsOn
    {p c : ℕ} {U : Finset ℕ} :
    c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U ↔
      c ∈ U ∧ 0 < c ∧ canonicalLargestPrimeFactor c < p ∧ c * p ∈ U := by
  simp [squareRootCanonicalRoughFreshPrimeParentsOn]

/-- Parents are active sites. -/
theorem squareRootCanonicalRoughFreshPrimeParentsOn_subset
    (p : ℕ) (U : Finset ℕ) :
    squareRootCanonicalRoughFreshPrimeParentsOn p U ⊆ U := by
  intro c hc
  exact (mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hc).1

/-- Every generated child is active by construction. -/
theorem squareRootCanonicalRoughFreshPrimeChildrenOn_subset
    (p : ℕ) (U : Finset ℕ) :
    squareRootCanonicalRoughFreshPrimeChildrenOn p U ⊆ U := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨c, hc, rfl⟩
  exact (mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hc).2.2.2

/-- A legal fresh-prime parent cannot itself be one of the generated children:
the child has canonical largest prime exactly `p`. -/
theorem squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_childrenOn
    {p : ℕ} (U : Finset ℕ) (hp : p.Prime) :
    Disjoint (squareRootCanonicalRoughFreshPrimeParentsOn p U)
      (squareRootCanonicalRoughFreshPrimeChildrenOn p U) := by
  rw [Finset.disjoint_left]
  intro n hnParent hnChild
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hnParent with
    ⟨_hnU, _hnpos, hnrough, _hnchild⟩
  rcases Finset.mem_image.mp hnChild with ⟨c, hcParent, hcn⟩
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, hcrough, _hcchild⟩
  subst n
  have hlpf := canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcpos hp hcrough
  rw [hlpf] at hnrough
  exact (lt_irrefl p hnrough)

/-- The paired portion is a subset of the current active carrier. -/
theorem squareRootCanonicalRoughFreshPrimePairedOn_subset
    (p : ℕ) (U : Finset ℕ) :
    squareRootCanonicalRoughFreshPrimePairedOn p U ⊆ U := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact squareRootCanonicalRoughFreshPrimeParentsOn_subset p U hn
  · exact squareRootCanonicalRoughFreshPrimeChildrenOn_subset p U hn

/-- Reindexing the paired part by its unique parents produces the literal sum of
parent/child covariance pairs. -/
theorem sum_squareRootCanonicalRoughFreshPrimePairedOn_eq_sum_pairs
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
        squareRootCanonicalRoughResponseCenteredSummand R n) =
      ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        (squareRootCanonicalRoughResponseCenteredSummand R c +
          squareRootCanonicalRoughResponseCenteredSummand R (c * p)) := by
  unfold squareRootCanonicalRoughFreshPrimePairedOn
  rw [Finset.sum_union
    (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_childrenOn U hp)]
  unfold squareRootCanonicalRoughFreshPrimeChildrenOn
  rw [Finset.sum_image]
  · rw [Finset.sum_add_distrib]
  · intro a _ha b _hb hab
    exact Nat.mul_right_cancel hp.pos hab

/-- Boundary charge produced by one Euler-prime descent step. -/
def squareRootCanonicalRoughFreshPrimeBoundaryMass
    (R p : ℕ) (U : Finset ℕ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    canonicalMoebiusWeight c *
      (squareRootCanonicalRoughFreshPrimeUpperBoundary R c p -
        squareRootCanonicalRoughFreshPrimeLowerBoundary R c p)

/-- The entire paired covariance contribution is exactly the signed two-boundary
charge of that prime. -/
theorem sum_squareRootCanonicalRoughFreshPrimePairedOn_eq_boundaryMass
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
        squareRootCanonicalRoughResponseCenteredSummand R n) =
      squareRootCanonicalRoughFreshPrimeBoundaryMass R p U := by
  rw [sum_squareRootCanonicalRoughFreshPrimePairedOn_eq_sum_pairs R U hp]
  unfold squareRootCanonicalRoughFreshPrimeBoundaryMass
  apply Finset.sum_congr rfl
  intro c hc
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hc with
    ⟨_hcU, hcpos, hcrough, _hcchild⟩
  exact squareRootCanonicalRoughResponseCenteredSummand_add_mul_freshPrime
    hR hcpos hp hcrough

/-- **One exact prime-addition descent step.**  Processing one fresh prime on any
active carrier decomposes the complete centered covariance numerator into its
signed two-boundary charge plus the still-unpaired centered carrier.  No term is
normed separately. -/
theorem sum_squareRootCanonicalRoughResponseCentered_eq_boundaryMass_add_survivors
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ n ∈ U, squareRootCanonicalRoughResponseCenteredSummand R n) =
      squareRootCanonicalRoughFreshPrimeBoundaryMass R p U +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredSummand R n := by
  have hsub := squareRootCanonicalRoughFreshPrimePairedOn_subset p U
  have hsplit :
      (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredSummand R n) +
        (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
          squareRootCanonicalRoughResponseCenteredSummand R n) =
        ∑ n ∈ U, squareRootCanonicalRoughResponseCenteredSummand R n := by
    simpa [squareRootCanonicalRoughFreshPrimeSurvivorsOn] using
      (Finset.sum_sdiff hsub
        (f := squareRootCanonicalRoughResponseCenteredSummand R))
  rw [sum_squareRootCanonicalRoughFreshPrimePairedOn_eq_boundaryMass
    R U hR hp] at hsplit
  calc
    (∑ n ∈ U, squareRootCanonicalRoughResponseCenteredSummand R n) =
        (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredSummand R n) +
          squareRootCanonicalRoughFreshPrimeBoundaryMass R p U := hsplit.symm
    _ = squareRootCanonicalRoughFreshPrimeBoundaryMass R p U +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredSummand R n := by ring

/-- Active carrier remaining after a chronological list of Euler primes. -/
def squareRootCanonicalRoughPrimeDescentSurvivors :
    List ℕ → Finset ℕ → Finset ℕ
  | [], U => U
  | p :: ps, U =>
      squareRootCanonicalRoughPrimeDescentSurvivors ps
        (squareRootCanonicalRoughFreshPrimeSurvivorsOn p U)

/-- Cumulative signed boundary charge generated by the same chronological prime
list.  Each next prime acts only on the carrier left by the previous ones. -/
def squareRootCanonicalRoughPrimeDescentBoundaryMass
    (R : ℕ) : List ℕ → Finset ℕ → ℂ
  | [], _U => 0
  | p :: ps, U =>
      squareRootCanonicalRoughFreshPrimeBoundaryMass R p U +
        squareRootCanonicalRoughPrimeDescentBoundaryMass R ps
          (squareRootCanonicalRoughFreshPrimeSurvivorsOn p U)

/-- **Sequential prime-addition covariance descent.**  Along any list of genuine
primes, the centered covariance numerator telescopes exactly into the cumulative
signed two-boundary charges plus the final survivor carrier. -/
theorem sum_squareRootCanonicalRoughResponseCentered_eq_primeDescent
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ U, squareRootCanonicalRoughResponseCenteredSummand R n) =
      squareRootCanonicalRoughPrimeDescentBoundaryMass R ps U +
        ∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors ps U,
          squareRootCanonicalRoughResponseCenteredSummand R n := by
  induction ps generalizing U with
  | nil =>
      simp [squareRootCanonicalRoughPrimeDescentBoundaryMass,
        squareRootCanonicalRoughPrimeDescentSurvivors]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      rw [sum_squareRootCanonicalRoughResponseCentered_eq_boundaryMass_add_survivors
        R U hR hp]
      rw [ih (U := squareRootCanonicalRoughFreshPrimeSurvivorsOn p U) hps]
      simp [squareRootCanonicalRoughPrimeDescentBoundaryMass,
        squareRootCanonicalRoughPrimeDescentSurvivors]
      ring

/-- Physical cofactor carrier of the canonical rough covariance. -/
def squareRootCanonicalRoughCofactorCarrier (R : ℕ) : Finset ℕ :=
  Finset.Icc 1 (squareRootEndpoint R)

/-- **Canonical rough covariance prime-addition descent.**  This is the concrete
sequential Euler theorem: after multiplying the normalized covariance by its
physical cofactor population, any chosen sequence of genuine prime additions
leaves exactly the cumulative signed prime-count boundaries and the centered
survivor carrier. -/
theorem squareRootCanonicalRoughCovariance_primeAdditionDescent
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (squareRootCanonicalRoughCofactorCard R : ℂ) *
        squareRootCanonicalRoughCovariance R =
      squareRootCanonicalRoughPrimeDescentBoundaryMass R ps
          (squareRootCanonicalRoughCofactorCarrier R) +
        ∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors ps
            (squareRootCanonicalRoughCofactorCarrier R),
          squareRootCanonicalRoughResponseCenteredSummand R n := by
  rw [squareRootCanonicalRoughCofactorCard_mul_covariance_eq_sum_responseCentered
    R hR]
  exact sum_squareRootCanonicalRoughResponseCentered_eq_primeDescent
    R hR ps (squareRootCanonicalRoughCofactorCarrier R) hprime

end CanonicalRoughPrimeAdditionDescent

end RHLean.Proof