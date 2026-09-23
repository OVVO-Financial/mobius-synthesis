import RHLean.Proof.StableFarWallRenewalDescent
import RHLean.Proof.CanonicalRoughAdaptiveWeightedIteration
import RHLean.Proof.CanonicalRoughCriticalDefectWindows

/-!
# Stable-far crossings are adaptive four-corner cancellations

The stable-far q^2 renewal and the adaptive rough-prime descent are two
coordinates on the same arithmetic square.

A stripped far-wall triple has shape `(q,(d,p))` with

  q < R < p,
  P+(d) < q,
  q*d*p <= X_R.

Viewed at the low owner `q`, the far prime `p` is therefore a *strictly larger
physical extension* of the current child `d*q`.  The four corners

  d, d*q, d*p, d*q*p

all lie on the full raw carrier whenever the largest corner does.  In a
descending prime schedule, `p` is processed before `q`.  The already-compiled
four-corner theorem then zeroes the evolved raw coefficients of both `d` and
`d*q` at the `p` step, permanently through the rest of the schedule.

This is the cross-prime cancellation that ownerwise q^2 norms cannot see: the
far prime which defines the stable wall itself kills the coefficient mismatch
of the lower q-renewal before the q coordinate is processed.

No estimate, norm, or asymptotic input is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- **Far-wall four-corner coefficient kill.**

For every actual stripped stable-far triple, if a descending schedule is split
at its far prime and every earlier coordinate is still larger, then the raw
adaptive coefficients of the stripped parent `d` and low-prime child `d*q` are
both exactly zero after that split. -/
theorem lowWheelFarPrimeLowCofactorTriple_rawCoefficient_pair_eq_zero_at_farPrime
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger : ∀ r ∈ pre, t.2.2 < r) :
    squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ t.2.2 :: post)
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) t.2.1 = 0 ∧
      squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ t.2.2 :: post)
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) (t.2.1 * t.1) = 0 := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hq, hqR, hd1, hp, hpR, _hdsq, hdq, hcut⟩
  have hdpos : 0 < t.2.1 := by omega
  have hqp : t.1 < t.2.2 := by omega
  have hupper : (t.2.1 * t.1) * t.2.2 ≤ squareRootEndpoint R := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcut
  exact
    squareRootCanonicalRoughAdaptiveRawCoefficient_pair_eq_zero_of_larger_extension_split
      pre post hdpos hq hp hdq hqp hupper hprePrime hpreLarger

/-- The same cancellation applies in particular to every strict q^2 crossing
triple.  Crossing versus descended is irrelevant for the four-corner kill: the
single-insertion product `q*d*p <= X_R` already supplies the larger-prime
corner needed by the descending adaptive schedule. -/
theorem lowWheelFarPrimeQ2CrossingTriple_rawCoefficient_pair_eq_zero_at_farPrime
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger : ∀ r ∈ pre, t.2.2 < r) :
    squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ t.2.2 :: post)
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) t.2.1 = 0 ∧
      squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ t.2.2 :: post)
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) (t.2.1 * t.1) = 0 := by
  exact lowWheelFarPrimeLowCofactorTriple_rawCoefficient_pair_eq_zero_at_farPrime
    (Finset.mem_filter.mp ht).1 pre post hprePrime hpreLarger

/-- Consequently every stable-far strict crossing carries a literal larger-prime
witness for the adaptive mismatch annihilation: its own far prime. -/
theorem lowWheelFarPrimeQ2CrossingTriple_has_larger_extension
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2CrossingTriples R) :
    squareRootCanonicalRoughHasPrimeExtensionAbove
      R t.1 (t.2.1 * t.1) := by
  have hdata := lowWheelFarPrimeLowCofactorTriple_data
    (Finset.mem_filter.mp ht).1
  rcases hdata with
    ⟨hq, hqR, hd1, hp, hpR, _hdsq, hdq, hcut⟩
  refine ⟨t.2.2, hp, ?_, ?_⟩
  · omega
  · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcut

/-- **The actual lower-owner raw pair has zero evolved amplitude after the far
prime is processed.**  This is stronger than killing only the mismatch term:
both weighted endpoints of the `d -> d*q` pair vanish before the `q` step. -/
theorem lowWheelFarPrimeLowCofactorTriple_weightedRawPair_eq_zero_at_farPrime
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger : ∀ r ∈ pre, t.2.2 < r) :
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient
      (pre ++ t.2.2 :: post)
      (Finset.Icc 1 (squareRootEndpoint R))
      (fun _ => (1 : ℂ))
    a t.2.1 * squareRootCanonicalRoughRawCorrelationSummand R t.2.1 +
        a (t.2.1 * t.1) *
          squareRootCanonicalRoughRawCorrelationSummand R (t.2.1 * t.1) = 0 := by
  dsimp
  have hzero :=
    lowWheelFarPrimeLowCofactorTriple_rawCoefficient_pair_eq_zero_at_farPrime
      ht pre post hprePrime hpreLarger
  rw [hzero.1, hzero.2]
  simp

/-- **Pointwise annihilation of the entire adaptive raw correction at the lower
owner.**  After the far-prime four-corner kill, neither the signed physical
`Loss-Birth` boundary term nor the coefficient-mismatch term survives at `q`.
Thus a stable-far state cannot contribute a new error when the lower owner is
processed; its amplitude has already been transported to the earlier/larger
prime layer. -/
theorem lowWheelFarPrimeLowCofactorTriple_rawStepCorrection_eq_zero_at_farPrime
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger : ∀ r ∈ pre, t.2.2 < r) :
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient
      (pre ++ t.2.2 :: post)
      (Finset.Icc 1 (squareRootEndpoint R))
      (fun _ => (1 : ℂ))
    a t.2.1 * canonicalMoebiusWeight t.2.1 *
        (((squareRootCanonicalRoughFreshLossBoundary R t.2.1 t.1).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R t.2.1 t.1).card : ℂ)) +
      (a (t.2.1 * t.1) - a t.2.1) *
        squareRootCanonicalRoughRawCorrelationSummand R (t.2.1 * t.1) = 0 := by
  dsimp
  have hzero :=
    lowWheelFarPrimeLowCofactorTriple_rawCoefficient_pair_eq_zero_at_farPrime
      ht pre post hprePrime hpreLarger
  rw [hzero.1, hzero.2]
  simp

/-- In particular the strict q^2-crossing sector contributes **zero** to the
later low-owner adaptive raw correction once its own far prime has occurred in
the descending chronology.  No estimate of the crossing population is needed. -/
theorem lowWheelFarPrimeQ2CrossingTriple_rawStepCorrection_eq_zero_at_farPrime
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger : ∀ r ∈ pre, t.2.2 < r) :
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient
      (pre ++ t.2.2 :: post)
      (Finset.Icc 1 (squareRootEndpoint R))
      (fun _ => (1 : ℂ))
    a t.2.1 * canonicalMoebiusWeight t.2.1 *
        (((squareRootCanonicalRoughFreshLossBoundary R t.2.1 t.1).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R t.2.1 t.1).card : ℂ)) +
      (a (t.2.1 * t.1) - a t.2.1) *
        squareRootCanonicalRoughRawCorrelationSummand R (t.2.1 * t.1) = 0 := by
  exact
    lowWheelFarPrimeLowCofactorTriple_rawStepCorrection_eq_zero_at_farPrime
      (Finset.mem_filter.mp ht).1 pre post hprePrime hpreLarger

/-! ## Post-root far-prime boundary transposition -/

/-- Once a fresh prime is strictly above the root, its child has no rough-prime
response at all, so the loss boundary is the complete parent partner set. -/
theorem squareRootCanonicalRoughFreshLossBoundary_eq_partnerSet_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughFreshLossBoundary R c p =
      squareRootCanonicalRoughPrimePartnerSet R c := by
  unfold squareRootCanonicalRoughFreshLossBoundary
  rw [Nat.mul_comm p c,
    squareRootCanonicalRoughPrimePartnerSet_mul_freshPrime_eq_empty_of_rootPrime
      hR hc hp hfresh hRp]
  simp

/-- A post-root fresh prime also creates no birth population. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughFreshBirthBoundary R c p = ∅ := by
  unfold squareRootCanonicalRoughFreshBirthBoundary
  rw [Nat.mul_comm p c,
    squareRootCanonicalRoughPrimePartnerSet_mul_freshPrime_eq_empty_of_rootPrime
      hR hc hp hfresh hRp]
  simp

/-- The unweighted raw child atom itself vanishes at a post-root fresh prime. -/
theorem squareRootCanonicalRoughRawCorrelationSummand_mul_freshPrime_eq_zero_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughRawCorrelationSummand R (c * p) = 0 := by
  unfold squareRootCanonicalRoughRawCorrelationSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R (c * p) hR,
    squareRootCanonicalRoughPrimePartnerCount_mul_freshPrime_eq_zero_of_rootPrime
      hR hc hp hfresh hRp]
  simp

/-- **Post-root raw boundary = parent raw correlation.** -/
theorem squareRootCanonicalRoughFreshPrimeRawBoundary_eq_parentRaw_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) =
      squareRootCanonicalRoughRawCorrelationSummand R c := by
  rw [squareRootCanonicalRoughFreshLossBoundary_eq_partnerSet_of_rootPrime
      hR hc hp hfresh hRp,
    squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_rootPrime
      hR hc hp hfresh hRp]
  simp only [Finset.card_empty, Nat.cast_zero, sub_zero]
  unfold squareRootCanonicalRoughRawCorrelationSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR,
    squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card R c]

/-- The parent raw correlation is literally a signed incidence column over its
canonical rough-prime partners. -/
theorem squareRootCanonicalRoughRawCorrelationSummand_eq_partnerIncidenceSum
    (R c : ℕ) (hR : 2 ≤ R) :
    squareRootCanonicalRoughRawCorrelationSummand R c =
      ∑ _q ∈ squareRootCanonicalRoughPrimePartnerSet R c,
        canonicalMoebiusWeight c := by
  unfold squareRootCanonicalRoughRawCorrelationSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR,
    squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card R c]
  simp [mul_comm]

/-- Coefficient-weighted form used by the actual adaptive boundary mass. -/
theorem weighted_squareRootCanonicalRoughFreshPrimeRawBoundary_eq_partnerIncidenceSum_of_rootPrime
    {R c p : ℕ} (a : ℕ → ℂ) (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    a c * canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) =
      ∑ _q ∈ squareRootCanonicalRoughPrimePartnerSet R c,
        a c * canonicalMoebiusWeight c := by
  calc
    a c * canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) =
      a c *
        (canonicalMoebiusWeight c *
          (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
            ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ))) := by ring
    _ = a c * squareRootCanonicalRoughRawCorrelationSummand R c := by
      rw [squareRootCanonicalRoughFreshPrimeRawBoundary_eq_parentRaw_of_rootPrime
        hR hc hp hfresh hRp]
    _ = a c *
        (∑ _q ∈ squareRootCanonicalRoughPrimePartnerSet R c,
          canonicalMoebiusWeight c) := by
      rw [squareRootCanonicalRoughRawCorrelationSummand_eq_partnerIncidenceSum R c hR]
    _ = ∑ _q ∈ squareRootCanonicalRoughPrimePartnerSet R c,
        a c * canonicalMoebiusWeight c := by
      rw [Finset.mul_sum]

/-- Every actual stable-far triple's far prime is itself a literal partner of
its original low cofactor `q*d`. -/
theorem lowWheelFarPrimeLowCofactorTriple_farPrime_mem_partnerSet
    {R : ℕ} {t : ℕ × (ℕ × ℕ)} (hR : 2 ≤ R)
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    t.2.2 ∈ squareRootCanonicalRoughPrimePartnerSet R (t.1 * t.2.1) := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hqPrime, hqR, hd1, hpPrime, hpR, _hdsq, hdq, hcut⟩
  have hcpos : 0 < t.1 * t.2.1 := Nat.mul_pos hqPrime.pos (by omega)
  have hlpf : canonicalLargestPrimeFactor (t.1 * t.2.1) = t.1 := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hd1 hqPrime hdq
  apply (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hcpos).2
  refine ⟨hpPrime, ?_, ?_, ?_⟩
  · rw [hlpf]
    omega
  · have hpR' : R ≤ t.2.2 := by omega
    have hc1 : 1 ≤ t.1 * t.2.1 := Nat.succ_le_iff.mpr hcpos
    calc
      R ≤ t.2.2 := hpR'
      _ = 1 * t.2.2 := by simp
      _ ≤ (t.1 * t.2.1) * t.2.2 := Nat.mul_le_mul_right t.2.2 hc1
  · simpa [Nat.mul_assoc] using hcut

/-- **Stable-far post-root boundary transposition.**  On every actual stripped
stable-far triple, the complete physical raw boundary generated at its far prime
is exactly the intact signed partner column of the original low cofactor. -/
theorem lowWheelFarPrimeLowCofactorTriple_farPrimeRawBoundary_eq_partnerIncidenceSum
    {R : ℕ} {t : ℕ × (ℕ × ℕ)} (hR : 2 ≤ R)
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    canonicalMoebiusWeight (t.1 * t.2.1) *
        (((squareRootCanonicalRoughFreshLossBoundary
            R (t.1 * t.2.1) t.2.2).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary
            R (t.1 * t.2.1) t.2.2).card : ℂ)) =
      ∑ _r ∈ squareRootCanonicalRoughPrimePartnerSet R (t.1 * t.2.1),
        canonicalMoebiusWeight (t.1 * t.2.1) := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hqPrime, hqR, hd1, hpPrime, hpR, _hdsq, hdq, _hcut⟩
  have hcpos : 0 < t.1 * t.2.1 := Nat.mul_pos hqPrime.pos (by omega)
  have hlpf : canonicalLargestPrimeFactor (t.1 * t.2.1) = t.1 := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hd1 hqPrime hdq
  have hfresh : canonicalLargestPrimeFactor (t.1 * t.2.1) < t.2.2 := by
    rw [hlpf]
    omega
  have hRp : R < t.2.2 := by omega
  calc
    canonicalMoebiusWeight (t.1 * t.2.1) *
        (((squareRootCanonicalRoughFreshLossBoundary
            R (t.1 * t.2.1) t.2.2).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary
            R (t.1 * t.2.1) t.2.2).card : ℂ)) =
      squareRootCanonicalRoughRawCorrelationSummand R (t.1 * t.2.1) :=
        squareRootCanonicalRoughFreshPrimeRawBoundary_eq_parentRaw_of_rootPrime
          hR hcpos hpPrime hfresh hRp
    _ = ∑ _r ∈ squareRootCanonicalRoughPrimePartnerSet R (t.1 * t.2.1),
          canonicalMoebiusWeight (t.1 * t.2.1) :=
        squareRootCanonicalRoughRawCorrelationSummand_eq_partnerIncidenceSum
          R (t.1 * t.2.1) hR

end RHLean.Proof
