import Mathlib
import RHLean.Analysis.DyadicTransportCompression
import RHLean.Proof.MiddlePrimeFibreCollapse
import RHLean.Proof.PrimeCombVisualizationDynamics
import RHLean.Proof.LargePrimeTerminalFlipLayers

/-!
# Arbitrary-endpoint reciprocal-band cancellation in the prime comb

The prime-comb animation already proves the exact one-prime post-root score law

`Delta_p(W) = 2 * (1 - M(floor(W/p)))`.

This file packages that law on the reciprocal quotient bands

`W/(z+1) < p <= W/z`.

Every prime in one such band has the same quotient `floor(W/p)=z`, hence the
same proper-multiple seat set `{2,...,z}`, the same signed cofactor channel
`M(z)-1`, and the same score correction `2*(1-M(z))`.

More fundamentally, once `p > sqrt W`, the complete final `p`-family is an
exact sign-reversed copy of the already-completed lower prefix:

`sum_{1 <= c <= floor(W/p)} mu(c*p) = -M(floor(W/p))`.

Thus on one reciprocal band every large prime carries the same final family
mass `-M(z)`, seat by seat through `mu(c*p) = -mu(c)`.  Summing the post-root
part of a band therefore gives exactly its prime cardinality times `-M(z)`, and
summing every post-root prime gives the negative of the repository's complete
Mertens-weighted prime tail.

The adjacent-band finite difference is especially important:

`D(z+1) - D(z) = -2 * mu(z+1)`.

Thus the reciprocal bands are constant-action cells of the literal ordered-prime
walk, and each newly exposed lower cofactor changes the next-band correction in
the opposite direction of its Mobius sign.  These are exact finite identities;
no asymptotic estimate or RH-scale saving is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Prime coordinates in the reciprocal quotient band with quotient `z`. -/
def primeCombReciprocalBand (W z : ℕ) : Finset ℕ :=
  (Finset.Ioc (W / (z + 1)) (W / z)).filter Nat.Prime

@[simp] theorem mem_primeCombReciprocalBand
    {W z p : ℕ} :
    p ∈ primeCombReciprocalBand W z ↔
      W / (z + 1) < p ∧ p ≤ W / z ∧ p.Prime := by
  simp [primeCombReciprocalBand, and_assoc]

/-- Every coordinate in a positive reciprocal band has the advertised exact
quotient `floor(W/p)=z`. -/
theorem primeCombReciprocalBand_div_eq
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    W / p = z := by
  rcases mem_primeCombReciprocalBand.mp hp with ⟨hlower, hupper, _hpPrime⟩
  have hlo : z * p ≤ W := by
    have h := (Nat.le_div_iff_mul_le hz).1 hupper
    simpa [Nat.mul_comm] using h
  have hhi : W < (z + 1) * p := by
    have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < z + 1)).1 hlower
    simpa [Nat.mul_comm] using h
  exact Nat.div_eq_of_lt_le hlo hhi

/-- Band membership already includes primality. -/
theorem primeCombReciprocalBand_prime
    {W z p : ℕ} (hp : p ∈ primeCombReciprocalBand W z) :
    p.Prime :=
  (mem_primeCombReciprocalBand.mp hp).2.2

/-- A prime in a reciprocal band lies inside the ambient block. -/
theorem primeCombReciprocalBand_le_endpoint
    {W z p : ℕ} (hp : p ∈ primeCombReciprocalBand W z) :
    p ≤ W := by
  have hupper := (mem_primeCombReciprocalBand.mp hp).2.1
  exact hupper.trans (Nat.div_le_self W z)

/-- The geometric rake on a reciprocal band is literally the fixed cofactor
interval `{2,...,z}`. -/
theorem primeCombReciprocalBand_multiplierSet_eq
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    primeCombProperMultiplierSet p W = Finset.Icc 2 z := by
  unfold primeCombProperMultiplierSet
  rw [primeCombReciprocalBand_div_eq hz hp]

/-- Hence every prime in the band has exactly `z-1` candidate proper-multiple
seats.  Squareful cofactors among these seats contribute zero to the signed
cofactor channel below through `mu(c)=0`. -/
theorem primeCombReciprocalBand_seatCount
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    (primeCombProperMultiplierSet p W).card = z - 1 := by
  rw [card_primeCombProperMultiplierSet,
    primeCombReciprocalBand_div_eq hz hp]

/-- The signed cofactor channel is constant on a reciprocal band and is exactly
`M(z)-1`. -/
theorem primeCombReciprocalBand_channelMass_eq
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    primeCombTailChannelMass W p =
      RHLean.Analysis.mertensSummatory z - 1 := by
  have hpPrime := primeCombReciprocalBand_prime hp
  have hpW := primeCombReciprocalBand_le_endpoint hp
  rw [primeCombTailChannelMass_eq_mertens_sub_one hpPrime.pos hpW,
    primeCombReciprocalBand_div_eq hz hp]

/-! ## The final large-prime family is a reversed lower prefix -/

/-- Final Möbius mass of all multiples `c*p <= W` in the family of one prime
`p`, including the prime seat `c=1`. -/
def primeCombLargePrimeFamilyMass (W p : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (W / p), canonicalMoebiusWeight (c * p)

/-- **Arbitrary-endpoint sign-reversed family theorem.**  Once `p` lies above
`sqrt W`, every admissible lower cofactor satisfies `c < p`, so the fresh prime
reverses its completed Möbius sign.  Consequently the entire final `p`-family
is exactly the negative lower Mertens prefix at the reciprocal cutoff. -/
theorem primeCombLargePrimeFamilyMass_eq_neg_mertens
    {W p : ℕ} (hp : p.Prime) (hpRoot : Nat.sqrt W < p) :
    primeCombLargePrimeFamilyMass W p =
      -RHLean.Analysis.mertensSummatory (W / p) := by
  unfold primeCombLargePrimeFamilyMass
  calc
    (∑ c ∈ Finset.Icc 1 (W / p), canonicalMoebiusWeight (c * p)) =
        ∑ c ∈ Finset.Icc 1 (W / p), -canonicalMoebiusWeight c := by
      apply Finset.sum_congr rfl
      intro c hc
      rcases Finset.mem_Icc.mp hc with ⟨hc1, hcTop⟩
      have hcpW : c * p ≤ W :=
        (Nat.le_div_iff_mul_le hp.pos).1 hcTop
      exact canonicalMoebiusWeight_mul_largePrime_eq_neg_cofactor
        hp hpRoot (by omega) hcpW
    _ = -(∑ c ∈ Finset.Icc 1 (W / p), canonicalMoebiusWeight c) := by
      simp
    _ = -RHLean.Analysis.mertensSummatory (W / p) := by
      have hM := cofactorMobiusPrefixMass_eq_mertensSummatory (W / p)
      unfold cofactorMobiusPrefixMass at hM
      rw [hM]

/-- **Reciprocal-band family cancellation.**  Every post-root prime in the
same quotient band carries the same final signed family `-M(z)`. -/
theorem primeCombReciprocalBand_familyMass_eq_neg_mertens
    {W z p : ℕ} (hz : 0 < z) (hpRoot : Nat.sqrt W < p)
    (hp : p ∈ primeCombReciprocalBand W z) :
    primeCombLargePrimeFamilyMass W p =
      -RHLean.Analysis.mertensSummatory z := by
  calc
    primeCombLargePrimeFamilyMass W p =
        -RHLean.Analysis.mertensSummatory (W / p) :=
      primeCombLargePrimeFamilyMass_eq_neg_mertens
        (primeCombReciprocalBand_prime hp) hpRoot
    _ = -RHLean.Analysis.mertensSummatory z := by
      rw [primeCombReciprocalBand_div_eq hz hp]

/-- The post-root portion of reciprocal band `z`. -/
def primeCombPostRootReciprocalBand (W z : ℕ) : Finset ℕ :=
  (primeCombReciprocalBand W z).filter fun p => Nat.sqrt W < p

@[simp] theorem mem_primeCombPostRootReciprocalBand
    {W z p : ℕ} :
    p ∈ primeCombPostRootReciprocalBand W z ↔
      p ∈ primeCombReciprocalBand W z ∧ Nat.sqrt W < p := by
  simp [primeCombPostRootReciprocalBand]

/-- Final signed mass of all large-prime families in one post-root reciprocal
band. -/
def primeCombPostRootReciprocalBandFamilyMass (W z : ℕ) : ℂ :=
  ∑ p ∈ primeCombPostRootReciprocalBand W z,
    primeCombLargePrimeFamilyMass W p

/-- **Whole-band cancellation law.**  After the square-root frontier, the entire
reciprocal band is exactly its prime population times the common sign-reversed
lower prefix `-M(z)`. -/
theorem primeCombPostRootReciprocalBandFamilyMass_eq_card_mul_neg_mertens
    (W z : ℕ) (hz : 0 < z) :
    primeCombPostRootReciprocalBandFamilyMass W z =
      ((primeCombPostRootReciprocalBand W z).card : ℂ) *
        (-RHLean.Analysis.mertensSummatory z) := by
  unfold primeCombPostRootReciprocalBandFamilyMass
  calc
    (∑ p ∈ primeCombPostRootReciprocalBand W z,
        primeCombLargePrimeFamilyMass W p) =
      ∑ p ∈ primeCombPostRootReciprocalBand W z,
        (-RHLean.Analysis.mertensSummatory z) := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases mem_primeCombPostRootReciprocalBand.mp hp with ⟨hpBand, hpRoot⟩
      exact primeCombReciprocalBand_familyMass_eq_neg_mertens hz hpRoot hpBand
    _ = ((primeCombPostRootReciprocalBand W z).card : ℂ) *
        (-RHLean.Analysis.mertensSummatory z) := by
      simp

/-- Final signed mass of every post-root prime family at endpoint `W`. -/
def primeCombPostRootFamilyMass (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
    if p.Prime then primeCombLargePrimeFamilyMass W p else 0

/-- **Complete arbitrary-endpoint post-root cancellation.**  The union of all
post-root prime families is exactly the negative Mertens-weighted prime tail.
Each large prime contributes one sign-reversed lower prefix and nothing else. -/
theorem primeCombPostRootFamilyMass_eq_neg_mertensPrimeTail
    (W : ℕ) :
    primeCombPostRootFamilyMass W =
      -primeSieveMertensPrimeTail (Nat.sqrt W) W := by
  unfold primeCombPostRootFamilyMass primeSieveMertensPrimeTail
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hpRange
  have hpRoot := (Finset.mem_Ioc.mp hpRange).1
  by_cases hpPrime : p.Prime
  · simp [hpPrime,
      primeCombLargePrimeFamilyMass_eq_neg_mertens hpPrime hpRoot]
  · simp [hpPrime]

/-- The same complete post-root family mass in reciprocal-band coordinates. -/
theorem primeCombPostRootFamilyMass_eq_neg_reciprocalPrimeTail
    (W : ℕ) :
    primeCombPostRootFamilyMass W =
      -RHLean.Analysis.primeSieveReciprocalPrimeTail (Nat.sqrt W) W := by
  rw [primeCombPostRootFamilyMass_eq_neg_mertensPrimeTail,
    RHLean.Analysis.primeSieveMertensPrimeTail_eq_reciprocalPrimeTail]

/-- The final family kernel attached to quotient band `z`. -/
def primeCombReciprocalBandFamilyKernel (z : ℕ) : ℂ :=
  -RHLean.Analysis.mertensSummatory z

/-- Adding the next lower cofactor changes the final family by exactly the
opposite Möbius sign. -/
theorem primeCombReciprocalBandFamilyKernel_succ_sub
    (z : ℕ) :
    primeCombReciprocalBandFamilyKernel (z + 1) -
        primeCombReciprocalBandFamilyKernel z =
      -(((μ (z + 1) : ℤ) : ℂ)) := by
  unfold primeCombReciprocalBandFamilyKernel
  rw [RHLean.Analysis.mertensSummatory_succ]
  ring

/-! ## The displayed score correction -/

/-- The constant signed correction attached to quotient band `z`. -/
def primeCombReciprocalBandKernel (z : ℕ) : ℂ :=
  2 * (1 - RHLean.Analysis.mertensSummatory z)

/-- Every prime in the same reciprocal band has the same post-root tail
correction. -/
theorem primeCombReciprocalBand_signedDelta_eq
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    primeCombTailSignedDelta W p =
      primeCombReciprocalBandKernel z := by
  have hpPrime := primeCombReciprocalBand_prime hp
  have hpW := primeCombReciprocalBand_le_endpoint hp
  unfold primeCombReciprocalBandKernel
  rw [primeCombTailSignedDelta_eq hpPrime.pos hpW,
    primeCombReciprocalBand_div_eq hz hp]

/-- Total signed correction of an entire reciprocal band. -/
def primeCombReciprocalBandSignedDelta (W z : ℕ) : ℂ :=
  ∑ p ∈ primeCombReciprocalBand W z, primeCombTailSignedDelta W p

/-- Band aggregation introduces no new arithmetic: it is simply the number of
prime coordinates in the band times the one common lower-prefix correction. -/
theorem primeCombReciprocalBandSignedDelta_eq_card_mul
    (W z : ℕ) (hz : 0 < z) :
    primeCombReciprocalBandSignedDelta W z =
      ((primeCombReciprocalBand W z).card : ℂ) *
        primeCombReciprocalBandKernel z := by
  unfold primeCombReciprocalBandSignedDelta
  calc
    (∑ p ∈ primeCombReciprocalBand W z, primeCombTailSignedDelta W p) =
        ∑ p ∈ primeCombReciprocalBand W z,
          primeCombReciprocalBandKernel z := by
      apply Finset.sum_congr rfl
      intro p hp
      exact primeCombReciprocalBand_signedDelta_eq hz hp
    _ = ((primeCombReciprocalBand W z).card : ℂ) *
          primeCombReciprocalBandKernel z := by
      simp

/-- **Adjacent-band cancellation law.**  Exposing one additional lower cofactor
changes the next reciprocal-band correction by the opposite of twice its
Möbius sign.

This is the exact negative-feedback identity visible in the prime-comb movie. -/
theorem primeCombReciprocalBandKernel_succ_sub
    (z : ℕ) :
    primeCombReciprocalBandKernel (z + 1) -
        primeCombReciprocalBandKernel z =
      -2 * (((μ (z + 1) : ℤ) : ℂ)) := by
  unfold primeCombReciprocalBandKernel
  rw [RHLean.Analysis.mertensSummatory_succ]
  ring

/-- Equivalent recurrence form of the adjacent-band law. -/
theorem primeCombReciprocalBandKernel_succ
    (z : ℕ) :
    primeCombReciprocalBandKernel (z + 1) =
      primeCombReciprocalBandKernel z -
        2 * (((μ (z + 1) : ℤ) : ℂ)) := by
  have h := primeCombReciprocalBandKernel_succ_sub z
  linear_combination h

/-! ## Deterministic non-iid Möbius replication -/

/-- A same-sign run after zero Möbius values are ignored.  This is deliberately
deterministic: it makes no independence assumption about the remaining signs. -/
def IsSameSignNonzeroMobiusRun (a b : ℕ) (s : ℤ) : Prop :=
  (s = 1 ∨ s = -1) ∧
    ∀ n ∈ Finset.Ioc a b, μ n ≠ 0 → μ n = s

/-- Number of nonzero observations in `(a,b]`. -/
def sameSignNonzeroMobiusRunLength (a b : ℕ) : ℕ :=
  ((Finset.Ioc a b).filter fun n => μ n ≠ 0).card

/-- A same-sign nonzero run produces its entire signed excursion exactly. -/
theorem sameSignNonzeroMobiusRun_sum
    {a b : ℕ} {s : ℤ}
    (hrun : IsSameSignNonzeroMobiusRun a b s) :
    (∑ n ∈ Finset.Ioc a b, μ n) =
      s * (sameSignNonzeroMobiusRunLength a b : ℤ) := by
  classical
  rcases hrun with ⟨_hs, hsign⟩
  let S : Finset ℕ := Finset.Ioc a b
  let T : Finset ℕ := S.filter fun n => μ n ≠ 0
  have hsub : T ⊆ S := Finset.filter_subset _ _
  have hvanish : ∀ n ∈ S, n ∉ T → μ n = 0 := by
    intro n hnS hnT
    by_contra hne
    exact hnT (Finset.mem_filter.mpr ⟨hnS, hne⟩)
  have hrestrict :
      (∑ n ∈ S, μ n) = ∑ n ∈ T, μ n :=
    (Finset.sum_subset hsub hvanish).symm
  calc
    (∑ n ∈ Finset.Ioc a b, μ n) = ∑ n ∈ T, μ n := by
      simpa [S] using hrestrict
    _ = ∑ _n ∈ T, s := by
      apply Finset.sum_congr rfl
      intro n hnT
      have hmem := Finset.mem_filter.mp hnT
      exact hsign n hmem.1 hmem.2
    _ = (T.card : ℤ) * s := by simp
    _ = s * (sameSignNonzeroMobiusRunLength a b : ℤ) := by
      simp [T, S, sameSignNonzeroMobiusRunLength, mul_comm]

/-- Any admissible post-root replication with a genuine cofactor `c >= 2` is
forced into the middle sector `R < q <= X_R/2`. -/
theorem nontrivialPostRootReplication_mem_middlePrimeSet
    {R q c : ℕ}
    (hqPrime : q.Prime) (hRq : R < q)
    (hc2 : 2 ≤ c) (hcq : c * q ≤ squareRootEndpoint R) :
    q ∈ middlePrimeSet R := by
  apply mem_middlePrimeSet.mpr
  refine ⟨hRq, ?_, hqPrime⟩
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
  calc
    q * 2 = 2 * q := by omega
    _ ≤ c * q := Nat.mul_le_mul_right q hc2
    _ ≤ squareRootEndpoint R := hcq

/-- Conversely, a top-sector prime has no positive admissible cofactor except
`1`: the top sector cannot generate nontrivial prefix replication. -/
theorem topPrime_admissibleCofactor_eq_one
    {R q c : ℕ}
    (hqmem : q ∈ squareRootTopFibrePrimes R)
    (hc1 : 1 ≤ c) (hcq : c * q ≤ squareRootEndpoint R) :
    c = 1 := by
  have hqPrime : q.Prime := (Finset.mem_filter.mp hqmem).2
  have hcdiv : c ≤ squareRootEndpoint R / q :=
    (Nat.le_div_iff_mul_le hqPrime.pos).2 hcq
  rw [middlePrimeTop_quotient_eq_one hqmem] at hcdiv
  omega

/-- Pointwise deterministic sign inheritance in every middle prime fibre. -/
theorem middlePrimeFibre_moebius_eq_neg
    {R q c : ℕ} (hqmem : q ∈ middlePrimeSet R)
    (hc : c ∈ Finset.Icc 1 (squareRootEndpoint R / q)) :
    μ (c * q) = -μ c := by
  rcases mem_middlePrimeSet.mp hqmem with ⟨hRq, _hqle, hqPrime⟩
  have hquotR : squareRootEndpoint R / q < R :=
    (Finset.mem_Ico.mp (middlePrime_quotient_mem_Ico hqmem)).2
  have hcData := Finset.mem_Icc.mp hc
  have hcR : c < R := hcData.2.trans_lt hquotR
  have hcq : c < q := hcR.trans hRq
  have hcop : Nat.Coprime c q :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hcData.1) hcq hqPrime).symm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hqPrime]
  ring

/-- Lower-prefix coordinates carrying one exact Möbius state. -/
def prefixMobiusStateSet (N : ℕ) (z : ℤ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun c => μ c = z

/-- Cofactor coordinates in one middle prime fibre carrying state `z`. -/
def middlePrimeFibreStateSet (R q : ℕ) (z : ℤ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R / q)).filter fun c => μ (c * q) = z

/-- **Exact three-state transport.**  A middle prime does not resample the
Möbius distribution.  The `z` population is literally the lower-prefix `-z`
population on the same cofactor coordinates. -/
theorem middlePrimeFibreStateSet_eq_prefix_neg
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) (z : ℤ) :
    middlePrimeFibreStateSet R q z =
      prefixMobiusStateSet (squareRootEndpoint R / q) (-z) := by
  classical
  ext c
  simp only [middlePrimeFibreStateSet, prefixMobiusStateSet,
    Finset.mem_filter]
  constructor
  · rintro ⟨hc, hz⟩
    refine ⟨hc, ?_⟩
    have hflip := middlePrimeFibre_moebius_eq_neg hqmem hc
    rw [hflip] at hz
    omega
  · rintro ⟨hc, hz⟩
    refine ⟨hc, ?_⟩
    have hflip := middlePrimeFibre_moebius_eq_neg hqmem hc
    rw [hflip, hz]
    simp

/-- Cardinal version: zeros are preserved and the two nonzero populations are
swapped exactly. -/
theorem middlePrimeFibre_zero_pos_neg_counts
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) :
    (middlePrimeFibreStateSet R q 0).card =
        (prefixMobiusStateSet (squareRootEndpoint R / q) 0).card ∧
    (middlePrimeFibreStateSet R q 1).card =
        (prefixMobiusStateSet (squareRootEndpoint R / q) (-1)).card ∧
    (middlePrimeFibreStateSet R q (-1)).card =
        (prefixMobiusStateSet (squareRootEndpoint R / q) 1).card := by
  constructor
  · rw [middlePrimeFibreStateSet_eq_prefix_neg hqmem]
    simp
  constructor
  · rw [middlePrimeFibreStateSet_eq_prefix_neg hqmem]
  · rw [middlePrimeFibreStateSet_eq_prefix_neg hqmem]
    simp

/-! ## Exact non-iid finite difference in the replication weights -/

/-- Integer multiplicity attached to one fixed lower cofactor in the square
endpoint replication response. -/
def orderedPrimeReplicationWeightInt (R c : ℕ) : ℤ :=
  (Nat.primeCounting (squareRootEndpoint R / c) : ℤ) -
    (Nat.primeCounting R : ℤ)

/-- One signed lower-prefix contribution to the ordered replication response. -/
def orderedPrimeReplicationTermInt (R c : ℕ) : ℤ :=
  μ c * orderedPrimeReplicationWeightInt R c

/-- Integer form of the complete fixed-prefix replication response. -/
def orderedPrimeReplicationResponseInt (R : ℕ) : ℤ :=
  ∑ c ∈ Finset.Ico 1 R, orderedPrimeReplicationTermInt R c

/-- **Dyadic parent/child cancellation of the prime-clock baseline.**  For an
odd lower cofactor `c`, deterministic Möbius dependence gives
`mu(2c)=-mu(c)`.  Hence the two replication channels cancel the common
`-pi(R)` term exactly and leave only the finite difference of the two prime
counts.  This identity is unavailable under an iid sign model. -/
theorem orderedPrimeReplication_dyadic_pair
    (R c : ℕ) (hc : Odd c) :
    orderedPrimeReplicationTermInt R c +
        orderedPrimeReplicationTermInt R (2 * c) =
      μ c *
        ((Nat.primeCounting (squareRootEndpoint R / c) : ℤ) -
          (Nat.primeCounting (squareRootEndpoint R / (2 * c)) : ℤ)) := by
  have hmu := RHLean.Arithmetic.moebius_two_mul_of_odd c hc
  unfold orderedPrimeReplicationTermInt orderedPrimeReplicationWeightInt
  rw [hmu]
  ring

/-- The pre-existing dyadic transport theorem is the fibrewise version of the
same non-iid mechanism: every complete lower prefix collapses exactly to its
odd dyadic boundary. -/
theorem middlePrimeFibre_inheritedPrefix_eq_dyadicBoundary
    {R q : ℕ} (hR : 0 < R) (hqmem : q ∈ middlePrimeSet R) :
    primeDilatedLowCofactorMass R q =
      dyadicPrimeFiberBoundaryMass R q := by
  rcases mem_middlePrimeSet.mp hqmem with ⟨hRq, _hqle, hqPrime⟩
  exact primeDilatedLowCofactorMass_eq_dyadicPrimeFiberBoundaryMass
    R q hR hRq hqPrime.pos

end RHLean.Proof
