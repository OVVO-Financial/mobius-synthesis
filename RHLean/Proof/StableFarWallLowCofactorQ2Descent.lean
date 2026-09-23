import RHLean.Proof.LowWheelFrozenCofactorTopImageHighPrimeObstruction
import RHLean.Proof.LowWheelFrozenSquareResidualQ2Reindex
import RHLean.Proof.CanonicalSignedParent

/-!
# Canonical q^2 descent of the stable far wall through its low cofactor

The outer far prime `p > R` has zero `p^2` daughter scale, so it is the wrong
Euler coordinate on which to recurse.  The low cofactor `c < R` still carries
its complete squarefree prime history.  This file strips the canonical largest
prime `q=P+(c)` from every nonunit far-wall cofactor before any norm is taken.

For one far pair `(c,p)` with `c>1`, write

  `c = q*d`,  `q=P+(c)`,  `d=canonicalCofactor c`.

Then `q<R<p`, `P+(d)<q`, `d` is squarefree, and

  `mu(c) = -mu(d)`.

The resulting tagged triple `(q,d,p)` is injective: the original pair is
recovered as `(q*d,p)`.  We then split these triples exactly at the second
`q`-insertion wall

  `q^2*d*p <= X_R`  versus  `X_R < q^2*d*p`.

This is only carrier/sign bookkeeping.  No assertion is yet made that either
half equals a previously named daughter or transport ledger.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The nonunit part of the literal squarefree far-prime pair carrier.  The
unit cofactor is intentionally retained as a separate signed face rather than
bounded. -/
def lowWheelFarPrimeNonUnitPairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFarPrimeSquarefreePairSet R).filter fun cp => 1 < cp.1

/-- Canonical low-cofactor descent tag `(q,d,p)`, where `q=P+(c)` and
`d=c/q`. -/
def lowWheelFarPrimeLowCofactorTag (cp : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  (canonicalLargestPrimeFactor cp.1, (canonicalCofactor cp.1, cp.2))

/-- Tagged nonunit far-wall carrier after stripping the largest low prime. -/
def lowWheelFarPrimeLowCofactorTriples (R : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeNonUnitPairSet R).image lowWheelFarPrimeLowCofactorTag

/-- Every nonunit far-wall pair has the exact canonical low-cofactor geometry
needed by a second `q` insertion. -/
theorem lowWheelFarPrimeNonUnitPair_data
    {R c p : ℕ} (hcp : (c,p) ∈ lowWheelFarPrimeNonUnitPairSet R) :
    let q := canonicalLargestPrimeFactor c
    let d := canonicalCofactor c
    q.Prime ∧ q < R ∧ R < p ∧ p.Prime ∧
      Squarefree d ∧ canonicalLargestPrimeFactor d < q ∧
      q * d = c ∧ q < p ∧ q * d * p ≤ squareRootEndpoint R ∧
      canonicalMoebiusWeight c = -canonicalMoebiusWeight d := by
  rcases Finset.mem_filter.mp hcp with ⟨hcpSq, hcgt⟩
  rcases mem_lowWheelFarPrimeSquarefreePairSet.mp hcpSq with
    ⟨hcpFar, hcsq⟩
  rcases mem_lowWheelFarPrimePairSet.mp hcpFar with
    ⟨hcRange, hpRange, hpPrime, hcpX⟩
  rcases Finset.mem_Ico.mp hcRange with ⟨_hc1, hcR⟩
  rcases Finset.mem_Icc.mp hpRange with ⟨hpFar, _hpX⟩
  let q := canonicalLargestPrimeFactor c
  let d := canonicalCofactor c
  have hqPrime : q.Prime := by
    dsimp [q]
    exact canonicalLargestPrimeFactor_prime hcgt
  have hprod0 : canonicalCofactor c * canonicalLargestPrimeFactor c = c :=
    canonicalCofactor_mul_largestPrimeFactor hcgt
  have hprod : q * d = c := by
    dsimp [q, d]
    simpa [Nat.mul_comm] using hprod0
  have hqDvd : q ∣ c := by
    dsimp [q]
    exact canonicalLargestPrimeFactor_dvd hcgt
  have hcpos : 0 < c := by omega
  have hqLeC : q ≤ c := Nat.le_of_dvd hcpos hqDvd
  have hqR : q < R := hqLeC.trans_lt hcR
  have hpR : R < p := by omega
  have hqp : q < p := hqR.trans hpR
  have hdSq : Squarefree d := by
    dsimp [d]
    exact squarefree_canonicalCofactor hcsq hcgt
  have hdLt : canonicalLargestPrimeFactor d < q := by
    dsimp [q, d]
    exact canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hcgt hcsq
  have hprodX : q * d * p ≤ squareRootEndpoint R := by
    simpa [hprod] using hcpX
  have hmuInt : μ c = -μ d := by
    dsimp [d]
    exact canonicalSignedParent_moebius hcsq hcgt
  have hweight : canonicalMoebiusWeight c = -canonicalMoebiusWeight d := by
    unfold canonicalMoebiusWeight
    rw [hmuInt]
    push_cast
    ring
  exact ⟨hqPrime, hqR, hpR, hpPrime, hdSq, hdLt, hprod, hqp, hprodX, hweight⟩

/-- The canonical tag loses no multiplicity on the nonunit far wall. -/
theorem lowWheelFarPrimeLowCofactorTag_injOn (R : ℕ) :
    Set.InjOn lowWheelFarPrimeLowCofactorTag
      (lowWheelFarPrimeNonUnitPairSet R : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  rcases a with ⟨c,p⟩
  rcases b with ⟨e,r⟩
  change
    (canonicalLargestPrimeFactor c, (canonicalCofactor c, p)) =
      (canonicalLargestPrimeFactor e, (canonicalCofactor e, r)) at hab
  have hq : canonicalLargestPrimeFactor c = canonicalLargestPrimeFactor e :=
    congrArg (fun z : ℕ × (ℕ × ℕ) => z.1) hab
  have hd : canonicalCofactor c = canonicalCofactor e :=
    congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1) hab
  have hp : p = r :=
    congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.2) hab
  have hcgt : 1 < c := by
    exact (Finset.mem_filter.mp ha).2
  have hegt : 1 < e := by
    exact (Finset.mem_filter.mp hb).2
  have hcprod := canonicalCofactor_mul_largestPrimeFactor hcgt
  have heprod := canonicalCofactor_mul_largestPrimeFactor hegt
  have hce : c = e := by
    calc
      c = canonicalCofactor c * canonicalLargestPrimeFactor c := hcprod.symm
      _ = canonicalCofactor e * canonicalLargestPrimeFactor e := by rw [hd, hq]
      _ = e := heprod
  exact Prod.ext hce hp

/-- Reindexing the nonunit far wall by `(q,d,p)` is exact for every additive
observable. -/
theorem lowWheelFarPrimeLowCofactorTriples_sum
    (R : ℕ) (f : ℕ × (ℕ × ℕ) → ℂ) :
    (∑ t ∈ lowWheelFarPrimeLowCofactorTriples R, f t) =
      ∑ cp ∈ lowWheelFarPrimeNonUnitPairSet R,
        f (lowWheelFarPrimeLowCofactorTag cp) := by
  unfold lowWheelFarPrimeLowCofactorTriples
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact lowWheelFarPrimeLowCofactorTag_injOn R ha hb hab

/-- Signed mass form: stripping the canonical largest low prime reverses the
Möbius sign once. -/
theorem lowWheelFarPrimeNonUnitPairMass_eq_neg_strippedMass (R : ℕ) :
    (∑ cp ∈ lowWheelFarPrimeNonUnitPairSet R,
        canonicalMoebiusWeight cp.1) =
      -∑ t ∈ lowWheelFarPrimeLowCofactorTriples R,
        canonicalMoebiusWeight t.2.1 := by
  rw [lowWheelFarPrimeLowCofactorTriples_sum R
    (fun t => canonicalMoebiusWeight t.2.1)]
  calc
    (∑ cp ∈ lowWheelFarPrimeNonUnitPairSet R,
        canonicalMoebiusWeight cp.1) =
      ∑ cp ∈ lowWheelFarPrimeNonUnitPairSet R,
        -canonicalMoebiusWeight (lowWheelFarPrimeLowCofactorTag cp).2.1 := by
          apply Finset.sum_congr rfl
          intro cp hcp
          rcases cp with ⟨c,p⟩
          have hdata := lowWheelFarPrimeNonUnitPair_data hcp
          dsimp [lowWheelFarPrimeLowCofactorTag]
          exact hdata.2.2.2.2.2.2.2.2.2
    _ = -∑ cp ∈ lowWheelFarPrimeNonUnitPairSet R,
        canonicalMoebiusWeight (lowWheelFarPrimeLowCofactorTag cp).2.1 := by
          rw [Finset.sum_neg_distrib]

/-- Triples whose second insertion of the canonical low prime still fits below
the old square endpoint. -/
def lowWheelFarPrimeQ2DescendedTriples (R : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeLowCofactorTriples R).filter fun t =>
    t.1 * t.1 * t.2.1 * t.2.2 ≤ squareRootEndpoint R

/-- Complementary strict second-contact crossing triples. -/
def lowWheelFarPrimeQ2CrossingTriples (R : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeLowCofactorTriples R).filter fun t =>
    squareRootEndpoint R < t.1 * t.1 * t.2.1 * t.2.2

/-- The nonunit far-wall triples partition exactly into the q^2-descended and
strict second-contact crossing populations. -/
theorem lowWheelFarPrimeLowCofactorTriples_sum_eq_descended_add_crossing
    (R : ℕ) (f : ℕ × (ℕ × ℕ) → ℂ) :
    (∑ t ∈ lowWheelFarPrimeLowCofactorTriples R, f t) =
      (∑ t ∈ lowWheelFarPrimeQ2DescendedTriples R, f t) +
        ∑ t ∈ lowWheelFarPrimeQ2CrossingTriples R, f t := by
  unfold lowWheelFarPrimeQ2DescendedTriples lowWheelFarPrimeQ2CrossingTriples
  have h := Finset.sum_filter_add_sum_filter_not
    (lowWheelFarPrimeLowCofactorTriples R)
    (fun t => t.1 * t.1 * t.2.1 * t.2.2 ≤ squareRootEndpoint R) f
  calc
    (∑ t ∈ lowWheelFarPrimeLowCofactorTriples R, f t) =
        (∑ t ∈ (lowWheelFarPrimeLowCofactorTriples R).filter
            (fun t => t.1 * t.1 * t.2.1 * t.2.2 ≤ squareRootEndpoint R), f t) +
          ∑ t ∈ (lowWheelFarPrimeLowCofactorTriples R).filter
            (fun t => ¬ t.1 * t.1 * t.2.1 * t.2.2 ≤ squareRootEndpoint R), f t :=
      h.symm
    _ = (∑ t ∈ (lowWheelFarPrimeLowCofactorTriples R).filter
            (fun t => t.1 * t.1 * t.2.1 * t.2.2 ≤ squareRootEndpoint R), f t) +
          ∑ t ∈ (lowWheelFarPrimeLowCofactorTriples R).filter
            (fun t => squareRootEndpoint R < t.1 * t.1 * t.2.1 * t.2.2), f t := by
      congr 1
      apply Finset.sum_congr
      · ext t
        simp
      · intro t ht
        rfl

end RHLean.Proof
