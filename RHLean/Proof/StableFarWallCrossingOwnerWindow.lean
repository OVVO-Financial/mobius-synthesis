import RHLean.Proof.StableFarWallUnitRenewalCentering
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.PrimeWheelProperSubwheelDepthTwo

/-!
# Exact outer-owner window of the centered stable-far renewal

After depth-one renewal, every nonunit crossing return lands at one descended
child `y = (r,(e,p))`.  The remaining coefficient is the number of old outer
owners `q` that could have produced that same child.

This file makes that multiplicity arithmetic.  The fibre over `y` is in
bijection, by the outer-owner coordinate, with the prime window

  r < q < R,
  q*r*e*p <= X_R < q^2*r*e*p.

No owner is discarded and no cardinality estimate is used.  This is the exact
prime-window coordinate on which a first-failure/Buchstab or prime-count
finite-difference argument can act.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Exact fibre of nonunit crossings returning to one descended child. -/
def lowWheelFarPrimeQ2CrossingNextFiber
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeQ2NonUnitCrossingTriples R).filter fun t =>
    lowWheelFarPrimeQ2CrossingNextChild t = y

/-- Arithmetic window of possible old outer owners for one descended child. -/
def lowWheelFarPrimeQ2CrossingOuterOwnerSet
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : Finset ℕ :=
  (primesUpTo (R - 1)).filter fun q =>
    y.1 < q ∧
      q * y.1 * y.2.1 * y.2.2 ≤ squareRootEndpoint R ∧
      squareRootEndpoint R < q * q * y.1 * y.2.1 * y.2.2

/-- A point in one next-child fibre has its stripped cofactor and far prime
uniquely recovered from the child. -/
theorem lowWheelFarPrimeQ2CrossingNextFiber_coordinates
    {R : ℕ} {y t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2CrossingNextFiber R y) :
    t.2.1 = y.1 * y.2.1 ∧ t.2.2 = y.2.2 := by
  have htNon := (Finset.mem_filter.mp ht).1
  have hnext := (Finset.mem_filter.mp ht).2
  have hdgt : 1 < t.2.1 := (Finset.mem_filter.mp htNon).2
  have hlpf : canonicalLargestPrimeFactor t.2.1 = y.1 :=
    congrArg (fun z : ℕ × (ℕ × ℕ) => z.1) hnext
  have hcof : canonicalCofactor t.2.1 = y.2.1 :=
    congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1) hnext
  have hpNext := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.2) hnext
  have hp : t.2.2 = y.2.2 := hpNext
  have hprod := canonicalCofactor_mul_largestPrimeFactor hdgt
  constructor
  · calc
      t.2.1 = canonicalCofactor t.2.1 *
          canonicalLargestPrimeFactor t.2.1 := hprod.symm
      _ = y.2.1 * y.1 := by rw [hcof, hlpf]
      _ = y.1 * y.2.1 := by ring
  · exact hp

/-- Forgetting everything except the old outer owner is injective on one
next-child fibre. -/
theorem lowWheelFarPrimeQ2CrossingNextFiber_fst_injOn
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) :
    Set.InjOn Prod.fst (lowWheelFarPrimeQ2CrossingNextFiber R y :
      Set (ℕ × (ℕ × ℕ))) := by
  intro a ha b hb hq
  have haCoord := lowWheelFarPrimeQ2CrossingNextFiber_coordinates
    (Finset.mem_coe.mp ha)
  have hbCoord := lowWheelFarPrimeQ2CrossingNextFiber_coordinates
    (Finset.mem_coe.mp hb)
  apply Prod.ext hq
  apply Prod.ext
  · exact haCoord.1.trans hbCoord.1.symm
  · exact haCoord.2.trans hbCoord.2.symm

/-- **Exact owner-window classification.**  On an actual descended child, the
outer-owner projection of its renewal fibre is precisely the explicit prime
window `r<q<R`, `q*r*e*p<=X_R<q^2*r*e*p`. -/
theorem lowWheelFarPrimeQ2CrossingNextFiber_fst_image_eq_ownerSet
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    (lowWheelFarPrimeQ2CrossingNextFiber R y).image Prod.fst =
      lowWheelFarPrimeQ2CrossingOuterOwnerSet R y := by
  ext q
  constructor
  · intro hqImage
    rcases Finset.mem_image.mp hqImage with ⟨t, htFiber, htq⟩
    have htNon := (Finset.mem_filter.mp htFiber).1
    have htCross := (Finset.mem_filter.mp htNon).1
    have hbase : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp htCross).1
    have hcross := (Finset.mem_filter.mp htCross).2
    rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
      ⟨htPrime, htR, _hd1, _hpPrime, _hpR, _hdsq, hdq, hcut⟩
    have hnext := (Finset.mem_filter.mp htFiber).2
    have hlpf : canonicalLargestPrimeFactor t.2.1 = y.1 :=
      congrArg (fun z : ℕ × (ℕ × ℕ) => z.1) hnext
    have hcoord := lowWheelFarPrimeQ2CrossingNextFiber_coordinates htFiber
    subst q
    apply Finset.mem_filter.mpr
    refine ⟨mem_primesUpTo.mpr ⟨htPrime, Nat.le_pred_of_lt htR⟩, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hlpf] using hdq
    · simpa [hcoord.1, hcoord.2, Nat.mul_assoc] using hcut
    · simpa [hcoord.1, hcoord.2, Nat.mul_assoc] using hcross
  · intro hqOwner
    rcases Finset.mem_filter.mp hqOwner with ⟨hqOld, hrq, hcut, hcross⟩
    have hqData := mem_primesUpTo.mp hqOld
    have hyBase : y ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp hy).1
    rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
      ⟨hrPrime, hrR, he1, hpPrime, hpR, heSq, her, _hyCut⟩
    have hRpos : 0 < R := hrPrime.pos.trans hrR
    have hqR : q < R := Nat.lt_of_le_pred hRpos hqData.2
    have hnot : ¬ y.1 ∣ y.2.1 :=
      squareRootLowPrimePrime_fresh_of_lpf_lt he1 hrPrime her
    have hcop : Nat.Coprime y.1 y.2.1 :=
      (hrPrime.coprime_iff_not_dvd).2 hnot
    have hdSq : Squarefree (y.1 * y.2.1) :=
      (Nat.squarefree_mul hcop).2 ⟨hrPrime.squarefree, heSq⟩
    have hd1 : 1 ≤ y.1 * y.2.1 := by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hrPrime.ne_zero (by omega))
    have hlpf : canonicalLargestPrimeFactor (y.1 * y.2.1) = y.1 := by
      have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        (by omega : 0 < y.2.1) hrPrime her
      simpa [Nat.mul_comm] using h
    have hcof : canonicalCofactor (y.1 * y.2.1) = y.2.1 := by
      have h := canonicalCofactor_mul_prime_eq_of_rough
        (by omega : 0 < y.2.1) hrPrime her
      simpa [Nat.mul_comm] using h
    have hdq : canonicalLargestPrimeFactor (y.1 * y.2.1) < q := by
      rw [hlpf]
      exact hrq
    have htriple :
        (q, (y.1 * y.2.1, y.2.2)) ∈ lowWheelFarPrimeLowCofactorTriples R := by
      apply lowWheelFarPrimeLowCofactorTriple_mem_of_data
        hqData.1 hqR hd1 hpPrime hpR hdSq hdq
      simpa [Nat.mul_assoc] using hcut
    have hcrossTriple :
        (q, (y.1 * y.2.1, y.2.2)) ∈ lowWheelFarPrimeQ2CrossingTriples R :=
      Finset.mem_filter.mpr ⟨htriple, by
        simpa [Nat.mul_assoc] using hcross⟩
    have hdgt : 1 < y.1 * y.2.1 := by
      have hr2 := hrPrime.two_le
      nlinarith
    have hnon :
        (q, (y.1 * y.2.1, y.2.2)) ∈
          lowWheelFarPrimeQ2NonUnitCrossingTriples R :=
      Finset.mem_filter.mpr ⟨hcrossTriple, hdgt⟩
    have hnext :
        lowWheelFarPrimeQ2CrossingNextChild
            (q, (y.1 * y.2.1, y.2.2)) = y := by
      simp [lowWheelFarPrimeQ2CrossingNextChild, hlpf, hcof]
    have hfiber :
        (q, (y.1 * y.2.1, y.2.2)) ∈
          lowWheelFarPrimeQ2CrossingNextFiber R y :=
      Finset.mem_filter.mpr ⟨hnon, hnext⟩
    exact Finset.mem_image.mpr
      ⟨(q, (y.1 * y.2.1, y.2.2)), hfiber, rfl⟩

/-- **Multiplicity is exactly prime-window cardinality.**  The centered
coefficient introduced in the renewal normal form is not an opaque fibre count:
it is the number of primes in the explicit second-contact owner window. -/
theorem lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_ownerSet_card
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingNextMultiplicity R y =
      (lowWheelFarPrimeQ2CrossingOuterOwnerSet R y).card := by
  have himage := lowWheelFarPrimeQ2CrossingNextFiber_fst_image_eq_ownerSet hy
  have hinj := lowWheelFarPrimeQ2CrossingNextFiber_fst_injOn R y
  calc
    lowWheelFarPrimeQ2CrossingNextMultiplicity R y =
        (lowWheelFarPrimeQ2CrossingNextFiber R y).card := by rfl
    _ = ((lowWheelFarPrimeQ2CrossingNextFiber R y).image Prod.fst).card := by
      symm
      exact Finset.card_image_iff.mpr hinj
    _ = (lowWheelFarPrimeQ2CrossingOuterOwnerSet R y).card := by rw [himage]

/-! ## Reciprocal-depth normal form of the owner window

The two inequalities in the physical owner window can be solved exactly for
`q`.  If `A = r*e*p` and `T = floor(X_R/A)`, then

`q*A <= X_R < q^2*A`

is equivalent to

`sqrt(T) < q <= T`.

Thus the many-to-one renewal coefficient is a prime-count finite difference on
one literal multiplicative interval.  This is the interface needed by a signed
Buchstab/Abel argument; no estimate is introduced here.
-/

/-- Reciprocal depth attached to one descended child. -/
def lowWheelFarPrimeQ2CrossingOwnerDepth
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : ℕ :=
  squareRootEndpoint R / (y.1 * y.2.1 * y.2.2)

/-- Lower endpoint of the solved owner window. -/
def lowWheelFarPrimeQ2CrossingOwnerLower
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : ℕ :=
  max y.1 (Nat.sqrt (lowWheelFarPrimeQ2CrossingOwnerDepth R y))

/-- Upper endpoint of the solved owner window. -/
def lowWheelFarPrimeQ2CrossingOwnerUpper
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : ℕ :=
  min (R - 1) (lowWheelFarPrimeQ2CrossingOwnerDepth R y)

/-- **Solved owner window.**  On every actual descended child, the old owners
are exactly the primes in one interval `(max(r,sqrt T), min(R-1,T)]`. -/
theorem lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_primeInterval
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOuterOwnerSet R y =
      (Finset.Ioc (lowWheelFarPrimeQ2CrossingOwnerLower R y)
        (lowWheelFarPrimeQ2CrossingOwnerUpper R y)).filter Nat.Prime := by
  have hyBase : y ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
    ⟨hrPrime, _hrR, he1, hpPrime, _hpR, _heSq, _her, _hyCut⟩
  let A : ℕ := y.1 * y.2.1 * y.2.2
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.mul_pos (Nat.mul_pos hrPrime.pos (by omega)) hpPrime.pos
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqOld, hrq, hcut, hcross⟩
    rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqR⟩
    have hqDepth : q ≤ lowWheelFarPrimeQ2CrossingOwnerDepth R y := by
      unfold lowWheelFarPrimeQ2CrossingOwnerDepth
      apply (Nat.le_div_iff_mul_le hApos).2
      simpa [A, Nat.mul_assoc] using hcut
    have hdepthSq :
        lowWheelFarPrimeQ2CrossingOwnerDepth R y < q * q := by
      unfold lowWheelFarPrimeQ2CrossingOwnerDepth
      apply (Nat.div_lt_iff_lt_mul hApos).2
      simpa [A, Nat.mul_assoc] using hcross
    have hsqrt :
        Nat.sqrt (lowWheelFarPrimeQ2CrossingOwnerDepth R y) < q := by
      apply (Nat.sqrt_lt').2
      simpa [pow_two] using hdepthSq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hqPrime⟩
    · unfold lowWheelFarPrimeQ2CrossingOwnerLower
      exact max_lt hrq hsqrt
    · unfold lowWheelFarPrimeQ2CrossingOwnerUpper
      exact le_min hqR hqDepth
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqInterval, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqInterval with ⟨hlower, hupper⟩
    have hrq : y.1 < q := by
      exact lt_of_le_of_lt (le_max_left _ _) hlower
    have hsqrt :
        Nat.sqrt (lowWheelFarPrimeQ2CrossingOwnerDepth R y) < q := by
      exact lt_of_le_of_lt (le_max_right _ _) hlower
    have hqBounds := le_min_iff.mp hupper
    have hqR : q ≤ R - 1 := hqBounds.1
    have hqDepth : q ≤ lowWheelFarPrimeQ2CrossingOwnerDepth R y := hqBounds.2
    have hcut : q * y.1 * y.2.1 * y.2.2 ≤ squareRootEndpoint R := by
      have hmul := (Nat.le_div_iff_mul_le hApos).1 hqDepth
      simpa [lowWheelFarPrimeQ2CrossingOwnerDepth, A, Nat.mul_assoc] using hmul
    have hdepthSq :
        lowWheelFarPrimeQ2CrossingOwnerDepth R y < q * q := by
      have hs := (Nat.sqrt_lt').1 hsqrt
      simpa [pow_two] using hs
    have hcross : squareRootEndpoint R < q * q * y.1 * y.2.1 * y.2.2 := by
      have hmul := (Nat.div_lt_iff_lt_mul hApos).1 hdepthSq
      simpa [lowWheelFarPrimeQ2CrossingOwnerDepth, A, Nat.mul_assoc] using hmul
    apply Finset.mem_filter.mpr
    exact ⟨mem_primesUpTo.mpr ⟨hqPrime, hqR⟩, hrq, hcut, hcross⟩

/-- The renewal multiplicity is therefore the cardinality of that solved prime
interval. -/
theorem lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_primeInterval_card
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingNextMultiplicity R y =
      ((Finset.Ioc (lowWheelFarPrimeQ2CrossingOwnerLower R y)
        (lowWheelFarPrimeQ2CrossingOwnerUpper R y)).filter Nat.Prime).card := by
  rw [lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_ownerSet_card hy,
    lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_primeInterval hy]

/-- Whenever the solved interval is ordered, the exact multiplicity is the
corresponding prime-count finite difference, written additively to avoid
truncated subtraction. -/
theorem lowWheelFarPrimeQ2CrossingNextMultiplicity_add_primeCounting_lower_eq_upper
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (hLU : lowWheelFarPrimeQ2CrossingOwnerLower R y ≤
      lowWheelFarPrimeQ2CrossingOwnerUpper R y) :
    lowWheelFarPrimeQ2CrossingNextMultiplicity R y +
        Nat.primeCounting (lowWheelFarPrimeQ2CrossingOwnerLower R y) =
      Nat.primeCounting (lowWheelFarPrimeQ2CrossingOwnerUpper R y) := by
  rw [lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_primeInterval_card hy]
  exact primeCard_Ioc_add_primeCounting_eq hLU

/-! ## Euler telescope on the actual stable-far owner window -/

/-- On every descended stable-far child the reciprocal owner depth is strictly
below the physical root.  The far-prime coordinate alone supplies the strict
scale drop. -/
theorem lowWheelFarPrimeQ2CrossingOwnerDepth_lt_root
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOwnerDepth R y < R := by
  have hyBase : y ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
    ⟨hrPrime, hrR, he1, hpPrime, hpR, _heSq, _her, _hyCut⟩
  let A : ℕ := y.1 * y.2.1 * y.2.2
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.mul_pos (Nat.mul_pos hrPrime.pos (by omega)) hpPrime.pos
  unfold lowWheelFarPrimeQ2CrossingOwnerDepth
  apply (Nat.div_lt_iff_lt_mul hApos).2
  have hRpos : 0 < R := hrPrime.pos.trans hrR
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  have hre : 1 ≤ y.1 * y.2.1 := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hrPrime.ne_zero (by omega))
  have hpLeA : y.2.2 ≤ A := by
    dsimp [A]
    have h := Nat.mul_le_mul_right y.2.2 hre
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hRA : R < A := by
    have hRp : R < y.2.2 := by omega
    exact hRp.trans_le hpLeA
  have hRRlt : R * R < R * A :=
    Nat.mul_lt_mul_of_pos_left hRA hRpos
  exact hXlt.trans hRRlt

/-- Consequently the nominal `R-1` cap in the solved owner window is inactive. -/
theorem lowWheelFarPrimeQ2CrossingOwnerUpper_eq_depth
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOwnerUpper R y =
      lowWheelFarPrimeQ2CrossingOwnerDepth R y := by
  unfold lowWheelFarPrimeQ2CrossingOwnerUpper
  have hlt := lowWheelFarPrimeQ2CrossingOwnerDepth_lt_root hy
  have hle : lowWheelFarPrimeQ2CrossingOwnerDepth R y ≤ R - 1 :=
    Nat.le_pred_of_lt hlt
  exact min_eq_right hle

/-- The child's own returned owner and the square-root threshold both lie below
its reciprocal depth. -/
theorem lowWheelFarPrimeQ2CrossingOwnerLower_le_depth
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOwnerLower R y ≤
      lowWheelFarPrimeQ2CrossingOwnerDepth R y := by
  have hyBase : y ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
    ⟨hrPrime, _hrR, he1, hpPrime, _hpR, _heSq, _her, _hyCut⟩
  have hdesc := (Finset.mem_filter.mp hy).2
  let A : ℕ := y.1 * y.2.1 * y.2.2
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.mul_pos (Nat.mul_pos hrPrime.pos (by omega)) hpPrime.pos
  have hrDepth : y.1 ≤ lowWheelFarPrimeQ2CrossingOwnerDepth R y := by
    unfold lowWheelFarPrimeQ2CrossingOwnerDepth
    apply (Nat.le_div_iff_mul_le hApos).2
    simpa [A, Nat.mul_assoc] using hdesc
  have hsqrtDepth :
      Nat.sqrt (lowWheelFarPrimeQ2CrossingOwnerDepth R y) ≤
        lowWheelFarPrimeQ2CrossingOwnerDepth R y :=
    Nat.sqrt_le_self _
  unfold lowWheelFarPrimeQ2CrossingOwnerLower
  exact max_le hrDepth hsqrtDepth

/-- **Canonical stable-far owner interval.**  The actual old owners returning to
one descended child are exactly the primes in `(max(r,sqrt T), T]`; no root cap
remains. -/
theorem lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_depthPrimeInterval
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOuterOwnerSet R y =
      (Finset.Ioc (lowWheelFarPrimeQ2CrossingOwnerLower R y)
        (lowWheelFarPrimeQ2CrossingOwnerDepth R y)).filter Nat.Prime := by
  rw [lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_primeInterval hy,
    lowWheelFarPrimeQ2CrossingOwnerUpper_eq_depth hy]

/-- The renewal multiplicity is the prime count on that uncapped reciprocal
owner interval. -/
theorem lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_depthPrimeInterval_card
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingNextMultiplicity R y =
      ((Finset.Ioc (lowWheelFarPrimeQ2CrossingOwnerLower R y)
        (lowWheelFarPrimeQ2CrossingOwnerDepth R y)).filter Nat.Prime).card := by
  rw [lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_ownerSet_card hy,
    lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_depthPrimeInterval hy]

/-- The square-root lower endpoint forces the cubic proper-subwheel condition at
one reciprocal depth. -/
private theorem crossingOwnerDepth_lt_lowerSuccCube
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) :
    lowWheelFarPrimeQ2CrossingOwnerDepth R y <
      (lowWheelFarPrimeQ2CrossingOwnerLower R y + 1) ^ 3 := by
  let T := lowWheelFarPrimeQ2CrossingOwnerDepth R y
  let Y := lowWheelFarPrimeQ2CrossingOwnerLower R y
  have hroot : Nat.sqrt T ≤ Y := by
    dsimp [Y, T, lowWheelFarPrimeQ2CrossingOwnerLower]
    exact le_max_right _ _
  have hsucc : Nat.sqrt T + 1 ≤ Y + 1 := Nat.add_le_add_right hroot 1
  have hT : T < (Nat.sqrt T + 1) ^ 2 := Nat.lt_succ_sqrt' T
  have hsq : (Nat.sqrt T + 1) ^ 2 ≤ (Y + 1) ^ 2 :=
    Nat.pow_le_pow_left hsucc 2
  have hone : 1 ≤ Y + 1 := Nat.succ_le_succ (Nat.zero_le Y)
  have hcube : (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 := by
    calc
      (Y + 1) ^ 2 = 1 * (Y + 1) ^ 2 := by simp
      _ ≤ (Y + 1) * (Y + 1) ^ 2 :=
        Nat.mul_le_mul_right ((Y + 1) ^ 2) hone
      _ = (Y + 1) ^ 3 := by ring
  dsimp [T, Y] at hT hsq hcube ⊢
  exact hT.trans_le (hsq.trans hcube)

/-- **Stable-far Euler updates telescope before squaring.**  For every actual
descended child, advance the frozen base through its entire solved old-owner
window and subtract the matching moving boundary at the same time.  The whole
first-power owner chronology disappears exactly.  What remains is the ordinary
lower Mertens endpoint at reciprocal depth `T` plus the literal square-daughter
column `M(T/q^2)` on the same owner interval.

No norm, triangle inequality, PNT estimate, or RH-scale hypothesis is used. -/
theorem lowWheelFarPrimeQ2CrossingOwnerWindow_telescope
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    frozenPrimeUniverseMass
          (primesUpTo (lowWheelFarPrimeQ2CrossingOwnerLower R y))
          (lowWheelFarPrimeQ2CrossingOwnerDepth R y) -
        (∑ q ∈ frozenPrimeUniverseHighPrimeSet
            (lowWheelFarPrimeQ2CrossingOwnerLower R y)
            (lowWheelFarPrimeQ2CrossingOwnerDepth R y),
          frozenPrimeUniverseMass (primesUpTo q)
            (lowWheelFarPrimeQ2CrossingOwnerDepth R y / q)) =
      mertensSummatoryInt (lowWheelFarPrimeQ2CrossingOwnerDepth R y) +
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet
            (lowWheelFarPrimeQ2CrossingOwnerLower R y)
            (lowWheelFarPrimeQ2CrossingOwnerDepth R y),
          mertensSummatoryInt
            (lowWheelFarPrimeQ2CrossingOwnerDepth R y / (q * q)) := by
  let T := lowWheelFarPrimeQ2CrossingOwnerDepth R y
  let Y := lowWheelFarPrimeQ2CrossingOwnerLower R y
  have hYT : Y ≤ T := by
    dsimp [Y, T]
    exact lowWheelFarPrimeQ2CrossingOwnerLower_le_depth hy
  have hcubic : T < (Y + 1) ^ 3 := by
    dsimp [Y, T]
    exact crossingOwnerDepth_lt_lowerSuccCube R y
  have htel :=
    properSubwheel_base_sub_boundaryPrefix_eq_advancedBase_add_squares
      T Y T hYT le_rfl hcubic
  rw [frozenPrimeUniverseMass_primesUpTo_self_eq_mertensSummatoryInt] at htel
  simpa [T, Y] using htel

end RHLean.Proof
