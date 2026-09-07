import Mathlib
import RHLean.Geometry.ComplexSquareRecovery
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SignedPrefixEventLifetime

/-!
# Ordered Euler cut projection

The final oriented square-root boundary is not treated here as unrelated
coordinate systems. One tagged occurrence `(t,(c,p))` is kept intact and
projected simultaneously to

* the low Boolean-face product `a = P(t)`;
* the crossing prime `p`;
* the rough high cofactor `c`;
* the squarefree parent integer `m = c*a`;
* the fresh-prime child integer `n = c*(p*a)`;
* the half-open root lifetime in which the occurrence remains exposed.

On the actual oriented carrier the quotient coordinate is already the canonical
pivot. Every face prime is below that pivot and every cofactor prime is above it.
Consequently the signed low-wheel weight is the ordinary Möbius weight of `m`,
and adjoining the crossing prime changes it to its negative.

The main theorem gives an exact static lifetime representation. For a valid
ordered cut, membership in the oriented tagged boundary at root `R` is equivalent
to one interval condition `birthRoot <= R < deathRoot`. Thus the same atom can
be followed through all square roots without rebuilding its sign or factor
coordinates at each endpoint.

No norm, asymptotic estimate, prime-gap input, independence assumption, PNT input,
or RH hypothesis appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- One occurrence of the canonically oriented boundary, with its Boolean face
retained. -/
abbrev OrderedEulerCutTaggedState :=
  Finset ℕ × LowWheelCofactorQuotientState

/-- Static arithmetic validity of an ordered Euler cut. This predicate has no
root parameter: it records only factor ordering and squarefree data. -/
def OrderedEulerCutShape (y : OrderedEulerCutTaggedState) : Prop :=
  y.2.2.Prime ∧
    1 ≤ y.2.1 ∧
    Squarefree y.2.1 ∧
    ¬ y.2.2 ∣ y.2.1 ∧
    (∀ q ∈ y.1, q.Prime ∧ q < y.2.2) ∧
    RoughAbove y.2.2 y.2.1

/-- Product of all already-processed face primes, i.e. the root-side parent. -/
def orderedEulerCutLowProduct (y : OrderedEulerCutTaggedState) : ℕ :=
  primeFaceProduct y.1

/-- The distinguished crossing prime. -/
def orderedEulerCutPivot (y : OrderedEulerCutTaggedState) : ℕ :=
  y.2.2

/-- The rough cofactor whose prime factors lie strictly above the crossing
prime. -/
def orderedEulerCutHighCofactor (y : OrderedEulerCutTaggedState) : ℕ :=
  y.2.1

/-- The squarefree parent integer before the crossing prime is inserted. -/
def orderedEulerCutParentInteger (y : OrderedEulerCutTaggedState) : ℕ :=
  orderedEulerCutHighCofactor y * orderedEulerCutLowProduct y

/-- The physical child integer after the crossing prime is inserted. -/
def orderedEulerCutChildInteger (y : OrderedEulerCutTaggedState) : ℕ :=
  orderedEulerCutHighCofactor y *
    (orderedEulerCutPivot y * orderedEulerCutLowProduct y)

/-- Signed occurrence weight in the native low-wheel coordinates. -/
def orderedEulerCutWeight (y : OrderedEulerCutTaggedState) : ℂ :=
  canonicalMoebiusWeight (orderedEulerCutHighCofactor y) *
    (booleanCubeSign y.1 : ℂ)

/-- Root at which all monotone entrance constraints for the occurrence have
become true. The three pieces are `P(t) <= R`, `c < R`, and the physical square
cutoff `c*p*P(t) <= R^2-1`. -/
def orderedEulerCutBirthRoot (y : OrderedEulerCutTaggedState) : ℕ :=
  max (orderedEulerCutLowProduct y)
    (max (orderedEulerCutHighCofactor y + 1)
      (Nat.sqrt (orderedEulerCutChildInteger y) + 1))

/-- Root at which the missing fresh-prime partner becomes complete. -/
def orderedEulerCutDeathRoot (y : OrderedEulerCutTaggedState) : ℕ :=
  orderedEulerCutPivot y * orderedEulerCutLowProduct y

/-- The root-dependent tagged oriented occurrence predicate. -/
def OrderedEulerCutOccursAt (R : ℕ) (y : OrderedEulerCutTaggedState) : Prop :=
  y.1 ∈ (primesUpTo R).powerset ∧
    y.2 ∈ lowWheelCanonicalDowncrossOrientedPart R y.1

/-- Concrete finite tagged occurrence carrier at one root. -/
def orderedEulerCutCarrier (R : ℕ) : Finset OrderedEulerCutTaggedState :=
  ((primesUpTo R).powerset.product
      (lowWheelCanonicalDowncrossOrientedStateAmbient R)).filter fun y =>
    y.2 ∈ lowWheelCanonicalDowncrossOrientedPart R y.1

@[simp] theorem mem_orderedEulerCutCarrier
    {R : ℕ} {y : OrderedEulerCutTaggedState} :
    y ∈ orderedEulerCutCarrier R ↔ OrderedEulerCutOccursAt R y := by
  constructor
  · intro hy
    have h := Finset.mem_filter.mp hy
    have hp := Finset.mem_product.mp h.1
    exact ⟨hp.1, h.2⟩
  · rintro ⟨ht, hx⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨ht, ?_⟩, hx⟩
    exact lowWheelCanonicalDowncrossOrientedPart_subset_stateAmbient hx

/-- A prime divisor which is minimal among all prime divisors is `minFac`. -/
private theorem minFac_eq_of_prime_dvd_and_le_prime_divisors
    {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hle : ∀ r, r.Prime → r ∣ n → p ≤ r) :
    Nat.minFac n = p := by
  have hminLe : Nat.minFac n ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le hpn
  have hn1 : n ≠ 1 := by
    intro hn
    have hp1 : p ∣ 1 := by simpa [hn] using hpn
    have hpEq : p = 1 := Nat.dvd_one.mp hp1
    exact hp.ne_one hpEq
  have hminPrime : (Nat.minFac n).Prime := Nat.minFac_prime hn1
  have hminDvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have hpLeMin : p ≤ Nat.minFac n := hle _ hminPrime hminDvd
  exact Nat.le_antisymm hminLe hpLeMin

/-- The static ordering data force the quotient coordinate to be its own
canonical least-prime pivot. -/
theorem orderedEulerCutShape_canonicalPivot
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    lowWheelCanonicalDowncrossPivot y.2 = orderedEulerCutPivot y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨hp, hc1, _hcsq, _hpc, _hfaces, hrough⟩
  change Nat.minFac (c * p) = p
  have hc0 : c ≠ 0 := by omega
  apply minFac_eq_of_prime_dvd_and_le_prime_divisors hp
  · exact dvd_mul_left p c
  · intro r hr hrd
    rcases hr.dvd_mul.mp hrd with hrc | hrp
    · have hrcMem : r ∈ c.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hr, hrc, hc0⟩
      exact Nat.le_of_lt (hrough r hrcMem)
    · have hre : r = p :=
        (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
      simp [hre]

/-- Face products are positive for every ordered cut. -/
theorem orderedEulerCutLowProduct_pos
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    0 < orderedEulerCutLowProduct y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨_hp, _hc1, _hcsq, _hpc, hfaces, _hrough⟩
  change 0 < primeFaceProduct t
  have ht : t ∈ (primesUpTo p).powerset := by
    apply Finset.mem_powerset.mpr
    intro q hq
    exact mem_primesUpTo.mpr
      ⟨(hfaces q hq).1, Nat.le_of_lt (hfaces q hq).2⟩
  exact primeFaceProduct_pos_of_mem_powerset ht

/-- The crossing prime is fresh to the complete low face product. -/
theorem orderedEulerCutPivot_not_dvd_lowProduct
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    ¬ orderedEulerCutPivot y ∣ orderedEulerCutLowProduct y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨hp, _hc1, _hcsq, _hpc, hfaces, _hrough⟩
  change ¬ p ∣ primeFaceProduct t
  intro hpdiv
  have hpdiv' : p ∣ t.prod id := by
    simpa [primeFaceProduct] using hpdiv
  rcases (Prime.dvd_finset_prod_iff hp.prime id).mp hpdiv' with
    ⟨q, hqt, hpq⟩
  have hqPrime := (hfaces q hqt).1
  have hpEq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hqPrime).mp hpq
  have hlt := (hfaces q hqt).2
  rw [← hpEq] at hlt
  exact (Nat.lt_irrefl p) hlt

/-- The low face product is a canonical ancestry core below the distinguished
crossing prime. -/
theorem orderedEulerCut_lowSourceData
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    CanonicalSourceData (orderedEulerCutPivot y)
      (orderedEulerCutLowProduct y) := by
  have hlowPos0 := orderedEulerCutLowProduct_pos hy
  have hpNot0 := orderedEulerCutPivot_not_dvd_lowProduct hy
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨hp, _hc1, _hcsq, _hpc, hfaces, _hrough⟩
  have hlowPos : 0 < primeFaceProduct t := by
    simpa [orderedEulerCutLowProduct] using hlowPos0
  have hpNot : ¬ p ∣ primeFaceProduct t := by
    simpa [orderedEulerCutPivot, orderedEulerCutLowProduct] using hpNot0
  have hmu : μ (primeFaceProduct t) = booleanCubeSign t :=
    moebius_primeFaceProduct_eq_booleanCubeSign t
      (fun q hq => (hfaces q hq).1)
  have hmuNe : μ (primeFaceProduct t) ≠ 0 := by
    rw [hmu]
    unfold booleanCubeSign
    exact pow_ne_zero _ (by norm_num)
  have hsq : Squarefree (primeFaceProduct t) :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
  have hcop : Nat.Coprime p (primeFaceProduct t) :=
    (hp.coprime_iff_not_dvd).2 hpNot
  change CanonicalSourceData p (primeFaceProduct t)
  refine ⟨hp, Nat.succ_le_iff.mpr hlowPos, hsq, hcop, ?_⟩
  intro q hqPrime hqDvd
  have hqProd : q ∣ t.prod id := by
    simpa [primeFaceProduct] using hqDvd
  rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqProd with
    ⟨r, hrt, hqr⟩
  have hrPrime := (hfaces r hrt).1
  have hqrEq : q = r :=
    (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
  subst q
  exact (hfaces r hrt).2

/-- The rough high cofactor and low face product have disjoint prime support. -/
theorem orderedEulerCut_highCofactor_coprime_lowProduct
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    Nat.Coprime (orderedEulerCutHighCofactor y)
      (orderedEulerCutLowProduct y) := by
  have hlowPos0 := orderedEulerCutLowProduct_pos hy
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨_hp, hc1, _hcsq, _hpc, hfaces, hrough⟩
  have hc0 : c ≠ 0 := by omega
  have ha0 : primeFaceProduct t ≠ 0 := by
    have hpos : 0 < primeFaceProduct t := by
      simpa [orderedEulerCutLowProduct] using hlowPos0
    exact Nat.ne_of_gt hpos
  change Nat.Coprime c (primeFaceProduct t)
  rw [← Nat.disjoint_primeFactors hc0 ha0]
  rw [Finset.disjoint_left]
  intro q hqc hqa
  have hqHigh : p < q := hrough q hqc
  rcases Nat.mem_primeFactors.mp hqa with ⟨hqPrime, hqDvd, _ha0⟩
  have hqProd : q ∣ t.prod id := by
    simpa [primeFaceProduct] using hqDvd
  rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqProd with
    ⟨r, hrt, hqr⟩
  have hrPrime := (hfaces r hrt).1
  have hqrEq : q = r :=
    (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
  subst q
  have hrLow := (hfaces r hrt).2
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hqHigh)) hrLow

/-- The native low-wheel sign is exactly the ordinary Möbius weight of the
single parent integer `c * P(t)`. -/
theorem orderedEulerCutWeight_eq_parentMoebius
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    orderedEulerCutWeight y =
      canonicalMoebiusWeight (orderedEulerCutParentInteger y) := by
  have hcop0 := orderedEulerCut_highCofactor_coprime_lowProduct hy
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨_hp, _hc1, _hcsq, _hpc, hfaces, _hrough⟩
  have hcop : Nat.Coprime c (primeFaceProduct t) := by
    simpa [orderedEulerCutHighCofactor, orderedEulerCutLowProduct] using hcop0
  have hface : μ (primeFaceProduct t) = booleanCubeSign t :=
    moebius_primeFaceProduct_eq_booleanCubeSign t
      (fun q hq => (hfaces q hq).1)
  have hmu : μ (c * primeFaceProduct t) = μ c * μ (primeFaceProduct t) :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  change canonicalMoebiusWeight c * (booleanCubeSign t : ℂ) =
    canonicalMoebiusWeight (c * primeFaceProduct t)
  unfold canonicalMoebiusWeight
  rw [hmu, hface]
  push_cast
  ring

/-- The crossing prime is fresh to the entire parent integer. -/
theorem orderedEulerCutPivot_not_dvd_parentInteger
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    ¬ orderedEulerCutPivot y ∣ orderedEulerCutParentInteger y := by
  have hpLow0 := orderedEulerCutPivot_not_dvd_lowProduct hy
  rcases y with ⟨t, ⟨c, p⟩⟩
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨hp, _hc1, _hcsq, hpc, _hfaces, _hrough⟩
  have hpLow : ¬ p ∣ primeFaceProduct t := by
    simpa [orderedEulerCutPivot, orderedEulerCutLowProduct] using hpLow0
  change ¬ p ∣ c * primeFaceProduct t
  intro hdiv
  rcases hp.dvd_mul.mp hdiv with hc | ha
  · exact hpc hc
  · exact hpLow ha

/-- **Euler sign reversal on the common integer coordinate.** The physical
child has exactly the opposite Möbius weight from the tagged parent occurrence. -/
theorem orderedEulerCutChildWeight_eq_neg
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    canonicalMoebiusWeight (orderedEulerCutChildInteger y) =
      -orderedEulerCutWeight y := by
  have hchild : orderedEulerCutChildInteger y =
      orderedEulerCutParentInteger y * orderedEulerCutPivot y := by
    unfold orderedEulerCutChildInteger orderedEulerCutParentInteger
      orderedEulerCutHighCofactor orderedEulerCutLowProduct orderedEulerCutPivot
    ring
  have hflip :
      canonicalMoebiusWeight
          (orderedEulerCutParentInteger y * orderedEulerCutPivot y) =
        -canonicalMoebiusWeight (orderedEulerCutParentInteger y) :=
    canonicalMoebiusWeight_mul_freshPrime hy.1
      (orderedEulerCutPivot_not_dvd_parentInteger hy)
  calc
    canonicalMoebiusWeight (orderedEulerCutChildInteger y) =
        canonicalMoebiusWeight
          (orderedEulerCutParentInteger y * orderedEulerCutPivot y) :=
      congrArg canonicalMoebiusWeight hchild
    _ = -canonicalMoebiusWeight (orderedEulerCutParentInteger y) := hflip
    _ = -orderedEulerCutWeight y := by
      exact congrArg (fun z : ℂ => -z)
        (orderedEulerCutWeight_eq_parentMoebius hy).symm

/-- A positive child lies below `R^2 - 1` exactly when its integer square root
is strictly below `R`. -/
theorem orderedEulerCutChild_le_endpoint_iff
    {R : ℕ} {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    orderedEulerCutChildInteger y ≤ squareRootEndpoint R ↔
      Nat.sqrt (orderedEulerCutChildInteger y) < R := by
  have hcpos : 0 < orderedEulerCutHighCofactor y := by
    exact lt_of_lt_of_le Nat.zero_lt_one hy.2.1
  have hchildPos : 0 < orderedEulerCutChildInteger y := by
    unfold orderedEulerCutChildInteger
    exact Nat.mul_pos hcpos
      (Nat.mul_pos hy.1.pos (orderedEulerCutLowProduct_pos hy))
  constructor
  · intro hle
    have hendPos : 0 < squareRootEndpoint R :=
      lt_of_lt_of_le hchildPos hle
    have hsqPos : 0 < R ^ 2 := by
      have hendLe : squareRootEndpoint R ≤ R ^ 2 := by
        unfold squareRootEndpoint
        exact Nat.sub_le _ _
      exact lt_of_lt_of_le hendPos hendLe
    have hendLt : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      exact Nat.sub_lt hsqPos (by norm_num)
    exact (Nat.sqrt_lt').2 (hle.trans_lt hendLt)
  · intro hsqrt
    have hlt : orderedEulerCutChildInteger y < R ^ 2 :=
      (Nat.sqrt_lt').1 hsqrt
    unfold squareRootEndpoint
    exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlt)

/-- **Exact lifetime characterization.** For a static ordered Euler cut, being
an oriented physical boundary occurrence at root `R` is equivalent to one
half-open lifetime interval. -/
theorem orderedEulerCutOccursAt_iff_lifetime
    {R : ℕ} {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    OrderedEulerCutOccursAt R y ↔
      orderedEulerCutBirthRoot y ≤ R ∧ R < orderedEulerCutDeathRoot y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  have hyShape : OrderedEulerCutShape (t, (c, p)) := hy
  change p.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ ¬ p ∣ c ∧
    (∀ q ∈ t, q.Prime ∧ q < p) ∧ RoughAbove p c at hy
  rcases hy with ⟨hp, hc1, hcsq, hpc, hfaces, hrough⟩
  have hpivot : lowWheelCanonicalDowncrossPivot (c, p) = p :=
    orderedEulerCutShape_canonicalPivot hyShape
  have hpivotCQ : lowWheelCanonicalCofactorQuotientPivot (c, p) = p := by
    exact hpivot
  have hlowPos : 0 < primeFaceProduct t := by
    simpa [orderedEulerCutLowProduct] using orderedEulerCutLowProduct_pos hyShape
  have hcpos : 0 < c := by omega
  constructor
  · rintro ⟨_ht, hx⟩
    have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
    have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
    dsimp only at hgeom
    have hparent := lowWheelCanonicalDowncrossOriented_parent_eq_faceProduct hx
    have hphys :=
      mem_lowWheelCanonicalPhysicalStateSet.mp
        (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
    have hcR : c < R := (Finset.mem_Ico.mp hphys.1).2
    have hparentR := hgeom.2.2.2.1
    rw [hparent] at hparentR
    have hdeath := hgeom.2.2.2.2.1
    rw [hpivot, hparent] at hdeath
    have hchild := hgeom.2.2.2.2.2
    rw [hpivot, hparent] at hchild
    have hchildWrapped :
        orderedEulerCutChildInteger (t, (c, p)) ≤ squareRootEndpoint R := by
      change c * (p * primeFaceProduct t) ≤ squareRootEndpoint R
      exact hchild
    have hsqrtWrapped :=
      (orderedEulerCutChild_le_endpoint_iff (R := R) hyShape).1 hchildWrapped
    have hsqrt : Nat.sqrt (c * (p * primeFaceProduct t)) < R := by
      exact hsqrtWrapped
    constructor
    · change max (primeFaceProduct t)
        (max (c + 1) (Nat.sqrt (c * (p * primeFaceProduct t)) + 1)) ≤ R
      apply Nat.max_le.mpr
      refine ⟨hparentR, Nat.max_le.mpr ⟨Nat.succ_le_iff.mpr hcR, ?_⟩⟩
      exact Nat.succ_le_iff.mpr hsqrt
    · change R < p * primeFaceProduct t
      exact hdeath
  · rintro ⟨hbirth, hdeath⟩
    change max (primeFaceProduct t)
      (max (c + 1) (Nat.sqrt (c * (p * primeFaceProduct t)) + 1)) ≤ R at hbirth
    change R < p * primeFaceProduct t at hdeath
    rcases Nat.max_le.mp hbirth with ⟨hlowR, hrest⟩
    rcases Nat.max_le.mp hrest with ⟨hcSuccR, hsqrtSuccR⟩
    have hcLt : c < R := Nat.lt_of_succ_le hcSuccR
    have hsqrt : Nat.sqrt (c * (p * primeFaceProduct t)) < R :=
      Nat.lt_of_succ_le hsqrtSuccR
    have hchild : c * (p * primeFaceProduct t) ≤ squareRootEndpoint R := by
      exact (orderedEulerCutChild_le_endpoint_iff (R := R) hyShape).2 hsqrt
    have htPow : t ∈ (primesUpTo R).powerset := by
      apply Finset.mem_powerset.mpr
      intro q hqt
      have hqData := hfaces q hqt
      have hqDvd : q ∣ primeFaceProduct t := by
        simpa [primeFaceProduct] using Finset.dvd_prod_of_mem id hqt
      have hqLe : q ≤ primeFaceProduct t := Nat.le_of_dvd hlowPos hqDvd
      exact mem_primesUpTo.mpr ⟨hqData.1, hqLe.trans hlowR⟩
    have hchildPos : 0 < c * (p * primeFaceProduct t) :=
      Nat.mul_pos hcpos (Nat.mul_pos hp.pos hlowPos)
    have hpDvdChild : p ∣ c * (p * primeFaceProduct t) := by
      refine ⟨c * primeFaceProduct t, ?_⟩
      ring
    have hpLeChild : p ≤ c * (p * primeFaceProduct t) :=
      Nat.le_of_dvd hchildPos hpDvdChild
    have hphysical : (c, p) ∈ lowWheelCanonicalPhysicalStateSet R t := by
      apply mem_lowWheelCanonicalPhysicalStateSet.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨hc1, hcLt⟩,
        Finset.mem_Icc.mpr ⟨hp.one_le, hpLeChild.trans hchild⟩,
        hcsq, ?_⟩
      unfold LowWheelTransportPairCarrier
      refine ⟨hc1, hcLt, ?_, ?_⟩
      · simpa [Nat.mul_comm] using hdeath
      · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hchild
    have hnotPivot :
        ¬ lowWheelCanonicalCofactorQuotientPivot (c, p) ∣ c := by
      rw [hpivotCQ]
      exact hpc
    have hdownLow :
        primeFaceProduct t *
            (p / lowWheelCanonicalCofactorQuotientPivot (c, p)) ≤ R := by
      rw [hpivotCQ, Nat.div_self hp.pos, Nat.mul_one]
      exact hlowR
    have hdown : (c, p) ∈ lowWheelCanonicalDowncrossPart R t :=
      mem_lowWheelCanonicalDowncrossPart.mpr
        ⟨hphysical, hnotPivot, hdownLow⟩
    have horiented : (c, p) ∈ lowWheelCanonicalDowncrossOrientedPart R t := by
      apply mem_lowWheelCanonicalDowncrossOrientedPart.mpr
      refine ⟨hdown, ?_⟩
      intro q hqParent
      unfold LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent at hqParent
      rw [hpivot, Nat.div_self hp.pos, Nat.mul_one] at hqParent
      rcases Nat.mem_primeFactors.mp hqParent with
        ⟨hqPrime, hqDvd, _hface0⟩
      have hqProd : q ∣ t.prod id := by
        simpa [primeFaceProduct] using hqDvd
      rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqProd with
        ⟨r, hrt, hqr⟩
      have hrPrime := (hfaces r hrt).1
      have hqrEq : q = r :=
        (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
      subst q
      rw [hpivot]
      exact (hfaces r hrt).2
    exact ⟨htPow, horiented⟩

/-- The abstract lifetime indicator applies literally to every static ordered
cut which occurs at `R`. -/
theorem orderedEulerCut_lifetimeActivity_eq_one
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hocc : OrderedEulerCutOccursAt R y) :
    lifetimeActivity (orderedEulerCutBirthRoot y)
        (orderedEulerCutDeathRoot y) R = 1 := by
  have hlife := (orderedEulerCutOccursAt_iff_lifetime hy).1 hocc
  unfold lifetimeActivity
  rw [if_pos hlife]

/-- Every actual tagged carrier point has the static ordered-cut shape. -/
theorem orderedEulerCutShape_of_mem_carrier
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : y ∈ orderedEulerCutCarrier R) : OrderedEulerCutShape y := by
  have hocc := mem_orderedEulerCutCarrier.mp hy
  rcases y with ⟨t, ⟨c, k⟩⟩
  rcases hocc with ⟨ht, hx⟩
  have hq : k = lowWheelCanonicalDowncrossPivot (c, k) :=
    lowWheelCanonicalDowncrossOriented_quotient_eq_pivot hx
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hphys :=
    mem_lowWheelCanonicalPhysicalStateSet.mp
      (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
  have hkPrime : k.Prime := by
    simpa only [← hq] using hgeom.1
  have hkNot : ¬ k ∣ c := by
    simpa only [← hq] using hgeom.2.1
  have hfaces : ∀ q ∈ t, q.Prime ∧ q < k := by
    intro q hqt
    have hqPrime := prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hqt)
    have hqLt := lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot ht hx hqt
    refine ⟨hqPrime, ?_⟩
    simpa only [← hq] using hqLt
  have hroughPivot := lowWheelCanonicalDowncrossOriented_cofactor_roughAbove hx
  have hrough : RoughAbove k c := by
    simpa only [← hq] using hroughPivot
  change OrderedEulerCutShape (t, (c, k))
  exact ⟨hkPrime, (Finset.mem_Ico.mp hphys.1).1, hphys.2.2.1,
    hkNot, hfaces, hrough⟩

/-- Hence the finite root carrier is literally the set of static ordered cuts
whose lifetime contains the current root. -/
theorem mem_orderedEulerCutCarrier_iff_shape_lifetime
    {R : ℕ} {y : OrderedEulerCutTaggedState} :
    y ∈ orderedEulerCutCarrier R ↔
      OrderedEulerCutShape y ∧
        orderedEulerCutBirthRoot y ≤ R ∧ R < orderedEulerCutDeathRoot y := by
  constructor
  · intro hy
    have hshape := orderedEulerCutShape_of_mem_carrier hy
    have hocc := mem_orderedEulerCutCarrier.mp hy
    exact ⟨hshape, (orderedEulerCutOccursAt_iff_lifetime hshape).1 hocc⟩
  · rintro ⟨hshape, hlife⟩
    apply mem_orderedEulerCutCarrier.mpr
    exact (orderedEulerCutOccursAt_iff_lifetime hshape).2 hlife

/-- **Simultaneous tagged projection of the oriented ledger.** The original
oriented boundary is exactly the signed sum over the common ordered-cut carrier.
The equality is before every norm and keeps the same atoms used by the lifetime,
Möbius-parent, and ancestry projections above. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_orderedEulerCutWeights
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      ∑ y ∈ orderedEulerCutCarrier R, orderedEulerCutWeight y := by
  unfold lowWheelCanonicalDowncrossOrientedLedger orderedEulerCutCarrier
    orderedEulerCutWeight orderedEulerCutHighCofactor
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t _ht
  change
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedPart R t,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
        if x ∈ lowWheelCanonicalDowncrossOrientedPart R t then
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)
        else 0
  exact sum_orientedPart_eq_sum_stateAmbient_indicator R t

/-!
## Squared Fermat realization of the same ordered-cut atom

The lifetime carrier above already contains the original complex/Fermat
geometry.  The two factors used here are the rough high cofactor `c` and the
death factor `q = p * P(t)`.  Their product is exactly the physical child
integer.  Squaring the associated Fermat point therefore places every ordered
cut on the vertical fibre whose real coordinate is that child integer.

For fixed `c` and low face product `a`, varying the crossing pivot `p` varies the
imaginary coordinate strictly monotonically.  Hence a pivot interval is exactly
a vertical-height interval, with no probabilistic or analytic input.
-/

open RHLean.Geometry

/-- The upper Fermat factor attached to one ordered cut.  It is exactly the root
at which the missing Euler partner becomes complete. -/
def orderedEulerCutUpperFactor (y : OrderedEulerCutTaggedState) : ℕ :=
  orderedEulerCutDeathRoot y

@[simp] theorem orderedEulerCutUpperFactor_eq
    (y : OrderedEulerCutTaggedState) :
    orderedEulerCutUpperFactor y =
      orderedEulerCutPivot y * orderedEulerCutLowProduct y := rfl

/-- The Fermat factor product is exactly the physical child integer. -/
@[simp] theorem orderedEulerCutHighCofactor_mul_upperFactor
    (y : OrderedEulerCutTaggedState) :
    orderedEulerCutHighCofactor y * orderedEulerCutUpperFactor y =
      orderedEulerCutChildInteger y := rfl

/-- The complex Fermat point of the ordered cut, using the factor pair
`(c, p * P(t))`. -/
noncomputable def orderedEulerCutFermatPoint
    (y : OrderedEulerCutTaggedState) : ℂ :=
  fermatPoint (orderedEulerCutHighCofactor y : ℝ)
    (orderedEulerCutUpperFactor y : ℝ)

/-- Imaginary coordinate of the squared Fermat point. -/
noncomputable def orderedEulerCutVerticalHeight
    (y : OrderedEulerCutTaggedState) : ℝ :=
  ((orderedEulerCutUpperFactor y : ℝ) ^ 2 -
      (orderedEulerCutHighCofactor y : ℝ) ^ 2) / 2

/-- Squaring straightens the ordered cut onto the vertical line whose real
coordinate is the child integer. -/
theorem orderedEulerCutFermatPoint_sq_re
    (y : OrderedEulerCutTaggedState) :
    ((orderedEulerCutFermatPoint y) ^ 2).re =
      (orderedEulerCutChildInteger y : ℝ) := by
  unfold orderedEulerCutFermatPoint
  rw [fermatPoint_sq_re]
  exact_mod_cast orderedEulerCutHighCofactor_mul_upperFactor y

/-- The vertical coordinate is exactly the Fermat imbalance
`(q^2-c^2)/2`. -/
theorem orderedEulerCutFermatPoint_sq_im
    (y : OrderedEulerCutTaggedState) :
    ((orderedEulerCutFermatPoint y) ^ 2).im =
      orderedEulerCutVerticalHeight y := by
  unfold orderedEulerCutFermatPoint orderedEulerCutVerticalHeight
  exact fermatPoint_sq_im
    (orderedEulerCutHighCofactor y : ℝ)
    (orderedEulerCutUpperFactor y : ℝ)

/-- Full squared-complex coordinate identity for one ordered cut. -/
theorem orderedEulerCutFermatPoint_sq
    (y : OrderedEulerCutTaggedState) :
    (orderedEulerCutFermatPoint y) ^ 2 =
      ⟨(orderedEulerCutChildInteger y : ℝ),
        orderedEulerCutVerticalHeight y⟩ := by
  apply Complex.ext
  · exact orderedEulerCutFermatPoint_sq_re y
  · exact orderedEulerCutFermatPoint_sq_im y

/-- During its exposed lifetime, the root lies strictly between the two Fermat
factors `c` and `p * P(t)`. -/
theorem orderedEulerCutOccursAt_factor_window
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hocc : OrderedEulerCutOccursAt R y) :
    orderedEulerCutHighCofactor y < R ∧
      R < orderedEulerCutUpperFactor y := by
  have hlife := (orderedEulerCutOccursAt_iff_lifetime hy).1 hocc
  have hbirth := hlife.1
  unfold orderedEulerCutBirthRoot at hbirth
  rcases Nat.max_le.mp hbirth with ⟨_hlow, hrest⟩
  rcases Nat.max_le.mp hrest with ⟨hcSucc, _hsqrtSucc⟩
  refine ⟨Nat.lt_of_succ_le hcSucc, ?_⟩
  change R < orderedEulerCutDeathRoot y
  exact hlife.2

/-- Exact discrete square-root demarcation of an exposed ordered cut:
`c <= floor(sqrt n) < R < q`, with `n = c*q`. -/
theorem orderedEulerCutOccursAt_sqrt_factor_window
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hocc : OrderedEulerCutOccursAt R y) :
    orderedEulerCutHighCofactor y ≤
        Nat.sqrt (orderedEulerCutChildInteger y) ∧
      Nat.sqrt (orderedEulerCutChildInteger y) < R ∧
      R < orderedEulerCutUpperFactor y := by
  have hfactor := orderedEulerCutOccursAt_factor_window hy hocc
  have hcq : orderedEulerCutHighCofactor y ≤ orderedEulerCutUpperFactor y :=
    Nat.le_of_lt (lt_trans hfactor.1 hfactor.2)
  have hsq :
      orderedEulerCutHighCofactor y * orderedEulerCutHighCofactor y ≤
        orderedEulerCutChildInteger y := by
    calc
      orderedEulerCutHighCofactor y * orderedEulerCutHighCofactor y ≤
          orderedEulerCutHighCofactor y * orderedEulerCutUpperFactor y :=
        Nat.mul_le_mul_left _ hcq
      _ = orderedEulerCutChildInteger y :=
        orderedEulerCutHighCofactor_mul_upperFactor y
  have hcsqrt :
      orderedEulerCutHighCofactor y ≤
        Nat.sqrt (orderedEulerCutChildInteger y) :=
    (Nat.le_sqrt).2 hsq
  have hlife := (orderedEulerCutOccursAt_iff_lifetime hy).1 hocc
  have hbirth := hlife.1
  unfold orderedEulerCutBirthRoot at hbirth
  rcases Nat.max_le.mp hbirth with ⟨_hlow, hrest⟩
  rcases Nat.max_le.mp hrest with ⟨_hcSucc, hsqrtSucc⟩
  exact ⟨hcsqrt, Nat.lt_of_succ_le hsqrtSucc, hfactor.2⟩

/-- Vertical height of a potential pivot on fixed cofactor/low-product data. -/
noncomputable def orderedEulerPivotVerticalHeight
    (c a p : ℕ) : ℝ :=
  ((((p * a : ℕ) : ℝ) ^ 2) - (c : ℝ) ^ 2) / 2

/-- The atom height is exactly the height obtained from its own pivot. -/
@[simp] theorem orderedEulerCutVerticalHeight_eq_pivotHeight
    (y : OrderedEulerCutTaggedState) :
    orderedEulerCutVerticalHeight y =
      orderedEulerPivotVerticalHeight
        (orderedEulerCutHighCofactor y)
        (orderedEulerCutLowProduct y)
        (orderedEulerCutPivot y) := rfl

/-- For a positive low product, increasing the crossing pivot strictly increases
the squared-complex vertical coordinate.  Prime order and vertical order are
therefore identical on each fixed `(c,a)` fibre. -/
theorem orderedEulerPivotVerticalHeight_strictMono
    {c a p₁ p₂ : ℕ}
    (ha : 0 < a)
    (hp : p₁ < p₂) :
    orderedEulerPivotVerticalHeight c a p₁ <
      orderedEulerPivotVerticalHeight c a p₂ := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hpR : (p₁ : ℝ) < (p₂ : ℝ) := by exact_mod_cast hp
  have hp1R : 0 ≤ (p₁ : ℝ) := by positivity
  have hp2R : 0 ≤ (p₂ : ℝ) := by positivity
  have hdiff :
      0 < ((p₂ : ℝ) - (p₁ : ℝ)) * (a : ℝ) :=
    mul_pos (sub_pos.mpr hpR) haR
  have hpa :
      (p₁ : ℝ) * (a : ℝ) < (p₂ : ℝ) * (a : ℝ) := by
    nlinarith
  have hq1 : 0 ≤ (p₁ : ℝ) * (a : ℝ) :=
    mul_nonneg hp1R (le_of_lt haR)
  have hp2pos : 0 < (p₂ : ℝ) := by linarith
  have hq2 : 0 < (p₂ : ℝ) * (a : ℝ) :=
    mul_pos hp2pos haR
  have hprod :
      0 < ((p₂ : ℝ) * (a : ℝ) - (p₁ : ℝ) * (a : ℝ)) *
        ((p₂ : ℝ) * (a : ℝ) + (p₁ : ℝ) * (a : ℝ)) :=
    mul_pos (sub_pos.mpr hpa) (add_pos_of_pos_of_nonneg hq2 hq1)
  unfold orderedEulerPivotVerticalHeight
  push_cast
  nlinarith

/-- Weak monotonicity version of the pivot-height ordering. -/
theorem orderedEulerPivotVerticalHeight_mono
    {c a p₁ p₂ : ℕ}
    (ha : 0 < a)
    (hp : p₁ ≤ p₂) :
    orderedEulerPivotVerticalHeight c a p₁ ≤
      orderedEulerPivotVerticalHeight c a p₂ := by
  rcases eq_or_lt_of_le hp with hEq | hLt
  · subst p₂
    exact le_rfl
  · exact le_of_lt (orderedEulerPivotVerticalHeight_strictMono ha hLt)

/-- A pivot interval is exactly its vertical-height interval on a fixed ordered
Euler fibre.  This is the literal interval form of the original squared-strip
picture. -/
theorem orderedEulerPivotVerticalHeight_between_iff
    {c a p lo hi : ℕ}
    (ha : 0 < a) :
    (orderedEulerPivotVerticalHeight c a lo ≤
        orderedEulerPivotVerticalHeight c a p ∧
      orderedEulerPivotVerticalHeight c a p ≤
        orderedEulerPivotVerticalHeight c a hi) ↔
      lo ≤ p ∧ p ≤ hi := by
  constructor
  · intro h
    constructor
    · by_contra hnot
      have hpLo : p < lo := Nat.lt_of_not_ge hnot
      have hs :=
        orderedEulerPivotVerticalHeight_strictMono (c := c) ha hpLo
      exact (not_lt_of_ge h.1) hs
    · by_contra hnot
      have hHiP : hi < p := Nat.lt_of_not_ge hnot
      have hs :=
        orderedEulerPivotVerticalHeight_strictMono (c := c) ha hHiP
      exact (not_lt_of_ge h.2) hs
  · rintro ⟨hlo, hhi⟩
    exact ⟨orderedEulerPivotVerticalHeight_mono ha hlo,
      orderedEulerPivotVerticalHeight_mono ha hhi⟩

/-- **Complex/Fermat package for one exposed Euler atom.**  The same carrier
point simultaneously has the child product as squared real coordinate, the
ordered vertical height as squared imaginary coordinate, the exact square-root
factor window, and the fresh-prime Möbius sign reversal. -/
theorem orderedEulerCut_complexFiber_lifetime_package
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hocc : OrderedEulerCutOccursAt R y) :
    ((orderedEulerCutFermatPoint y) ^ 2).re =
        (orderedEulerCutChildInteger y : ℝ) ∧
      ((orderedEulerCutFermatPoint y) ^ 2).im =
        orderedEulerCutVerticalHeight y ∧
      orderedEulerCutHighCofactor y ≤
        Nat.sqrt (orderedEulerCutChildInteger y) ∧
      Nat.sqrt (orderedEulerCutChildInteger y) < R ∧
      R < orderedEulerCutUpperFactor y ∧
      canonicalMoebiusWeight (orderedEulerCutChildInteger y) =
        -orderedEulerCutWeight y := by
  have hsqrt := orderedEulerCutOccursAt_sqrt_factor_window hy hocc
  refine ⟨orderedEulerCutFermatPoint_sq_re y,
    orderedEulerCutFermatPoint_sq_im y,
    hsqrt.1, hsqrt.2.1, hsqrt.2.2, ?_⟩
  exact orderedEulerCutChildWeight_eq_neg hy

end RHLean.Proof