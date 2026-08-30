import Mathlib
import RHLean.Proof.LowWheelCanonicalPairingFrontier
import RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell

/-!
# Global transport partner for the Go crossing kernel

The hyperbolic Go recursion isolates a large crossing population indexed by
ordered primes `r < q` and a squarefree parent `d`.  At the square endpoint
`X_R = R^2 - 1`, a strict crossing has

`R < r*q`

while the already-proved first-contact geometry gives

`q*(r*d) <= X_R`.

Thus the same incidence is already a literal state of the global low-wheel
transport carrier:

`(t,x) = ({r}, (d,q))`.

Its transport weight is exactly the Go source weight `mu(q*d)`.  More
importantly, this state is not a canonical transport defect.  The full birth
boundary forces `d > 1`, and every prime factor of `d` is strictly below
`r < q`.  Hence the canonical least-prime pivot of `d*q` lies in `d`.  The
canonical cofactor/quotient toggle therefore removes that pivot from `d`, stays
inside the physical transport carrier, and reverses the sign.

So every strict Go crossing incidence already has its missing opposite-sign
partner inside the global transport identity before the canonical downcross
frontier is formed.  The only crossing not covered by this transport embedding
is the arithmetic equality `r*q = R`, where the transport root inequality is
not strict; that is a separate root-boundary population rather than unfinished
Euler recursion.

No norm, Mertens estimate, PNT input, lower-envelope hypothesis, or asymptotic
claim is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem squareRootLowPrimeGo_liveOwner_lt_root
    {R q : ℕ} (hR : 2 ≤ R) (_hq : q.Prime)
    (hcube : q ^ 3 ≤ squareRootEndpoint R) :
    q < R := by
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hq3lt : q ^ 3 < R ^ 2 := hcube.trans_lt hXlt
  by_contra hnot
  have hRq : R ≤ q := Nat.le_of_not_gt hnot
  have hR2leR3 : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := by simp
      _ ≤ R ^ 2 * R := Nat.mul_le_mul_left (R ^ 2) (by omega)
      _ = R ^ 3 := by ring
  have hR3leQ3 : R ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hRq 3
  omega

/-- A full Go birth-boundary parent is genuinely nontrivial.  If `d = 1`, the
birth condition `q <= r*d` would contradict `r < q`. -/
theorem squareRootLowPrimeGoFullBirthBoundary_parent_one_lt
    {q r d : ℕ} (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    1 < d := by
  have houter := squareRootLowPrimeGoFullBirthBoundary_outer_le_child hr hd
  have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).1
  have hdne : d ≠ 1 := by
    intro hdOne
    subst d
    simp at houter
    omega
  omega

/-- **Strict Go crossings are already global transport states.**

The singleton low-wheel face carries the smaller owner `r`; the residual
quotient is the outer owner `q`; and the low cofactor is the stripped parent
`d`.  The strict hyperbolic crossing is exactly the transport root inequality,
while the Go first-contact theorem supplies the square-endpoint ceiling. -/
theorem squareRootLowPrimeGoStrictCrossing_mem_transport
    {R q r d : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (_hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R)
    (hroot : R < r * q)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q
      (squareRootEndpoint R) r) :
    (d, q) ∈ lowWheelCanonicalPhysicalStateSet R ({r} : Finset ℕ) := by
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull with
    ⟨hd1, _hdq1, hsq, _hrough, _hbirth⟩
  have hqR : q < R := squareRootLowPrimeGo_liveOwner_lt_root hR hq hcube
  have hRX : R ≤ squareRootEndpoint R := by
    have hsqR : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hfirst :=
    squareRootLowPrimeGoFullBirthBoundary_firstContact_le
      hq hrq hcube hfull
  apply mem_lowWheelCanonicalPhysicalStateSet.mpr
  refine ⟨Finset.mem_Ico.mpr ⟨hd1, by omega⟩,
    Finset.mem_Icc.mpr ⟨hq.one_le, hqR.le.trans hRX⟩,
    hsq, ?_⟩
  refine ⟨hd1, by omega, ?_, ?_⟩
  · simpa [primeFaceProduct, Nat.mul_comm] using hroot
  · simpa [primeFaceProduct, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hfirst

/-- The singleton face of a strict Go crossing is one of the actual low-wheel
faces in the global transport ledger. -/
theorem squareRootLowPrimeGoStrictCrossing_face_mem_global
    {R q r : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R) :
    ({r} : Finset ℕ) ∈ (primesUpTo R).powerset := by
  have hqR : q < R := squareRootLowPrimeGo_liveOwner_lt_root hR hq hcube
  apply Finset.mem_powerset.mpr
  intro p hp
  have hpr : p = r := by simpa using hp
  subst p
  exact mem_primesUpTo.mpr ⟨hr, by omega⟩

/-- The canonical least-prime pivot of the transport state `(d,q)` lies in the
old cofactor `d`, not in the prime quotient `q`.  This is the arithmetic reason
the Go crossing is an interior transport state rather than a global downcross
defect. -/
theorem squareRootLowPrimeGoFullBirthBoundary_canonicalPivot_dvd_parent
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    lowWheelCanonicalCofactorQuotientPivot (d, q) ∣ d := by
  have hdgt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hd
  have hdata := mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd
  have hrough : canonicalLargestPrimeFactor d < r := hdata.2.2.2.1
  have hsPrime : (canonicalLargestPrimeFactor d).Prime :=
    canonicalLargestPrimeFactor_prime hdgt
  have hsDvd : canonicalLargestPrimeFactor d ∣ d :=
    canonicalLargestPrimeFactor_dvd hdgt
  have hsDvdProd : canonicalLargestPrimeFactor d ∣ d * q :=
    dvd_mul_of_dvd_left hsDvd q
  have hpLe :
      lowWheelCanonicalCofactorQuotientPivot (d, q) ≤
        canonicalLargestPrimeFactor d := by
    have h := Nat.minFac_le_of_dvd hsPrime.two_le hsDvdProd
    simpa [lowWheelCanonicalCofactorQuotientPivot] using h
  have hpLtQ : lowWheelCanonicalCofactorQuotientPivot (d, q) < q :=
    lt_of_le_of_lt hpLe (hrough.trans hrq)
  have hne : d * q ≠ 1 := by nlinarith [hdgt, hq.two_le]
  have hpPrime := lowWheelCanonicalCofactorQuotientPivot_prime hne
  rcases lowWheelCanonicalCofactorQuotientPivot_active hne with hpd | hpq
  · exact hpd
  · have heq : lowWheelCanonicalCofactorQuotientPivot (d, q) = q :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hq).mp hpq
    omega

/-- **The missing partner is already present globally.**

Every strict Go crossing state belongs to the pairable part of the global
low-wheel transport carrier.  Its canonical mate therefore occurs in the same
physical carrier and is distinct. -/
theorem squareRootLowPrimeGoStrictCrossing_mem_transport_pairable
    {R q r d : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R)
    (hroot : R < r * q)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q
      (squareRootEndpoint R) r) :
    (d, q) ∈ lowWheelCanonicalPairablePart
      (lowWheelCanonicalPhysicalStateSet R ({r} : Finset ℕ)) := by
  have hsource :=
    squareRootLowPrimeGoStrictCrossing_mem_transport
      hR hq hr hrq hcube hroot hd
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hdgt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hfull
  have hsourceData := mem_lowWheelCanonicalPhysicalStateSet.mp hsource
  have hsq := hsourceData.2.2.1
  have hcarrier := hsourceData.2.2.2
  have hne : d * q ≠ 1 := by nlinarith [hdgt, hq.two_le]
  have hpPrime := lowWheelCanonicalCofactorQuotientPivot_prime hne
  have hpDvd :=
    squareRootLowPrimeGoFullBirthBoundary_canonicalPivot_dvd_parent
      hq hr hrq hfull
  have hmateCarrier :
      LowWheelTransportPairCarrier R ({r} : Finset ℕ)
        (lowWheelCanonicalCofactorQuotientToggle (d, q)) := by
    unfold lowWheelCanonicalCofactorQuotientToggle
    exact lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
      hpPrime hcarrier hpDvd
  have hmateRanges := lowWheelTransportPairCarrier_mem_ranges hmateCarrier
  have hmateSq := lowWheelCanonicalToggle_squarefree hsq hne
  have hmateMem :
      lowWheelCanonicalCofactorQuotientToggle (d, q) ∈
        lowWheelCanonicalPhysicalStateSet R ({r} : Finset ℕ) :=
    mem_lowWheelCanonicalPhysicalStateSet.mpr
      ⟨hmateRanges.1, hmateRanges.2, hmateSq, hmateCarrier⟩
  have hmateNe : lowWheelCanonicalCofactorQuotientToggle (d, q) ≠ (d, q) := by
    intro heq
    have hsecond := congrArg Prod.snd heq
    unfold lowWheelCanonicalCofactorQuotientToggle
      lowWheelCofactorQuotientToggleAt at hsecond
    rw [if_pos hpDvd] at hsecond
    have hlt :
        q < lowWheelCanonicalCofactorQuotientPivot (d, q) * q := by
      calc
        q = 1 * q := by simp
        _ < lowWheelCanonicalCofactorQuotientPivot (d, q) * q :=
          Nat.mul_lt_mul_of_pos_right hpPrime.one_lt hq.pos
    exact (Nat.ne_of_gt hlt) hsecond
  exact Finset.mem_filter.mpr ⟨hsource, hmateMem, hmateNe⟩

/-- The transport sign of the embedded Go state is exactly its source Möbius
sign `mu(q*d)`.  Thus no sign convention is being changed by the embedding. -/
theorem squareRootLowPrimeGoFullBirthBoundary_transportWeight_eq_sourceWeight
    {q r d : ℕ} (hq : q.Prime)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    canonicalMoebiusWeight d *
        (booleanCubeSign ({r} : Finset ℕ) : ℂ) =
      canonicalMoebiusWeight (q * d) := by
  have hdata := mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd
  have hdPos : 0 < d := by omega
  have hdUpper := hdata.2.1
  have hnotdvd : ¬ q ∣ d := by
    intro hdiv
    have hqd : q ≤ d := Nat.le_of_dvd hdPos hdiv
    omega
  have hcop : Nat.Coprime q d := hq.coprime_iff_not_dvd.mpr hnotdvd
  unfold canonicalMoebiusWeight
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hq]
  simp [booleanCubeSign]

/-- The canonical global mate carries exactly the opposite Go source weight. -/
theorem squareRootLowPrimeGoFullBirthBoundary_partnerWeight_eq_neg_sourceWeight
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    canonicalMoebiusWeight
        (lowWheelCanonicalCofactorQuotientToggle (d, q)).1 *
        (booleanCubeSign ({r} : Finset ℕ) : ℂ) =
      -canonicalMoebiusWeight (q * d) := by
  have hdgt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hd
  have hsq := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).2.2.1
  have hne : d * q ≠ 1 := by nlinarith [hdgt, hq.two_le]
  rw [lowWheelCanonicalCofactorQuotientToggle_weight_neg hsq hne]
  rw [squareRootLowPrimeGoFullBirthBoundary_transportWeight_eq_sourceWeight
    hq hd]

/-- Pointwise cancellation of a strict Go crossing incidence with the partner
already present in the global transport ledger. -/
theorem squareRootLowPrimeGoStrictCrossing_globalPartner_cancel
    {R q r d : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R)
    (hroot : R < r * q)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q
      (squareRootEndpoint R) r) :
    (canonicalMoebiusWeight d *
        (booleanCubeSign ({r} : Finset ℕ) : ℂ)) +
      (canonicalMoebiusWeight
          (lowWheelCanonicalCofactorQuotientToggle (d, q)).1 *
        (booleanCubeSign ({r} : Finset ℕ) : ℂ)) = 0 := by
  have _hpair := squareRootLowPrimeGoStrictCrossing_mem_transport_pairable
    hR hq hr hrq hcube hroot hd
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  rw [squareRootLowPrimeGoFullBirthBoundary_partnerWeight_eq_neg_sourceWeight
      hq hr hrq hfull,
    squareRootLowPrimeGoFullBirthBoundary_transportWeight_eq_sourceWeight
      hq hfull]
  ring

end RHLean.Proof
