import Mathlib
import RHLean.Proof.MutableSupportBound
import RHLean.Proof.SquareRootLowPrimeGoGlobalPartner

/-!
# Root-equality boundary for the global Go partner

`SquareRootLowPrimeGoGlobalPartner` puts every strict crossing incidence

`R < r*q`

into the pairable part of the already-existing global low-wheel transport
ledger.  At the square endpoint, the hyperbolic crossing condition itself
forces

`R <= r*q`.

Hence the only crossing incidence not covered by the strict transport partner
has the exact arithmetic equality

`r*q = R`.

This file packages that equality population as one literal finite carrier and
charges it injectively to its parent coordinate `d < R`.  The resulting global
boundary has cardinality at most `R`; there is no remaining prime-owner
multiplicity on this exceptional root face.  After that ownership theorem is
proved, the signed Mobius mass of the same carrier is bounded by `R` using only
`|mu| <= 1`.

No estimate is made on the isolated Go crossing kernel.  Strict crossings are
returned to their global transport partners first; only the exact root-equality
boundary is counted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

private theorem squareRootLowPrimeGoRootEquality_liveOwner_lt_root
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

/-- A square-endpoint hyperbolic crossing cannot lie strictly below the root
product. -/
theorem squareRootLowPrimeGo_crossing_forces_root_le_product
    {R q r : ℕ}
    (hcross : squareRootEndpoint R < (q * r) ^ 2) :
    R ≤ r * q := by
  by_contra hnot
  have hprod : r * q < R := Nat.lt_of_not_ge hnot
  have hsq : (r * q) ^ 2 < R ^ 2 :=
    Nat.pow_lt_pow_left hprod (by norm_num : 2 ≠ 0)
  have hle : (r * q) ^ 2 ≤ R ^ 2 - 1 := by omega
  have hle' : (q * r) ^ 2 ≤ squareRootEndpoint R := by
    simpa [squareRootEndpoint, Nat.mul_comm] using hle
  omega

/-- An ordered factorization of one integer into two distinct increasing primes
is unique. -/
theorem squareRootLowPrimeGo_rootEquality_primePair_unique
    {R r q s t : ℕ}
    (hr : r.Prime) (_hq : q.Prime) (hrs : r < q)
    (hs : s.Prime) (ht : t.Prime) (hst : s < t)
    (hrqR : r * q = R) (hstR : s * t = R) :
    r = s ∧ q = t := by
  have hdiv : r ∣ s * t := by
    refine ⟨q, ?_⟩
    exact hstR.trans hrqR.symm
  rcases hr.dvd_mul.mp hdiv with hrsDvd | hrtDvd
  · have hrsEq : r = s :=
      (Nat.prime_dvd_prime_iff_eq hr hs).mp hrsDvd
    subst s
    have hprod : r * q = r * t := hrqR.trans hstR.symm
    exact ⟨rfl, Nat.mul_left_cancel hr.pos hprod⟩
  · have hrtEq : r = t :=
      (Nat.prime_dvd_prime_iff_eq hr ht).mp hrtDvd
    subst t
    have hprod : r * q = s * r := hrqR.trans hstR.symm
    have hprod' : q * r = s * r := by
      simpa [Nat.mul_comm] using hprod
    have hqs : q = s := Nat.mul_right_cancel hr.pos hprod'
    omega

/-- Literal exceptional carrier.  Coordinates are `((r,q),d)`: the two prime
owners on the exact root product and the second-boundary parent. -/
def squareRootLowPrimeGoRootEqualityDefectCarrier
    (R : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.range R).product (Finset.range R)).product (Finset.range R)).filter
    fun z =>
      z.1.1.Prime ∧ z.1.2.Prime ∧ z.1.1 < z.1.2 ∧
        z.1.1 * z.1.2 = R ∧
        z.1.2 ^ 3 ≤ squareRootEndpoint R ∧
        z.2 ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
          z.1.2 (squareRootEndpoint R) z.1.1

@[simp] theorem mem_squareRootLowPrimeGoRootEqualityDefectCarrier
    {R r q d : ℕ} :
    ((r, q), d) ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R ↔
      r < R ∧ q < R ∧ d < R ∧
        r.Prime ∧ q.Prime ∧ r < q ∧ r * q = R ∧
        q ^ 3 ≤ squareRootEndpoint R ∧
        d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
          q (squareRootEndpoint R) r := by
  simp [squareRootLowPrimeGoRootEqualityDefectCarrier, and_assoc]

/-- The parent coordinate recovers the entire root-equality incidence.  The
prime pair is unique because it is the increasing prime factorization of `R`. -/
theorem squareRootLowPrimeGoRootEquality_parentProjection_injOn
    (R : ℕ) :
    Set.InjOn (fun z : (ℕ × ℕ) × ℕ => z.2)
      (squareRootLowPrimeGoRootEqualityDefectCarrier R) := by
  intro a ha b hb hab
  rcases a with ⟨⟨r, q⟩, d⟩
  rcases b with ⟨⟨s, t⟩, e⟩
  rcases mem_squareRootLowPrimeGoRootEqualityDefectCarrier.mp ha with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hrqR, _hcube, _hd⟩
  rcases mem_squareRootLowPrimeGoRootEqualityDefectCarrier.mp hb with
    ⟨_hsR, _htR, _heR, hs, ht, hst, hstR, _hcube', _he⟩
  have hpairs :=
    squareRootLowPrimeGo_rootEquality_primePair_unique
      hr hq hrq hs ht hst hrqR hstR
  rcases hpairs with ⟨hrs, hqt⟩
  subst s
  subst t
  simp only at hab
  subst e
  rfl

/-- **Global root-boundary bound.**  All equality incidences inject into their
single parent integer `d < R`.  In particular there is no factor for the number
of prime-owner pairs. -/
theorem squareRootLowPrimeGoRootEqualityDefectCarrier_card_le_root
    (R : ℕ) :
    (squareRootLowPrimeGoRootEqualityDefectCarrier R).card ≤ R := by
  let encode : ((ℕ × ℕ) × ℕ) → ℕ := fun z => z.2
  have hinj : Set.InjOn encode
      (squareRootLowPrimeGoRootEqualityDefectCarrier R) := by
    simpa [encode] using
      squareRootLowPrimeGoRootEquality_parentProjection_injOn R
  have himage :
      (squareRootLowPrimeGoRootEqualityDefectCarrier R).image encode ⊆
        Finset.range R := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨z, hz, rfl⟩
    rcases z with ⟨⟨r, q⟩, c⟩
    exact Finset.mem_range.mpr
      (mem_squareRootLowPrimeGoRootEqualityDefectCarrier.mp hz).2.2.1
  have hcard :
      ((squareRootLowPrimeGoRootEqualityDefectCarrier R).image encode).card =
        (squareRootLowPrimeGoRootEqualityDefectCarrier R).card :=
    Finset.card_image_iff.mpr hinj
  rw [← hcard]
  simpa using Finset.card_le_card himage

/-- Signed Go source mass on the only crossing population left after global
transport pairing. -/
def squareRootLowPrimeGoRootEqualityDefectMass (R : ℕ) : ℤ :=
  ∑ z ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R,
    μ (z.1.2 * z.2)

/-- **Quantitative root-equality closure.**  Once strict crossings have been
reattached to their global transport partners, the remaining exact root face
has signed mass at most `R`.  Absolute values enter only after the canonical
carrier and its injective root charge have been established. -/
theorem abs_squareRootLowPrimeGoRootEqualityDefectMass_le_root
    (R : ℕ) :
    |squareRootLowPrimeGoRootEqualityDefectMass R| ≤ (R : ℤ) := by
  unfold squareRootLowPrimeGoRootEqualityDefectMass
  calc
    |∑ z ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R,
        μ (z.1.2 * z.2)| ≤
      ∑ z ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R,
        |μ (z.1.2 * z.2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro z _hz
      exact abs_moebius_le_one _
    _ = ((squareRootLowPrimeGoRootEqualityDefectCarrier R).card : ℤ) := by simp
    _ ≤ (R : ℤ) := by
      exact_mod_cast squareRootLowPrimeGoRootEqualityDefectCarrier_card_le_root R

/-- **Complete crossing classification at the square endpoint.**  Every
second-boundary crossing incidence either has its opposite-sign partner in the
existing global transport ledger, or belongs to the `<= R` root-equality
carrier above. -/
theorem squareRootLowPrimeGoCrossing_pairable_or_rootEquality
    {R q r d : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R)
    (hcross : squareRootEndpoint R < (q * r) ^ 2)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q
      (squareRootEndpoint R) r) :
    ((d, q) ∈ lowWheelCanonicalPairablePart
        (lowWheelCanonicalPhysicalStateSet R ({r} : Finset ℕ))) ∨
      (((r, q), d) ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R) := by
  have hroot : R ≤ r * q :=
    squareRootLowPrimeGo_crossing_forces_root_le_product hcross
  rcases lt_or_eq_of_le hroot with hstrict | heq
  · exact Or.inl
      (squareRootLowPrimeGoStrictCrossing_mem_transport_pairable
        hR hq hr hrq hcube hstrict hd)
  · right
    have hqR : q < R :=
      squareRootLowPrimeGoRootEquality_liveOwner_lt_root hR hq hcube
    have hrR : r < R := hrq.trans hqR
    have hfull :=
      (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
    have hdq :=
      (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).2.1
    have hdR : d < R := by omega
    apply mem_squareRootLowPrimeGoRootEqualityDefectCarrier.mpr
    exact ⟨hrR, hqR, hdR, hr, hq, hrq, heq.symm, hcube, hd⟩

end RHLean.Proof
