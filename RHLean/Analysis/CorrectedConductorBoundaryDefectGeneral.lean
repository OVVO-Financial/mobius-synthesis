import Mathlib
import RHLean.Analysis.PrimeWheelFullConductorUniformPacket

/-!
# General corrected-conductor boundary defects

The conductor-three computation is a special case of a general exact fact.
For every nontrivial reduced additive conductor, the common interval bulk is
killed by the complementary-divisor Moebius sum before any norm is taken.
The corrected `raw - 2 * smooth` packet is therefore a torus-normalized signed
combination of finite divisor-residue boundary defects.

This file also proves the endpoint periodicity which is implicit in that
boundary description.  If `d | q`, adding a full conductor period `q` adds an
integer number of complete residue cycles modulo `d`, so the corresponding
boundary defect is unchanged.  Consequently every corrected conductor packet
with `q > 1` is exactly `q`-periodic as long as both endpoints remain in the
same primorial wheel block.

Thus conductor one is the only conductor which can carry a growing interval
bulk.  No estimate, Gram bound, or triangle inequality is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The complete divisor-boundary defect attached to conductor `q` and shift
`a`.  For `q > 1` this is exactly the corresponding shifted Ramanujan interval
sum. -/
def conductorBoundaryDefect
    (q a lower upper : ℕ) : ℤ :=
  ∑ d ∈ q.divisors,
    μ (q / d) * divisorIntervalBoundary d a lower upper

/-- The smooth boundary packet is the negative Moebius-weighted sum of the
complete conductor boundary defects. -/
theorem primeWheelSmoothBoundaryPacket_eq_neg_weightedConductorBoundaryDefects
    (W : PrimeWheelFiniteSystem) (x q : ℕ) :
    primeWheelSmoothBoundaryPacket W x q =
      -(∑ a ∈ primeWheelSmoothDivisorSites W,
        μ a * conductorBoundaryDefect q a W.lower x) := by
  classical
  unfold primeWheelSmoothBoundaryPacket conductorBoundaryDefect
  calc
    (∑ a ∈ primeWheelSmoothDivisorSites W,
        -(μ a) *
          ∑ d ∈ q.divisors,
            μ (q / d) * divisorIntervalBoundary d a W.lower x) =
      ∑ a ∈ primeWheelSmoothDivisorSites W,
        -(μ a *
          ∑ d ∈ q.divisors,
            μ (q / d) * divisorIntervalBoundary d a W.lower x) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
    _ = -(∑ a ∈ primeWheelSmoothDivisorSites W,
        μ a *
          ∑ d ∈ q.divisors,
            μ (q / d) * divisorIntervalBoundary d a W.lower x) := by
          rw [Finset.sum_neg_distrib]

/-- Boundary part of the uniform corrected conductor packet. -/
def primorialCorrectedConductorBoundaryPart
    (k x q : ℕ) : ℂ :=
  primorialRawConductorArithmeticCoefficient k q *
      ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (((conductorBoundaryDefect q 0
          (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))) -
    2 *
      ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (((primeWheelSmoothBoundaryPacket
          (primorialMinimalWheelSystem k) x q : ℤ) : ℂ)))

/-- Bulk part of the uniform corrected conductor packet.  The Kronecker factor
makes its support visibly concentrated at conductor one. -/
def primorialCorrectedConductorBulkPart
    (k x q : ℕ) : ℂ :=
  primorialRawConductorArithmeticCoefficient k q *
      ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (((((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
          (if q = 1 then 1 else 0) : ℤ) : ℂ))) -
    2 *
      ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (((primeWheelSmoothBulkMass (primorialMinimalWheelSystem k) *
          ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
          (if q = 1 then 1 else 0) : ℤ) : ℂ)))

/-- The all-conductor explicit packet splits exactly into boundary and bulk
parts, still before any norm is taken. -/
theorem primorialPeriodicRawExplicitAllConductorPacket_eq_boundary_add_bulk
    (k x q : ℕ) :
    primorialPeriodicRawExplicitAllConductorPacket k x q =
      primorialCorrectedConductorBoundaryPart k x q +
        primorialCorrectedConductorBulkPart k x q := by
  unfold primorialPeriodicRawExplicitAllConductorPacket
    primorialCorrectedConductorBoundaryPart
    primorialCorrectedConductorBulkPart conductorBoundaryDefect
  push_cast
  ring

/-- Every non-one conductor has identically zero interval bulk. -/
theorem primorialCorrectedConductorBulkPart_eq_zero_of_ne_one
    (k x q : ℕ) (hq : q ≠ 1) :
    primorialCorrectedConductorBulkPart k x q = 0 := by
  simp [primorialCorrectedConductorBulkPart, hq]

/-- In particular every nontrivial conductor is boundary-only. -/
theorem primorialCorrectedConductorBulkPart_eq_zero_of_one_lt
    (k x q : ℕ) (hq : 1 < q) :
    primorialCorrectedConductorBulkPart k x q = 0 :=
  primorialCorrectedConductorBulkPart_eq_zero_of_ne_one
    k x q (Nat.ne_of_gt hq)

/-- The signed boundary numerator in the form requested for the Gram stage:
one raw boundary defect plus the actual smooth-site correction, with all signs
retained. -/
def primorialCorrectedConductorBoundaryNumerator
    (k x q : ℕ) : ℂ :=
  primorialRawConductorArithmeticCoefficient k q *
      (((conductorBoundaryDefect q 0
        (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)) +
    2 *
      (((∑ a ∈ primeWheelSmoothDivisorSites
          (primorialMinimalWheelSystem k),
        μ a * conductorBoundaryDefect q a
          (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))

/-- The boundary part is one common torus normalization multiplying the full
signed corrected boundary numerator. -/
theorem primorialCorrectedConductorBoundaryPart_eq_normalizedNumerator
    (k x q : ℕ) :
    primorialCorrectedConductorBoundaryPart k x q =
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        primorialCorrectedConductorBoundaryNumerator k x q := by
  unfold primorialCorrectedConductorBoundaryPart
    primorialCorrectedConductorBoundaryNumerator
  rw [primeWheelSmoothBoundaryPacket_eq_neg_weightedConductorBoundaryDefects]
  push_cast
  ring

/-- The actual corrected response at every nontrivial divisor conductor is
exactly the normalized boundary numerator; there is no growing bulk term. -/
theorem primorialPeriodicRawJointConductorResponse_eq_boundaryDefectGeneral
    (k x q : ℕ)
    (hqmem : q ∈ (primorialMinimalWheelSystem k).modulus.divisors)
    (hx : x ≤ (primorialMinimalWheelSystem k).upper)
    (hq : 1 < q) :
    primorialPeriodicRawJointConductorResponse k x q =
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        primorialCorrectedConductorBoundaryNumerator k x q := by
  rw [primorialPeriodicRawJointConductorResponse_eq_explicitAllConductor
    k x q hqmem hx]
  rw [primorialPeriodicRawExplicitAllConductorPacket_eq_boundary_add_bulk]
  rw [primorialCorrectedConductorBulkPart_eq_zero_of_one_lt k x q hq]
  simp only [add_zero]
  exact primorialCorrectedConductorBoundaryPart_eq_normalizedNumerator k x q

/-- The conductor-one divisor boundary defect is identically zero. -/
theorem conductorBoundaryDefect_one_eq_zero
    (a lower upper : ℕ) :
    conductorBoundaryDefect 1 a lower upper = 0 := by
  have hdiv : (1 : ℕ).divisors = ({1} : Finset ℕ) := by
    native_decide
  unfold conductorBoundaryDefect
  rw [hdiv]
  simp [divisorIntervalBoundary_one_eq_zero]

/-- Conductor one has no boundary component at all. -/
theorem primorialCorrectedConductorBoundaryPart_one_eq_zero
    (k x : ℕ) :
    primorialCorrectedConductorBoundaryPart k x 1 = 0 := by
  rw [primorialCorrectedConductorBoundaryPart_eq_normalizedNumerator]
  simp [primorialCorrectedConductorBoundaryNumerator,
    conductorBoundaryDefect_one_eq_zero]

/-- Hence the conductor-one explicit packet is purely the possible interval
bulk, complementary to the boundary-only theorem for `q > 1`. -/
theorem primorialPeriodicRawExplicitAllConductorPacket_one_eq_bulk
    (k x : ℕ) :
    primorialPeriodicRawExplicitAllConductorPacket k x 1 =
      primorialCorrectedConductorBulkPart k x 1 := by
  rw [primorialPeriodicRawExplicitAllConductorPacket_eq_boundary_add_bulk]
  rw [primorialCorrectedConductorBoundaryPart_one_eq_zero]
  simp

/-- A complete interval of length `d` contains exactly one representative of
any residue class modulo positive `d`. -/
private theorem divisorResidueCount_complete_period
    (d a upper : ℕ) (hd : 0 < d) :
    divisorResidueCount (Finset.Ioc upper (upper + d)) d a = 1 := by
  classical
  let S : Finset ℕ := Finset.Ico (upper + 1) (upper + 1 + d)
  have hI : Finset.Ioc upper (upper + d) = S := by
    ext m
    simp [S]
    omega
  have himage :
      Finset.image (fun m : ℕ => m % d) S = Finset.range d := by
    simpa [S] using Nat.image_Ico_mod (upper + 1) d
  have hinj : Set.InjOn (fun m : ℕ => m % d) ↑S := by
    simpa [S] using Nat.mod_injOn_Ico (upper + 1) d
  have haRange : a % d ∈ Finset.range d :=
    Finset.mem_range.mpr (Nat.mod_lt a hd)
  have haImage : a % d ∈ Finset.image (fun m : ℕ => m % d) S := by
    rw [himage]
    exact haRange
  rcases Finset.mem_image.mp haImage with ⟨m, hmS, hm⟩
  have hfilter :
      S.filter (fun n : ℕ => n % d = a % d) = {m} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hn
      apply hinj hn.1 hmS
      exact hn.2.trans hm.symm
    · intro hn
      subst n
      exact ⟨hmS, hm⟩
  rw [hI]
  unfold divisorResidueCount
  change
    (∑ m ∈ S, if m % d = a % d then (1 : ℤ) else 0) = 1
  calc
    (∑ m ∈ S, if m % d = a % d then (1 : ℤ) else 0) =
        ∑ m ∈ S with m % d = a % d, (1 : ℤ) := by
          rw [Finset.sum_filter]
    _ = 1 := by
      rw [hfilter]
      simp

/-- A complete residue period has zero divisor-residue boundary defect. -/
private theorem divisorResidueBoundary_complete_period
    (d a upper : ℕ) (hd : 0 < d) :
    divisorResidueBoundary (Finset.Ioc upper (upper + d)) d a = 0 := by
  unfold divisorResidueBoundary
  rw [divisorResidueCount_complete_period d a upper hd]
  simp

/-- Divisor-residue boundary defects are additive on disjoint finite sets. -/
private theorem divisorResidueBoundary_union
    (I J : Finset ℕ) (d a : ℕ) (hdisj : Disjoint I J) :
    divisorResidueBoundary (I ∪ J) d a =
      divisorResidueBoundary I d a + divisorResidueBoundary J d a := by
  classical
  unfold divisorResidueBoundary divisorResidueCount
  rw [Finset.sum_union hdisj]
  rw [Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

/-- One divisor boundary is periodic in its upper endpoint with its own positive
modulus. -/
theorem divisorIntervalBoundary_add_period
    (d a lower upper : ℕ) (hd : 0 < d) (hlower : lower ≤ upper) :
    divisorIntervalBoundary d a lower (upper + d) =
      divisorIntervalBoundary d a lower upper := by
  have hupper : upper ≤ upper + d := by omega
  have hsplit :
      Finset.Ioc lower upper ∪ Finset.Ioc upper (upper + d) =
        Finset.Ioc lower (upper + d) :=
    Finset.Ioc_union_Ioc_eq_Ioc hlower hupper
  have hdisj :
      Disjoint (Finset.Ioc lower upper) (Finset.Ioc upper (upper + d)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  unfold divisorIntervalBoundary
  rw [← hsplit]
  rw [divisorResidueBoundary_union
    (Finset.Ioc lower upper) (Finset.Ioc upper (upper + d)) d a hdisj]
  rw [divisorResidueBoundary_complete_period d a upper hd]
  simp

/-- Every multiple of `d` is also a period of the upper-endpoint divisor
boundary once the endpoint lies to the right of the pinned lower endpoint. -/
theorem divisorIntervalBoundary_add_multiple
    (d a lower upper q : ℕ)
    (hd : 0 < d) (hdq : d ∣ q) (hlower : lower ≤ upper) :
    divisorIntervalBoundary d a lower (upper + q) =
      divisorIntervalBoundary d a lower upper := by
  rcases hdq with ⟨c, rfl⟩
  induction c with
  | zero => simp
  | succ c ih =>
      have hle : lower ≤ upper + d * c := by omega
      calc
        divisorIntervalBoundary d a lower (upper + d * Nat.succ c) =
            divisorIntervalBoundary d a lower ((upper + d * c) + d) := by
              simp only [Nat.mul_succ, Nat.add_assoc]
        _ = divisorIntervalBoundary d a lower (upper + d * c) :=
          divisorIntervalBoundary_add_period d a lower (upper + d * c) hd hle
        _ = divisorIntervalBoundary d a lower upper := ih

/-- The complete conductor boundary defect is periodic with the conductor:
every inner divisor period divides `q`. -/
theorem conductorBoundaryDefect_add_conductor
    {q : ℕ} (hq : 1 < q)
    (a lower upper : ℕ) (hlower : lower ≤ upper) :
    conductorBoundaryDefect q a lower (upper + q) =
      conductorBoundaryDefect q a lower upper := by
  classical
  have _hqpos : 0 < q := Nat.zero_lt_of_lt hq
  unfold conductorBoundaryDefect
  apply Finset.sum_congr rfl
  intro d hdmem
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hdmem
  rw [divisorIntervalBoundary_add_multiple
    d a lower upper q hdpos hdq hlower]

/-- The full corrected boundary numerator inherits exact conductor periodicity. -/
theorem primorialCorrectedConductorBoundaryNumerator_add_conductor
    (k x q : ℕ) (hq : 1 < q)
    (hlower : (primorialMinimalWheelSystem k).lower ≤ x) :
    primorialCorrectedConductorBoundaryNumerator k (x + q) q =
      primorialCorrectedConductorBoundaryNumerator k x q := by
  classical
  have hraw := conductorBoundaryDefect_add_conductor hq 0
    (primorialMinimalWheelSystem k).lower x hlower
  have hsmooth :
      (∑ a ∈ primeWheelSmoothDivisorSites (primorialMinimalWheelSystem k),
        μ a * conductorBoundaryDefect q a
          (primorialMinimalWheelSystem k).lower (x + q)) =
      ∑ a ∈ primeWheelSmoothDivisorSites (primorialMinimalWheelSystem k),
        μ a * conductorBoundaryDefect q a
          (primorialMinimalWheelSystem k).lower x := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [conductorBoundaryDefect_add_conductor hq a
      (primorialMinimalWheelSystem k).lower x hlower]
  unfold primorialCorrectedConductorBoundaryNumerator
  rw [hraw, hsmooth]

/-- Every nontrivial corrected conductor packet is exactly periodic with period
`q` inside one wheel block.  Thus no fixed `q > 1` packet can retain a growing
interval bulk. -/
theorem primorialPeriodicRawJointConductorResponse_add_conductor
    (k x q : ℕ)
    (hqmem : q ∈ (primorialMinimalWheelSystem k).modulus.divisors)
    (hq : 1 < q)
    (hlower : (primorialMinimalWheelSystem k).lower ≤ x)
    (hupper : x + q ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawJointConductorResponse k (x + q) q =
      primorialPeriodicRawJointConductorResponse k x q := by
  have hx : x ≤ (primorialMinimalWheelSystem k).upper := by omega
  rw [primorialPeriodicRawJointConductorResponse_eq_boundaryDefectGeneral
    k (x + q) q hqmem hupper hq]
  rw [primorialPeriodicRawJointConductorResponse_eq_boundaryDefectGeneral
    k x q hqmem hx hq]
  rw [primorialCorrectedConductorBoundaryNumerator_add_conductor
    k x q hq hlower]

end RHLean.Analysis
