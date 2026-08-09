import Mathlib
import RHLean.Analysis.PrimeWheelRawConductorCoefficient

/-!
# Full conductor recombination with the zero shell retained

The RH-facing prime-wheel criterion bounds the full corrected residual.  The
nontrivial-conductor divisor-boundary formulas are exact, but they use `q > 1`
to cancel the common Ramanujan bulk term.  This file restores the conductor-one
packet beside those formulas before any norm is taken.

Thus the final arithmetic decomposition again has the same scope as the actual
historical residual: the additive zero frequency is retained explicitly, and
every divisor conductor `q > 1` is replaced by the finite arithmetic boundary
packet proved in `PrimeWheelRawConductorCoefficient`.

No analytic estimate is asserted here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The conductor-one shell is exactly the additive zero frequency. -/
theorem reducedAdditiveConductor_eq_one_iff_zero
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    reducedAdditiveConductor r = 1 ↔ r = 0 := by
  rw [reducedAdditiveConductor_eq_addOrderOf W r]
  exact AddMonoid.addOrderOf_eq_one_iff

/-- Predicate-oriented form used by conductor-shell sums. -/
theorem one_eq_reducedAdditiveConductor_iff_zero
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    1 = reducedAdditiveConductor r ↔ r = 0 := by
  constructor
  · intro h
    exact (reducedAdditiveConductor_eq_one_iff_zero W r).mp h.symm
  · intro h
    exact ((reducedAdditiveConductor_eq_one_iff_zero W r).mpr h).symm

/-- Consequently the complete conductor-one joint response consists of the
single zero-frequency atom. -/
theorem primorialPeriodicRawJointConductorResponse_one_eq_zeroAtom
    (k x : ℕ) :
    primorialPeriodicRawJointConductorResponse k x 1 =
      primorialPeriodicRawJointSpectralAtom k x 0 := by
  classical
  unfold primorialPeriodicRawJointConductorResponse
  simp [one_eq_reducedAdditiveConductor_iff_zero]

/-- A conductor value that does not divide the ambient modulus carries no
frequency and therefore has zero joint response. -/
private theorem primorialPeriodicRawJointConductorResponse_eq_zero_of_not_dvd
    (k x q : ℕ)
    (hq : ¬ q ∣ (primorialMinimalWheelSystem k).modulus) :
    primorialPeriodicRawJointConductorResponse k x q = 0 := by
  classical
  unfold primorialPeriodicRawJointConductorResponse
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hcond : q = reducedAdditiveConductor r
  · exfalso
    apply hq
    rw [hcond]
    exact reducedConductor_dvd_modulus
      (primorialMinimalWheelSystem k) r
  · simp [hcond]

/-- The complete residual can be partitioned over actual divisors of the torus
modulus rather than over the larger ambient range of possible naturals. -/
theorem primorialPeriodicRawResidual_eq_sum_divisorConductorResponses
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      ∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        primorialPeriodicRawJointConductorResponse k x q := by
  let N := (primorialMinimalWheelSystem k).modulus
  have hNne : N ≠ 0 :=
    Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos
  have hfilter :
      (Finset.range (N + 1)).filter (fun q => q ∣ N) = N.divisors := by
    simpa [Nat.succ_eq_add_one] using (Nat.filter_dvd_eq_divisors hNne)
  rw [primorialPeriodicRawResidual_eq_sum_conductorResponses
    k hlower hupper]
  rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hqrange
  by_cases hqdiv : q ∣ N
  · simp [hqdiv]
  · have hzero : primorialPeriodicRawJointConductorResponse k x q = 0 := by
      apply primorialPeriodicRawJointConductorResponse_eq_zero_of_not_dvd
      simpa [N] using hqdiv
    simp [hqdiv, hzero]

/-- Every divisor conductor is realized by the canonical residue `N / q`, so
the nontrivial boundary theorem can be instantiated without an external shell
representative. -/
private theorem reducedAdditiveConductor_natCast_quotient
    (W : PrimeWheelFiniteSystem) (q : ℕ)
    (hqmod : q ∣ W.modulus) :
    reducedAdditiveConductor
        (((W.modulus / q : ℕ) : ZMod W.modulus)) = q := by
  rw [reducedAdditiveConductor_eq_addOrderOf W]
  have hNne : W.modulus ≠ 0 := Nat.ne_of_gt W.modulus_pos
  rw [ZMod.addOrderOf_coe _ hNne]
  have hprod : q * (W.modulus / q) = W.modulus :=
    Nat.mul_div_cancel' hqmod
  have hquotdvd : W.modulus / q ∣ W.modulus := by
    refine ⟨q, ?_⟩
    simpa [Nat.mul_comm] using hprod.symm
  rw [Nat.gcd_eq_right_iff_dvd.mpr hquotdvd]
  have hquotpos : 0 < W.modulus / q :=
    Nat.pos_of_dvd_of_pos hquotdvd W.modulus_pos
  apply Nat.div_eq_of_eq_mul_right hquotpos
  simpa [Nat.mul_comm] using hprod.symm

/-- Explicit arithmetic packet used for every nontrivial divisor conductor. -/
def primorialPeriodicRawExplicitNontrivialConductorPacket
    (k x q : ℕ) : ℂ :=
  primorialRawConductorArithmeticCoefficient k q *
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (((∑ d ∈ q.divisors,
          μ (q / d) *
            divisorIntervalBoundary d 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)) -
    2 *
      ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (((primeWheelSmoothBoundaryPacket
          (primorialMinimalWheelSystem k) x q : ℤ) : ℂ)))

/-- Every nontrivial divisor of the torus modulus is an occupied conductor and
its actual joint response is exactly the arithmetic boundary packet. -/
theorem primorialPeriodicRawJointConductorResponse_eq_explicit_of_divisor
    (k x q : ℕ)
    (hqmem : q ∈ (primorialMinimalWheelSystem k).modulus.divisors)
    (hq : 1 < q)
    (hx : x ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawJointConductorResponse k x q =
      primorialPeriodicRawExplicitNontrivialConductorPacket k x q := by
  have hqmod : q ∣ (primorialMinimalWheelSystem k).modulus :=
    Nat.dvd_of_mem_divisors hqmem
  let r : ZMod (primorialMinimalWheelSystem k).modulus :=
    (((primorialMinimalWheelSystem k).modulus / q : ℕ) :
      ZMod (primorialMinimalWheelSystem k).modulus)
  have hr : q = reducedAdditiveConductor r := by
    dsimp [r]
    exact (reducedAdditiveConductor_natCast_quotient
      (primorialMinimalWheelSystem k) q hqmod).symm
  unfold primorialPeriodicRawExplicitNontrivialConductorPacket
  exact primorialPeriodicRawJointConductorResponse_eq_arithmeticDivisorBoundary
    k x q r hr hq hx

/-- Full realigned terminal decomposition.  The left-hand side is the actual
historical corrected residual.  On the right, conductor one remains as the
single zero-frequency joint atom, while every divisor conductor `q > 1` is the
fully explicit finite arithmetic boundary packet.  No sub-piece is required to
satisfy an RH-scale estimate independently. -/
theorem primorialPeriodicRawResidual_eq_zeroConductor_add_nontrivialBoundary
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      primorialPeriodicRawJointSpectralAtom k x 0 +
        ∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors.erase 1,
          primorialPeriodicRawExplicitNontrivialConductorPacket k x q := by
  rw [primorialPeriodicRawResidual_eq_sum_divisorConductorResponses
    k hlower hupper]
  have hNne : (primorialMinimalWheelSystem k).modulus ≠ 0 :=
    Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos
  have h1mem :
      1 ∈ (primorialMinimalWheelSystem k).modulus.divisors :=
    (Nat.one_mem_divisors).2 hNne
  calc
    (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        primorialPeriodicRawJointConductorResponse k x q) =
      primorialPeriodicRawJointConductorResponse k x 1 +
        ∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors.erase 1,
          primorialPeriodicRawJointConductorResponse k x q := by
            exact (Finset.add_sum_erase
              (primorialMinimalWheelSystem k).modulus.divisors
              (fun q => primorialPeriodicRawJointConductorResponse k x q)
              h1mem).symm
    _ = primorialPeriodicRawJointSpectralAtom k x 0 +
        ∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors.erase 1,
          primorialPeriodicRawExplicitNontrivialConductorPacket k x q := by
            rw [primorialPeriodicRawJointConductorResponse_one_eq_zeroAtom]
            apply congrArg (fun z : ℂ =>
              primorialPeriodicRawJointSpectralAtom k x 0 + z)
            apply Finset.sum_congr rfl
            intro q hqerase
            have hqdata := Finset.mem_erase.mp hqerase
            have hqne : q ≠ 1 := hqdata.1
            have hqmem :
                q ∈ (primorialMinimalWheelSystem k).modulus.divisors :=
              hqdata.2
            have hqpos : 0 < q := Nat.pos_of_mem_divisors hqmem
            have hqgt : 1 < q := by omega
            have hx : x ≤ (primorialMinimalWheelSystem k).upper := by
              simpa using hupper
            exact
              primorialPeriodicRawJointConductorResponse_eq_explicit_of_divisor
                k x q hqmem hqgt hx

end RHLean.Analysis
