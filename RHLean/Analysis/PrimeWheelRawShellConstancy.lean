import Mathlib
import RHLean.Analysis.PrimeWheelRawUnitOrbit
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse
import RHLean.Analysis.SquareWheelQuadraticSampling

/-!
# Reduced-conductor shell constancy of the actual periodic raw spectrum

The previous unit-orbit theorem proves that the actual periodic raw DFT is
constant under multiplication of its frequency by a unit.  This file closes the
remaining algebraic step: in `ZMod N`, two elements of the same additive order
are unit associates.  Since the repository's reduced additive conductor is
exactly additive order, every reduced-conductor shell is one unit orbit.

Consequently the shell-constancy hypothesis in
`PrimeWheelPeriodicRawConductorResponse` is discharged as an ordinary theorem.
No estimate is used.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Multiplication by a ring unit preserves additive order in `ZMod N`. -/
private theorem addOrderOf_unit_mul
    {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (z : ZMod N) :
    addOrderOf ((u : ZMod N) * z) = addOrderOf z := by
  rw [addOrderOf_eq_addOrderOf_iff]
  intro n
  let e : ZMod N ≃+ ZMod N := AddAut.mulLeft u
  have he : e z = (u : ZMod N) * z := by
    simp [e, Units.smul_def, smul_eq_mul]
  rw [← he, ← map_nsmul e n z]
  exact e.map_eq_zero_iff

/-- A divisor `d` of a nonzero modulus has additive order exactly `N / d`
when regarded as a residue modulo `N`. -/
private theorem addOrderOf_natCast_divisor
    {N d : ℕ} [NeZero N] (hd : d ∣ N) :
    addOrderOf (d : ZMod N) = N / d := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [ZMod.addOrderOf_coe d hN]
  rw [Nat.gcd_eq_right_iff_dvd.mpr hd]

/-- In a nonzero cyclic residue ring, equal additive order implies membership in
the same multiplicative unit orbit. -/
theorem zmod_exists_unit_mul_of_addOrderOf_eq
    {N : ℕ} [NeZero N]
    (r s : ZMod N)
    (horder : addOrderOf r = addOrderOf s) :
    ∃ u : (ZMod N)ˣ, s = (u : ZMod N) * r := by
  rcases ZMod.eq_unit_mul_divisor r with
    ⟨dr, hdr, ur, hur, hr⟩
  rcases ZMod.eq_unit_mul_divisor s with
    ⟨ds, hds, us, hus, hs⟩
  rcases hur with ⟨ur', hur'⟩
  rcases hus with ⟨us', hus'⟩
  rw [← hur'] at hr
  rw [← hus'] at hs
  have hordr : addOrderOf r = N / dr := by
    rw [hr, addOrderOf_unit_mul]
    exact addOrderOf_natCast_divisor hdr
  have hords : addOrderOf s = N / ds := by
    rw [hs, addOrderOf_unit_mul]
    exact addOrderOf_natCast_divisor hds
  have hdiv : N / dr = N / ds := by
    rw [← hordr, ← hords]
    exact horder
  have hqpos : 0 < N / dr := by
    rw [← hordr]
    exact addOrderOf_pos r
  have hprod : dr * (N / dr) = ds * (N / dr) := by
    calc
      dr * (N / dr) = N := Nat.mul_div_cancel' hdr
      _ = ds * (N / ds) := (Nat.mul_div_cancel' hds).symm
      _ = ds * (N / dr) := by rw [hdiv]
  have hdsdr : ds = dr := by
    exact Nat.eq_of_mul_eq_mul_right hqpos hprod.symm
  subst ds
  refine ⟨us' * ur'⁻¹, ?_⟩
  rw [hs, hr]
  simp [mul_assoc]

/-- Equal reduced additive conductor is exactly enough to put two frequencies in
one multiplicative unit orbit. -/
theorem zmod_exists_unit_mul_of_reducedConductor_eq
    (W : PrimeWheelFiniteSystem)
    (r s : ZMod W.modulus)
    (hcond : reducedAdditiveConductor r = reducedAdditiveConductor s) :
    ∃ u : (ZMod W.modulus)ˣ, s = (u : ZMod W.modulus) * r := by
  apply zmod_exists_unit_mul_of_addOrderOf_eq r s
  rw [← reducedAdditiveConductor_eq_addOrderOf W r]
  rw [← reducedAdditiveConductor_eq_addOrderOf W s]
  exact hcond

/-- The actual periodic raw spectrum is constant on every reduced-conductor
shell.  This discharges the shell-constancy hypothesis left explicit in an earlier layer. -/
theorem primorialPeriodicRawSpectrum_eq_of_reducedConductor_eq
    (k : ℕ)
    (r s : ZMod (primorialMinimalWheelSystem k).modulus)
    (hcond : reducedAdditiveConductor r = reducedAdditiveConductor s) :
    primorialPeriodicRawSpectrum k r =
      primorialPeriodicRawSpectrum k s := by
  rcases zmod_exists_unit_mul_of_reducedConductor_eq
    (primorialMinimalWheelSystem k) r s hcond with ⟨u, hs⟩
  rw [hs, primorialPeriodicRawSpectrum_unit_mul]

/-- Once one frequency in a shell is named, its actual raw coefficient is the
constant coefficient of the whole shell. -/
theorem primorialPeriodicRawSpectrum_shell_constant
    (k q : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus)
    (hr : q = reducedAdditiveConductor r) :
    ∀ s : ZMod (primorialMinimalWheelSystem k).modulus,
      q = reducedAdditiveConductor s →
        primorialPeriodicRawSpectrum k s =
          primorialPeriodicRawSpectrum k r := by
  intro s hs
  apply primorialPeriodicRawSpectrum_eq_of_reducedConductor_eq k s r
  rw [← hs, ← hr]

/-- The raw contribution of a nonempty conductor shell is now unconditionally
its actual common Fourier coefficient times the exact Ramanujan-kernel window. -/
theorem primorialPeriodicRawConductorResponse_eq_frequency_mul_ramanujanWindow
    (k x q : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus)
    (hr : q = reducedAdditiveConductor r) :
    primorialPeriodicRawConductorResponse k x q =
      primorialPeriodicRawSpectrum k r *
        primorialReducedConductorRamanujanWindow k x q := by
  exact primorialPeriodicRawConductorResponse_eq_constant_mul_ramanujanWindow
    k x q (primorialPeriodicRawSpectrum k r)
    (primorialPeriodicRawSpectrum_shell_constant k q r hr)

/-- The actual signed packet is therefore raw Ramanujan response minus twice the
smooth packet, with no shell-constancy hypothesis remaining. -/
theorem primorialPeriodicRawJointConductorResponse_eq_frequencyRamanujan_sub_two_smooth
    (k x q : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus)
    (hr : q = reducedAdditiveConductor r) :
    primorialPeriodicRawJointConductorResponse k x q =
      primorialPeriodicRawSpectrum k r *
          primorialReducedConductorRamanujanWindow k x q -
        2 * primorialPeriodicSmoothConductorResponse k x q := by
  exact primorialPeriodicRawJointConductorResponse_eq_constantRamanujan_sub_two_smooth
    k x q (primorialPeriodicRawSpectrum k r)
    (primorialPeriodicRawSpectrum_shell_constant k q r hr)

end RHLean.Analysis
