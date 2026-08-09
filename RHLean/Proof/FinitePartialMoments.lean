import Mathlib

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The nonnegative part of a real number. -/
def positivePart (x : ℝ) : ℝ :=
  max x 0

/-- The magnitude of the nonpositive part of a real number. -/
def negativePart (x : ℝ) : ℝ :=
  max (-x) 0

/-- The difference of the positive and negative parts recovers the original
real number. -/
theorem positivePart_sub_negativePart (x : ℝ) :
    positivePart x - negativePart x = x := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, negativePart, max_eq_left hx,
      max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, negativePart, max_eq_right hx',
      max_eq_left (neg_nonneg.mpr hx')]

/-- The sum of the positive and negative parts is the absolute value. -/
theorem positivePart_add_negativePart (x : ℝ) :
    positivePart x + negativePart x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, negativePart, max_eq_left hx,
      max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, negativePart, max_eq_right hx',
      max_eq_left (neg_nonneg.mpr hx'), abs_of_nonpos hx']

/-- The signed natural power induced by the positive/negative-part split. -/
def signedPowerNat (d : ℕ) (x : ℝ) : ℝ :=
  positivePart x ^ d - negativePart x ^ d

/-- Upper partial moment of natural degree `d` over a finite index set. -/
def upperPartialMomentNat {ι : Type*}
    (d : ℕ) (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, positivePart (x i) ^ d

/-- Lower partial moment of natural degree `d` over a finite index set. -/
def lowerPartialMomentNat {ι : Type*}
    (d : ℕ) (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, negativePart (x i) ^ d

/-- Signed natural-power moment over a finite index set. -/
def signedPowerMomentNat {ι : Type*}
    (d : ℕ) (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, signedPowerNat d (x i)

/-- Absolute natural-power mass over a finite index set. -/
def absolutePowerMomentNat {ι : Type*}
    (d : ℕ) (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, |x i| ^ d

/-- The upper-minus-lower partial moment is exactly the signed power moment. -/
theorem upperPartialMomentNat_sub_lowerPartialMomentNat
    {ι : Type*} (d : ℕ) (s : Finset ι) (x : ι → ℝ) :
    upperPartialMomentNat d s x - lowerPartialMomentNat d s x =
      signedPowerMomentNat d s x := by
  unfold upperPartialMomentNat lowerPartialMomentNat signedPowerMomentNat
  rw [← Finset.sum_sub_distrib]
  rfl

/-- At every positive natural degree, the sum of the two pointwise partial
powers is the corresponding absolute power. -/
theorem positivePart_pow_add_negativePart_pow
    (d : ℕ) (hd : d ≠ 0) (x : ℝ) :
    positivePart x ^ d + negativePart x ^ d = |x| ^ d := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, negativePart, max_eq_left hx,
      max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx, hd]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, negativePart, max_eq_right hx',
      max_eq_left (neg_nonneg.mpr hx'), abs_of_nonpos hx', hd]

/-- At every positive natural degree, upper plus lower partial moments equal
the finite absolute-power mass. -/
theorem upperPartialMomentNat_add_lowerPartialMomentNat
    {ι : Type*} (d : ℕ) (hd : d ≠ 0)
    (s : Finset ι) (x : ι → ℝ) :
    upperPartialMomentNat d s x + lowerPartialMomentNat d s x =
      absolutePowerMomentNat d s x := by
  unfold upperPartialMomentNat lowerPartialMomentNat absolutePowerMomentNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact positivePart_pow_add_negativePart_pow d hd (x i)

/-- Degree one signed power is the original value. -/
@[simp] theorem signedPowerNat_one (x : ℝ) :
    signedPowerNat 1 x = x := by
  simpa [signedPowerNat] using positivePart_sub_negativePart x

/-- The ordinary finite signed sum. -/
def finiteSignedSum {ι : Type*} (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, x i

/-- The ordinary finite absolute mass. -/
def finiteAbsoluteMass {ι : Type*} (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, |x i|

/-- Degree-one upper partial mass. -/
def upperPartialMass {ι : Type*} (s : Finset ι) (x : ι → ℝ) : ℝ :=
  upperPartialMomentNat 1 s x

/-- Degree-one lower partial mass. -/
def lowerPartialMass {ι : Type*} (s : Finset ι) (x : ι → ℝ) : ℝ :=
  lowerPartialMomentNat 1 s x

/-- Degree-one upper minus lower mass is the ordinary signed sum. -/
theorem upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    upperPartialMass s x - lowerPartialMass s x = finiteSignedSum s x := by
  unfold upperPartialMass lowerPartialMass upperPartialMomentNat
    lowerPartialMomentNat finiteSignedSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa using positivePart_sub_negativePart (x i)

/-- Degree-one upper plus lower mass is the ordinary absolute mass. -/
theorem upperPartialMass_add_lowerPartialMass_eq_finiteAbsoluteMass
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    upperPartialMass s x + lowerPartialMass s x = finiteAbsoluteMass s x := by
  unfold upperPartialMass lowerPartialMass upperPartialMomentNat
    lowerPartialMomentNat finiteAbsoluteMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa using positivePart_add_negativePart (x i)

/-- Denominator-free degree-one balance numerator. -/
def degreeOneBalanceNumerator {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) : ℝ :=
  2 * upperPartialMass s x -
    (upperPartialMass s x + lowerPartialMass s x)

/-- The denominator-free degree-one balance numerator is exactly the signed
sum. -/
theorem degreeOneBalanceNumerator_eq_finiteSignedSum
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    degreeOneBalanceNumerator s x = finiteSignedSum s x := by
  rw [← upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum]
  unfold degreeOneBalanceNumerator
  ring

/-- Degree-one upper-mass share. The ratio is total as a real-valued
expression; the exact signed-sum reconstruction below requires nonzero total
absolute mass. -/
def degreeOneBalanceRatio {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) : ℝ :=
  upperPartialMass s x /
    (upperPartialMass s x + lowerPartialMass s x)

/-- Guarded exact degree-one partial-moment identity:
`signed sum = absolute mass * (2 * upper share - 1)`. -/
theorem finiteSignedSum_eq_absoluteMass_mul_two_ratio_sub_one
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hQ : finiteAbsoluteMass s x ≠ 0) :
    finiteSignedSum s x =
      finiteAbsoluteMass s x * (2 * degreeOneBalanceRatio s x - 1) := by
  have hden : upperPartialMass s x + lowerPartialMass s x ≠ 0 := by
    rw [upperPartialMass_add_lowerPartialMass_eq_finiteAbsoluteMass]
    exact hQ
  rw [← upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum,
    ← upperPartialMass_add_lowerPartialMass_eq_finiteAbsoluteMass]
  unfold degreeOneBalanceRatio
  field_simp [hden]
  ring

/-- A real number is sign-valued when it belongs to `{-1,0,1}`. -/
def IsSignValue (x : ℝ) : Prop :=
  x = -1 ∨ x = 0 ∨ x = 1

/-- For sign-valued inputs, every positive natural signed power collapses to
the original sign. -/
theorem signedPowerNat_eq_self_of_isSignValue
    (d : ℕ) (hd : d ≠ 0) (x : ℝ) (hx : IsSignValue x) :
    signedPowerNat d x = x := by
  rcases hx with h | h | h
  · subst x
    simp [signedPowerNat, positivePart, negativePart, hd]
  · subst x
    simp [signedPowerNat, positivePart, negativePart, hd]
  · subst x
    simp [signedPowerNat, positivePart, negativePart, hd]

/-- A finite sign-valued sequence has the same signed power moment at every
positive natural degree. -/
theorem signedPowerMomentNat_eq_finiteSignedSum_of_signValues
    {ι : Type*} (d : ℕ) (hd : d ≠ 0)
    (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, IsSignValue (x i)) :
    signedPowerMomentNat d s x = finiteSignedSum s x := by
  unfold signedPowerMomentNat finiteSignedSum
  apply Finset.sum_congr rfl
  intro i hi
  exact signedPowerNat_eq_self_of_isSignValue d hd (x i) (hx i hi)

end RHLean.Analysis
