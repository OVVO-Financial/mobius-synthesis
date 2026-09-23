import RHLean.Proof.PostRootCovariancePrimeWheel210Scratch
import RHLean.Analysis.RoughWheelFiniteCounting
import RHLean.Arithmetic.PrimorialReciprocalMobiusFactorization

/-!
# Quantitative finite wheels and the cost of their child bands

Every bound uses the exact signed wheel identity before estimating individual
bands.  The resulting constants improve at 6, 30 and 210.  Their iteration is
also audited: density contracts by `1-1/p`, but the additional child intervals
cost `1+1/p`, so separate-band counting has factor `1-1/p^2`.

That audit also proves where this method stops: the separate-band leading
coefficient has a positive floor.  Concrete deeper-wheel counting is therefore
not kept on the production path.  Further progress must estimate the exact
signed finite-difference aggregate before absolute values are taken; the
focused research checks exercise that continuation directly.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The finite carrier used by the interval count has exactly Euler's
reduced-residue cardinality; this connects the density calculation to that
literal carrier. -/
theorem roughWheelResidues_card_eq_totient (W : ℕ) :
    (roughWheelResidues W).card = Nat.totient W := by
  unfold roughWheelResidues Nat.totient
  congr 1
  apply Finset.filter_congr
  intro n _hn
  exact Nat.coprime_comm

/-- Fresh-prime residue contraction on the same finite counting carrier. -/
theorem roughWheelResidueDensity_mul_freshPrime
    {W p : ℕ} (hW : 0 < W) (hp : Nat.Prime p) (hcop : Nat.Coprime W p) :
    ((roughWheelResidues (W * p)).card : ℝ) / ((W * p : ℕ) : ℝ) =
      ((roughWheelResidues W).card : ℝ) / W * (1 - 1 / (p : ℝ)) := by
  rw [roughWheelResidues_card_eq_totient, Nat.totient_mul hcop,
    Nat.totient_prime hp, roughWheelResidues_card_eq_totient]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hWR, hpR]

/-- The covariance prefix and the wheel-one prefix have identical endpoints. -/
theorem realMertensLength_succ_eq_roughMertens_one (B : ℕ) :
    realMertensLength (B + 1) = (roughMertens 1 B : ℝ) := by
  simp [realMertensLength, realMoebiusStep, roughMertens, roughMoebius]

/-- Finite `6`-wheel bound, including all incomplete-period and floor costs. -/
theorem abs_realMertensLength_succ_le_sixWheel (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (2 / 9 : ℝ) * B + 9 := by
  have h0 := abs_roughInterval_le_density (W := 6)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  rw [roughWheelResidues_card_six] at h0
  norm_num at h0
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  have h1 := abs_roughInterval_le_density (W := 6)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  rw [roughWheelResidues_card_six] at h1
  norm_num at h1
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  have hwidthNat : 3 * (B + B / 3) ≤
      2 * B + 3 * (B / 2 + B / 6) + 6 := by omega
  have hwidth : (3 : ℝ) * ((B : ℝ) + ((B / 3 : ℕ) : ℝ)) ≤
      2 * (B : ℝ) + 3 * (((B / 2 : ℕ) : ℝ) + ((B / 6 : ℕ) : ℝ)) + 6 := by
    exact_mod_cast hwidthNat
  rw [realMertensLength_succ_eq_roughMertens_one,
    roughMertens_one_eq_sixWheel_twoBands]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The same finite bound on the exact post-root Bessel remainder. -/
theorem postRootCovarianceRemainder_le_sixWheelSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((2 / 9 : ℝ) * W + 9) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_sixWheel W)

/-- Finite `30`-wheel bound, including all incomplete-period and floor costs. -/
theorem abs_realMertensLength_succ_le_thirtyWheel (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (16 / 75 : ℝ) * B + 66 := by
  have h0 := abs_roughInterval_le_density (W := 30)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  rw [roughWheelResidues_card_thirty] at h0
  norm_num at h0
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  have h1 := abs_roughInterval_le_density (W := 30)
    (a := B / 10) (b := B / 5) (by norm_num) (by omega)
  rw [roughWheelResidues_card_thirty] at h1
  norm_num at h1
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  have h2 := abs_roughInterval_le_density (W := 30)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  rw [roughWheelResidues_card_thirty] at h2
  norm_num at h2
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  have h3 := abs_roughInterval_le_density (W := 30)
    (a := B / 30) (b := B / 15) (by norm_num) (by omega)
  rw [roughWheelResidues_card_thirty] at h3
  norm_num at h3
  obtain ⟨h3lo, h3hi⟩ := abs_le.mp h3
  have hwidthNat : 5 * (B + B / 5 + B / 3 + B / 15) ≤
      4 * B + 5 * (B / 2 + B / 10 + B / 6 + B / 30) + 20 := by omega
  have hwidth : (5 : ℝ) * ((B : ℝ) + ((B / 5 : ℕ) : ℝ) + ((B / 3 : ℕ) : ℝ) + ((B / 15 : ℕ) : ℝ)) ≤
      4 * (B : ℝ) + 5 * (((B / 2 : ℕ) : ℝ) + ((B / 10 : ℕ) : ℝ) + ((B / 6 : ℕ) : ℝ) + ((B / 30 : ℕ) : ℝ)) + 20 := by
    exact_mod_cast hwidthNat
  rw [realMertensLength_succ_eq_roughMertens_one,
    roughMertens_one_eq_thirtyWheel_fourBands]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The same finite bound on the exact post-root Bessel remainder. -/
theorem postRootCovarianceRemainder_le_thirtyWheelSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((16 / 75 : ℝ) * W + 66) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_thirtyWheel W)

/-- Finite `210`-wheel bound, including all incomplete-period and floor costs. -/
theorem abs_realMertensLength_succ_le_twoTenWheel (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (256 / 1225 : ℝ) * B + 770 := by
  have h0 := abs_roughInterval_le_density (W := 210)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h0
  norm_num at h0
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  have h1 := abs_roughInterval_le_density (W := 210)
    (a := B / 14) (b := B / 7) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h1
  norm_num at h1
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  have h2 := abs_roughInterval_le_density (W := 210)
    (a := B / 10) (b := B / 5) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h2
  norm_num at h2
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  have h3 := abs_roughInterval_le_density (W := 210)
    (a := B / 70) (b := B / 35) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h3
  norm_num at h3
  obtain ⟨h3lo, h3hi⟩ := abs_le.mp h3
  have h4 := abs_roughInterval_le_density (W := 210)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h4
  norm_num at h4
  obtain ⟨h4lo, h4hi⟩ := abs_le.mp h4
  have h5 := abs_roughInterval_le_density (W := 210)
    (a := B / 42) (b := B / 21) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h5
  norm_num at h5
  obtain ⟨h5lo, h5hi⟩ := abs_le.mp h5
  have h6 := abs_roughInterval_le_density (W := 210)
    (a := B / 30) (b := B / 15) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h6
  norm_num at h6
  obtain ⟨h6lo, h6hi⟩ := abs_le.mp h6
  have h7 := abs_roughInterval_le_density (W := 210)
    (a := B / 210) (b := B / 105) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h7
  norm_num at h7
  obtain ⟨h7lo, h7hi⟩ := abs_le.mp h7
  have hw0 := natDiv_interval_width_le B 2 1 (by norm_num) (by norm_num)
  have hw1 := natDiv_interval_width_le B 14 7 (by norm_num) (by norm_num)
  have hw2 := natDiv_interval_width_le B 10 5 (by norm_num) (by norm_num)
  have hw3 := natDiv_interval_width_le B 70 35 (by norm_num) (by norm_num)
  have hw4 := natDiv_interval_width_le B 6 3 (by norm_num) (by norm_num)
  have hw5 := natDiv_interval_width_le B 42 21 (by norm_num) (by norm_num)
  have hw6 := natDiv_interval_width_le B 30 15 (by norm_num) (by norm_num)
  have hw7 := natDiv_interval_width_le B 210 105 (by norm_num) (by norm_num)
  have hwidth : (35 : ℝ) * ((B : ℝ) + ((B / 7 : ℕ) : ℝ) + ((B / 5 : ℕ) : ℝ) + ((B / 35 : ℕ) : ℝ) + ((B / 3 : ℕ) : ℝ) + ((B / 21 : ℕ) : ℝ) + ((B / 15 : ℕ) : ℝ) + ((B / 105 : ℕ) : ℝ)) ≤
      32 * (B : ℝ) + 35 * (((B / 2 : ℕ) : ℝ) + ((B / 14 : ℕ) : ℝ) + ((B / 10 : ℕ) : ℝ) + ((B / 70 : ℕ) : ℝ) + ((B / 6 : ℕ) : ℝ) + ((B / 42 : ℕ) : ℝ) + ((B / 30 : ℕ) : ℝ) + ((B / 210 : ℕ) : ℝ)) + 280 := by
    norm_num at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ⊢
    linarith
  rw [realMertensLength_succ_eq_roughMertens_one,
    roughMertens_one_eq_twoTenWheel_eightBands]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The same finite bound on the exact post-root Bessel remainder. -/
theorem postRootCovarianceRemainder_le_twoTenWheelSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((256 / 1225 : ℝ) * W + 770) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_twoTenWheel W)

/-- Leading coefficient for separately counted bands after the initial
2-wheel, with `P` containing the subsequent odd primes. -/
def primeWheelBandSupportCoefficient (P : Finset ℕ) : ℝ :=
  (1 / 4) * primorialSquarefreeEulerFactor P

/-- The existing exact finite-cube factorization accounts for both the
thinner residue population and the extra child-band lengths. -/
theorem primeWheelBandSupportCoefficient_eq_density_mul_bandLength (P : Finset ℕ) :
    primeWheelBandSupportCoefficient P =
      ((1 / 2) * primorialSignedContractionFactor P) *
        ((1 / 2) * primorialSquarefreeSupportFactor P) := by
  rw [primeWheelBandSupportCoefficient,
    ← primorial_signed_mul_support_eq_squarefreeEuler]
  ring

/-- A new prime contracts this particular unsigned majorant by `1-1/p^2`. -/
theorem primeWheelBandSupportCoefficient_insert
    (P : Finset ℕ) (p : ℕ) (hp : p ∉ P) :
    primeWheelBandSupportCoefficient (insert p P) =
      primeWheelBandSupportCoefficient P * (1 - 1 / (p : ℝ) ^ 2) := by
  classical
  simp only [primeWheelBandSupportCoefficient, primorialSquarefreeEulerFactor,
    Finset.prod_insert hp]
  ring

/-- The leading coefficients of the three actual interval estimates above. -/
theorem primeWheelBandSupportCoefficient_6_30_210 :
    primeWheelBandSupportCoefficient {3} = (2 / 9 : ℝ) ∧
      primeWheelBandSupportCoefficient {3, 5} = (16 / 75 : ℝ) ∧
      primeWheelBandSupportCoefficient {3, 5, 7} = (256 / 1225 : ℝ) := by
  norm_num [primeWheelBandSupportCoefficient, primorialSquarefreeEulerFactor]

private theorem squareReciprocalProduct_Icc (N : ℕ) :
    (∏ n ∈ Finset.Icc 3 (N + 2), (1 - 1 / (n : ℝ) ^ 2)) =
      2 * ((N : ℝ) + 3) / (3 * ((N : ℝ) + 2)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [show N + 1 + 2 = (N + 2) + 1 by omega,
        Finset.prod_Icc_succ_top (by omega), ih]
      push_cast
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      have h3 : (N : ℝ) + 3 ≠ 0 := by positivity
      field_simp [h2, h3]
      ring

/-- An elementary uniform positive floor for separate-band counting.
Even allowing *all* integers at least three as factors leaves at least `1/6`.
Thus this majorant cannot be made arbitrarily small by feeding it more primes.
This is a statement about this unsigned estimate, not a lower bound on `|M|`. -/
theorem primeWheelBandSupportCoefficient_ge_one_sixth
    (P : Finset ℕ) (hP : ∀ p ∈ P, 3 ≤ p) :
    (1 / 6 : ℝ) ≤ primeWheelBandSupportCoefficient P := by
  classical
  let N := P.sup id
  let T := Finset.Icc 3 (N + 2)
  have hsub : P ⊆ T := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨hP p hp,
      (Finset.le_sup (f := id) hp).trans (by omega)⟩
  have hfilter : T.filter (fun p => p ∈ P) = P := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hprod : (∏ p ∈ T, (1 - 1 / (p : ℝ) ^ 2)) ≤
      ∏ p ∈ T.filter (fun p => p ∈ P), (1 - 1 / (p : ℝ) ^ 2) := by
    rw [Finset.prod_filter]
    apply Finset.prod_le_prod
    · intro p hp
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
      apply sub_nonneg.mpr
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).mpr
      nlinarith
    · intro p _hp
      split_ifs
      · rfl
      · have hnonneg : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
        linarith
  rw [hfilter] at hprod
  have hexact := squareReciprocalProduct_Icc N
  change (∏ p ∈ T, (1 - 1 / (p : ℝ) ^ 2)) = _ at hexact
  have hfloor : (2 / 3 : ℝ) ≤ 2 * ((N : ℝ) + 3) / (3 * ((N : ℝ) + 2)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  rw [hexact] at hprod
  unfold primeWheelBandSupportCoefficient primorialSquarefreeEulerFactor
  linarith

end RHLean.Proof