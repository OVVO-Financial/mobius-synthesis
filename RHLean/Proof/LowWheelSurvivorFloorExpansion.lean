import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Proof.LowWheelSurvivorInclusionExclusion

/-!
# Floor expansion of low-wheel survivor frequencies

The Boolean-cube expansion of the high-prime survivor count is now converted
into the exact arithmetic floor formula.  For each low-prime face `t`, the
number of multiples of its squarefree product `d = primeFaceProduct t` in the
interval `(R,B]` is

`floor(B/d) - floor(R/d)`.

Specializing `B = floor((R^2-1)/c)` therefore removes the prime-count function
from every transport multiplicity.  The high-prime frequency is expressed
entirely through low-prime Boolean-cube signs and the hyperbolic cutoff
`c * d * k <= R^2 - 1`.

The second half records the exact closure of the resulting one-prime frontier
coordinate.  Its pointwise incidence is both a centered cofactor hyperbola and
a finite Mertens bundle.  On the top half of the root range it is literally
`1 - M(floor((R^2-1)/n))`, so a positive energy contains local Mertens energy
verbatim.  The remaining signed bootstrap collapses by `mu * 1 = delta` to
`M(X) = M(X)`.

No norm estimate, prime-number theorem, Strong Mertens estimate, asymptotic,
or RH input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Exact count of multiples of a positive integer in a half-open interval. -/
theorem card_Ioc_filter_dvd_eq_div_sub_div
    (A B d : ℕ) (hd : 0 < d) :
    ((Finset.Ioc A B).filter fun q => d ∣ q).card =
      B / d - A / d := by
  classical
  have hbij :
      (Finset.Ioc (A / d) (B / d)).card =
        ((Finset.Ioc A B).filter fun q => d ∣ q).card := by
    refine Finset.card_bij (fun k _hk => d * k) ?_ ?_ ?_
    · intro k hk
      rcases Finset.mem_Ioc.mp hk with ⟨hlow, hupp⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Ioc.mpr
        constructor
        · have h := (Nat.div_lt_iff_lt_mul hd).1 hlow
          simpa [Nat.mul_comm] using h
        · have h := (Nat.le_div_iff_mul_le hd).1 hupp
          simpa [Nat.mul_comm] using h
      · exact ⟨k, rfl⟩
    · intro a _ha b _hb hab
      exact Nat.eq_of_mul_eq_mul_left hd hab
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqIoc, hdiv⟩
      rcases hdiv with ⟨k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      apply Finset.mem_Ioc.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hd).2
        simpa [Nat.mul_comm] using (Finset.mem_Ioc.mp hqIoc).1
      · apply (Nat.le_div_iff_mul_le hd).2
        simpa [Nat.mul_comm] using (Finset.mem_Ioc.mp hqIoc).2
  simpa using hbij.symm

/-- Every Boolean-cube prime-face product is positive. -/
theorem primeFaceProduct_pos_of_mem_powerset
    {R : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    0 < primeFaceProduct t := by
  unfold primeFaceProduct
  apply Finset.prod_pos
  intro p hp
  have hpR : p ∈ primesUpTo R := (Finset.mem_powerset.mp ht) hp
  exact (prime_of_mem_primesUpTo hpR).pos

/-- One face's divisibility population is the elementary floor difference. -/
theorem lowWheelFaceMultipleSet_card_eq_floorDiff
    {R B : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    (lowWheelFaceMultipleSet R B t).card =
      B / primeFaceProduct t - R / primeFaceProduct t := by
  unfold lowWheelFaceMultipleSet
  exact card_Ioc_filter_dvd_eq_div_sub_div
    R B (primeFaceProduct t) (primeFaceProduct_pos_of_mem_powerset ht)

/-- **Boolean-cube floor expansion.**  Every high-survivor count is now an
exact finite alternating sum of floor differences indexed only by low-prime
faces. -/
theorem lowWheelHighSurvivorSet_card_eq_faceFloorDiff
    (R B : ℕ) :
    ((lowWheelHighSurvivorSet R B).card : ℤ) =
      ∑ t ∈ (primesUpTo R).powerset,
        booleanCubeSign t *
          ((B / primeFaceProduct t - R / primeFaceProduct t : ℕ) : ℤ) := by
  rw [lowWheelHighSurvivorSet_card_eq_faceMultipleCounts]
  apply Finset.sum_congr rfl
  intro t ht
  rw [lowWheelFaceMultipleSet_card_eq_floorDiff ht]

/-- The cofactor-specific high-prime multiplicity has no remaining prime-count
term: it is a signed low-wheel face sum with a reciprocal hyperbolic cutoff. -/
theorem lowWheelHighPrimeMultiplicity_eq_faceFloorDiff
    (R c : ℕ) :
    (lowWheelHighPrimeMultiplicity R c : ℤ) =
      ∑ t ∈ (primesUpTo R).powerset,
        booleanCubeSign t *
          ((squareRootEndpoint R / (c * primeFaceProduct t) -
              R / primeFaceProduct t : ℕ) : ℤ) := by
  unfold lowWheelHighPrimeMultiplicity
  rw [lowWheelHighSurvivorSet_card_eq_faceFloorDiff]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Nat.div_div_eq_div_mul]

/-- Complex form of the exact frequency expansion, ready to substitute into
the cofactor-first transport sum without changing its signed order. -/
theorem lowWheelHighPrimeMultiplicity_cast_eq_faceFloorDiff
    (R c : ℕ) :
    (lowWheelHighPrimeMultiplicity R c : ℂ) =
      ∑ t ∈ (primesUpTo R).powerset,
        (booleanCubeSign t : ℂ) *
          ((squareRootEndpoint R / (c * primeFaceProduct t) -
              R / primeFaceProduct t : ℕ) : ℂ) := by
  have h := lowWheelHighPrimeMultiplicity_eq_faceFloorDiff R c
  exact_mod_cast h

/-- **Prime-count-free transport identity.**  The whole upper-prime transport
mass is a finite double sum over a low cofactor `c` and a low-prime Boolean face
`t`.  The high region now appears only through the floor cutoff. -/
theorem squareRootTransportCofactorFirst_eq_lowWheelFaceFloorSum
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      ∑ c ∈ Finset.Ico 1 R,
        ∑ t ∈ (primesUpTo R).powerset,
          canonicalMoebiusWeight c * (booleanCubeSign t : ℂ) *
            ((squareRootEndpoint R / (c * primeFaceProduct t) -
                R / primeFaceProduct t : ℕ) : ℂ) := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelFrequency R hR]
  unfold squareRootTransportLowWheelFrequency
  apply Finset.sum_congr rfl
  intro c _hc
  rw [lowWheelHighPrimeMultiplicity_cast_eq_faceFloorDiff R c]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-! ## Exact closure of the one-prime frontier coordinate -/

/-- Pointwise canonical frontier incidence in its exact lower-scale Mertens
bundle form. -/
def canonicalFrontierIncidence (R n : ℕ) : ℂ :=
  1 - ∑ q ∈ Finset.Icc 1 (R / n),
    mertensSummatory (squareRootEndpoint R / (n * q))

/-- The pointwise incidence is exactly the finite lower-scale Mertens bundle. -/
theorem canonicalIncidence_eq_one_sub_mertensBundle
    (R n : ℕ) :
    canonicalFrontierIncidence R n =
      1 - ∑ q ∈ Finset.Icc 1 (R / n),
        mertensSummatory (squareRootEndpoint R / (n * q)) := by
  rfl

/-- Summing Mertens over a reciprocal half-open interval is exactly the
Möbius-weighted floor-difference hyperbola. -/
theorem sum_mertensSummatory_Ioc_eq_moebius_floorDiff
    (N T : ℕ) :
    (∑ q ∈ Finset.Ioc T N, mertensSummatory (N / q)) =
      ∑ c ∈ Finset.Icc 1 N,
        canonicalMoebiusWeight c * (((N / c - T : ℕ) : ℂ)) := by
  classical
  calc
    (∑ q ∈ Finset.Ioc T N, mertensSummatory (N / q)) =
      ∑ q ∈ Finset.Ioc T N,
        ∑ c ∈ Finset.Icc 1 N,
          if c * q ≤ N then canonicalMoebiusWeight c else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqpos : 0 < q := by
              have := (Finset.mem_Ioc.mp hq).1
              omega
            rw [RHLean.Analysis.mertensSummatory_eq_sum_Icc]
            have hset :
                Finset.Icc 1 (N / q) =
                  (Finset.Icc 1 N).filter (fun c => c * q ≤ N) := by
              ext c
              simp only [Finset.mem_Icc, Finset.mem_filter]
              constructor
              · rintro ⟨hc1, hcdiv⟩
                have hmul : c * q ≤ N :=
                  (Nat.le_div_iff_mul_le hqpos).1 hcdiv
                have hcN : c ≤ N :=
                  (Nat.le_mul_of_pos_right c hqpos).trans hmul
                exact ⟨⟨hc1, hcN⟩, hmul⟩
              · rintro ⟨⟨hc1, _hcN⟩, hmul⟩
                exact ⟨hc1, (Nat.le_div_iff_mul_le hqpos).2 hmul⟩
            rw [hset, Finset.sum_filter]
            simp [canonicalMoebiusWeight]
    _ = ∑ c ∈ Finset.Icc 1 N,
        ∑ q ∈ Finset.Ioc T N,
          if c * q ≤ N then canonicalMoebiusWeight c else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ c ∈ Finset.Icc 1 N,
        canonicalMoebiusWeight c * (((N / c - T : ℕ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro c hc
          have hcpos : 0 < c := by
            have := (Finset.mem_Icc.mp hc).1
            omega
          have hfilter :
              (Finset.Ioc T N).filter (fun q => c * q ≤ N) =
                Finset.Ioc T (N / c) := by
            ext q
            simp only [Finset.mem_filter, Finset.mem_Ioc]
            constructor
            · rintro ⟨⟨hTq, _hqN⟩, hmul⟩
              have hqdiv : q ≤ N / c := by
                apply (Nat.le_div_iff_mul_le hcpos).2
                simpa [Nat.mul_comm] using hmul
              exact ⟨hTq, hqdiv⟩
            · rintro ⟨hTq, hqdiv⟩
              have hmul : c * q ≤ N := by
                have := (Nat.le_div_iff_mul_le hcpos).1 hqdiv
                simpa [Nat.mul_comm] using this
              have hqN : q ≤ N := hqdiv.trans (Nat.div_le_self N c)
              exact ⟨⟨hTq, hqN⟩, hmul⟩
          have hfilterOne :
              (Finset.Ioc T (N / c)).filter (fun q => 1 ∣ q) =
                Finset.Ioc T (N / c) := by
            ext q
            simp
          have hcard : (Finset.Ioc T (N / c)).card = N / c - T := by
            calc
              (Finset.Ioc T (N / c)).card =
                  ((Finset.Ioc T (N / c)).filter (fun q => 1 ∣ q)).card := by
                    rw [hfilterOne]
              _ = (N / c) / 1 - T / 1 :=
                card_Ioc_filter_dvd_eq_div_sub_div
                  T (N / c) 1 Nat.zero_lt_one
              _ = N / c - T := by simp only [Nat.div_one]
          rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul,
            hcard]
          ring

/-- The incidence bundle is the complementary tail of the classical unit
Mertens hyperbola after the cutoff `floor(R/n)`. -/
theorem canonicalFrontierIncidence_eq_mertensTail
    {R n : ℕ} (hR : 2 ≤ R) (hn : 1 ≤ n) (hnR : n ≤ R) :
    canonicalFrontierIncidence R n =
      ∑ q ∈ Finset.Ioc (R / n) (squareRootEndpoint R / n),
        mertensSummatory ((squareRootEndpoint R / n) / q) := by
  classical
  have hnpos : 0 < n := by omega
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hTleN : R / n ≤ squareRootEndpoint R / n :=
    Nat.div_le_div_right hRX
  have hT1 : 1 ≤ R / n := (Nat.one_le_div_iff hnpos).2 hnR
  have hN1 : 1 ≤ squareRootEndpoint R / n :=
    (Nat.one_le_div_iff hnpos).2 (hnR.trans hRX)
  have hset :
      Finset.Icc 1 (squareRootEndpoint R / n) =
        Finset.Icc 1 (R / n) ∪
          Finset.Ioc (R / n) (squareRootEndpoint R / n) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · intro hq
      by_cases hqT : q ≤ R / n
      · exact Or.inl ⟨hq.1, hqT⟩
      · exact Or.inr ⟨Nat.lt_of_not_ge hqT, hq.2⟩
    · rintro (hq | hq)
      · exact ⟨hq.1, hq.2.trans hTleN⟩
      · exact ⟨hT1.trans (Nat.le_of_lt hq.1), hq.2⟩
  have hdisj :
      Disjoint (Finset.Icc 1 (R / n))
        (Finset.Ioc (R / n) (squareRootEndpoint R / n)) := by
    rw [Finset.disjoint_left]
    intro q hqlo hqhi
    simp only [Finset.mem_Icc] at hqlo
    simp only [Finset.mem_Ioc] at hqhi
    omega
  have hunit := RHLean.Analysis.sum_mertensSummatory_div_eq_one hN1
  have hprefix :
      (∑ q ∈ Finset.Icc 1 (R / n),
          mertensSummatory (squareRootEndpoint R / (n * q))) =
        ∑ q ∈ Finset.Icc 1 (R / n),
          mertensSummatory ((squareRootEndpoint R / n) / q) := by
    apply Finset.sum_congr rfl
    intro q _hq
    rw [Nat.div_div_eq_div_mul]
  unfold canonicalFrontierIncidence
  rw [hprefix]
  rw [← hunit, hset, Finset.sum_union hdisj]
  ring

/-- **Centered cofactor-hyperbola form of the canonical incidence.**  The same
pointwise field obtained by the one-prime frontier is the complete signed low
cofactor population through the square endpoint, centered by `floor(R/n)`. -/
theorem canonicalIncidence_eq_centeredCofactorHyperbola
    {R n : ℕ} (hR : 2 ≤ R) (hn : 1 ≤ n) (hnR : n ≤ R) :
    canonicalFrontierIncidence R n =
      ∑ c ∈ Finset.Ico 1 R,
        canonicalMoebiusWeight c *
          (((squareRootEndpoint R / (n * c) - R / n : ℕ) : ℂ)) := by
  classical
  have hnpos : 0 < n := by omega
  rw [canonicalFrontierIncidence_eq_mertensTail hR hn hnR,
    sum_mertensSummatory_Ioc_eq_moebius_floorDiff]
  have hsubset :
      Finset.Ico 1 R ⊆ Finset.Icc 1 (squareRootEndpoint R / n) := by
    intro c hc
    rcases Finset.mem_Ico.mp hc with ⟨hc1, hcR⟩
    have hcnLt : c * n < R * R := by
      have h1 : c * n < R * n := Nat.mul_lt_mul_of_pos_right hcR hnpos
      have h2 : R * n ≤ R * R := Nat.mul_le_mul_left R hnR
      exact h1.trans_le h2
    have hcnX : c * n ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      have hpow : R ^ 2 = R * R := by ring
      rw [hpow]
      omega
    exact Finset.mem_Icc.mpr
      ⟨hc1, (Nat.le_div_iff_mul_le hnpos).2 hcnX⟩
  have hzero :
      ∀ c ∈ Finset.Icc 1 (squareRootEndpoint R / n),
        c ∉ Finset.Ico 1 R →
        canonicalMoebiusWeight c *
          ((((squareRootEndpoint R / n) / c - R / n : ℕ) : ℂ)) = 0 := by
    intro c hc hcnot
    have hcdata := Finset.mem_Icc.mp hc
    have hcR : R ≤ c := by
      by_contra hnot
      have hcLt : c < R := Nat.lt_of_not_ge hnot
      exact hcnot (Finset.mem_Ico.mpr ⟨hcdata.1, hcLt⟩)
    have hle : (squareRootEndpoint R / n) / c ≤ R / n := by
      by_contra hnot
      have hgt : R / n < (squareRootEndpoint R / n) / c :=
        Nat.lt_of_not_ge hnot
      have hRlt :
          R < ((squareRootEndpoint R / n) / c) * n :=
        (Nat.div_lt_iff_lt_mul hnpos).1 hgt
      have hRpos : 0 < R := by omega
      have hsqLt :
          R * R < (((squareRootEndpoint R / n) / c) * n) * R :=
        Nat.mul_lt_mul_of_pos_right hRlt hRpos
      have hRtoC :
          (((squareRootEndpoint R / n) / c) * n) * R ≤
            (((squareRootEndpoint R / n) / c) * n) * c :=
        Nat.mul_le_mul_left (((squareRootEndpoint R / n) / c) * n) hcR
      have hdivC :
          (squareRootEndpoint R / n) / c * c ≤ squareRootEndpoint R / n :=
        Nat.div_mul_le_self (squareRootEndpoint R / n) c
      have hmulN :
          ((squareRootEndpoint R / n) / c * c) * n ≤
            (squareRootEndpoint R / n) * n :=
        Nat.mul_le_mul_right n hdivC
      have hdivN :
          (squareRootEndpoint R / n) * n ≤ squareRootEndpoint R :=
        Nat.div_mul_le_self (squareRootEndpoint R) n
      have hprod :
          (((squareRootEndpoint R / n) / c) * n) * c ≤
            squareRootEndpoint R := by
        calc
          (((squareRootEndpoint R / n) / c) * n) * c =
              ((squareRootEndpoint R / n) / c * c) * n := by ring
          _ ≤ (squareRootEndpoint R / n) * n := hmulN
          _ ≤ squareRootEndpoint R := hdivN
      have hbad : R * R < squareRootEndpoint R :=
        hsqLt.trans_le (hRtoC.trans hprod)
      unfold squareRootEndpoint at hbad
      have hsqpos : 0 < R ^ 2 := by positivity
      have hpow : R ^ 2 = R * R := by ring
      rw [← hpow] at hbad
      omega
    have hsub : (squareRootEndpoint R / n) / c - R / n = 0 :=
      Nat.sub_eq_zero_of_le hle
    simp [hsub]
  calc
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / n),
        canonicalMoebiusWeight c *
          ((((squareRootEndpoint R / n) / c - R / n : ℕ) : ℂ))) =
      ∑ c ∈ Finset.Ico 1 R,
        canonicalMoebiusWeight c *
          ((((squareRootEndpoint R / n) / c - R / n : ℕ) : ℂ)) :=
        (Finset.sum_subset hsubset hzero).symm
    _ = ∑ c ∈ Finset.Ico 1 R,
        canonicalMoebiusWeight c *
          (((squareRootEndpoint R / (n * c) - R / n : ℕ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [Nat.div_div_eq_div_mul]

/-- On the upper half of the root range the bundle has only the `q = 1` term. -/
theorem canonicalIncidence_eq_one_sub_mertens_of_half_lt
    {R n : ℕ} (hn : 1 ≤ n) (hnR : n ≤ R) (hhalf : R / 2 < n) :
    canonicalFrontierIncidence R n =
      1 - mertensSummatory (squareRootEndpoint R / n) := by
  have hnpos : 0 < n := by omega
  have hRlt : R < n * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hhalf
  have hlt2 : R / n < 2 := by
    apply (Nat.div_lt_iff_lt_mul hnpos).2
    simpa [Nat.mul_comm] using hRlt
  have hge1 : 1 ≤ R / n := (Nat.one_le_div_iff hnpos).2 hnR
  have hdiv : R / n = 1 := by omega
  simp [canonicalFrontierIncidence, hdiv]

/-- Positive top-half energy of the incidence field. -/
def canonicalFrontierTopEnergy (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (R / 2) R,
    (n : ℝ) * ‖canonicalFrontierIncidence R n‖ ^ 2

/-- The top-half positive energy literally contains the local Mertens values
`M(floor((R^2-1)/n))`; no positive norm has removed them. -/
theorem canonicalFrontierTopEnergy_eq_localMertensEnergy
    (R : ℕ) :
    canonicalFrontierTopEnergy R =
      ∑ n ∈ Finset.Ioc (R / 2) R,
        (n : ℝ) * ‖1 - mertensSummatory (squareRootEndpoint R / n)‖ ^ 2 := by
  classical
  unfold canonicalFrontierTopEnergy
  apply Finset.sum_congr rfl
  intro n hnI
  rcases Finset.mem_Ioc.mp hnI with ⟨hhalf, hnR⟩
  have hn : 1 ≤ n := by omega
  rw [canonicalIncidence_eq_one_sub_mertens_of_half_lt hn hnR hhalf]

/-- Generic triangular Möbius collapse.  Regrouping by `m = n*q` gives
coefficient `sum_{n | m} mu(n)`, hence only `m = 1` survives. -/
theorem mobius_hyperbola_double_sum_eq_head
    (F : ℕ → ℂ) {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) =
      F 1 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) =
      ∑ n ∈ Finset.Icc 1 R,
        ∑ q ∈ Finset.Icc 1 (R / n),
          (((μ n : ℤ) : ℂ)) * F (n * q) := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 R,
        ∑ p ∈ m.divisorsAntidiagonal,
          (((μ p.1 : ℤ) : ℂ)) * F (p.1 * p.2) := by
            symm
            exact RHLean.Analysis.sum_Icc_divisorsAntidiagonal_eq_sum_div
              (fun a b => (((μ a : ℤ) : ℂ)) * F (a * b)) R
    _ = ∑ m ∈ Finset.Icc 1 R,
        (if m = 1 then F 1 else 0) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hanti :
              (∑ p ∈ m.divisorsAntidiagonal,
                  (((μ p.1 : ℤ) : ℂ)) * F (p.1 * p.2)) =
                ∑ d ∈ m.divisors,
                  (((μ d : ℤ) : ℂ)) * F (d * (m / d)) :=
            Nat.sum_divisorsAntidiagonal
              (f := fun a b => (((μ a : ℤ) : ℂ)) * F (a * b))
          rw [hanti]
          calc
            (∑ d ∈ m.divisors,
                (((μ d : ℤ) : ℂ)) * F (d * (m / d))) =
              ∑ d ∈ m.divisors,
                (((μ d : ℤ) : ℂ)) * F m := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  have hdData := Nat.mem_divisors.mp hd
                  rw [Nat.mul_div_cancel' hdData.1]
            _ = (∑ d ∈ m.divisors, (((μ d : ℤ) : ℂ))) * F m := by
                  rw [Finset.sum_mul]
            _ = (if m = 1 then (1 : ℂ) else 0) * F m := by
                  rw [RHLean.Analysis.sum_divisors_moebius_eq_ite]
            _ = if m = 1 then F 1 else 0 := by
                  by_cases hm1 : m = 1
                  · subst m
                    simp
                  · simp [hm1]
    _ = F 1 := by
      have h1mem : (1 : ℕ) ∈ Finset.Icc 1 R :=
        Finset.mem_Icc.mpr ⟨le_rfl, hR⟩
      simp [h1mem]

/-- The complete signed incidence sum is exactly the original square-endpoint
Mertens gap; the pointwise coordinate has not introduced a new signed scalar. -/
theorem canonicalFrontierIncidence_signedSum_eq_mertensGap
    (R : ℕ) (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) * canonicalFrontierIncidence R n) =
      mertensSummatory R - mertensSummatory (squareRootEndpoint R) := by
  unfold canonicalFrontierIncidence
  calc
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          (1 - ∑ q ∈ Finset.Icc 1 (R / n),
            mertensSummatory (squareRootEndpoint R / (n * q)))) =
      (∑ n ∈ Finset.Icc 1 R, (((μ n : ℤ) : ℂ))) -
        ∑ n ∈ Finset.Icc 1 R,
          (((μ n : ℤ) : ℂ)) *
            ∑ q ∈ Finset.Icc 1 (R / n),
              mertensSummatory (squareRootEndpoint R / (n * q)) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro n _hn
                ring
    _ = mertensSummatory R - mertensSummatory (squareRootEndpoint R) := by
      rw [← RHLean.Analysis.mertensSummatory_eq_sum_Icc R]
      rw [mobius_hyperbola_double_sum_eq_head
        (F := fun m => mertensSummatory (squareRootEndpoint R / m)) hR]
      simp

/-- Corrected lower-half/top-half bootstrap expression. -/
def frontierBootstrapRHS (R : ℕ) : ℂ :=
  mertensSummatory (R / 2) -
    ∑ n ∈ Finset.Icc 1 (R / 2),
      (((μ n : ℤ) : ℂ)) * canonicalFrontierIncidence R n +
    ∑ n ∈ Finset.Ioc (R / 2) R,
      (((μ n : ℤ) : ℂ)) *
        mertensSummatory (squareRootEndpoint R / n)

/-- The corrected split bootstrap is exactly the full triangular Möbius bundle.
This is the algebraic step that makes the no-go transparent. -/
theorem frontierBootstrapRHS_eq_fullHyperbola
    (R : ℕ) :
    frontierBootstrapRHS R =
      ∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n),
            mertensSummatory (squareRootEndpoint R / (n * q)) := by
  classical
  let H := R / 2
  have hset : Finset.Icc 1 R = Finset.Icc 1 H ∪ Finset.Ioc H R := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 H) (Finset.Ioc H R) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo
    simp only [Finset.mem_Ioc] at hnhi
    omega
  have hM : mertensSummatory H =
      ∑ n ∈ Finset.Icc 1 H, (((μ n : ℤ) : ℂ)) :=
    RHLean.Analysis.mertensSummatory_eq_sum_Icc H
  have htop :
      (∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) *
            ∑ q ∈ Finset.Icc 1 (R / n),
              mertensSummatory (squareRootEndpoint R / (n * q))) =
        ∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) *
            mertensSummatory (squareRootEndpoint R / n) := by
    apply Finset.sum_congr rfl
    intro n hnI
    rcases Finset.mem_Ioc.mp hnI with ⟨hHn, hnR⟩
    have hnpos : 0 < n := by omega
    have hRlt : R < n * 2 := by
      dsimp [H] at hHn
      exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hHn
    have hlt2 : R / n < 2 := by
      apply (Nat.div_lt_iff_lt_mul hnpos).2
      simpa [Nat.mul_comm] using hRlt
    have hge1 : 1 ≤ R / n := (Nat.one_le_div_iff hnpos).2 hnR
    have hdiv : R / n = 1 := by omega
    simp [hdiv]
  have hlow :
      mertensSummatory H -
          ∑ n ∈ Finset.Icc 1 H,
            (((μ n : ℤ) : ℂ)) * canonicalFrontierIncidence R n =
        ∑ n ∈ Finset.Icc 1 H,
          (((μ n : ℤ) : ℂ)) *
            ∑ q ∈ Finset.Icc 1 (R / n),
              mertensSummatory (squareRootEndpoint R / (n * q)) := by
    rw [hM]
    unfold canonicalFrontierIncidence
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  unfold frontierBootstrapRHS
  change
    mertensSummatory H -
          ∑ n ∈ Finset.Icc 1 H,
            (((μ n : ℤ) : ℂ)) * canonicalFrontierIncidence R n +
        ∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) *
            mertensSummatory (squareRootEndpoint R / n) =
      ∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n),
            mertensSummatory (squareRootEndpoint R / (n * q))
  rw [hlow]
  rw [hset, Finset.sum_union hdisj]
  rw [htop]

/-- Corrected finite self-consistency relation. -/
theorem frontier_bootstrap_self_consistency
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) = frontierBootstrapRHS R := by
  rw [frontierBootstrapRHS_eq_fullHyperbola R]
  symm
  simpa using mobius_hyperbola_double_sum_eq_head
    (F := fun m => mertensSummatory (squareRootEndpoint R / m))
    (R := R) (by omega)

/-- **Definitive one-prime-frontier no-go.**  After the incidence bundle is
substituted, the bootstrap is exactly `mu * 1 = delta`; it collapses to the
identity `M(X) = M(X)` and imposes no additional finite-volume constraint. -/
theorem frontier_bootstrap_collapses_to_identity
    (R : ℕ) (hR : 2 ≤ R) :
    frontierBootstrapRHS R = mertensSummatory (squareRootEndpoint R) := by
  exact (frontier_bootstrap_self_consistency R hR).symm

/-- Landmark closure statement for the one-prime frontier coordinate: its
positive top-half energy is local Mertens energy, while its signed bootstrap is
the identity. -/
theorem frontier_cohomology_trivial
    (R : ℕ) (hR : 2 ≤ R) :
    frontierBootstrapRHS R = mertensSummatory (squareRootEndpoint R) ∧
      canonicalFrontierTopEnergy R =
        ∑ n ∈ Finset.Ioc (R / 2) R,
          (n : ℝ) * ‖1 - mertensSummatory (squareRootEndpoint R / n)‖ ^ 2 := by
  exact ⟨frontier_bootstrap_collapses_to_identity R hR,
    canonicalFrontierTopEnergy_eq_localMertensEnergy R⟩

end RHLean.Proof
