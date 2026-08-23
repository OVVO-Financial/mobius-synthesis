import Mathlib
import RHLean.Proof.ReplacementFibreOrientationSplit

/-!
# Cofactor-prime windows for replacement fibres

This companion to `ReplacementFibreOrientationSplit` reindexes the two signed
orientation fibres by canonical cofactor and prime.  The output is the exact
Type-II incidence through the dilated reciprocal windows `I_z^(c)`.

No norm or estimate is taken here.  In particular, the prime window counts are
multiplied by the signed cofactor Möbius weight before any later analytic
operation.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-! ## Root orientation -/

/-- Geometric root population in reciprocal fibre `z`.  Squarefreeness is not
part of the set: nonsquarefree sources have zero Möbius weight. -/
def replacementFibreRootGeometricSourceSet (R z : ℕ) : Finset ℕ :=
  (Finset.Icc R (squareRootEndpoint R)).filter fun n =>
    squareRootEndpoint R / n = z ∧
      canonicalCofactor n < canonicalLargestPrimeFactor n

/-- Signed Möbius mass of the geometric root population. -/
def replacementFibreRootGeometricSourceMass (R z : ℕ) : ℂ :=
  ∑ n ∈ replacementFibreRootGeometricSourceSet R z,
    canonicalMoebiusWeight n

/-- Removing squarefreeness from the root set changes no signed mass because
nonsquarefree integers carry zero Möbius weight. -/
theorem replacementFibreRootMass_eq_geometricSourceMass
    (R z : ℕ) :
    replacementFibreRootMass R z =
      replacementFibreRootGeometricSourceMass R z := by
  classical
  unfold replacementFibreRootMass replacementFibreRootGeometricSourceMass
    replacementFibreRootGeometricSourceSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hdiv : squareRootEndpoint R / n = z
  · by_cases horient :
        canonicalCofactor n < canonicalLargestPrimeFactor n
    · by_cases hsq : Squarefree n
      · simp [hdiv, horient, ReplacementRootOriented, hsq,
          canonicalMoebiusWeight]
      · have hzero : (μ n : ℤ) = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        simp [hdiv, horient, ReplacementRootOriented, hsq,
          canonicalMoebiusWeight, hzero]
    · simp [hdiv, horient, ReplacementRootOriented]
  · simp [hdiv]

/-- The automatic root-scale cofactor cutoff only uses the strict geometric
orientation `c < q`; squarefreeness is unnecessary. -/
theorem replacementRootGeometric_cofactor_lt_root
    {R n : ℕ} (hR : 2 ≤ R) (hn2 : 2 ≤ n)
    (hnX : n ≤ squareRootEndpoint R)
    (horient : canonicalCofactor n < canonicalLargestPrimeFactor n) :
    canonicalCofactor n < R := by
  have hn : 1 < n := by omega
  have hfactor := canonicalCofactor_mul_largestPrimeFactor hn
  by_contra hnot
  have hRc : R ≤ canonicalCofactor n := Nat.le_of_not_gt hnot
  have hRq : R ≤ canonicalLargestPrimeFactor n :=
    hRc.trans horient.le
  have hsqle : R ^ 2 ≤
      canonicalCofactor n * canonicalLargestPrimeFactor n := by
    simpa [pow_two] using Nat.mul_le_mul hRc hRq
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hnlt : n < R ^ 2 := hnX.trans_lt hXlt
  rw [hfactor] at hsqle
  exact (Nat.not_lt_of_ge hsqle) hnlt

/-- Canonical cofactor-prime coordinates for the geometric root population. -/
def replacementFibreRootPairSet (R z : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (R - 1)).product
      (Finset.Icc 2 (squareRootEndpoint R))).filter fun cq =>
    cq.2.Prime ∧ cq.1 < cq.2 ∧
      squareRootEndpoint R / (cq.1 * cq.2) = z

/-- Signed source mass in the cofactor-prime root coordinates. -/
def replacementFibreRootPairMass (R z : ℕ) : ℂ :=
  ∑ cq ∈ replacementFibreRootPairSet R z,
    canonicalMoebiusWeight (cq.1 * cq.2)

private theorem rootGeometricSource_to_pair_mem
    {R z n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ replacementFibreRootGeometricSourceSet R z) :
    (canonicalCofactor n, canonicalLargestPrimeFactor n) ∈
      replacementFibreRootPairSet R z := by
  classical
  rcases Finset.mem_filter.mp hn with ⟨hnTail, hdiv, horient⟩
  rcases Finset.mem_Icc.mp hnTail with ⟨hnR, hnX⟩
  have hn2 : 2 ≤ n := hR.trans hnR
  have hn1 : 1 < n := by omega
  have hcpos : 1 ≤ canonicalCofactor n :=
    CanonicalGapAncestryBridge.canonicalCofactor_pos hn1
  have hcR := replacementRootGeometric_cofactor_lt_root hR hn2 hnX horient
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hqdvd := canonicalLargestPrimeFactor_dvd hn1
  have hqle : canonicalLargestPrimeFactor n ≤ n :=
    Nat.le_of_dvd (by omega) hqdvd
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
    hqPrime, horient, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨hcpos, by omega⟩
  · exact Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqle.trans hnX⟩
  · rw [canonicalCofactor_mul_largestPrimeFactor hn1]
    exact hdiv

private theorem rootGeometricSource_pair_injective
    {R z m n : ℕ} (hR : 2 ≤ R)
    (hm : m ∈ replacementFibreRootGeometricSourceSet R z)
    (hn : n ∈ replacementFibreRootGeometricSourceSet R z)
    (hpair :
      (canonicalCofactor m, canonicalLargestPrimeFactor m) =
        (canonicalCofactor n, canonicalLargestPrimeFactor n)) :
    m = n := by
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1 with ⟨hmR, _⟩
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1 with ⟨hnR, _⟩
  have hm1 : 1 < m := by
    have hm2 : 2 ≤ m := hR.trans hmR
    omega
  have hn1 : 1 < n := by
    have hn2 : 2 ≤ n := hR.trans hnR
    omega
  have hmprod := canonicalCofactor_mul_largestPrimeFactor hm1
  have hnprod := canonicalCofactor_mul_largestPrimeFactor hn1
  have hc : canonicalCofactor m = canonicalCofactor n :=
    congrArg Prod.fst hpair
  have hq : canonicalLargestPrimeFactor m = canonicalLargestPrimeFactor n :=
    congrArg Prod.snd hpair
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hmprod.symm
    _ = canonicalCofactor n * canonicalLargestPrimeFactor n := by rw [hc, hq]
    _ = n := hnprod

private theorem rootPair_surjective
    {R z : ℕ} (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R)
    (cq : ℕ × ℕ) (hcq : cq ∈ replacementFibreRootPairSet R z) :
    ∃ n ∈ replacementFibreRootGeometricSourceSet R z,
      (canonicalCofactor n, canonicalLargestPrimeFactor n) = cq := by
  classical
  rcases Finset.mem_filter.mp hcq with
    ⟨hbase, hqPrime, hcqLt, hdiv⟩
  rcases Finset.mem_product.mp hbase with ⟨hcMem, hqMem⟩
  rcases Finset.mem_Icc.mp hcMem with ⟨hc1, _hcR⟩
  rcases Finset.mem_Icc.mp hqMem with ⟨_hq2, _hqX⟩
  have hcpos : 0 < cq.1 := by omega
  have hprodpos : 0 < cq.1 * cq.2 :=
    Nat.mul_pos hcpos hqPrime.pos
  have hinterval :=
    (squareRootEndpoint_div_eq_iff_mem_replacementFibre
      (R := R) (n := cq.1 * cq.2) (z := z) hprodpos hz).1 hdiv
  have htailDiv :=
    (replacementTailFibre_mem_iff R z (cq.1 * cq.2) hR hz hzR).2 hinterval
  have htop := canonicalLargestPrimeFactor_mul_prime_eq hcpos hcqLt hqPrime
  have hcore := canonicalCofactor_mul_prime_eq hcpos hcqLt hqPrime
  refine ⟨cq.1 * cq.2, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨htailDiv.1, htailDiv.2, ?_⟩
    rw [htop, hcore]
    exact hcqLt
  · apply Prod.ext
    · exact hcore
    · exact htop

/-- Exact bijective reindex from root-oriented integers to their canonical
cofactor-prime coordinates. -/
theorem replacementFibreRootGeometricSourceMass_eq_pairMass
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreRootGeometricSourceMass R z =
      replacementFibreRootPairMass R z := by
  classical
  unfold replacementFibreRootGeometricSourceMass replacementFibreRootPairMass
  refine Finset.sum_bij
    (fun n _hn => (canonicalCofactor n, canonicalLargestPrimeFactor n))
    (fun n hn => rootGeometricSource_to_pair_mem hR hn)
    (fun m hm n hn hmn => rootGeometricSource_pair_injective hR hm hn hmn)
    (fun cq hcq => by simpa using rootPair_surjective hR hz hzR cq hcq)
    ?_
  intro n hn
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1 with ⟨hnR, _hnX⟩
  have hn1 : 1 < n := by
    have hn2 : 2 ≤ n := hR.trans hnR
    omega
  rw [canonicalCofactor_mul_largestPrimeFactor hn1]

/-- Prime count in the dilated reciprocal window for one root cofactor.  The
value is represented in `ℂ` so it can be multiplied directly by the signed
Möbius coefficient. -/
def replacementFibreRootPrimeWindowCount (R z c : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc
      (replacementDilatedFibreLower R z c)
      (replacementDilatedFibreUpper R z c),
    if q.Prime ∧ c < q then 1 else 0

private theorem replacementRootPrimeWindow_filter_eq
    {R z c : ℕ} (hc : 1 ≤ c) (hz : 1 ≤ z) :
    (Finset.Icc 2 (squareRootEndpoint R)).filter
        (fun q => q.Prime ∧ c < q ∧
          squareRootEndpoint R / (c * q) = z) =
      (Finset.Icc
        (replacementDilatedFibreLower R z c)
        (replacementDilatedFibreUpper R z c)).filter
          (fun q => q.Prime ∧ c < q) := by
  classical
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨_hqIcc, hprime, hcq, hdiv⟩
    apply Finset.mem_filter.mpr
    exact ⟨(squareRootEndpoint_div_mul_eq_iff_mem_dilatedFibre
      hc hprime.one_le hz).1 hdiv, hprime, hcq⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqWin, hprime, hcq⟩
    have hdiv :=
      (squareRootEndpoint_div_mul_eq_iff_mem_dilatedFibre
        hc hprime.one_le hz).2 hqWin
    have hqUpper := (Finset.mem_Icc.mp hqWin).2
    have hupperX : replacementDilatedFibreUpper R z c ≤ squareRootEndpoint R := by
      unfold replacementDilatedFibreUpper
      exact Nat.div_le_self _ _
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hprime.two_le, hqUpper.trans hupperX⟩,
      hprime, hcq, hdiv⟩

/-- Fubini plus the dilated-window reindex turns the root pair mass into a
signed cofactor-weighted prime-window count. -/
theorem replacementFibreRootPairMass_eq_neg_cofactorPrimeWindows
    (R z : ℕ) (hz : 1 ≤ z) :
    replacementFibreRootPairMass R z =
      -∑ c ∈ Finset.Icc 1 (R - 1),
        canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c := by
  classical
  unfold replacementFibreRootPairMass replacementFibreRootPairSet
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈ (Finset.Icc 1 (R - 1)).product
          (Finset.Icc 2 (squareRootEndpoint R)),
        if cq.2.Prime ∧ cq.1 < cq.2 ∧
            squareRootEndpoint R / (cq.1 * cq.2) = z then
          canonicalMoebiusWeight (cq.1 * cq.2)
        else 0) =
      ∑ c ∈ Finset.Icc 1 (R - 1),
        ∑ q ∈ Finset.Icc 2 (squareRootEndpoint R),
          if q.Prime ∧ c < q ∧ squareRootEndpoint R / (c * q) = z then
            canonicalMoebiusWeight (c * q)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Icc 1 (R - 1))
          (t := Finset.Icc 2 (squareRootEndpoint R))
          (f := fun cq : ℕ × ℕ =>
            if cq.2.Prime ∧ cq.1 < cq.2 ∧
                squareRootEndpoint R / (cq.1 * cq.2) = z then
              canonicalMoebiusWeight (cq.1 * cq.2)
            else 0))
    _ = ∑ c ∈ Finset.Icc 1 (R - 1),
        -(canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c) := by
      apply Finset.sum_congr rfl
      intro c hcMem
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcMem).1
      have hcpos : 0 < c := by omega
      have hset := replacementRootPrimeWindow_filter_eq
        (R := R) (z := z) hc1 hz
      rw [← Finset.sum_filter, hset]
      unfold replacementFibreRootPrimeWindowCount
      rw [← Finset.sum_filter]
      calc
        (∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ c < q),
            canonicalMoebiusWeight (c * q)) =
          ∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ c < q),
            -canonicalMoebiusWeight c := by
              apply Finset.sum_congr rfl
              intro q hq
              rcases (Finset.mem_filter.mp hq).2 with ⟨hprime, hcq⟩
              exact canonicalMoebiusWeight_mul_prime_eq_neg hcpos hcq hprime
        _ = -(canonicalMoebiusWeight c *
            ∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ c < q), (1 : ℂ)) := by
              rw [Finset.mul_sum]
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro q _hq
              ring
    _ = -∑ c ∈ Finset.Icc 1 (R - 1),
        canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c := by
      rw [Finset.sum_neg_distrib]

/-- **Root fibre prime-window dictionary.**  This is the first exact place at
which a prime-distribution estimate could later enter; no estimate is used here. -/
theorem replacementFibreRootMass_eq_neg_cofactorPrimeWindows
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreRootMass R z =
      -∑ c ∈ Finset.Icc 1 (R - 1),
        canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c := by
  rw [replacementFibreRootMass_eq_geometricSourceMass,
    replacementFibreRootGeometricSourceMass_eq_pairMass R z hR hz hzR,
    replacementFibreRootPairMass_eq_neg_cofactorPrimeWindows R z hz]

/-! ## Smooth orientation -/

private theorem replacementPrimeFactor_le_canonicalLargestPrimeFactor
    {n p : ℕ} (hn : 1 < n) (hp : p ∈ n.primeFactors) :
    p ≤ canonicalLargestPrimeFactor n := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hn]
  exact Finset.le_max' n.primeFactors p hp

/-- In a squarefree source, the largest prime of the canonical cofactor is
strictly below the source's canonical largest prime. -/
theorem canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree
    {n : ℕ} (hn : 1 < n) (hsq : Squarefree n) :
    canonicalLargestPrimeFactor (canonicalCofactor n) <
      canonicalLargestPrimeFactor n := by
  have hqPrime := canonicalLargestPrimeFactor_prime hn
  by_cases hc1 : canonicalCofactor n = 1
  · have hp1 : canonicalLargestPrimeFactor (canonicalCofactor n) = 1 := by
      rw [hc1]
      unfold canonicalLargestPrimeFactor
      rw [dif_neg (by omega)]
    rw [hp1]
    exact hqPrime.one_lt
  · have hcpos := CanonicalGapAncestryBridge.canonicalCofactor_pos hn
    have hcgt : 1 < canonicalCofactor n := by omega
    have hpPrime := canonicalLargestPrimeFactor_prime hcgt
    have hpdvdC := canonicalLargestPrimeFactor_dvd hcgt
    have hprod := canonicalCofactor_mul_largestPrimeFactor hn
    have hcdvdN : canonicalCofactor n ∣ n :=
      ⟨canonicalLargestPrimeFactor n, hprod.symm⟩
    have hpdvdN := hpdvdC.trans hcdvdN
    have hpmem :
        canonicalLargestPrimeFactor (canonicalCofactor n) ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpdvdN, by omega⟩
    have hple :
        canonicalLargestPrimeFactor (canonicalCofactor n) ≤
          canonicalLargestPrimeFactor n :=
      replacementPrimeFactor_le_canonicalLargestPrimeFactor hn hpmem
    have hne :
        canonicalLargestPrimeFactor (canonicalCofactor n) ≠
          canonicalLargestPrimeFactor n := by
      intro heq
      apply canonicalLargestPrimeFactor_not_dvd_cofactor hsq hn
      rw [← heq]
      exact hpdvdC
    omega

/-- Geometric smooth population in reciprocal fibre `z`.  The roughness
condition is the canonical-source condition `P+(c) < q`; nonsquarefree sources
may remain in the set because their Möbius weight is zero. -/
def replacementFibreSmoothGeometricSourceSet (R z : ℕ) : Finset ℕ :=
  (Finset.Icc R (squareRootEndpoint R)).filter fun n =>
    squareRootEndpoint R / n = z ∧
      canonicalLargestPrimeFactor (canonicalCofactor n) <
        canonicalLargestPrimeFactor n ∧
      canonicalLargestPrimeFactor n < canonicalCofactor n

/-- Signed Möbius mass of the geometric smooth population. -/
def replacementFibreSmoothGeometricSourceMass (R z : ℕ) : ℂ :=
  ∑ n ∈ replacementFibreSmoothGeometricSourceSet R z,
    canonicalMoebiusWeight n

/-- The strict smooth fibre equals its rough geometric realization. -/
theorem replacementFibreSmoothMass_eq_geometricSourceMass
    (R z : ℕ) (hR : 2 ≤ R) :
    replacementFibreSmoothMass R z =
      replacementFibreSmoothGeometricSourceMass R z := by
  classical
  unfold replacementFibreSmoothMass replacementFibreSmoothGeometricSourceMass
    replacementFibreSmoothGeometricSourceSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hnTail
  by_cases hdiv : squareRootEndpoint R / n = z
  · by_cases horient :
        canonicalLargestPrimeFactor n < canonicalCofactor n
    · have hnR : R ≤ n := (Finset.mem_Icc.mp hnTail).1
      have hn1 : 1 < n := by
        have hn2 : 2 ≤ n := hR.trans hnR
        omega
      by_cases hsq : Squarefree n
      · have hrough :=
          canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hn1 hsq
        simp [hdiv, horient, ReplacementSmoothOriented, hsq, hrough,
          canonicalMoebiusWeight]
      · by_cases hrough :
            canonicalLargestPrimeFactor (canonicalCofactor n) <
              canonicalLargestPrimeFactor n
        · have hzero : (μ n : ℤ) = 0 :=
            ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
          have hweightzero : canonicalMoebiusWeight n = 0 := by
            unfold canonicalMoebiusWeight
            rw [hzero]
            norm_num
          simp [hdiv, horient, ReplacementSmoothOriented, hsq, hrough,
            hweightzero]
        · simp [hdiv, horient, ReplacementSmoothOriented, hsq, hrough]
    · simp [hdiv, horient, ReplacementSmoothOriented]
  · simp [hdiv]

/-- Canonical cofactor-prime coordinates for the geometric smooth population. -/
def replacementFibreSmoothPairSet (R z : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (squareRootEndpoint R)).product
      (Finset.Icc 2 (R - 1))).filter fun cq =>
    cq.2.Prime ∧
      canonicalLargestPrimeFactor cq.1 < cq.2 ∧
      cq.2 < cq.1 ∧
      squareRootEndpoint R / (cq.1 * cq.2) = z

/-- Signed source mass in the cofactor-prime smooth coordinates. -/
def replacementFibreSmoothPairMass (R z : ℕ) : ℂ :=
  ∑ cq ∈ replacementFibreSmoothPairSet R z,
    canonicalMoebiusWeight (cq.1 * cq.2)

private theorem smoothGeometricSource_to_pair_mem
    {R z n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ replacementFibreSmoothGeometricSourceSet R z) :
    (canonicalCofactor n, canonicalLargestPrimeFactor n) ∈
      replacementFibreSmoothPairSet R z := by
  classical
  rcases Finset.mem_filter.mp hn with
    ⟨hnTail, hdiv, hrough, horient⟩
  rcases Finset.mem_Icc.mp hnTail with ⟨hnR, hnX⟩
  have hn2 : 2 ≤ n := hR.trans hnR
  have hn1 : 1 < n := by omega
  have hcpos : 1 ≤ canonicalCofactor n :=
    CanonicalGapAncestryBridge.canonicalCofactor_pos hn1
  have hcdvd : canonicalCofactor n ∣ n :=
    CanonicalGapAncestryBridge.canonicalCofactor_dvd hn1
  have hcle : canonicalCofactor n ≤ n := Nat.le_of_dvd (by omega) hcdvd
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hqR := canonicalLargestPrimeFactor_lt_of_bornOrientation
    hn1 hnX horient.le
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
    hqPrime, hrough, horient, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨hcpos, hcle.trans hnX⟩
  · exact Finset.mem_Icc.mpr ⟨hqPrime.two_le, by omega⟩
  · rw [canonicalCofactor_mul_largestPrimeFactor hn1]
    exact hdiv

private theorem smoothGeometricSource_pair_injective
    {R z m n : ℕ} (hR : 2 ≤ R)
    (hm : m ∈ replacementFibreSmoothGeometricSourceSet R z)
    (hn : n ∈ replacementFibreSmoothGeometricSourceSet R z)
    (hpair :
      (canonicalCofactor m, canonicalLargestPrimeFactor m) =
        (canonicalCofactor n, canonicalLargestPrimeFactor n)) :
    m = n := by
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1 with ⟨hmR, _⟩
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1 with ⟨hnR, _⟩
  have hm1 : 1 < m := by
    have hm2 : 2 ≤ m := hR.trans hmR
    omega
  have hn1 : 1 < n := by
    have hn2 : 2 ≤ n := hR.trans hnR
    omega
  have hmprod := canonicalCofactor_mul_largestPrimeFactor hm1
  have hnprod := canonicalCofactor_mul_largestPrimeFactor hn1
  have hc : canonicalCofactor m = canonicalCofactor n :=
    congrArg Prod.fst hpair
  have hq : canonicalLargestPrimeFactor m = canonicalLargestPrimeFactor n :=
    congrArg Prod.snd hpair
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hmprod.symm
    _ = canonicalCofactor n * canonicalLargestPrimeFactor n := by rw [hc, hq]
    _ = n := hnprod

private theorem smoothPair_surjective
    {R z : ℕ} (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R)
    (cq : ℕ × ℕ) (hcq : cq ∈ replacementFibreSmoothPairSet R z) :
    ∃ n ∈ replacementFibreSmoothGeometricSourceSet R z,
      (canonicalCofactor n, canonicalLargestPrimeFactor n) = cq := by
  classical
  rcases Finset.mem_filter.mp hcq with
    ⟨hbase, hqPrime, hrough, hqc, hdiv⟩
  rcases Finset.mem_product.mp hbase with ⟨hcMem, _hqMem⟩
  have hc1 : 1 ≤ cq.1 := (Finset.mem_Icc.mp hcMem).1
  have hcpos : 0 < cq.1 := by omega
  have hprodpos : 0 < cq.1 * cq.2 :=
    Nat.mul_pos hcpos hqPrime.pos
  have hinterval :=
    (squareRootEndpoint_div_eq_iff_mem_replacementFibre
      (R := R) (n := cq.1 * cq.2) (z := z) hprodpos hz).1 hdiv
  have htailDiv :=
    (replacementTailFibre_mem_iff R z (cq.1 * cq.2) hR hz hzR).2 hinterval
  have htop := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
    hcpos hqPrime hrough
  have hcore := canonicalCofactor_mul_prime_eq_of_rough
    hcpos hqPrime hrough
  refine ⟨cq.1 * cq.2, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨htailDiv.1, htailDiv.2, ?_, ?_⟩
    · rw [htop, hcore]
      exact hrough
    · rw [htop, hcore]
      exact hqc
  · apply Prod.ext
    · exact hcore
    · exact htop

/-- Exact bijective reindex from smooth-oriented integers to their canonical
cofactor-prime coordinates. -/
theorem replacementFibreSmoothGeometricSourceMass_eq_pairMass
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreSmoothGeometricSourceMass R z =
      replacementFibreSmoothPairMass R z := by
  classical
  unfold replacementFibreSmoothGeometricSourceMass replacementFibreSmoothPairMass
  refine Finset.sum_bij
    (fun n _hn => (canonicalCofactor n, canonicalLargestPrimeFactor n))
    (fun n hn => smoothGeometricSource_to_pair_mem hR hn)
    (fun m hm n hn hmn => smoothGeometricSource_pair_injective hR hm hn hmn)
    (fun cq hcq => by simpa using smoothPair_surjective hR hz hzR cq hcq)
    ?_
  intro n hn
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1 with ⟨hnR, _hnX⟩
  have hn1 : 1 < n := by
    have hn2 : 2 ≤ n := hR.trans hnR
    omega
  rw [canonicalCofactor_mul_largestPrimeFactor hn1]

/-- Prime count in the dilated reciprocal window for one smooth cofactor.  The
canonical roughness and strict smooth orientation remain inside the count. -/
def replacementFibreSmoothPrimeWindowCount (R z c : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc
      (replacementDilatedFibreLower R z c)
      (replacementDilatedFibreUpper R z c),
    if q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q < c then 1 else 0

private theorem replacementSmoothPrimeWindow_filter_eq
    {R z c : ℕ} (hR : 2 ≤ R) (hc : 1 ≤ c)
    (hz : 1 ≤ z) (hzR : z < R) :
    (Finset.Icc 2 (R - 1)).filter
        (fun q => q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q < c ∧
          squareRootEndpoint R / (c * q) = z) =
      (Finset.Icc
        (replacementDilatedFibreLower R z c)
        (replacementDilatedFibreUpper R z c)).filter
          (fun q => q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q < c) := by
  classical
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with
      ⟨_hqIcc, hprime, hrough, hqc, hdiv⟩
    apply Finset.mem_filter.mpr
    exact ⟨(squareRootEndpoint_div_mul_eq_iff_mem_dilatedFibre
      hc hprime.one_le hz).1 hdiv, hprime, hrough, hqc⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with
      ⟨hqWin, hprime, hrough, hqc⟩
    have hdiv :=
      (squareRootEndpoint_div_mul_eq_iff_mem_dilatedFibre
        hc hprime.one_le hz).2 hqWin
    have hcpos : 0 < c := by omega
    have hprodpos : 0 < c * q := Nat.mul_pos hcpos hprime.pos
    have hinterval :=
      (squareRootEndpoint_div_eq_iff_mem_replacementFibre
        (R := R) (n := c * q) (z := z) hprodpos hz).1 hdiv
    have htail :=
      (replacementTailFibre_mem_iff R z (c * q) hR hz hzR).2 hinterval
    have hnX := (Finset.mem_Icc.mp htail.1).2
    have htop := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hcpos hprime hrough
    have hcore := canonicalCofactor_mul_prime_eq_of_rough
      hcpos hprime hrough
    have hm1 : 1 < c * q := by
      calc
        1 < q := hprime.one_lt
        _ = 1 * q := (one_mul q).symm
        _ ≤ c * q := Nat.mul_le_mul_right q hc
    have hborn :
        canonicalLargestPrimeFactor (c * q) ≤ canonicalCofactor (c * q) := by
      rw [htop, hcore]
      exact hqc.le
    have hqR := canonicalLargestPrimeFactor_lt_of_bornOrientation
      hm1 hnX hborn
    rw [htop] at hqR
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hprime.two_le, by omega⟩,
      hprime, hrough, hqc, hdiv⟩

/-- Fubini plus the dilated-window reindex turns the smooth pair mass into a
signed cofactor-weighted rough prime-window count. -/
theorem replacementFibreSmoothPairMass_eq_neg_cofactorPrimeWindows
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreSmoothPairMass R z =
      -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          replacementFibreSmoothPrimeWindowCount R z c := by
  classical
  unfold replacementFibreSmoothPairMass replacementFibreSmoothPairSet
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈ (Finset.Icc 1 (squareRootEndpoint R)).product
          (Finset.Icc 2 (R - 1)),
        if cq.2.Prime ∧ canonicalLargestPrimeFactor cq.1 < cq.2 ∧
            cq.2 < cq.1 ∧ squareRootEndpoint R / (cq.1 * cq.2) = z then
          canonicalMoebiusWeight (cq.1 * cq.2)
        else 0) =
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        ∑ q ∈ Finset.Icc 2 (R - 1),
          if q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q < c ∧
              squareRootEndpoint R / (c * q) = z then
            canonicalMoebiusWeight (c * q)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Icc 1 (squareRootEndpoint R))
          (t := Finset.Icc 2 (R - 1))
          (f := fun cq : ℕ × ℕ =>
            if cq.2.Prime ∧ canonicalLargestPrimeFactor cq.1 < cq.2 ∧
                cq.2 < cq.1 ∧ squareRootEndpoint R / (cq.1 * cq.2) = z then
              canonicalMoebiusWeight (cq.1 * cq.2)
            else 0))
    _ = ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        -(canonicalMoebiusWeight c *
          replacementFibreSmoothPrimeWindowCount R z c) := by
      apply Finset.sum_congr rfl
      intro c hcMem
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcMem).1
      have hcpos : 0 < c := by omega
      have hset := replacementSmoothPrimeWindow_filter_eq
        (R := R) (z := z) hR hc1 hz hzR
      rw [← Finset.sum_filter, hset]
      unfold replacementFibreSmoothPrimeWindowCount
      rw [← Finset.sum_filter]
      calc
        (∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q < c),
            canonicalMoebiusWeight (c * q)) =
          ∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q < c),
            -canonicalMoebiusWeight c := by
              apply Finset.sum_congr rfl
              intro q hq
              rcases (Finset.mem_filter.mp hq).2 with ⟨hprime, hrough, _hqc⟩
              exact canonicalMoebiusWeight_mul_prime_eq_neg_of_rough
                hcpos hprime hrough
        _ = -(canonicalMoebiusWeight c *
            ∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q < c),
              (1 : ℂ)) := by
              rw [Finset.mul_sum]
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro q _hq
              ring
    _ = -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          replacementFibreSmoothPrimeWindowCount R z c := by
      rw [Finset.sum_neg_distrib]

/-- **Smooth fibre prime-window dictionary.**  The roughness condition remains
inside the prime count, and no norm or fibrewise absolute value is taken. -/
theorem replacementFibreSmoothMass_eq_neg_cofactorPrimeWindows
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreSmoothMass R z =
      -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          replacementFibreSmoothPrimeWindowCount R z c := by
  rw [replacementFibreSmoothMass_eq_geometricSourceMass R z hR,
    replacementFibreSmoothGeometricSourceMass_eq_pairMass R z hR hz hzR,
    replacementFibreSmoothPairMass_eq_neg_cofactorPrimeWindows R z hR hz hzR]

end RHLean.Proof
