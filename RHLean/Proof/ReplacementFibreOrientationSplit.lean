import Mathlib
import RHLean.Proof.RootSmoothCrossRegionGram
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm

/-!
# Replacement fibre orientation split

This module identifies the surviving reciprocal-fibre Möbius state with the
repository's existing canonical root/smooth orientation.

For `X_R = R^2 - 1` and `1 <= z < R`, the reciprocal fibre is

`I_z = (floor(X_R/(z+1)), floor(X_R/z)]`.

Every squarefree `n > 1` has canonical coordinates

`n = c * q`,  `q = P+(n)`,  `c = n / q`,

and equality `c = q` is impossible. Hence the fibre splits exactly into

* root orientation `c < q`;
* smooth orientation `q < c`.

On the root side, `c < R` is automatic from `n <= R^2 - 1`. Primes are the
special face `c = 1`; they are not a separate arithmetic state.

No norm, energy estimate, first-moment estimate, or new Gram is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Native strict root orientation on an integer source. -/
def ReplacementRootOriented (n : ℕ) : Prop :=
  Squarefree n ∧ canonicalCofactor n < canonicalLargestPrimeFactor n

/-- Native strict smooth orientation on an integer source. -/
def ReplacementSmoothOriented (n : ℕ) : Prop :=
  Squarefree n ∧ canonicalLargestPrimeFactor n < canonicalCofactor n

instance instDecidableReplacementRootOriented (n : ℕ) :
    Decidable (ReplacementRootOriented n) := by
  unfold ReplacementRootOriented
  infer_instance

instance instDecidableReplacementSmoothOriented (n : ℕ) :
    Decidable (ReplacementSmoothOriented n) := by
  unfold ReplacementSmoothOriented
  infer_instance

/-- For a nontrivial squarefree source the two strict canonical orientations
are exhaustive. Equality of the canonical cofactor and largest prime would
force that prime to divide the cofactor, contradicting squarefreeness. -/
theorem replacementOrientation_exhaustive
    {n : ℕ} (hn : 1 < n) (hsq : Squarefree n) :
    ReplacementRootOriented n ∨ ReplacementSmoothOriented n := by
  have hne : canonicalCofactor n ≠ canonicalLargestPrimeFactor n := by
    intro heq
    apply canonicalLargestPrimeFactor_not_dvd_cofactor hsq hn
    rw [heq]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl ⟨hsq, hlt⟩
  · exact Or.inr ⟨hsq, hgt⟩

/-- The two strict orientations are disjoint. -/
theorem replacementOrientation_disjoint
    {n : ℕ} : ¬(ReplacementRootOriented n ∧ ReplacementSmoothOriented n) := by
  rintro ⟨hroot, hsmooth⟩
  exact Nat.lt_asymm hroot.2 hsmooth.2

/-- At the complete square endpoint, every root-oriented squarefree source has
canonical cofactor strictly below the induction scale. -/
theorem replacementRootOriented_cofactor_lt_root
    {R n : ℕ} (hR : 2 ≤ R) (hn2 : 2 ≤ n)
    (hnX : n ≤ squareRootEndpoint R)
    (hroot : ReplacementRootOriented n) :
    canonicalCofactor n < R := by
  have hn : 1 < n := by omega
  have hfactor := canonicalCofactor_mul_largestPrimeFactor hn
  by_contra hnot
  have hRc : R ≤ canonicalCofactor n := Nat.le_of_not_gt hnot
  have hRq : R ≤ canonicalLargestPrimeFactor n :=
    hRc.trans hroot.2.le
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

/-- Public reciprocal-interval form of the elementary floor identity used by
the fibre dictionary. -/
theorem squareRootEndpoint_div_eq_iff_mem_replacementFibre
    {R n z : ℕ} (hn : 1 ≤ n) (hz : 1 ≤ z) :
    squareRootEndpoint R / n = z ↔
      n ∈ Finset.Icc
        (squareRootReplacementFibreLower R z)
        (squareRootReplacementFibreUpper R z) := by
  have hnpos : 0 < n := by omega
  have hzpos : 0 < z := by omega
  have hzp : 0 < z + 1 := by omega
  unfold squareRootReplacementFibreLower squareRootReplacementFibreUpper
  constructor
  · intro hdiv
    have hlt : squareRootEndpoint R / n < z + 1 := by omega
    have hxlt : squareRootEndpoint R < (z + 1) * n :=
      (Nat.div_lt_iff_lt_mul hnpos).1 hlt
    have hlower : squareRootEndpoint R / (z + 1) < n :=
      (Nat.div_lt_iff_lt_mul hzp).2
        (by simpa [Nat.mul_comm] using hxlt)
    have hle : z ≤ squareRootEndpoint R / n := by omega
    have hmul : z * n ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hnpos).1 hle
    have hupper : n ≤ squareRootEndpoint R / z :=
      (Nat.le_div_iff_mul_le hzpos).2
        (by simpa [Nat.mul_comm] using hmul)
    exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩
  · intro hmem
    rcases Finset.mem_Icc.mp hmem with ⟨hlower, hupper⟩
    have hlower' : squareRootEndpoint R / (z + 1) < n := by omega
    have hxlt : squareRootEndpoint R < n * (z + 1) :=
      (Nat.div_lt_iff_lt_mul hzp).1 hlower'
    have hlt : squareRootEndpoint R / n < z + 1 :=
      (Nat.div_lt_iff_lt_mul hnpos).2
        (by simpa [Nat.mul_comm] using hxlt)
    have hmul : n * z ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hzpos).1 hupper
    have hle : z ≤ squareRootEndpoint R / n :=
      (Nat.le_div_iff_mul_le hnpos).2
        (by simpa [Nat.mul_comm] using hmul)
    omega

/-- Root-oriented Möbius mass carried by reciprocal fibre `z`. -/
def replacementFibreRootMass (R z : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    if squareRootEndpoint R / n = z then
      if ReplacementRootOriented n then (((μ n : ℤ) : ℂ)) else 0
    else 0

/-- Smooth-oriented Möbius mass carried by reciprocal fibre `z`. -/
def replacementFibreSmoothMass (R z : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    if squareRootEndpoint R / n = z then
      if ReplacementSmoothOriented n then (((μ n : ℤ) : ℂ)) else 0
    else 0

/-- The root fibre is literally the root-oriented Möbius sum on `I_z`. -/
theorem replacementFibreRootMass_eq_intervalSum
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreRootMass R z =
      ∑ n ∈ Finset.Icc
          (squareRootReplacementFibreLower R z)
          (squareRootReplacementFibreUpper R z),
        if ReplacementRootOriented n then (((μ n : ℤ) : ℂ)) else 0 := by
  classical
  have hset :
      (Finset.Icc R (squareRootEndpoint R)).filter
          (fun n => squareRootEndpoint R / n = z) =
        Finset.Icc
          (squareRootReplacementFibreLower R z)
          (squareRootReplacementFibreUpper R z) := by
    ext n
    simp only [Finset.mem_filter]
    rw [replacementTailFibre_mem_iff R z n hR hz hzR]
  unfold replacementFibreRootMass
  rw [← Finset.sum_filter, hset]

/-- The smooth fibre is literally the smooth-oriented Möbius sum on `I_z`. -/
theorem replacementFibreSmoothMass_eq_intervalSum
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreSmoothMass R z =
      ∑ n ∈ Finset.Icc
          (squareRootReplacementFibreLower R z)
          (squareRootReplacementFibreUpper R z),
        if ReplacementSmoothOriented n then (((μ n : ℤ) : ℂ)) else 0 := by
  classical
  have hset :
      (Finset.Icc R (squareRootEndpoint R)).filter
          (fun n => squareRootEndpoint R / n = z) =
        Finset.Icc
          (squareRootReplacementFibreLower R z)
          (squareRootReplacementFibreUpper R z) := by
    ext n
    simp only [Finset.mem_filter]
    rw [replacementTailFibre_mem_iff R z n hR hz hzR]
  unfold replacementFibreSmoothMass
  rw [← Finset.sum_filter, hset]

/-- **Exact orientation split of the surviving Type-II fibre.** -/
theorem squareRootReplacementTailMoebiusCoefficient_eq_root_add_smooth
    (R z : ℕ) (hR : 2 ≤ R) :
    squareRootReplacementTailMoebiusCoefficient R z =
      replacementFibreRootMass R z + replacementFibreSmoothMass R z := by
  classical
  unfold squareRootReplacementTailMoebiusCoefficient
    replacementFibreRootMass replacementFibreSmoothMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hq : squareRootEndpoint R / n = z
  · simp only [hq, if_true]
    have hnR : R ≤ n := (Finset.mem_Icc.mp hn).1
    have hn2 : 2 ≤ n := hR.trans hnR
    have hn1 : 1 < n := by omega
    by_cases hsq : Squarefree n
    · rcases replacementOrientation_exhaustive hn1 hsq with hroot | hsmooth
      · have hnotSmooth : ¬ ReplacementSmoothOriented n := by
          intro hs
          exact replacementOrientation_disjoint ⟨hroot, hs⟩
        simp [hroot, hnotSmooth]
      · have hnotRoot : ¬ ReplacementRootOriented n := by
          intro hr
          exact replacementOrientation_disjoint ⟨hr, hsmooth⟩
        simp [hnotRoot, hsmooth]
    · have hzero : (μ n : ℤ) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      have hnotRoot : ¬ ReplacementRootOriented n := fun hr => hsq hr.1
      have hnotSmooth : ¬ ReplacementSmoothOriented n := fun hs => hsq hs.1
      simp [hzero, hnotRoot, hnotSmooth]
  · simp [hq]

/-- Direct root-oriented mass on the entire physical tail. -/
def replacementTailRootMass (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    if ReplacementRootOriented n then (((μ n : ℤ) : ℂ)) else 0

/-- Direct smooth-oriented mass on the entire physical tail. -/
def replacementTailSmoothMass (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    if ReplacementSmoothOriented n then (((μ n : ℤ) : ℂ)) else 0

/-- Summing root fibres before any norm recovers the complete root-oriented
tail mass. -/
theorem sum_replacementFibreRootMass_eq_tailRootMass
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ z ∈ Finset.range R, replacementFibreRootMass R z) =
      replacementTailRootMass R := by
  classical
  unfold replacementFibreRootMass replacementTailRootMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnR : R ≤ n := (Finset.mem_Icc.mp hn).1
  have hzlt : squareRootEndpoint R / n < R :=
    squareRootEndpoint_div_lt_root_of_root_le hR hnR
  have hzmem : squareRootEndpoint R / n ∈ Finset.range R :=
    Finset.mem_range.mpr hzlt
  simp [hzmem]

/-- Summing smooth fibres before any norm recovers the complete smooth-oriented
tail mass. -/
theorem sum_replacementFibreSmoothMass_eq_tailSmoothMass
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ z ∈ Finset.range R, replacementFibreSmoothMass R z) =
      replacementTailSmoothMass R := by
  classical
  unfold replacementFibreSmoothMass replacementTailSmoothMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnR : R ≤ n := (Finset.mem_Icc.mp hn).1
  have hzlt : squareRootEndpoint R / n < R :=
    squareRootEndpoint_div_lt_root_of_root_le hR hnR
  have hzmem : squareRootEndpoint R / n ∈ Finset.range R :=
    Finset.mem_range.mpr hzlt
  simp [hzmem]

/-- The high root plus high smooth masses are exactly the ordinary complementary
Mertens tail. This is a partition identity, not an estimate. -/
theorem replacementTailRoot_add_smooth_eq_mertens_sub_pred
    (R : ℕ) (hR : 2 ≤ R) :
    replacementTailRootMass R + replacementTailSmoothMass R =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        RHLean.Analysis.mertensSummatory (R - 1) := by
  calc
    replacementTailRootMass R + replacementTailSmoothMass R =
      (∑ z ∈ Finset.range R, replacementFibreRootMass R z) +
        ∑ z ∈ Finset.range R, replacementFibreSmoothMass R z := by
          rw [sum_replacementFibreRootMass_eq_tailRootMass R hR,
            sum_replacementFibreSmoothMass_eq_tailSmoothMass R hR]
    _ = ∑ z ∈ Finset.range R,
        (replacementFibreRootMass R z + replacementFibreSmoothMass R z) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z := by
          apply Finset.sum_congr rfl
          intro z _hz
          rw [squareRootReplacementTailMoebiusCoefficient_eq_root_add_smooth R z hR]
    _ = RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        RHLean.Analysis.mertensSummatory (R - 1) :=
      squareRootReplacementTailMoebius_sum_eq_complementaryMertensTail R hR

/-- Root-oriented low mass below the physical tail. -/
def replacementLowRootMass (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 (R - 1),
    if ReplacementRootOriented n then (((μ n : ℤ) : ℂ)) else 0

/-- Smooth-oriented low mass below the physical tail. -/
def replacementLowSmoothMass (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 (R - 1),
    if ReplacementSmoothOriented n then (((μ n : ℤ) : ℂ)) else 0

private theorem replacement_orientations_sum_eq_mobius_sum
    (s : Finset ℕ) (h2 : ∀ n ∈ s, 2 ≤ n) :
    (∑ n ∈ s, if ReplacementRootOriented n then (((μ n : ℤ) : ℂ)) else 0) +
      (∑ n ∈ s, if ReplacementSmoothOriented n then (((μ n : ℤ) : ℂ)) else 0) =
        ∑ n ∈ s, (((μ n : ℤ) : ℂ)) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn2 : 2 ≤ n := h2 n hn
  have hn1 : 1 < n := by omega
  by_cases hsq : Squarefree n
  · rcases replacementOrientation_exhaustive hn1 hsq with hroot | hsmooth
    · have hnotSmooth : ¬ ReplacementSmoothOriented n := by
        intro hs
        exact replacementOrientation_disjoint ⟨hroot, hs⟩
      simp [hroot, hnotSmooth]
    · have hnotRoot : ¬ ReplacementRootOriented n := by
        intro hr
        exact replacementOrientation_disjoint ⟨hr, hsmooth⟩
      simp [hnotRoot, hsmooth]
  · have hzero : (μ n : ℤ) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have hnotRoot : ¬ ReplacementRootOriented n := fun hr => hsq hr.1
    have hnotSmooth : ¬ ReplacementSmoothOriented n := fun hs => hsq hs.1
    simp [hzero, hnotRoot, hnotSmooth]

/-- The low orientation split is exactly `M(R-1)-1`. -/
theorem replacementLowRoot_add_smooth_eq_mertens_pred_sub_one
    (R : ℕ) (hR : 2 ≤ R) :
    replacementLowRootMass R + replacementLowSmoothMass R =
      RHLean.Analysis.mertensSummatory (R - 1) - 1 := by
  classical
  have hsplit := replacement_orientations_sum_eq_mobius_sum
    (Finset.Icc 2 (R - 1)) (fun n hn => (Finset.mem_Icc.mp hn).1)
  unfold replacementLowRootMass replacementLowSmoothMass
  rw [hsplit]
  have hset :
      Finset.Icc 1 (R - 1) = insert 1 (Finset.Icc 2 (R - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hM := RHLean.Analysis.mertensSummatory_eq_sum_Icc (R - 1)
  rw [hset] at hM
  have h1not : (1 : ℕ) ∉ Finset.Icc 2 (R - 1) := by simp
  rw [Finset.sum_insert h1not] at hM
  simp at hM
  rw [hM]
  ring

/-- Full root-oriented Möbius population on `2 <= n <= X_R`. -/
def replacementFullRootMass (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 (squareRootEndpoint R),
    if ReplacementRootOriented n then (((μ n : ℤ) : ℂ)) else 0

/-- Full smooth-oriented Möbius population on `2 <= n <= X_R`. -/
def replacementFullSmoothMass (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 (squareRootEndpoint R),
    if ReplacementSmoothOriented n then (((μ n : ℤ) : ℂ)) else 0

/-- The complete orientation split is exactly `M(X_R)-1`. -/
theorem replacementFullRoot_add_smooth_eq_mertens_sub_one
    (R : ℕ) (hR : 2 ≤ R) :
    replacementFullRootMass R + replacementFullSmoothMass R =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 := by
  classical
  have hsplit := replacement_orientations_sum_eq_mobius_sum
    (Finset.Icc 2 (squareRootEndpoint R)) (fun n hn => (Finset.mem_Icc.mp hn).1)
  unfold replacementFullRootMass replacementFullSmoothMass
  rw [hsplit]
  have hX1 : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    omega
  have hset :
      Finset.Icc 1 (squareRootEndpoint R) =
        insert 1 (Finset.Icc 2 (squareRootEndpoint R)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hM := RHLean.Analysis.mertensSummatory_eq_sum_Icc (squareRootEndpoint R)
  rw [hset] at hM
  have h1not : (1 : ℕ) ∉ Finset.Icc 2 (squareRootEndpoint R) := by simp
  rw [Finset.sum_insert h1not] at hM
  simp at hM
  rw [hM]
  ring

private theorem replacement_full_eq_low_add_tail
    (R : ℕ) (hR : 2 ≤ R)
    (orient : ℕ → Prop) [DecidablePred orient] :
    (∑ n ∈ Finset.Icc 2 (squareRootEndpoint R),
        if orient n then (((μ n : ℤ) : ℂ)) else 0) =
      (∑ n ∈ Finset.Icc 2 (R - 1),
        if orient n then (((μ n : ℤ) : ℂ)) else 0) +
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        if orient n then (((μ n : ℤ) : ℂ)) else 0 := by
  classical
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    exact Nat.le_sub_of_add_le hsq
  have hset :
      Finset.Icc 2 (squareRootEndpoint R) =
        Finset.Icc 2 (R - 1) ∪ Finset.Icc R (squareRootEndpoint R) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj :
      Disjoint (Finset.Icc 2 (R - 1))
        (Finset.Icc R (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo hnhi
    omega
  rw [hset, Finset.sum_union hdisj]

/-- Full root orientation is low root plus the complete root fibre vector. -/
theorem replacementFullRootMass_eq_low_add_fibres
    (R : ℕ) (hR : 2 ≤ R) :
    replacementFullRootMass R =
      replacementLowRootMass R +
        ∑ z ∈ Finset.range R, replacementFibreRootMass R z := by
  calc
    replacementFullRootMass R =
        replacementLowRootMass R + replacementTailRootMass R := by
      unfold replacementFullRootMass replacementLowRootMass replacementTailRootMass
      exact replacement_full_eq_low_add_tail R hR ReplacementRootOriented
    _ = replacementLowRootMass R +
        ∑ z ∈ Finset.range R, replacementFibreRootMass R z := by
      rw [sum_replacementFibreRootMass_eq_tailRootMass R hR]

/-- Full smooth orientation is low smooth plus the complete smooth fibre vector. -/
theorem replacementFullSmoothMass_eq_low_add_fibres
    (R : ℕ) (hR : 2 ≤ R) :
    replacementFullSmoothMass R =
      replacementLowSmoothMass R +
        ∑ z ∈ Finset.range R, replacementFibreSmoothMass R z := by
  calc
    replacementFullSmoothMass R =
        replacementLowSmoothMass R + replacementTailSmoothMass R := by
      unfold replacementFullSmoothMass replacementLowSmoothMass replacementTailSmoothMass
      exact replacement_full_eq_low_add_tail R hR ReplacementSmoothOriented
    _ = replacementLowSmoothMass R +
        ∑ z ∈ Finset.range R, replacementFibreSmoothMass R z := by
      rw [sum_replacementFibreSmoothMass_eq_tailSmoothMass R hR]

/-- The repository's complete smooth ancestry mass is exactly the full strict
smooth orientation on integers. -/
theorem ancestrySmoothMass_cast_eq_replacementFullSmoothMass
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootAncestrySmoothMassInt R : ℤ) : ℂ) =
      replacementFullSmoothMass R := by
  classical
  have hset :
      squareRootAncestrySmoothIntegerSet R =
        (Finset.Icc 2 (squareRootEndpoint R)).filter
          ReplacementSmoothOriented := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnRange, hn2, hsq, horient⟩
      have hnlt : n < R ^ 2 := by
        simpa [cumulativeSquarePrefixSet,
          Nat.sub_add_cancel (by omega : 1 ≤ R)] using hnRange
      have hnX : n ≤ squareRootEndpoint R := by
        unfold squareRootEndpoint
        omega
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hn2, hnX⟩, ⟨hsq, horient⟩⟩
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnIcc, hsmooth⟩
      rcases Finset.mem_Icc.mp hnIcc with ⟨hn2, hnX⟩
      rcases hsmooth with ⟨hsq, horient⟩
      have hnlt : n < R ^ 2 := by
        unfold squareRootEndpoint at hnX
        have hsqpos : 0 < R ^ 2 := by positivity
        omega
      apply Finset.mem_filter.mpr
      refine ⟨?_, hn2, hsq, horient⟩
      simpa [cumulativeSquarePrefixSet,
        Nat.sub_add_cancel (by omega : 1 ≤ R)] using hnlt
  unfold squareRootAncestrySmoothMassInt replacementFullSmoothMass
  push_cast
  rw [hset, Finset.sum_filter]

/-- Existing root plus smooth ancestry equals the integer Mertens endpoint. -/
private theorem ancestryRoot_add_smooth_eq_mertensInt_sub_one
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootAncestryRootPrimeMass R + squareRootAncestrySmoothMassInt R =
      mertensSummatoryInt (squareRootEndpoint R) - 1 := by
  have hreal := squareRootPrimeSmoothState_eq_mertensInt_sub_one R hR
  unfold squareRootPrimeRootReal squareRootSmoothMassReal at hreal
  exact_mod_cast hreal

/-- The repository's complete root coordinate is exactly the full strict root
orientation. -/
theorem ancestryRootMass_cast_eq_replacementFullRootMass
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootAncestryRootPrimeMass R : ℤ) : ℂ) =
      replacementFullRootMass R := by
  have htotalInt := ancestryRoot_add_smooth_eq_mertensInt_sub_one R hR
  have htotal := congrArg (fun z : ℤ => (z : ℂ)) htotalInt
  push_cast at htotal
  rw [mertensSummatoryInt_cast] at htotal
  have hsmooth := ancestrySmoothMass_cast_eq_replacementFullSmoothMass R hR
  have hfull := replacementFullRoot_add_smooth_eq_mertens_sub_one R hR
  calc
    ((squareRootAncestryRootPrimeMass R : ℤ) : ℂ) =
        (RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1) -
          ((squareRootAncestrySmoothMassInt R : ℤ) : ℂ) := by
            rw [← htotal]
            ring
    _ = (RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1) -
          replacementFullSmoothMass R := by rw [hsmooth]
    _ = replacementFullRootMass R := by
      rw [← hfull]
      ring

/-- **High/low reconstruction of the existing root state.** -/
theorem ancestryRootMass_cast_eq_low_add_fibres
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootAncestryRootPrimeMass R : ℤ) : ℂ) =
      replacementLowRootMass R +
        ∑ z ∈ Finset.range R, replacementFibreRootMass R z := by
  rw [ancestryRootMass_cast_eq_replacementFullRootMass R hR,
    replacementFullRootMass_eq_low_add_fibres R hR]

/-- **High/low reconstruction of the existing smooth state.** -/
theorem ancestrySmoothMass_cast_eq_low_add_fibres
    (R : ℕ) (hR : 2 ≤ R) :
    ((squareRootAncestrySmoothMassInt R : ℤ) : ℂ) =
      replacementLowSmoothMass R +
        ∑ z ∈ Finset.range R, replacementFibreSmoothMass R z := by
  rw [ancestrySmoothMass_cast_eq_replacementFullSmoothMass R hR,
    replacementFullSmoothMass_eq_low_add_fibres R hR]

/-! ## Cofactor-one face and dilated prime windows -/

/-- A prime source has canonical cofactor one and is therefore root-oriented. -/
theorem prime_replacementRootOriented {q : ℕ} (hq : q.Prime) :
    ReplacementRootOriented q := by
  have htop : canonicalLargestPrimeFactor q = q := by
    simpa using canonicalLargestPrimeFactor_mul_prime_eq
      (c := 1) (q := q) (by decide) hq.one_lt hq
  have hcore : canonicalCofactor q = 1 := by
    simpa using canonicalCofactor_mul_prime_eq
      (c := 1) (q := q) (by decide) hq.one_lt hq
  refine ⟨hq.squarefree, ?_⟩
  rw [htop, hcore]
  exact hq.one_lt

/-- Prime face of reciprocal fibre `z`. -/
def replacementFibrePrimeFaceMass (R z : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc R (squareRootEndpoint R),
    if squareRootEndpoint R / q = z ∧ q.Prime then
      (((μ q : ℤ) : ℂ))
    else 0

/-- Prime count on the literal reciprocal interval, represented in `ℂ`. -/
def replacementFibrePrimeCount (R z : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc
      (squareRootReplacementFibreLower R z)
      (squareRootReplacementFibreUpper R z),
    if q.Prime then 1 else 0

/-- The cofactor-one face is minus the prime count on `I_z`. -/
theorem replacementFibrePrimeFaceMass_eq_neg_primeCount
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibrePrimeFaceMass R z =
      -replacementFibrePrimeCount R z := by
  classical
  have hset :
      (Finset.Icc R (squareRootEndpoint R)).filter
          (fun q => squareRootEndpoint R / q = z) =
        Finset.Icc
          (squareRootReplacementFibreLower R z)
          (squareRootReplacementFibreUpper R z) := by
    ext q
    simp only [Finset.mem_filter]
    rw [replacementTailFibre_mem_iff R z q hR hz hzR]
  unfold replacementFibrePrimeFaceMass replacementFibrePrimeCount
  calc
    (∑ q ∈ Finset.Icc R (squareRootEndpoint R),
        if squareRootEndpoint R / q = z ∧ q.Prime then
          (((μ q : ℤ) : ℂ)) else 0) =
      ∑ q ∈ (Finset.Icc R (squareRootEndpoint R)).filter
          (fun q => squareRootEndpoint R / q = z),
        if q.Prime then (((μ q : ℤ) : ℂ)) else 0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro q _hq
          by_cases hdiv : squareRootEndpoint R / q = z <;>
            by_cases hprime : q.Prime <;> simp [hdiv, hprime]
    _ = ∑ q ∈ Finset.Icc
          (squareRootReplacementFibreLower R z)
          (squareRootReplacementFibreUpper R z),
        if q.Prime then (((μ q : ℤ) : ℂ)) else 0 := by rw [hset]
    _ = -∑ q ∈ Finset.Icc
          (squareRootReplacementFibreLower R z)
          (squareRootReplacementFibreUpper R z),
        if q.Prime then 1 else 0 := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro q _hq
          by_cases hprime : q.Prime
          · rw [if_pos hprime, if_pos hprime,
              ArithmeticFunction.moebius_apply_prime hprime]
            norm_num
          · simp [hprime]

/-- Left endpoint of the prime window obtained after fixing a positive
cofactor `c`. -/
def replacementDilatedFibreLower (R z c : ℕ) : ℕ :=
  squareRootEndpoint R / ((z + 1) * c) + 1

/-- Right endpoint of the prime window obtained after fixing a positive
cofactor `c`. -/
def replacementDilatedFibreUpper (R z c : ℕ) : ℕ :=
  squareRootEndpoint R / (z * c)

/-- **Dilated-window reindex.** For positive `c,z`, the atom `(c,q)` lands in
reciprocal fibre `z` exactly when the prime coordinate lies in `I_z^(c)`. -/
theorem squareRootEndpoint_div_mul_eq_iff_mem_dilatedFibre
    {R z c q : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    squareRootEndpoint R / (c * q) = z ↔
      q ∈ Finset.Icc
        (replacementDilatedFibreLower R z c)
        (replacementDilatedFibreUpper R z c) := by
  have hcpos : 0 < c := by omega
  have hqpos : 0 < q := by omega
  have hprodpos : 0 < c * q := Nat.mul_pos hcpos hqpos
  unfold replacementDilatedFibreLower replacementDilatedFibreUpper
  constructor
  · intro hdiv
    have hbase :=
      (squareRootEndpoint_div_eq_iff_mem_replacementFibre
        (R := R) (n := c * q) (z := z) hprodpos hz).1 hdiv
    rcases Finset.mem_Icc.mp hbase with ⟨hlowerProd, hupperProd⟩
    have hlower0 : squareRootEndpoint R / (z + 1) < c * q := by
      unfold squareRootReplacementFibreLower at hlowerProd
      omega
    have hlower : squareRootEndpoint R / ((z + 1) * c) < q := by
      rw [← Nat.div_div_eq_div_mul]
      apply (Nat.div_lt_iff_lt_mul hcpos).2
      simpa [Nat.mul_comm] using hlower0
    have hupper0 : c * q ≤ squareRootEndpoint R / z := by
      simpa [squareRootReplacementFibreUpper] using hupperProd
    have hupper : q ≤ squareRootEndpoint R / (z * c) := by
      rw [← Nat.div_div_eq_div_mul]
      apply (Nat.le_div_iff_mul_le hcpos).2
      simpa [Nat.mul_comm] using hupper0
    exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩
  · intro hmem
    rcases Finset.mem_Icc.mp hmem with ⟨hlower, hupper⟩
    have hlower' : squareRootEndpoint R / ((z + 1) * c) < q := by omega
    rw [← Nat.div_div_eq_div_mul] at hlower'
    have hlower0 : squareRootEndpoint R / (z + 1) < q * c :=
      (Nat.div_lt_iff_lt_mul hcpos).1 hlower'
    have hupper' : q ≤ squareRootEndpoint R / (z * c) := hupper
    rw [← Nat.div_div_eq_div_mul] at hupper'
    have hupper0 : q * c ≤ squareRootEndpoint R / z :=
      (Nat.le_div_iff_mul_le hcpos).1 hupper'
    apply (squareRootEndpoint_div_eq_iff_mem_replacementFibre
      (R := R) (n := c * q) (z := z) hprodpos hz).2
    apply Finset.mem_Icc.mpr
    constructor
    · unfold squareRootReplacementFibreLower
      have h : squareRootEndpoint R / (z + 1) < c * q := by
        simpa [Nat.mul_comm] using hlower0
      omega
    · unfold squareRootReplacementFibreUpper
      simpa [Nat.mul_comm] using hupper0

/-- A nonempty dilated window forces the elementary endpoint-scale cofactor
constraint. This is geometry of the incidence, not an estimate. -/
theorem replacementDilatedFibre_nonempty_imp_cofactor_mul_z_le_endpoint
    {R z c : ℕ} (hz : 1 ≤ z) (hc : 1 ≤ c)
    (hmem : ∃ q, q ∈ Finset.Icc
      (replacementDilatedFibreLower R z c)
      (replacementDilatedFibreUpper R z c)) :
    z * c ≤ squareRootEndpoint R := by
  rcases hmem with ⟨q, hq⟩
  have hlower := (Finset.mem_Icc.mp hq).1
  have hupper := (Finset.mem_Icc.mp hq).2
  have hLowerPos : 1 ≤ replacementDilatedFibreLower R z c := by
    unfold replacementDilatedFibreLower
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hq1 : 1 ≤ q := hLowerPos.trans hlower
  unfold replacementDilatedFibreUpper at hupper
  have hdiv1 : 1 ≤ squareRootEndpoint R / (z * c) := hq1.trans hupper
  have hzcpos : 0 < z * c := Nat.mul_pos (by omega) (by omega)
  exact (Nat.one_le_div_iff hzcpos).1 hdiv1

end RHLean.Proof
