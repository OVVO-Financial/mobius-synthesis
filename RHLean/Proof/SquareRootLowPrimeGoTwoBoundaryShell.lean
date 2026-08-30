import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoBirthBoundary
import RHLean.Proof.LowWheelSequentialGeometricSavings
import RHLean.Proof.LowWheelSequentialSmoothRoughBoundary

/-!
# The recursive Go stopping set is a genuine two-boundary shell

After stripping the unique smaller owner `r`, the fixed outer owner `q` leaves
its first roughness/birth boundary on the parent coordinate

`(q-1)/r < d <= q-1`,  with `P+(d) < r`.

At the square-dilated Go cutoff there is one further, independent condition:

`d <= (X/q^2)/r`.

Thus the actual terminal parent set is the full roughness first-failure shell
cut by the physical second-contact wall.  Its complement inside the full shell
satisfies

`(X/q^2)/r < d`.

Writing `n = r*d`, and assuming the owner is genuinely unfinished
`q^3 <= X`, the full birth shell gives `q <= n < q^2`, hence `q*n <= X`.
The complementary physical inequality gives `X < q^2*n`.  Therefore the
complement is *exactly supported on the repository's second-contact endpoint
shell*

`q*n <= X < q^2*n`.

This is the literal product-boundary + roughness-boundary interaction requested
by the Go/Othello reduction.  No norm or estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The complete roughness/birth shell for the descent `d -> r*d` across the
fixed outer threshold `q`. -/
def squareRootLowPrimeGoFullBirthBoundaryParents
    (q r : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSmoothCofactors r (q - 1)).filter fun d =>
    (q - 1) / r < d

@[simp] theorem mem_squareRootLowPrimeGoFullBirthBoundaryParents
    {q r d : ℕ} :
    d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r ↔
      1 ≤ d ∧ d ≤ q - 1 ∧ Squarefree d ∧
        canonicalLargestPrimeFactor d < r ∧ (q - 1) / r < d := by
  simp [squareRootLowPrimeGoFullBirthBoundaryParents,
    mem_squareRootLowPrimeGoSmoothCofactors, and_assoc]

/-- The part of the full roughness shell lying beyond the square-dilated
physical cutoff.  This is the second-boundary defect. -/
def squareRootLowPrimeGoSecondBoundaryDefectParents
    (q X r : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoFullBirthBoundaryParents q r).filter fun d =>
    X / (q * q) / r < d

@[simp] theorem mem_squareRootLowPrimeGoSecondBoundaryDefectParents
    {q X r d : ℕ} :
    d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r ↔
      d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r ∧
        X / (q * q) / r < d := by
  simp [squareRootLowPrimeGoSecondBoundaryDefectParents]

/-- **Literal two-boundary intersection.**  The terminal recursive Go parents
are exactly the full roughness/birth boundary filtered by the independent
square-dilated physical cutoff. -/
theorem squareRootLowPrimeGoBirthBoundaryParents_eq_full_filter_physical
    (q X r : ℕ) :
    squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
        (X / (q * q)) r =
      (squareRootLowPrimeGoFullBirthBoundaryParents q r).filter fun d =>
        d ≤ X / (q * q) / r := by
  ext d
  simp only [mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents,
    mem_squareRootLowPrimeGoSmallerOwnerParentStrip,
    mem_squareRootLowPrimeGoSmoothCofactors,
    Finset.mem_filter,
    mem_squareRootLowPrimeGoFullBirthBoundaryParents]
  constructor
  · rintro ⟨⟨⟨hd1, hdX, hsq, hrough⟩, hlower⟩, hdq⟩
    exact ⟨⟨hd1, by omega, hsq, hrough, hlower⟩, hdX⟩
  · rintro ⟨⟨hd1, hdq, hsq, hrough, hlower⟩, hdX⟩
    exact ⟨⟨⟨hd1, hdX, hsq, hrough⟩, hlower⟩, by omega⟩

/-- The full roughness shell is the disjoint union of the physically retained
terminal parents and the second-boundary defect. -/
theorem squareRootLowPrimeGoFullBirthBoundaryParents_eq_terminal_union_defect
    (q X r : ℕ) :
    squareRootLowPrimeGoFullBirthBoundaryParents q r =
      squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
          (X / (q * q)) r ∪
        squareRootLowPrimeGoSecondBoundaryDefectParents q X r := by
  rw [squareRootLowPrimeGoBirthBoundaryParents_eq_full_filter_physical]
  ext d
  simp only [Finset.mem_union, Finset.mem_filter,
    mem_squareRootLowPrimeGoSecondBoundaryDefectParents]
  by_cases hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r
  · by_cases hcut : d ≤ X / (q * q) / r
    · simp [hd, hcut, Nat.not_lt_of_ge hcut]
    · have hlt : X / (q * q) / r < d := Nat.lt_of_not_ge hcut
      simp [hd, hcut, hlt]
  · simp [hd]

/-- The terminal and defect parts of the full roughness shell are disjoint. -/
theorem squareRootLowPrimeGoTerminalParents_disjoint_secondBoundaryDefect
    (q X r : ℕ) :
    Disjoint
      (squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
        (X / (q * q)) r)
      (squareRootLowPrimeGoSecondBoundaryDefectParents q X r) := by
  rw [squareRootLowPrimeGoBirthBoundaryParents_eq_full_filter_physical,
    Finset.disjoint_left]
  intro d hterminal hdefect
  have hle := (Finset.mem_filter.mp hterminal).2
  have hlt :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hdefect).2
  omega

/-- Signed mass identity attached to the exact two-boundary partition. -/
theorem squareRootLowPrimeGoFullBirthBoundary_moebiusSum_eq_terminal_add_defect
    (q X r : ℕ) :
    (∑ d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r, μ d) =
      (∑ d ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
          (X / (q * q)) r, μ d) +
        ∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r, μ d := by
  rw [squareRootLowPrimeGoFullBirthBoundaryParents_eq_terminal_union_defect,
    Finset.sum_union
      (squareRootLowPrimeGoTerminalParents_disjoint_secondBoundaryDefect q X r)]

/-! ## The full birth shell is the native prime-product first-failure frontier -/

/-- Face form of the complete `r`-birth boundary at threshold `q-1`. -/
def squareRootLowPrimeGoFullBirthBoundaryFaces
    (q r : ℕ) : Finset (Finset ℕ) :=
  primeProductFirstFailureBoundary (primesUpTo r) (q - 1) r

/-- At a prime pivot `r`, the generic first-failure frontier is exactly the
predecessor-face shell `(q-1)/r < P(u) <= q-1`. -/
theorem squareRootLowPrimeGoFullBirthBoundaryFaces_eq_filter
    {q r : ℕ} (hr : r.Prime) :
    squareRootLowPrimeGoFullBirthBoundaryFaces q r =
      (primesUpTo (r - 1)).powerset.filter fun u =>
        (q - 1) / r < primeFaceProduct u ∧
          primeFaceProduct u ≤ q - 1 := by
  have hset : primesUpTo r = insert r (primesUpTo (r - 1)) :=
    primesUpTo_eq_insert_pred_of_prime hr
  have hnot : r ∉ primesUpTo (r - 1) :=
    freshPrime_not_mem_primesUpTo_pred hr
  have herase : (primesUpTo r).erase r = primesUpTo (r - 1) := by
    rw [hset]
    simp [hnot]
  ext u
  rw [squareRootLowPrimeGoFullBirthBoundaryFaces,
    mem_primeProductFirstFailureBoundary, herase]
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hu, hupper, hlower⟩
    have hlower' : q - 1 < primeFaceProduct u * r := by
      simpa [Nat.mul_comm] using hlower
    exact ⟨hu, (Nat.div_lt_iff_lt_mul hr.pos).2 hlower', hupper⟩
  · rintro ⟨hu, hlower, hupper⟩
    have hlower' : q - 1 < primeFaceProduct u * r :=
      (Nat.div_lt_iff_lt_mul hr.pos).1 hlower
    exact ⟨hu, hupper, by simpa [Nat.mul_comm] using hlower'⟩

/-- The native low-wheel smooth shell is precisely this one first-failure face
population when the pivot itself is used as the fresh coordinate. -/
theorem lowWheelSmoothFaceShellMass_eq_goFullBirthBoundaryFaceMass
    {q r : ℕ} (hr : r.Prime) :
    lowWheelSmoothFaceShellMass r (q - 1) =
      ∑ u ∈ squareRootLowPrimeGoFullBirthBoundaryFaces q r,
        booleanCubeSign u := by
  rw [squareRootLowPrimeGoFullBirthBoundaryFaces_eq_filter hr]
  unfold lowWheelSmoothFaceShellMass
  rw [Finset.sum_filter]

/-- Arithmetic products represented by the full first-failure face shell. -/
def squareRootLowPrimeGoFullBirthBoundaryCofactors
    (q r : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoFullBirthBoundaryFaces q r).image primeFaceProduct

/-- The face frontier and the squarefree rough-parent frontier are literally the
same arithmetic population. -/
theorem squareRootLowPrimeGoFullBirthBoundaryCofactors_eq_parents
    {q r : ℕ} (hr : r.Prime) :
    squareRootLowPrimeGoFullBirthBoundaryCofactors q r =
      squareRootLowPrimeGoFullBirthBoundaryParents q r := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨u, hu, rfl⟩
    have huFilter :
        u ∈ (primesUpTo (r - 1)).powerset.filter fun t =>
          (q - 1) / r < primeFaceProduct t ∧
            primeFaceProduct t ≤ q - 1 := by
      rw [← squareRootLowPrimeGoFullBirthBoundaryFaces_eq_filter hr]
      exact hu
    rcases Finset.mem_filter.mp huFilter with ⟨huPow, hlower, hupper⟩
    have hprime : ∀ p ∈ u, p.Prime := by
      intro p hp
      have hpOld := (Finset.mem_powerset.mp huPow) hp
      exact prime_of_mem_primesUpTo hpOld
    have hmuEq := moebius_primeFaceProduct_eq_booleanCubeSign u hprime
    have hmuNe : μ (primeFaceProduct u) ≠ 0 := by
      rw [hmuEq]
      unfold booleanCubeSign
      exact pow_ne_zero _ (by norm_num)
    have hsq : Squarefree (primeFaceProduct u) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    have hrough :=
      canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hr huPow
    have hpos := primeFaceProduct_pos_of_mem_powerset huPow
    exact mem_squareRootLowPrimeGoFullBirthBoundaryParents.mpr
      ⟨by omega, hupper, hsq, hrough, hlower⟩
  · intro hd
    rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd with
      ⟨hd1, hdupper, hsq, hrough, hdlower⟩
    let u := squarefreePrimeFace d
    have hprod : primeFaceProduct u = d := by
      simpa [u] using primeFaceProduct_squarefreePrimeFace hsq
    have huSub : u ⊆ primesUpTo (r - 1) := by
      intro p hp
      have hpData : p ∈ d.primeFactors := by
        simpa [u, squarefreePrimeFace] using hp
      have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hpData).1
      have hpDvd : p ∣ d := (Nat.mem_primeFactors.mp hpData).2.1
      have hdPos : 0 < d := by omega
      have hpLeD : p ≤ d := Nat.le_of_dvd hdPos hpDvd
      have hdGt : 1 < d := lt_of_lt_of_le hpPrime.one_lt hpLeD
      have hpLeLpf : p ≤ canonicalLargestPrimeFactor d := by
        unfold canonicalLargestPrimeFactor
        rw [dif_pos hdGt]
        exact Finset.le_max' d.primeFactors p hpData
      exact mem_primesUpTo.mpr ⟨hpPrime, by omega⟩
    have huFilter :
        u ∈ (primesUpTo (r - 1)).powerset.filter fun t =>
          (q - 1) / r < primeFaceProduct t ∧
            primeFaceProduct t ≤ q - 1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr huSub,
        by simpa [hprod] using hdlower,
        by simpa [hprod] using hdupper⟩
    have huFace : u ∈ squareRootLowPrimeGoFullBirthBoundaryFaces q r := by
      rw [squareRootLowPrimeGoFullBirthBoundaryFaces_eq_filter hr]
      exact huFilter
    unfold squareRootLowPrimeGoFullBirthBoundaryCofactors
    exact Finset.mem_image.mpr ⟨u, huFace, hprod⟩

/-- Hence the complete roughness/birth shell has exactly the existing low-wheel
smooth-shell Möbius mass. -/
theorem squareRootLowPrimeGoFullBirthBoundary_moebiusSum_eq_lowWheelSmoothFaceShellMass
    {q r : ℕ} (hr : r.Prime) :
    (∑ d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r, μ d) =
      lowWheelSmoothFaceShellMass r (q - 1) := by
  rw [← squareRootLowPrimeGoFullBirthBoundaryCofactors_eq_parents hr]
  unfold squareRootLowPrimeGoFullBirthBoundaryCofactors
  rw [Finset.sum_image]
  · rw [lowWheelSmoothFaceShellMass_eq_goFullBirthBoundaryFaceMass hr]
    apply Finset.sum_congr rfl
    intro u hu
    apply moebius_primeFaceProduct_eq_booleanCubeSign
    intro p hp
    have huOld : u ∈ (primesUpTo (r - 1)).powerset := by
      have huFilter :
          u ∈ (primesUpTo (r - 1)).powerset.filter fun t =>
            (q - 1) / r < primeFaceProduct t ∧
              primeFaceProduct t ≤ q - 1 := by
        rw [← squareRootLowPrimeGoFullBirthBoundaryFaces_eq_filter hr]
        exact hu
      exact (Finset.mem_filter.mp huFilter).1
    exact prime_of_mem_primesUpTo ((Finset.mem_powerset.mp huOld) hp)
  · intro u hu v hv huv
    have huOld : u ∈ (primesUpTo (r - 1)).powerset := by
      have huFilter :
          u ∈ (primesUpTo (r - 1)).powerset.filter fun t =>
            (q - 1) / r < primeFaceProduct t ∧
              primeFaceProduct t ≤ q - 1 := by
        rw [← squareRootLowPrimeGoFullBirthBoundaryFaces_eq_filter hr]
        exact hu
      exact (Finset.mem_filter.mp huFilter).1
    have hvOld : v ∈ (primesUpTo (r - 1)).powerset := by
      have hvFilter :
          v ∈ (primesUpTo (r - 1)).powerset.filter fun t =>
            (q - 1) / r < primeFaceProduct t ∧
              primeFaceProduct t ≤ q - 1 := by
        rw [← squareRootLowPrimeGoFullBirthBoundaryFaces_eq_filter hr]
        exact hv
      exact (Finset.mem_filter.mp hvFilter).1
    exact (primeFaceProduct_eq_iff
      (fun p hp => prime_of_mem_primesUpTo ((Finset.mem_powerset.mp huOld) hp))
      (fun p hp => prime_of_mem_primesUpTo ((Finset.mem_powerset.mp hvOld) hp))).mp huv

/-! ## The physical complement is exactly the second-contact endpoint shell -/

/-- Every full birth-boundary parent reconstructs a child `n=r*d` at or above
the fixed outer owner `q`. -/
theorem squareRootLowPrimeGoFullBirthBoundary_outer_le_child
    {q r d : ℕ} (hr : r.Prime)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    q ≤ r * d := by
  have hlower :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).2.2.2.2
  have hlt : q - 1 < d * r :=
    (Nat.div_lt_iff_lt_mul hr.pos).1 hlower
  simpa [Nat.mul_comm] using (show q ≤ d * r by omega)

/-- With `r<q`, every full birth-boundary child lies strictly below `q^2`. -/
theorem squareRootLowPrimeGoFullBirthBoundary_child_lt_ownerSquare
    {q r d : ℕ} (hq : q.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    r * d < q * q := by
  have hdupper :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).2.1
  have hdq : d < q := by omega
  have hdPos : 0 < d := by
    have hd1 :=
      (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).1
    omega
  calc
    r * d < q * d := Nat.mul_lt_mul_of_pos_right hrq hdPos
    _ < q * q := Nat.mul_lt_mul_of_pos_left hdq hq.pos

/-- In the unfinished region `q^3 <= X`, the first contact `q*(r*d)` of every
full birth-boundary child is automatically still inside the physical wall. -/
theorem squareRootLowPrimeGoFullBirthBoundary_firstContact_le
    {q X r d : ℕ} (hq : q.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    q * (r * d) ≤ X := by
  have hlt :=
    squareRootLowPrimeGoFullBirthBoundary_child_lt_ownerSquare hq hrq hd
  have hqpos := hq.pos
  have hfirstLt : q * (r * d) < q ^ 3 := by
    calc
      q * (r * d) < q * (q * q) := Nat.mul_lt_mul_of_pos_left hlt hqpos
      _ = q ^ 3 := by ring
  exact hfirstLt.le.trans hcube

/-- The complementary physical inequality is exactly failure at the second
contact `q^2*(r*d)`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    X < q * q * (r * d) := by
  have hdefect :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).2
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hqr : X / (q * q) < d * r :=
    (Nat.div_lt_iff_lt_mul hr.pos).1 hdefect
  have hX : X < (d * r) * (q * q) :=
    (Nat.div_lt_iff_lt_mul hq2Pos).1 hqr
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hX

/-- **The second-boundary defect is exactly a second-contact endpoint shell.**
No triangle inequality is involved: every defect atom has endpoint crossing
indicator `1`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_endpointCrossing_eq_one
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) :
    lowWheelEndpointCrossingDifference q X (r * d) = 1 := by
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hfirst :=
    squareRootLowPrimeGoFullBirthBoundary_firstContact_le hq hrq hcube hfull
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  rw [lowWheelEndpointCrossingDifference_eq_primeShell hq.one_le]
  simp [hfirst, hsecond]

/-- The physically retained terminal part has no second-contact crossing: its
second contact is still inside `X`. -/
theorem squareRootLowPrimeGoTerminalParent_endpointCrossing_eq_zero
    {q X r d : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hd : d ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents q
      (X / (q * q)) r) :
    lowWheelEndpointCrossingDifference q X (r * d) = 0 := by
  have hdStrip :=
    (mem_squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents.mp hd).1
  have hdSmooth :=
    (mem_squareRootLowPrimeGoSmallerOwnerParentStrip.mp hdStrip).1
  have hdCut := (mem_squareRootLowPrimeGoSmoothCofactors.mp hdSmooth).2.1
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hsecondLe0 : d * r ≤ X / (q * q) :=
    (Nat.le_div_iff_mul_le hr.pos).1 hdCut
  have hsecondLe : q * q * (r * d) ≤ X := by
    have h := (Nat.le_div_iff_mul_le hq2Pos).1 hsecondLe0
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  rw [lowWheelEndpointCrossingDifference_eq_primeShell hq.one_le]
  have hnot : ¬ X < q * q * (r * d) := Nat.not_lt_of_ge hsecondLe
  simp [hnot]

end RHLean.Proof
