import RHLean.Proof.LowWheelFrozenSquareResidualParentGeometry
import RHLean.Proof.LowWheelFrozenSecondContactWindowDescent

/-!
# Reverse post-root reassembly for the frozen q^2 parent carrier

The preceding module proves that every reassembled `(q,m)` product lies in the
post-root q-smooth strip

`R < m <= X_R/q^2`, `m` squarefree, `P+(m) < q`.

Here we attack the reverse inclusion.  The only non-obvious point is that the
first root-crossing source scale `A` of an arbitrary such `m` must occur in the
historical second-contact source-scale set.  We certify this constructively.

Recover the unique ordered Euler cut for `m`, write `m=A*d`, and let `p=P+(A)`
be its crossing prime.  Since `P+(m)<q`, we have `p<q`; since `q^2*d<=X_R/A`,
the reciprocal source cutoff `B=X_R/A` satisfies `q^2<=B`.  Hence `q<=B/2`.
Bertrand applied to `B/2` supplies a prime `r` with

`B/2 < r <= 2*(B/2) <= B < R`.

Since `r>=2`, the strict inequality `B<2*r` implies `B<r^2`.  Replacing the
old high cofactor by this single prime `r` therefore produces an actual frozen
repeated source at the *same* scale `A`, and `r^2>B` makes it a genuine second
contact.  Hence `A` is represented.  The original `d` then lies in the
daughter window at owner `q`, so `(q,m)` belongs to the flattened parent
carrier.

No norm or analytic estimate is used; Bertrand is only a finite carrier
saturation device.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

private theorem postRootSmooth_sourceScale_represented
    {R q m : ℕ} (hq : q.Prime) (hqR : q < R)
    (hm : m ∈ lowWheelFrozenSquareResidualPostRootSmoothCarrier R q) :
    ∃ A d,
      A ∈ lowWheelFrozenSecondContactSourceScaleSet R ∧
      d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
        (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q ∧
      q ∈ lowWheelFrozenSourceSquareResidualOwners
        (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) ∧
      A * d = m := by
  rcases Finset.mem_filter.mp hm with ⟨hmSmooth, hRm⟩
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hmSmooth with
    ⟨hm1, hmUpper, hmsq, hmTop⟩
  have hR2 : 2 ≤ R := hq.two_le.trans hqR.le
  have hmX : m ≤ squareRootEndpoint R :=
    hmUpper.trans (Nat.div_le_self _ _)
  have hmR2 : m < R ^ 2 := by
    unfold squareRootEndpoint at hmX
    have hRpos : 0 < R := by omega
    omega
  have hactive := orderedEulerCutActiveChild_of_squarefree_shell hR2 hmsq hRm hmR2
  rcases Finset.mem_image.mp hactive with ⟨y, hy, hchild⟩
  have hs := orderedEulerCutShape_of_mem_carrier hy
  have hlife := (mem_orderedEulerCutCarrier_iff_shape_lifetime.mp hy).2
  let p : ℕ := y.2.2
  let A : ℕ := p * primeFaceProduct y.1
  let d : ℕ := y.2.1
  have hpPrime : p.Prime := by simpa [p] using hs.1
  have hpivot : lowWheelTaggedDowncrossPivot y = p := by
    simpa [p] using orderedEulerCutShape_canonicalPivot hs
  have hAd : A * d = m := by
    rw [← hchild]
    simp [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
      orderedEulerCutPivot, orderedEulerCutLowProduct, A, d, p]
    ac_rfl
  have hAR : R < A := by
    have hdeath := hlife.2
    change R < y.2.2 * primeFaceProduct y.1 at hdeath
    simpa [A, p] using hdeath
  have hApos : 0 < A := by omega
  have htPred : y.1 ∈ (primesUpTo (p - 1)).powerset := by
    apply Finset.mem_powerset.mpr
    intro r hr
    have hrd := hs.2.2.2.2.1 r hr
    exact mem_primesUpTo.mpr ⟨hrd.1, by omega⟩
  have hpNot : p ∉ y.1 := by
    intro hp
    have hlt := (hs.2.2.2.2.1 p hp).2
    exact (Nat.lt_irrefl p) hlt
  have hAinsert : A = primeFaceProduct (insert p y.1) := by
    simp [A, primeFaceProduct, hpNot]
  have htopA : canonicalLargestPrimeFactor A = p := by
    rw [hAinsert]
    exact canonicalLargestPrimeFactor_insert_freshPrime hpPrime htPred
  have hmgt : 1 < m := by omega
  have hpDvdA : p ∣ A := by
    refine ⟨primeFaceProduct y.1, ?_⟩
    simp [A]
  have hpDvdM : p ∣ m := by
    rw [← hAd]
    exact dvd_mul_of_dvd_left hpDvdA d
  have hpLeTop : p ≤ canonicalLargestPrimeFactor m :=
    prime_dvd_le_canonicalLargestPrimeFactor hmgt hpPrime hpDvdM
  have hpq : p < q := hpLeTop.trans_lt hmTop
  have hd1 : 1 ≤ d := by simpa [d] using hs.2.1
  have hdSq : Squarefree d := by simpa [d] using hs.2.2.1
  have hdRough : RoughAbove p d := by simpa [d, p] using hs.2.2.2.2.2
  have hdTop : canonicalLargestPrimeFactor d < q := by
    by_cases hdOne : d = 1
    · rw [hdOne]
      simpa [canonicalLargestPrimeFactor] using hq.one_lt
    · have hdgt : 1 < d := by omega
      have hrPrime := canonicalLargestPrimeFactor_prime hdgt
      have hrDvdD := canonicalLargestPrimeFactor_dvd hdgt
      have hrDvdM : canonicalLargestPrimeFactor d ∣ m := by
        rw [← hAd]
        exact dvd_mul_of_dvd_right hrDvdD A
      exact (prime_dvd_le_canonicalLargestPrimeFactor hmgt hrPrime hrDvdM).trans_lt hmTop
  have hq2m : q * q * m ≤ squareRootEndpoint R := by
    have hqqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
    have h := (Nat.le_div_iff_mul_le hqqPos).1 hmUpper
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  let B : ℕ := squareRootEndpoint R / A
  have hq2d : q * q * d ≤ B := by
    apply (Nat.le_div_iff_mul_le hApos).2
    calc
      (q * q * d) * A = q * q * (A * d) := by ring
      _ = q * q * m := by rw [hAd]
      _ ≤ squareRootEndpoint R := hq2m
  have hq2B : q * q ≤ B := by
    have h := Nat.mul_le_mul_left (q * q) hd1
    simpa using h.trans hq2d
  have hBltR : B < R := by
    dsimp [B]
    apply (Nat.div_lt_iff_lt_mul hApos).2
    have hRpos : 0 < R := by omega
    have hXltR2 : squareRootEndpoint R < R * R := by
      unfold squareRootEndpoint
      have hsqNe : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
      simpa [pow_two] using Nat.pred_lt hsqNe
    have hR2ltRA : R * R < R * A :=
      Nat.mul_lt_mul_of_pos_left hAR hRpos
    exact hXltR2.trans hR2ltRA
  have hqHalf : q ≤ B / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
    have h2q : q * 2 ≤ q * q := Nat.mul_le_mul_left q hq.two_le
    exact h2q.trans hq2B
  have hhalf2 : 2 ≤ B / 2 := hq.two_le.trans hqHalf
  have hhalfNZ : B / 2 ≠ 0 := by omega
  obtain ⟨r, hrPrime, hhalfR, hr2half⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (B / 2) hhalfNZ
  have h2halfB : 2 * (B / 2) ≤ B := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self B 2
  have hrB : r ≤ B := hr2half.trans h2halfB
  have hrR : r < R := hrB.trans_lt hBltR
  have hBr2 : B < r * r := by
    have hB2r : B < r * 2 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hhalfR
    have h2rle : r * 2 ≤ r * r := Nat.mul_le_mul_left r hrPrime.two_le
    exact hB2r.trans_le h2rle
  have hpr : p < r := hpq.trans (hqHalf.trans_lt hhalfR)
  let z : LowWheelTaggedDowncrossState := (y.1, (r, p))
  have hzRough : RoughAbove p r := by
    intro a ha
    rcases Nat.mem_primeFactors.mp ha with ⟨haPrime, haDvd, _⟩
    have har : a = r :=
      (Nat.prime_dvd_prime_iff_eq haPrime hrPrime).mp haDvd
    simpa [har] using hpr
  have hpnr : ¬ p ∣ r := by
    intro hdiv
    have hprEq : p = r :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hrPrime).mp hdiv
    omega
  have hzShape : OrderedEulerCutShape z := by
    refine ⟨hpPrime, hrPrime.one_le, hrPrime.squarefree, hpnr, ?_, hzRough⟩
    intro a ha
    exact hs.2.2.2.2.1 a ha
  have hzPivot : lowWheelTaggedDowncrossPivot z = p :=
    orderedEulerCutShape_canonicalPivot hzShape
  have hzSource : lowWheelFrozenSecondContactSourceScale z = A := by
    change lowWheelTaggedDowncrossPivot z * primeFaceProduct y.1 = A
    rw [hzPivot]
  have hzChildLe : orderedEulerCutChildInteger z ≤ squareRootEndpoint R := by
    change r * (p * primeFaceProduct y.1) ≤ squareRootEndpoint R
    change r * A ≤ squareRootEndpoint R
    exact (Nat.le_div_iff_mul_le hApos).1 hrB
  have hzSqrt := (orderedEulerCutChild_le_endpoint_iff hzShape).1 hzChildLe
  have hfaceR : primeFaceProduct y.1 ≤ R := by
    have hb := hlife.1
    change max (primeFaceProduct y.1)
      (max (y.2.1 + 1) (Nat.sqrt (orderedEulerCutChildInteger y) + 1)) ≤ R at hb
    exact (le_max_left _ _).trans hb
  have hzBirth : orderedEulerCutBirthRoot z ≤ R := by
    change max (primeFaceProduct y.1)
      (max (r + 1) (Nat.sqrt (orderedEulerCutChildInteger z) + 1)) ≤ R
    exact max_le hfaceR (max_le (by omega) hzSqrt)
  have hzDeath : R < orderedEulerCutDeathRoot z := by
    change R < p * primeFaceProduct y.1
    simpa [A] using hAR
  have hzOrdered : z ∈ orderedEulerCutCarrier R :=
    mem_orderedEulerCutCarrier_iff_shape_lifetime.mpr
      ⟨hzShape, hzBirth, hzDeath⟩
  have hzFrozen := orderedEulerCut_mem_frozenCofactor_of_one_lt hzOrdered hrPrime.one_lt
  have htopZ : lowWheelFrozenCofactorTopPrime z = r := by
    have htopData := lowWheelFrozenCofactorTopPrime_data hzFrozen
    exact (Nat.prime_dvd_prime_iff_eq htopData.1 hrPrime).mp htopData.2.1
  have hwallX : squareRootEndpoint R < r * r * A := by
    have h := (Nat.div_lt_iff_lt_mul hApos).1 hBr2
    simpa [B, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hzSecond : z ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R := by
    apply Finset.mem_filter.mpr
    refine ⟨hzFrozen, ?_⟩
    change squareRootEndpoint R <
      lowWheelFrozenCofactorTopPrime z *
        primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace z)
    rw [htopZ, lowWheelCanonicalRepeatedFrozenProductOneFace_product hzFrozen]
    rw [hzPivot]
    dsimp [z]
    simpa [A, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hwallX
  have hAset : A ∈ lowWheelFrozenSecondContactSourceScaleSet R := by
    unfold lowWheelFrozenSecondContactSourceScaleSet
    exact Finset.mem_image.mpr ⟨z, hzSecond, hzSource⟩
  have hdB : d ≤ B / (q * q) := by
    have hqqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
    exact (Nat.le_div_iff_mul_le hqqPos).2
      (by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2d)
  have hdWindow : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q := by
    apply Finset.mem_filter.mpr
    rw [htopA]
    exact ⟨Finset.mem_Icc.mpr ⟨hd1, by simpa [B] using hdB⟩,
      hdSq, hdRough, hdTop⟩
  have hpqA : canonicalLargestPrimeFactor A < q := by
    simpa [htopA] using hpq
  have hchildResidual :=
    lowWheelFrozenSourceSquareResidualDaughter_child_mem hq hpqA hdWindow
  have hqOwner : q ∈ lowWheelFrozenSourceSquareResidualOwners
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) := by
    unfold lowWheelFrozenSourceSquareResidualOwners
    apply Finset.mem_image.mpr
    refine ⟨q * d, ?_, ?_⟩
    · exact (mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mp hchildResidual).1
    · exact (mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mp hchildResidual).2
  exact ⟨A, d, hAset, hdWindow, hqOwner, hAd⟩

/-- **Reverse inclusion.** Every post-root q-smooth predecessor below the q^2
cutoff occurs in the exact flattened parent carrier. -/
theorem lowWheelFrozenSquareResidualPostRootSmooth_subset_parentOwner
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    lowWheelFrozenSquareResidualPostRootSmoothCarrier R q ⊆
      ((lowWheelFrozenSquareResidualParentCarrier R).filter fun x => x.1 = q).image
        Prod.snd := by
  intro m hm
  rcases postRootSmooth_sourceScale_represented hq hqR hm with
    ⟨A, d, hA, hd, hqOwner, hAd⟩
  have htriple : (A, (q, d)) ∈ lowWheelFrozenSquareResidualTriples R :=
    mem_lowWheelFrozenSquareResidualTriples.mpr ⟨hA, hqOwner, hd⟩
  have hparent : (q, A * d) ∈ lowWheelFrozenSquareResidualParentCarrier R :=
    Finset.mem_image.mpr ⟨(A, (q, d)), htriple, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨(q, A * d), Finset.mem_filter.mpr ⟨hparent, rfl⟩, ?_⟩
  exact hAd

/-- **Exact post-root carrier identification.**  After the global A/q Fubini
reassembly, the q^2 residual is not merely a subpacket: for every prime owner
below the old root it is exactly the complete q-smooth post-root predecessor
strip at cutoff `X_R/q^2`. -/
theorem lowWheelFrozenSquareResidualParentOwner_eq_postRootSmooth
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    ((lowWheelFrozenSquareResidualParentCarrier R).filter fun x => x.1 = q).image
        Prod.snd =
      lowWheelFrozenSquareResidualPostRootSmoothCarrier R q := by
  apply Finset.Subset.antisymm
  · exact lowWheelFrozenSquareResidualParentOwner_subset_postRootSmooth
  · exact lowWheelFrozenSquareResidualPostRootSmooth_subset_parentOwner hq hqR

end RHLean.Proof
