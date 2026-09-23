import Mathlib
import RHLean.Proof.LowWheelFrozenCofactorTopBottomCancellation
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalHighPrimeBridge
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalInternalMate
import RHLean.Analysis.SquareRootMatchedTransport

/-!
# The frozen top image carries no high prime

After `LowWheelFrozenCofactorTopBottomCancellation` the canonical downcross
ledger reads

`D_R = U_R + F_R^{c=1} - T_R`,

where `T_R` is the signed mass of the post-root image of the frozen
nontrivial-cofactor sector.  A natural next move is to try to absorb `T_R` into
the already-controlled external high-prime population, whose unique-parent part
carries the root budget `R`.

**That route is closed, and this file records why.**

Every high-prime population in this repository is indexed by a prime strictly
above the root: `squareRootHighPrimeCofactorSet R c` filters
`Finset.Ioc R (squareRootEndpoint R)`, and
`lowWheelCanonicalRepeatedExternalTerminalPart R` filters on
`R < lowWheelTaggedDowncrossPivot y`.

The image states carry no such prime.  Writing `y = (t,(c,p))` for a frozen
state with `c > 1` and `q = P⁺(c)`, the image is `(t,(c/q, q*p))`, and

* the image pivot is still `p`, and `p < q ≤ c < R`;
* the image quotient is `q*p`, whose only prime factors are `q` and `p`, both
  `< R`.

So the entire image is `R`-rough-free: it lies strictly below the root wall in
every prime coordinate.  The high-prime populations are, by definition, exactly
the states carrying a prime above the root.  The two are complementary, not
nested.

Three consequences are compiled below.

1.  `lowWheelFrozenCofactorTopImage_quotient_primes_lt_root` — no prime factor
    of an image quotient reaches the root.
2.  `lowWheelFrozenCofactorTopImage_subset_repeatedExternalTerminal_iff` — the
    proposed containment holds **only** in the vacuous case where the frozen
    nontrivial-cofactor sector is itself empty.
3.  `norm_lowWheelFrozenCofactorTopImageLedger_eq` — and independently of any
    containment, the relocation is norm-preserving:
    `‖T_R‖ = ‖F_R^{c>1}‖`.  A sign-reversing bijection cannot change a
    magnitude, so bounding `T_R` *is* bounding the frozen `c > 1` sector.  No
    reindexing can supply that bound; it has to come from new information about
    the sector itself.

The final section adds the case-safe far-transport synthesis from the current
frozen/top/far residual attack.  It does not send the residual to the Go
root-equality carrier.  Instead, the already-compiled face/quotient Othello
reduction first identifies the entire far physical ledger with empty-face
squarefree `(c,q)` states.  Those are then reindexed exactly to the existing
far-prime Mertens transform.  This remains valid when the Go root-equality
carrier is empty.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

namespace FrozenCofactorTopBottom

/-! ## The image lies strictly below the root wall -/

theorem lowWheelFrozenCofactor_cofactor_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2.1 < R := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hcRange := (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).1
  exact (Finset.mem_Ico.mp hcRange).2

theorem lowWheelFrozenCofactorTopPrime_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenCofactorTopPrime y < R := by
  have hcgt := (Finset.mem_filter.mp hy).2
  rcases lowWheelFrozenCofactorTopPrime_data hy with ⟨_hqPrime, hqDvd, _hpq⟩
  have hcpos : 0 < y.2.1 := by omega
  have hqle : lowWheelFrozenCofactorTopPrime y ≤ y.2.1 :=
    Nat.le_of_dvd hcpos hqDvd
  exact lt_of_le_of_lt hqle (lowWheelFrozenCofactor_cofactor_lt_root hy)

theorem lowWheelFrozenCofactor_pivot_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossPivot y < R := by
  rcases lowWheelFrozenCofactorTopPrime_data hy with ⟨_hqPrime, _hqDvd, hpq⟩
  exact hpq.trans (lowWheelFrozenCofactorTopPrime_lt_root hy)

theorem lowWheelFrozenCofactorTopToggle_quotient
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelFrozenCofactorTopToggle y).2.2 =
      lowWheelFrozenCofactorTopPrime y * y.2.2 := by
  rw [lowWheelFrozenCofactorTopToggle_eq hy]

theorem lowWheelFrozenCofactorTopImage_pivot_lt_root
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    lowWheelTaggedDowncrossPivot z < R := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  have hpivot :
      lowWheelCanonicalCofactorQuotientPivot
          (lowWheelFrozenCofactorTopToggle y).2 =
        lowWheelTaggedDowncrossPivot y :=
    lowWheelFrozenCofactorTopToggle_pivot y
  have hgoal :
      lowWheelTaggedDowncrossPivot (lowWheelFrozenCofactorTopToggle y) =
        lowWheelTaggedDowncrossPivot y := hpivot
  rw [hgoal]
  exact lowWheelFrozenCofactor_pivot_lt_root hy

theorem lowWheelFrozenCofactorTopImage_quotient_primes_lt_root
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ z.2.2) :
    r < R := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  rcases lowWheelFrozenCofactorTopPrime_data hy with ⟨hqPrime, _hqDvd, _hpq⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime :=
    lowWheelFrozenCofactor_pivot_prime hy
  have hshape : y.2.2 = lowWheelTaggedDowncrossPivot y :=
    lowWheelFrozenCofactor_quotient_eq_pivot hy
  have hquot :
      (lowWheelFrozenCofactorTopToggle y).2.2 =
        lowWheelFrozenCofactorTopPrime y * y.2.2 :=
    lowWheelFrozenCofactorTopToggle_quotient hy
  rw [hquot, hshape] at hrdvd
  rcases (Nat.Prime.dvd_mul hr).mp hrdvd with hrq | hrp
  · have : r = lowWheelFrozenCofactorTopPrime y :=
      (Nat.prime_dvd_prime_iff_eq hr hqPrime).mp hrq
    rw [this]
    exact lowWheelFrozenCofactorTopPrime_lt_root hy
  · have : r = lowWheelTaggedDowncrossPivot y :=
      (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
    rw [this]
    exact lowWheelFrozenCofactor_pivot_lt_root hy

/-! ## The proposed containment is exactly the vacuous case -/

theorem lowWheelFrozenCofactorTopImage_disjoint_repeatedExternalTerminal
    (R : ℕ) :
    Disjoint (lowWheelFrozenCofactorTopImage R)
      (lowWheelCanonicalRepeatedExternalTerminalPart R) := by
  rw [Finset.disjoint_left]
  intro z hzImage hzExternal
  have hlt := lowWheelFrozenCofactorTopImage_pivot_lt_root hzImage
  have hgt := (mem_lowWheelCanonicalRepeatedExternalTerminalPart.mp hzExternal).2
  omega

theorem lowWheelFrozenCofactorTopImage_subset_repeatedExternalTerminal_iff
    (R : ℕ) :
    lowWheelFrozenCofactorTopImage R ⊆
        lowWheelCanonicalRepeatedExternalTerminalPart R ↔
      lowWheelCanonicalRepeatedFrozenCofactorPart R = ∅ := by
  constructor
  · intro hsub
    have hdisj :=
      lowWheelFrozenCofactorTopImage_disjoint_repeatedExternalTerminal R
    have himageEmpty : lowWheelFrozenCofactorTopImage R = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      exact (Finset.disjoint_left.mp hdisj) hz (hsub hz)
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    have : lowWheelFrozenCofactorTopToggle y ∈
        lowWheelFrozenCofactorTopImage R :=
      mem_lowWheelFrozenCofactorTopImage.mpr ⟨y, hy, rfl⟩
    rw [himageEmpty] at this
    exact absurd this (Finset.notMem_empty _)
  · intro hempty z hz
    rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, _⟩
    rw [hempty] at hy
    exact absurd hy (Finset.notMem_empty _)

/-! ## The relocation is norm-preserving -/

theorem norm_lowWheelFrozenCofactorTopImageLedger_eq
    (R : ℕ) :
    ‖lowWheelFrozenCofactorTopImageLedger R‖ =
      ‖lowWheelCanonicalFrozenCofactorLedger R‖ := by
  rw [lowWheelFrozenCofactorTopImageLedger_eq_neg, norm_neg]

theorem lowWheelCanonicalDowncrossLedger_norm_le_of_sectors
    {R : ℕ} {A B : ℝ}
    (hU : ‖lowWheelCanonicalDowncrossUniqueParentLedger R‖ ≤ A)
    (hT : ‖lowWheelCanonicalTerminalBoundaryLedger R‖ ≤ B)
    {C : ℝ}
    (hF : ‖lowWheelCanonicalFrozenCofactorLedger R‖ ≤ C) :
    ‖lowWheelCanonicalDowncrossLedger R‖ ≤ A + B + C := by
  rw [lowWheelCanonicalDowncrossLedger_eq_unique_add_terminal_sub_topImage]
  have hsplit :
      ‖lowWheelCanonicalDowncrossUniqueParentLedger R +
          lowWheelCanonicalTerminalBoundaryLedger R -
            lowWheelFrozenCofactorTopImageLedger R‖ ≤
        ‖lowWheelCanonicalDowncrossUniqueParentLedger R +
            lowWheelCanonicalTerminalBoundaryLedger R‖ +
          ‖lowWheelFrozenCofactorTopImageLedger R‖ :=
    norm_sub_le _ _
  have hadd :
      ‖lowWheelCanonicalDowncrossUniqueParentLedger R +
          lowWheelCanonicalTerminalBoundaryLedger R‖ ≤ A + B :=
    (norm_add_le _ _).trans (add_le_add hU hT)
  have himage : ‖lowWheelFrozenCofactorTopImageLedger R‖ ≤ C := by
    rw [norm_lowWheelFrozenCofactorTopImageLedger_eq]
    exact hF
  linarith

end FrozenCofactorTopBottom

/-! ## Exact far physical / far-prime transport identity -/

open RHLean.Analysis

/-- Canonical low-cofactor / far-prime pair carrier. -/
def lowWheelFarPrimePairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 R).product
      (Finset.Icc (R + 8) (squareRootEndpoint R))).filter fun cq =>
    cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R

@[simp] theorem mem_lowWheelFarPrimePairSet
    {R c q : ℕ} :
    (c, q) ∈ lowWheelFarPrimePairSet R ↔
      c ∈ Finset.Ico 1 R ∧
        q ∈ Finset.Icc (R + 8) (squareRootEndpoint R) ∧
        q.Prime ∧ c * q ≤ squareRootEndpoint R := by
  simp [lowWheelFarPrimePairSet, and_assoc]

/-- Physical stable pairs are the squarefree part of the same pair carrier. -/
def lowWheelFarPrimeSquarefreePairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFarPrimePairSet R).filter fun cq => Squarefree cq.1

@[simp] theorem mem_lowWheelFarPrimeSquarefreePairSet
    {R c q : ℕ} :
    (c, q) ∈ lowWheelFarPrimeSquarefreePairSet R ↔
      (c, q) ∈ lowWheelFarPrimePairSet R ∧ Squarefree c := by
  simp [lowWheelFarPrimeSquarefreePairSet]

/-- Empty-face embedding of a far-prime pair into the literal physical carrier. -/
def lowWheelFarPrimePairTag (cq : ℕ × ℕ) : LowWheelFullTaggedPhysicalState :=
  ((∅ : Finset ℕ), cq)

theorem lowWheelFarPrimePairTag_injective :
    Function.Injective lowWheelFarPrimePairTag := by
  intro a b hab
  simpa [lowWheelFarPrimePairTag] using congrArg Prod.snd hab

/-- The Othello-stable far physical states are precisely the squarefree
low-cofactor / far-prime pairs. -/
theorem lowWheelFarTaggedPhysicalStableCarrier_eq_pairImage
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFarTaggedPhysicalStableCarrier R =
      (lowWheelFarPrimeSquarefreePairSet R).image lowWheelFarPrimePairTag := by
  ext z
  constructor
  · intro hz
    rcases lowWheelFarTaggedPhysicalStable_geometry hR hz with
      ⟨hface, hqPrime, hqFar, hqX, hc, hsq, hcq⟩
    have hpair : (z.2.1, z.2.2) ∈ lowWheelFarPrimePairSet R :=
      mem_lowWheelFarPrimePairSet.mpr
        ⟨hc, Finset.mem_Icc.mpr ⟨hqFar, hqX⟩, hqPrime, hcq⟩
    have hpairSq :
        (z.2.1, z.2.2) ∈ lowWheelFarPrimeSquarefreePairSet R :=
      mem_lowWheelFarPrimeSquarefreePairSet.mpr ⟨hpair, hsq⟩
    apply Finset.mem_image.mpr
    refine ⟨(z.2.1, z.2.2), hpairSq, ?_⟩
    exact Prod.ext hface.symm rfl
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨cq, hcq, rfl⟩
    rcases cq with ⟨c, q⟩
    rcases mem_lowWheelFarPrimeSquarefreePairSet.mp hcq with
      ⟨hpair, hsq⟩
    rcases mem_lowWheelFarPrimePairSet.mp hpair with
      ⟨hc, hqRange, hqPrime, hprod⟩
    rcases Finset.mem_Icc.mp hqRange with ⟨hqFar, hqX⟩
    exact lowWheelFarTaggedPhysicalStable_of_prime
      hR hc hsq hqPrime hqFar hqX hprod

def lowWheelFarPrimeSquarefreePairMass (R : ℕ) : ℂ :=
  ∑ cq ∈ lowWheelFarPrimeSquarefreePairSet R,
    canonicalMoebiusWeight cq.1

theorem sum_lowWheelFarTaggedPhysicalStableCarrier_eq_squarefreePairMass
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z) =
      lowWheelFarPrimeSquarefreePairMass R := by
  rw [lowWheelFarTaggedPhysicalStableCarrier_eq_pairImage R hR]
  unfold lowWheelFarPrimeSquarefreePairMass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro cq hcq
    simp [lowWheelFarPrimePairTag, lowWheelFullTaggedPhysicalWeight,
      booleanCubeSign]
  · intro a ha b hb hab
    exact lowWheelFarPrimePairTag_injective hab

def lowWheelFarPrimePairMass (R : ℕ) : ℂ :=
  ∑ cq ∈ lowWheelFarPrimePairSet R,
    canonicalMoebiusWeight cq.1

theorem lowWheelFarPrimeSquarefreePairMass_eq_pairMass
    (R : ℕ) :
    lowWheelFarPrimeSquarefreePairMass R = lowWheelFarPrimePairMass R := by
  unfold lowWheelFarPrimeSquarefreePairMass lowWheelFarPrimeSquarefreePairSet
    lowWheelFarPrimePairMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro cq hcq
  by_cases hsq : Squarefree cq.1
  · simp [hsq]
  · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    simp [hsq, canonicalMoebiusWeight, hmu]

theorem lowWheelFarPrimePairMass_eq_farPrimeTransport
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFarPrimePairMass R = squareRootFarPrimeTransport R := by
  unfold lowWheelFarPrimePairMass lowWheelFarPrimePairSet
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈ (Finset.Ico 1 R).product
        (Finset.Icc (R + 8) (squareRootEndpoint R)),
        if cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R then
          canonicalMoebiusWeight cq.1 else 0) =
      ∑ c ∈ Finset.Ico 1 R,
        ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
          if q.Prime ∧ c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight c else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Ico 1 R)
          (t := Finset.Icc (R + 8) (squareRootEndpoint R))
          (f := fun cq : ℕ × ℕ =>
            if cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R then
              canonicalMoebiusWeight cq.1 else 0))
    _ = ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
        ∑ c ∈ Finset.Ico 1 R,
          if q.Prime ∧ c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight c else 0 := by
      exact Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
        if q.Prime then primeDilatedLowCofactorMass R q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hprime : q.Prime
      · simp [hprime, primeDilatedLowCofactorMass]
      · simp [hprime]
    _ = squareRootFarPrimeTransport R := by
      unfold squareRootFarPrimeTransport
      apply Finset.sum_congr rfl
      intro q hqMem
      by_cases hprime : q.Prime
      · have hRq : R < q := by
          have hqLow := (Finset.mem_Icc.mp hqMem).1
          omega
        have hmass := primeDilatedLowCofactorMass_eq_mertensSummatory
          R q (by omega) hRq hprime.pos
        simp [hprime, hmass]
      · simp [hprime]

/-- **Far physical transport identity.**  The literal far tagged physical
ledger is exactly the already-existing far-prime Mertens transform. -/
theorem lowWheelFarTaggedPhysicalLedger_eq_farPrimeTransport
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFarTaggedPhysicalLedger R = squareRootFarPrimeTransport R := by
  calc
    lowWheelFarTaggedPhysicalLedger R =
        ∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
          lowWheelFullTaggedPhysicalWeight z :=
      lowWheelFarTaggedPhysicalLedger_eq_stable R
    _ = lowWheelFarPrimeSquarefreePairMass R :=
      sum_lowWheelFarTaggedPhysicalStableCarrier_eq_squarefreePairMass R hR
    _ = lowWheelFarPrimePairMass R :=
      lowWheelFarPrimeSquarefreePairMass_eq_pairMass R
    _ = squareRootFarPrimeTransport R :=
      lowWheelFarPrimePairMass_eq_farPrimeTransport R hR

end RHLean.Proof
