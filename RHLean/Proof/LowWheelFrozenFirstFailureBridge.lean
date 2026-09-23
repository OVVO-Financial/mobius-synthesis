import Mathlib
import RHLean.Proof.LowWheelCanonicalFrozenReduction
import RHLean.Proof.LowWheelFrozenCofactorTopImageHighPrimeObstruction
import RHLean.Arithmetic.PrimeProductCubeFrontier
import RHLean.Arithmetic.PrimeFaceProductUniqueness
import RHLean.Analysis.CanonicalLowOccupancy

/-!
# Frozen downcrosses are literal first-failure faces

After the movable Othello population cancels, every remaining state has frozen
shape

`y = (t,(c,p))`,

where `p = minFac(c*p)`, every face prime is below `p`, and

`P(t) <= R < p*P(t)`.

This file makes the resulting dichotomy exact on the complete frozen carrier.
If `c > 1`, then `c` has a prime divisor strictly above the least pivot `p`;
since the physical carrier has `c < R`, necessarily `p < R`.  Hence every
nontrivial-cofactor frozen state is internal to the low-prime cube.

For every internal frozen state, the old face `t` is literally the existing
`primeProductFirstFailureBoundary (primesUpTo R) R p`: it is below the root and
adjoining the fresh prime `p` is the first crossing.  Conversely, a frozen state
with `p > R` must have `c = 1`, so the only external frozen population is the
terminal high-prime coordinate already present elsewhere in the repository.

The final section then uses the compiled reassembly to put the
remaining frozen/top/far scalar residual onto one literal far physical carrier.
The only term not contained in that far carrier is the internal-terminal mate
strip `R < P(t) < R+8`; its represented high product is injective, so it has at
most seven states and norm at most seven.  No Go root-equality assumption is
used in this reassembly.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A nontrivial frozen cofactor forces the canonical crossing prime strictly
below the root. -/
theorem lowWheelCanonicalFrozenDowncross_pivot_lt_root_of_cofactor_gt_one
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R)
    (hcgt : 1 < y.2.1) :
    lowWheelTaggedDowncrossPivot y < R := by
  have hcarrier := (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hcRange := (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).1
  have hcR : y.2.1 < R := (Finset.mem_Ico.mp hcRange).2
  have hpNotC := (mem_lowWheelCanonicalDowncrossPart.mp hx).2.1
  let q := canonicalLargestPrimeFactor y.2.1
  have hqPrime : q.Prime := by
    simpa [q] using canonicalLargestPrimeFactor_prime hcgt
  have hqDvdC : q ∣ y.2.1 := by
    simpa [q] using canonicalLargestPrimeFactor_dvd hcgt
  have hqDvdProd : q ∣ y.2.1 * y.2.2 :=
    dvd_mul_of_dvd_left hqDvdC y.2.2
  have hpLeQ : lowWheelTaggedDowncrossPivot y ≤ q := by
    change Nat.minFac (y.2.1 * y.2.2) ≤ q
    exact Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
  have hpNeQ : lowWheelTaggedDowncrossPivot y ≠ q := by
    intro heq
    apply hpNotC
    have hpDvd : lowWheelTaggedDowncrossPivot y ∣ y.2.1 := by
      simpa [heq] using hqDvdC
    simpa [lowWheelTaggedDowncrossPivot] using hpDvd
  have hpLtQ : lowWheelTaggedDowncrossPivot y < q :=
    lt_of_le_of_ne hpLeQ hpNeQ
  have hqLeC : q ≤ y.2.1 := Nat.le_of_dvd (by omega) hqDvdC
  exact hpLtQ.trans (hqLeC.trans_lt hcR)

/-- Every frozen external crossing has forced cofactor `1`. -/
theorem lowWheelCanonicalFrozenDowncross_cofactor_eq_one_of_root_lt_pivot
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R)
    (hpR : R < lowWheelTaggedDowncrossPivot y) :
    y.2.1 = 1 := by
  have hcarrier := (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hcRange := (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).1
  have hcOne : 1 ≤ y.2.1 := (Finset.mem_Ico.mp hcRange).1
  by_contra hne
  have hcgt : 1 < y.2.1 := by omega
  have hpLtR := lowWheelCanonicalFrozenDowncross_pivot_lt_root_of_cofactor_gt_one
    hy hcgt
  omega

/-- In frozen shape the adjacent-shell inequalities simplify to the literal
first-crossing inequalities `P(t) <= R < p*P(t)`. -/
theorem lowWheelCanonicalFrozenDowncross_firstCrossing_geometry
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R) :
    primeFaceProduct y.1 ≤ R ∧
      R < lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
  have hshape := (Finset.mem_filter.mp hy).2
  have hcarrier := (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  rcases lowWheelCanonicalDowncrossPart_adjacent_shell hx with
    ⟨hpRaw, _hpNotC, _hpDvdK, hdown, hup⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hpRaw
  change primeFaceProduct y.1 *
      (y.2.2 / lowWheelTaggedDowncrossPivot y) ≤ R at hdown
  change R < primeFaceProduct y.1 *
      (lowWheelTaggedDowncrossPivot y *
        (y.2.2 / lowWheelTaggedDowncrossPivot y)) at hup
  have hdiv :
      y.2.2 / lowWheelTaggedDowncrossPivot y = 1 := by
    rw [hshape.1]
    exact Nat.div_self hp.pos
  have hdown' : primeFaceProduct y.1 ≤ R := by
    rw [hdiv, Nat.mul_one] at hdown
    exact hdown
  have hup' : R < primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y := by
    rw [hdiv, Nat.mul_one] at hup
    exact hup
  exact ⟨hdown', by simpa [Nat.mul_comm] using hup'⟩

/-- An internal frozen crossing is exactly an existing truncated Boolean-cube
first-failure face at its canonical pivot. -/
theorem lowWheelCanonicalFrozenDowncross_face_mem_firstFailureBoundary
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R)
    (hpR : lowWheelTaggedDowncrossPivot y ≤ R) :
    y.1 ∈ primeProductFirstFailureBoundary
      (primesUpTo R) R (lowWheelTaggedDowncrossPivot y) := by
  have hshape := (Finset.mem_filter.mp hy).2
  have hcarrier := (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨ht, hx⟩
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hshell.1
  have hpGlobal : lowWheelTaggedDowncrossPivot y ∈ primesUpTo R :=
    mem_primesUpTo.mpr ⟨hp, hpR⟩
  have htSub : y.1 ⊆ primesUpTo R := Finset.mem_powerset.mp ht
  have hpNotFace : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hmem
    have hlt := hshape.2 _ hmem
    exact (Nat.lt_irrefl _) hlt
  have htErase : y.1 ⊆ (primesUpTo R).erase (lowWheelTaggedDowncrossPivot y) := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨by
      intro heq
      subst q
      exact hpNotFace hq, htSub hq⟩
  rcases lowWheelCanonicalFrozenDowncross_firstCrossing_geometry hy with
    ⟨hbelow, hcross⟩
  exact mem_primeProductFirstFailureBoundary.mpr
    ⟨htErase, hbelow, hcross⟩

/-- Every frozen state is either an internal first-failure crossing or a forced
external terminal state. -/
theorem lowWheelCanonicalFrozenDowncross_internal_or_externalTerminal
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalFrozenDowncrossPart R) :
    (lowWheelTaggedDowncrossPivot y ≤ R ∧
      y.1 ∈ primeProductFirstFailureBoundary
        (primesUpTo R) R (lowWheelTaggedDowncrossPivot y)) ∨
    (R < lowWheelTaggedDowncrossPivot y ∧ y.2.1 = 1) := by
  by_cases hpR : lowWheelTaggedDowncrossPivot y ≤ R
  · exact Or.inl ⟨hpR,
      lowWheelCanonicalFrozenDowncross_face_mem_firstFailureBoundary hy hpR⟩
  · have hRp : R < lowWheelTaggedDowncrossPivot y := Nat.lt_of_not_ge hpR
    exact Or.inr ⟨hRp,
      lowWheelCanonicalFrozenDowncross_cofactor_eq_one_of_root_lt_pivot hy hRp⟩

/-! ## Literal physical carrier for the frozen/top/far residual -/

open FrozenCofactorTopBottom

/-- Near internal-terminal mate mass, on the seven-integer root strip. -/
def lowWheelCanonicalRepeatedTerminalInternalMateNearLedger (R : ℕ) : ℂ :=
  ∑ z ∈ lowWheelCanonicalRepeatedTerminalInternalMateNearImage R,
    lowWheelFullTaggedPhysicalWeight z

/-- Far part of the same internal-terminal mate image. -/
def lowWheelCanonicalRepeatedTerminalInternalMateFarLedger (R : ℕ) : ℂ :=
  ∑ z ∈ lowWheelCanonicalRepeatedTerminalInternalMateFarImage R,
    lowWheelFullTaggedPhysicalWeight z

/-- The original mate ledger is exactly its near/far cutoff split. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateLedger_eq_near_add_far
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateLedger R =
      lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R +
        lowWheelCanonicalRepeatedTerminalInternalMateFarLedger R := by
  rw [lowWheelCanonicalRepeatedTerminalInternalMateLedger_eq_imageSum]
  change
    (∑ z ∈ lowWheelCanonicalRepeatedTerminalInternalMateImage R,
      lowWheelFullTaggedPhysicalWeight z) = _
  rw [lowWheelCanonicalRepeatedTerminalInternalMateImage_eq_near_union_far R,
    Finset.sum_union
      (lowWheelCanonicalRepeatedTerminalInternalMateNear_disjoint_far R)]
  rfl

/-- The frozen top-image ledger uses the same literal physical weight. -/
theorem lowWheelFrozenCofactorTopImageLedger_eq_fullPhysicalWeightSum
    (R : ℕ) :
    lowWheelFrozenCofactorTopImageLedger R =
      ∑ z ∈ lowWheelFrozenCofactorTopImage R,
        lowWheelFullTaggedPhysicalWeight z := by
  rfl

/-- The two already-owned far image populations, kept as one disjoint set. -/
def lowWheelFrozenTopFarOwnedImage (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  lowWheelCanonicalRepeatedTerminalInternalMateFarImage R ∪
    lowWheelFrozenCofactorTopImage R

/-- Both owned images are literal subcarriers of the far physical region. -/
theorem lowWheelFrozenTopFarOwnedImage_subset_farPhysical
    (R : ℕ) (hR : 6 ≤ R) :
    lowWheelFrozenTopFarOwnedImage R ⊆ lowWheelFarTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_union.mp hz with hmate | htop
  · exact lowWheelCanonicalRepeatedTerminalInternalMateFarImage_subset_farPhysical
      R hmate
  · exact lowWheelFrozenCofactorTopImage_subset_farPhysical R hR htop

/-- Signed mass of the owned far image union. -/
theorem sum_lowWheelFrozenTopFarOwnedImage_eq_farMate_add_top
    (R : ℕ) :
    (∑ z ∈ lowWheelFrozenTopFarOwnedImage R,
        lowWheelFullTaggedPhysicalWeight z) =
      lowWheelCanonicalRepeatedTerminalInternalMateFarLedger R +
        lowWheelFrozenCofactorTopImageLedger R := by
  unfold lowWheelFrozenTopFarOwnedImage
  rw [Finset.sum_union
    (lowWheelCanonicalRepeatedTerminalInternalMateFarImage_disjoint_topImage R)]
  unfold lowWheelCanonicalRepeatedTerminalInternalMateFarLedger
  rw [lowWheelFrozenCofactorTopImageLedger_eq_fullPhysicalWeightSum]

/-- Literal remaining far physical carrier after removing both owned images. -/
def lowWheelFrozenTopFarPhysicalResidualCarrier (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  lowWheelFarTaggedPhysicalCarrier R \ lowWheelFrozenTopFarOwnedImage R

/-- Signed mass of that literal remaining far carrier. -/
def lowWheelFrozenTopFarPhysicalResidualLedger (R : ℕ) : ℂ :=
  ∑ z ∈ lowWheelFrozenTopFarPhysicalResidualCarrier R,
    lowWheelFullTaggedPhysicalWeight z

/-- Exact set-difference decomposition of the far physical ledger. -/
theorem lowWheelFarTaggedPhysicalLedger_eq_residual_add_farMate_add_top
    (R : ℕ) (hR : 6 ≤ R) :
    lowWheelFarTaggedPhysicalLedger R =
      lowWheelFrozenTopFarPhysicalResidualLedger R +
        lowWheelCanonicalRepeatedTerminalInternalMateFarLedger R +
        lowWheelFrozenCofactorTopImageLedger R := by
  have hsub := lowWheelFrozenTopFarOwnedImage_subset_farPhysical R hR
  have hs := Finset.sum_sdiff hsub (f := lowWheelFullTaggedPhysicalWeight)
  calc
    lowWheelFarTaggedPhysicalLedger R =
        (∑ z ∈ lowWheelFrozenTopFarPhysicalResidualCarrier R,
          lowWheelFullTaggedPhysicalWeight z) +
        ∑ z ∈ lowWheelFrozenTopFarOwnedImage R,
          lowWheelFullTaggedPhysicalWeight z := by
      symm
      simpa [lowWheelFarTaggedPhysicalLedger,
        lowWheelFrozenTopFarPhysicalResidualCarrier] using hs
    _ = lowWheelFrozenTopFarPhysicalResidualLedger R +
          (lowWheelCanonicalRepeatedTerminalInternalMateFarLedger R +
            lowWheelFrozenCofactorTopImageLedger R) := by
      rw [sum_lowWheelFrozenTopFarOwnedImage_eq_farMate_add_top]
      rfl
    _ = lowWheelFrozenTopFarPhysicalResidualLedger R +
          lowWheelCanonicalRepeatedTerminalInternalMateFarLedger R +
          lowWheelFrozenCofactorTopImageLedger R := by ring

/-- Every internal-terminal mate occurrence remains strictly post-root in its
represented high product. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_root_lt_highProduct
    {R : ℕ} {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ lowWheelCanonicalRepeatedTerminalInternalMateImage R) :
    R < lowWheelTaggedHighProduct z := by
  have hfull :=
    lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_fullPhysical R hz
  have hphys := (mem_lowWheelFullTaggedPhysicalCarrier.mp hfull).2
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.2
  exact hcarrier.2.2.1

/-- The represented high product is injective on the complete internal-terminal
mate image.  State `(1,1)` leaves only the Boolean prime face, whose product
uniquely recovers that face. -/
theorem lowWheelTaggedHighProduct_injOn_internalMateImage
    (R : ℕ) :
    Set.InjOn lowWheelTaggedHighProduct
      (lowWheelCanonicalRepeatedTerminalInternalMateImage R) := by
  intro a ha b hb hab
  have haState :=
    lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one ha
  have hbState :=
    lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one hb
  have haFull :=
    lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_fullPhysical R ha
  have hbFull :=
    lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_fullPhysical R hb
  have haFace := (mem_lowWheelFullTaggedPhysicalCarrier.mp haFull).1
  have hbFace := (mem_lowWheelFullTaggedPhysicalCarrier.mp hbFull).1
  have hprod : primeFaceProduct a.1 = primeFaceProduct b.1 := by
    unfold lowWheelTaggedHighProduct at hab
    rw [haState, hbState] at hab
    simpa using hab
  have hface : a.1 = b.1 :=
    (primeFaceProduct_eq_iff
      (fun p hp => prime_of_mem_primesUpTo
        ((Finset.mem_powerset.mp haFace) hp))
      (fun p hp => prime_of_mem_primesUpTo
        ((Finset.mem_powerset.mp hbFace) hp))).mp hprod
  have hstate : a.2 = b.2 := haState.trans hbState.symm
  exact Prod.ext hface hstate

/-- The near internal-terminal mate strip has at most the seven integer homes
`R+1,...,R+7`. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateNearImage_card_le_seven
    (R : ℕ) :
    (lowWheelCanonicalRepeatedTerminalInternalMateNearImage R).card ≤ 7 := by
  let N := lowWheelCanonicalRepeatedTerminalInternalMateNearImage R
  let encode := lowWheelTaggedHighProduct
  have hinj : Set.InjOn encode N := by
    intro a ha b hb hab
    apply lowWheelTaggedHighProduct_injOn_internalMateImage R
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  have himage : N.image encode ⊆ Finset.Icc (R + 1) (R + 7) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    change lowWheelTaggedHighProduct z ∈ Finset.Icc (R + 1) (R + 7)
    have hzImage := (Finset.mem_filter.mp hz).1
    have hroot :=
      lowWheelCanonicalRepeatedTerminalInternalMateImage_root_lt_highProduct hzImage
    have hnear := (Finset.mem_filter.mp hz).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcardImage : (N.image encode).card = N.card :=
    Finset.card_image_iff.mpr hinj
  have hle := Finset.card_le_card himage
  rw [hcardImage] at hle
  have hI : (Finset.Icc (R + 1) (R + 7)).card = 7 := by
    rw [Nat.card_Icc]
    omega
  calc
    N.card ≤ (Finset.Icc (R + 1) (R + 7)).card := hle
    _ = 7 := hI

/-- Every literal tagged physical weight has norm at most one. -/
theorem norm_lowWheelFullTaggedPhysicalWeight_le_one
    (z : LowWheelFullTaggedPhysicalState) :
    ‖lowWheelFullTaggedPhysicalWeight z‖ ≤ 1 := by
  unfold lowWheelFullTaggedPhysicalWeight
  rw [norm_mul]
  have hsign : ‖(booleanCubeSign z.1 : ℂ)‖ = 1 := by
    simp [booleanCubeSign]
  rw [hsign, mul_one]
  exact norm_canonicalMoebiusWeight_le_one z.2.1

/-- Therefore the complete near internal-mate ledger is uniformly bounded by
seven. -/
theorem norm_lowWheelCanonicalRepeatedTerminalInternalMateNearLedger_le_seven
    (R : ℕ) :
    ‖lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R‖ ≤ 7 := by
  unfold lowWheelCanonicalRepeatedTerminalInternalMateNearLedger
  calc
    ‖∑ z ∈ lowWheelCanonicalRepeatedTerminalInternalMateNearImage R,
        lowWheelFullTaggedPhysicalWeight z‖ ≤
      ∑ z ∈ lowWheelCanonicalRepeatedTerminalInternalMateNearImage R,
        ‖lowWheelFullTaggedPhysicalWeight z‖ := norm_sum_le _ _
    _ ≤ ∑ _z ∈ lowWheelCanonicalRepeatedTerminalInternalMateNearImage R,
        (1 : ℝ) := by
      exact Finset.sum_le_sum fun z _ =>
        norm_lowWheelFullTaggedPhysicalWeight_le_one z
    _ = ((lowWheelCanonicalRepeatedTerminalInternalMateNearImage R).card : ℝ) := by
      simp
    _ ≤ 7 := by
      exact_mod_cast
        lowWheelCanonicalRepeatedTerminalInternalMateNearImage_card_le_seven R

/-- **Exact carrier normal form of the hard residual.**  Everything
far from the root is now one literal set-difference carrier; the only leftover
outside it is the bounded seven-integer internal-mate strip. -/
theorem lowWheelFrozenTopFarResidual_eq_physicalResidual_sub_near
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      lowWheelFrozenTopFarPhysicalResidualLedger R -
        lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R := by
  rw [lowWheelFrozenTopFarResidual_eq_farTransport_sub_internalMate_sub_topImage
      R hR,
    ← lowWheelFarTaggedPhysicalLedger_eq_farPrimeTransport R (by omega),
    lowWheelCanonicalRepeatedTerminalInternalMateLedger_eq_near_add_far R,
    lowWheelFarTaggedPhysicalLedger_eq_residual_add_farMate_add_top R (by omega)]
  ring

/-- Quantitative handoff: controlling the literal far residual carrier controls
the old scalar residual with only an additive constant seven. -/
theorem norm_lowWheelFrozenTopFarResidual_le_physicalResidual_add_seven
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowWheelFrozenTopFarResidual R‖ ≤
      ‖lowWheelFrozenTopFarPhysicalResidualLedger R‖ + 7 := by
  rw [lowWheelFrozenTopFarResidual_eq_physicalResidual_sub_near R hR]
  calc
    ‖lowWheelFrozenTopFarPhysicalResidualLedger R -
        lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R‖ ≤
      ‖lowWheelFrozenTopFarPhysicalResidualLedger R‖ +
        ‖lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R‖ :=
      norm_sub_le _ _
    _ ≤ ‖lowWheelFrozenTopFarPhysicalResidualLedger R‖ + 7 :=
      add_le_add_left
        (norm_lowWheelCanonicalRepeatedTerminalInternalMateNearLedger_le_seven R) _

end RHLean.Proof
