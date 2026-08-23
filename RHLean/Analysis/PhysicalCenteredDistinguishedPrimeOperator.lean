import Mathlib
import RHLean.Analysis.DistinguishedPrimeTransitionSupport
import RHLean.Analysis.SquareRootTransportRealization

/-!
# Physical centered distinguished-prime operator

The existing physical degree-one centering subtracts the row mean only on the
conditioned nonzero destination sector.  This file records the exact analogue
for the seven-state distinguished-prime support.

For a fixed large prime there is one inactive state and six active slot/sign
labels.  Arithmetic six-site uniqueness already forces every active source row
to vanish on all six active destinations.  Therefore centering *only the active
destination sector* commutes with the arithmetic support restriction: the row
mean of every active source is already zero, so the active-to-active block stays
identically zero.

This is deliberately different from centering the full seven-state constant
mode.  A full mass projection can refill the active-to-active block.  The
active-sector centering below is the normalization compatible with the existing
physical `N - rowMean` sign-sector architecture.

The final section supplies the canonical physical `(R,q)` raw coefficient
ledger.  A visible active hit is required to lie in the actual square-root
transport population `c*q <= R^2-1`, with `1 <= c < R`.  Crucially, the raw
kernel is *not* the empirical row-normalized kernel used in the finite sweep:
every entry is an explicit finite signed sum of the repository's canonical
cofactor Möbius weights over the local six-site `(c,q)` transport population.
Thus the centered coefficients retain the arithmetic mass needed by any later
global reconstruction.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RestrictedPrimeTransitionOperator
open RHLean.Arithmetic
open RHLean.Proof

/-- Sum of one kernel row over the six active destination labels. -/
def restrictedPrimeActiveDestinationSum
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) : ℂ :=
  ∑ t : PrimeActiveLabel, K s (some t)

/-- Uniform row mean on the six active destination labels. -/
def restrictedPrimeActiveDestinationMean
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) : ℂ :=
  restrictedPrimeActiveDestinationSum K s / 6

/-- Center a kernel only on the active destination sector.  The inactive
column is untouched. -/
def centerRestrictedPrimeActiveDestinationSector
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ) :
    SignedPrimeHitState → SignedPrimeHitState → ℂ
  | s, none => K s none
  | s, some t => K s (some t) - restrictedPrimeActiveDestinationMean K s

/-- A restricted active source row has zero total mass on active destinations. -/
@[simp] theorem restrictedPrimeActiveDestinationSum_some_eq_zero
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (hK : IsRestrictedPrimeKernel K)
    (s : PrimeActiveLabel) :
    restrictedPrimeActiveDestinationSum K (some s) = 0 := by
  unfold restrictedPrimeActiveDestinationSum
  apply Finset.sum_eq_zero
  intro t ht
  exact hK s t

/-- Hence its active-sector row mean is exactly zero. -/
@[simp] theorem restrictedPrimeActiveDestinationMean_some_eq_zero
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (hK : IsRestrictedPrimeKernel K)
    (s : PrimeActiveLabel) :
    restrictedPrimeActiveDestinationMean K (some s) = 0 := by
  unfold restrictedPrimeActiveDestinationMean
  rw [restrictedPrimeActiveDestinationSum_some_eq_zero K hK s]
  norm_num

/-- **Centering-sparsity gate.**  Active-sector row centering preserves the exact
thirteen-entry distinguished-prime support. -/
theorem centerRestrictedPrimeActiveDestinationSector_isRestricted
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (hK : IsRestrictedPrimeKernel K) :
    IsRestrictedPrimeKernel
      (centerRestrictedPrimeActiveDestinationSector K) := by
  intro s t
  change
    K (some s) (some t) -
        restrictedPrimeActiveDestinationMean K (some s) = 0
  rw [hK s t, restrictedPrimeActiveDestinationMean_some_eq_zero K hK s]
  ring

/-- Sum of a constant over the six active labels. -/
private theorem sum_primeActiveLabel_const (z : ℂ) :
    (∑ _ : PrimeActiveLabel, z) = 6 * z := by
  classical
  simp [nsmul_eq_mul]

/-- Active-sector centering removes the active destination constant mode on
every source row, without any support assumption. -/
theorem restrictedPrimeActiveDestinationSum_center_eq_zero
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) :
    restrictedPrimeActiveDestinationSum
      (centerRestrictedPrimeActiveDestinationSector K) s = 0 := by
  unfold restrictedPrimeActiveDestinationSum
  change
    (∑ t : PrimeActiveLabel,
      (K s (some t) - restrictedPrimeActiveDestinationMean K s)) = 0
  rw [Finset.sum_sub_distrib, sum_primeActiveLabel_const]
  unfold restrictedPrimeActiveDestinationMean restrictedPrimeActiveDestinationSum
  ring

/-- The kernel of every restricted operator satisfies the certified support. -/
theorem restrictedPrime_coeff_isRestricted
    (A : RestrictedPrimeTransitionOperator) :
    IsRestrictedPrimeKernel A.coeff := by
  intro s t
  rfl

/-- Mean of the six inactive-to-active coefficients. -/
def RestrictedPrimeTransitionOperator.activeDestinationMean
    (A : RestrictedPrimeTransitionOperator) : ℂ :=
  (∑ t : PrimeActiveLabel, A.inactiveToActive t) / 6

/-- Package active-sector centering back into the exact thirteen-coefficient
operator class.  Only the six inactive-to-active coefficients change. -/
def RestrictedPrimeTransitionOperator.activeSectorCentered
    (A : RestrictedPrimeTransitionOperator) :
    RestrictedPrimeTransitionOperator where
  inactiveInactive := A.inactiveInactive
  inactiveToActive := fun t => A.inactiveToActive t - A.activeDestinationMean
  activeToInactive := A.activeToInactive

@[simp] theorem RestrictedPrimeTransitionOperator.activeSectorCentered_inactiveInactive
    (A : RestrictedPrimeTransitionOperator) :
    A.activeSectorCentered.inactiveInactive = A.inactiveInactive := rfl

@[simp] theorem RestrictedPrimeTransitionOperator.activeSectorCentered_inactiveToActive
    (A : RestrictedPrimeTransitionOperator) (t : PrimeActiveLabel) :
    A.activeSectorCentered.inactiveToActive t =
      A.inactiveToActive t - A.activeDestinationMean := rfl

@[simp] theorem RestrictedPrimeTransitionOperator.activeSectorCentered_activeToInactive
    (A : RestrictedPrimeTransitionOperator) (s : PrimeActiveLabel) :
    A.activeSectorCentered.activeToInactive s = A.activeToInactive s := rfl

/-- The packaged operator is coefficient-for-coefficient equal to centering the
raw restricted kernel on the active destination sector. -/
theorem RestrictedPrimeTransitionOperator.activeSectorCentered_coeff_eq
    (A : RestrictedPrimeTransitionOperator)
    (s t : SignedPrimeHitState) :
    A.activeSectorCentered.coeff s t =
      centerRestrictedPrimeActiveDestinationSector A.coeff s t := by
  have hA : IsRestrictedPrimeKernel A.coeff :=
    restrictedPrime_coeff_isRestricted A
  rcases s with _ | s
  · rcases t with _ | t
    · rfl
    · change
        A.inactiveToActive t - A.activeDestinationMean =
          A.inactiveToActive t -
            restrictedPrimeActiveDestinationMean A.coeff none
      congr 1
  · rcases t with _ | t
    · rfl
    · change
        0 = A.coeff (some s) (some t) -
          restrictedPrimeActiveDestinationMean A.coeff (some s)
      rw [hA s t, restrictedPrimeActiveDestinationMean_some_eq_zero A.coeff hA s]
      ring

/-- The six centered inactive-to-active coefficients have exactly zero sum. -/
theorem RestrictedPrimeTransitionOperator.sum_activeSectorCentered_inactiveToActive_eq_zero
    (A : RestrictedPrimeTransitionOperator) :
    (∑ t : PrimeActiveLabel,
      A.activeSectorCentered.inactiveToActive t) = 0 := by
  change
    (∑ t : PrimeActiveLabel,
      (A.inactiveToActive t - A.activeDestinationMean)) = 0
  rw [Finset.sum_sub_distrib, sum_primeActiveLabel_const]
  unfold RestrictedPrimeTransitionOperator.activeDestinationMean
  ring

/-- Equivalently, the active constant input mode is killed before any norm is
taken. -/
theorem RestrictedPrimeTransitionOperator.activeSectorCentered_activeInputForm_const_eq_zero
    (A : RestrictedPrimeTransitionOperator) :
    A.activeSectorCentered.activeInputForm (fun _ => 1) = 0 := by
  unfold RestrictedPrimeTransitionOperator.activeInputForm
  simp only [mul_one]
  exact A.sum_activeSectorCentered_inactiveToActive_eq_zero

/-! ## Canonical physical `(R,q)` extraction -/

/-- A site belongs to the canonical square-root transport `q`-fibre exactly when
it is `c*q` for its reciprocal cofactor `c = n/q`, with `1 <= c < R`, and lies
below the complete-square endpoint.  The divisibility clause makes the quotient
representation exact rather than merely a floor approximation. -/
def PhysicalDistinguishedPrimeTransportHit (R q n : ℕ) : Prop :=
  q ∣ n ∧ 1 ≤ n / q ∧ n / q < R ∧ n ≤ squareRootEndpoint R

instance physicalDistinguishedPrimeTransportHitDecidable (R q n : ℕ) :
    Decidable (PhysicalDistinguishedPrimeTransportHit R q n) := by
  unfold PhysicalDistinguishedPrimeTransportHit
  infer_instance

/-- The quotient-form hit predicate is literally membership in the repository's
canonical `squareRootTransportPairSet` when `q` is a transport prime. -/
theorem physicalDistinguishedPrimeTransportHit_iff_pair
    {R q n : ℕ} (hq : q.Prime) (hRq : R < q) :
    PhysicalDistinguishedPrimeTransportHit R q n ↔
      (n / q, q) ∈ squareRootTransportPairSet R ∧
        (n / q) * q = n := by
  constructor
  · rintro ⟨hdiv, hc1, hcR, hnX⟩
    have hprod : (n / q) * q = n := Nat.div_mul_cancel hdiv
    have hqle : q ≤ n := by
      calc
        q = 1 * q := by simp
        _ ≤ (n / q) * q := Nat.mul_le_mul_right q hc1
        _ = n := hprod
    have hqX : q ≤ squareRootEndpoint R := hqle.trans hnX
    refine ⟨?_, hprod⟩
    unfold squareRootTransportPairSet
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Ico.mpr ⟨hc1, hcR⟩,
          Finset.mem_Ioc.mpr ⟨hRq, hqX⟩⟩
    · exact ⟨hq, by simpa [hprod] using hnX⟩
  · rintro ⟨hpair, hprod⟩
    unfold squareRootTransportPairSet at hpair
    rcases Finset.mem_filter.mp hpair with ⟨hbase, hdata⟩
    rcases Finset.mem_product.mp hbase with ⟨hcMem, _hqMem⟩
    rcases Finset.mem_Ico.mp hcMem with ⟨hc1, hcR⟩
    have hdiv : q ∣ n := by
      refine ⟨n / q, ?_⟩
      simpa [Nat.mul_comm] using hprod.symm
    have hnX : n ≤ squareRootEndpoint R := by
      simpa [hprod] using hdata.2
    exact ⟨hdiv, hc1, hcR, hnX⟩

/-- Bool encoding of the visible Möbius sign.  `true` is `+1` and `false` is
`-1`; this is only inspected after nonvanishing has been required. -/
def physicalDistinguishedPrimeVisibleSignBit (n : ℕ) : Bool :=
  decide (μ n = 1)

/-- The actual signed fixed-prime state of one physical three-slot cell.  A hit
is active only if it belongs to the canonical square-root `c*q` transport
population and its Möbius value is visible. -/
def physicalDistinguishedPrimeState (R q k : ℕ) : SignedPrimeHitState :=
  let n0 := threeSlotValue k 0
  let n1 := threeSlotValue k 1
  let n2 := threeSlotValue k 2
  if PhysicalDistinguishedPrimeTransportHit R q n0 ∧ μ n0 ≠ 0 then
    some ((0 : Fin 3), physicalDistinguishedPrimeVisibleSignBit n0)
  else if PhysicalDistinguishedPrimeTransportHit R q n1 ∧ μ n1 ≠ 0 then
    some ((1 : Fin 3), physicalDistinguishedPrimeVisibleSignBit n1)
  else if PhysicalDistinguishedPrimeTransportHit R q n2 ∧ μ n2 ≠ 0 then
    some ((2 : Fin 3), physicalDistinguishedPrimeVisibleSignBit n2)
  else
    none

/-- Every active physical state records a genuine divisibility hit by `q`. -/
theorem physicalDistinguishedPrimeState_some_dvd
    {R q k : ℕ} {a : PrimeActiveLabel}
    (hstate : physicalDistinguishedPrimeState R q k = some a) :
    q ∣ threeSlotValue k a.1 := by
  rcases a with ⟨i, sign⟩
  fin_cases i <;>
    unfold physicalDistinguishedPrimeState at hstate <;>
    dsimp at hstate ⊢ <;>
    split_ifs at hstate <;>
    simp_all [PhysicalDistinguishedPrimeTransportHit]

/-- Number of adjacent physical transitions whose destination three-slot cell is
fully inside the square-root carrier. -/
def physicalDistinguishedPrimeCarrierLength (R : ℕ) : ℕ :=
  (squareRootEndpoint R - 3) / 4

/-- Signed canonical cofactor mass from the physical `q`-fibre that lands in
one three-slot cell.  The summation variable is literally the lower cofactor
`1 <= c < R` from `primeDilatedLowCofactorMass`; no empirical row normalization
is present. -/
def physicalDistinguishedPrimeCellFibreMass
    (R q k : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    if c * q ≤ squareRootEndpoint R ∧
        ∃ i : Fin 3, c * q = threeSlotValue k i then
      canonicalMoebiusWeight c
    else
      0

/-- Signed mass of the canonical `(c,q)` fibre on the six physical sites of one
adjacent-cell transition. -/
def physicalDistinguishedPrimeLocalTransitionFibreMass
    (R q k : ℕ) : ℂ :=
  physicalDistinguishedPrimeCellFibreMass R q k +
    physicalDistinguishedPrimeCellFibreMass R q (k + 1)

/-- Exact finite signed mass of one fixed-prime transition class.  Every summand
is a finite signed cofactor-Möbius sum on the canonical `c*q` transport
population, while the state labels retain the physical slot and visible sign. -/
def physicalDistinguishedPrimeTransitionMass
    (R q : ℕ) (s t : SignedPrimeHitState) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    if physicalDistinguishedPrimeState R q k = s ∧
        physicalDistinguishedPrimeState R q (k + 1) = t then
      physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    else
      0

/-- **Raw physical fixed-prime kernel.**  Its entries are the signed canonical
cofactor-fibre transition sums themselves.  This deliberately does not reuse
the empirical row-normalized diagnostic kernel from the finite sweep. -/
def physicalDistinguishedPrimeRawKernel
    (R q : ℕ)
    (_hq : q.Prime)
    (_hRq : R < q) :
    SignedPrimeHitState → SignedPrimeHitState → ℂ :=
  fun s t => physicalDistinguishedPrimeTransitionMass R q s t

/-- Six-site uniqueness annihilates every active-to-active signed transition
mass, independently of the cofactor weights. -/
theorem physicalDistinguishedPrimeTransitionMass_some_some_eq_zero
    (R q : ℕ) (hq6 : 6 < q)
    (s t : PrimeActiveLabel) :
    physicalDistinguishedPrimeTransitionMass R q (some s) (some t) = 0 := by
  classical
  unfold physicalDistinguishedPrimeTransitionMass
  apply Finset.sum_eq_zero
  intro k hk
  split_ifs with hst
  · rcases hst with ⟨hs, ht⟩
    have hqs : q ∣ threeSlotValue k s.1 :=
      physicalDistinguishedPrimeState_some_dvd hs
    have hqt : q ∣ threeSlotValue (k + 1) t.1 :=
      physicalDistinguishedPrimeState_some_dvd ht
    exact (largeDivisor_current_next_threeSlot_impossible
      q k s.1 t.1 hq6 s.1.isLt t.1.isLt hqs hqt).elim
  · rfl

/-- **Physical support theorem.**  From the asymptotic range `R >= 6`, the
actual signed `(R,q)` raw kernel has exactly the certified thirteen-entry
support.  The lower cutoff is logically necessary for the existing six-site
uniqueness lemma: `R < q` alone still permits the exceptional primes `3` and
`5`. -/
theorem physicalDistinguishedPrimeRawKernel_isRestricted
    (R q : ℕ)
    (hq : q.Prime)
    (hRq : R < q)
    (hR6 : 6 ≤ R) :
    IsRestrictedPrimeKernel
      (physicalDistinguishedPrimeRawKernel R q hq hRq) := by
  intro s t
  have hq6 : 6 < q := lt_of_le_of_lt hR6 hRq
  simpa [physicalDistinguishedPrimeRawKernel] using
    physicalDistinguishedPrimeTransitionMass_some_some_eq_zero R q hq6 s t

/-- Direct arithmetic inactive-to-inactive signed coefficient. -/
def physicalDistinguishedPrimeA
    (R q : ℕ) (_hq : q.Prime) (_hRq : R < q) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    if physicalDistinguishedPrimeState R q k = none ∧
        physicalDistinguishedPrimeState R q (k + 1) = none then
      physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    else
      0

/-- Direct arithmetic inactive-to-active signed coefficient family. -/
def physicalDistinguishedPrimeB
    (R q : ℕ) (_hq : q.Prime) (_hRq : R < q)
    (t : PrimeActiveLabel) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    if physicalDistinguishedPrimeState R q k = none ∧
        physicalDistinguishedPrimeState R q (k + 1) = some t then
      physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    else
      0

/-- Direct arithmetic active-to-inactive signed coefficient family. -/
def physicalDistinguishedPrimeC
    (R q : ℕ) (_hq : q.Prime) (_hRq : R < q)
    (s : PrimeActiveLabel) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    if physicalDistinguishedPrimeState R q k = some s ∧
        physicalDistinguishedPrimeState R q (k + 1) = none then
      physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    else
      0

/-- Arithmetic mean of the six direct inactive-to-active coefficients. -/
def physicalDistinguishedPrimeBMean
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) : ℂ :=
  (∑ t : PrimeActiveLabel, physicalDistinguishedPrimeB R q hq hRq t) / 6

/-- The centered physical inactive-to-active coefficient. -/
def physicalDistinguishedPrimeCenteredB
    (R q : ℕ) (hq : q.Prime) (hRq : R < q)
    (t : PrimeActiveLabel) : ℂ :=
  physicalDistinguishedPrimeB R q hq hRq t -
    physicalDistinguishedPrimeBMean R q hq hRq

/-- Raw-kernel arithmetic identification of the inactive coefficient. -/
@[simp] theorem physicalDistinguishedPrimeRawKernel_none_none
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    physicalDistinguishedPrimeRawKernel R q hq hRq none none =
      physicalDistinguishedPrimeA R q hq hRq := by
  rfl

/-- Raw-kernel arithmetic identification of one inactive-to-active channel. -/
@[simp] theorem physicalDistinguishedPrimeRawKernel_none_some
    (R q : ℕ) (hq : q.Prime) (hRq : R < q)
    (t : PrimeActiveLabel) :
    physicalDistinguishedPrimeRawKernel R q hq hRq none (some t) =
      physicalDistinguishedPrimeB R q hq hRq t := by
  rfl

/-- Raw-kernel arithmetic identification of one active-to-inactive channel. -/
@[simp] theorem physicalDistinguishedPrimeRawKernel_some_none
    (R q : ℕ) (hq : q.Prime) (hRq : R < q)
    (s : PrimeActiveLabel) :
    physicalDistinguishedPrimeRawKernel R q hq hRq (some s) none =
      physicalDistinguishedPrimeC R q hq hRq s := by
  rfl

/-- Package the actual signed physical raw kernel and apply the support-preserving
active-sector centering from the preceding section. -/
def physicalCenteredDistinguishedPrimeOperator
    (R q : ℕ)
    (hq : q.Prime)
    (hRq : R < q) :
    RestrictedPrimeTransitionOperator :=
  (RestrictedPrimeTransitionOperator.ofKernel
    (physicalDistinguishedPrimeRawKernel R q hq hRq)).activeSectorCentered

/-- **Coefficient identification:** centering leaves the explicit arithmetic
`a_{R,q}` unchanged. -/
@[simp] theorem physicalCenteredDistinguishedPrimeOperator_inactiveInactive
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    (physicalCenteredDistinguishedPrimeOperator R q hq hRq).inactiveInactive =
      physicalDistinguishedPrimeA R q hq hRq := by
  change physicalDistinguishedPrimeRawKernel R q hq hRq none none =
    physicalDistinguishedPrimeA R q hq hRq
  exact physicalDistinguishedPrimeRawKernel_none_none R q hq hRq

/-- **Coefficient identification:**
`b^c_{R,q,t} = b_{R,q,t} - (1/6) * sum_u b_{R,q,u}`. -/
@[simp] theorem physicalCenteredDistinguishedPrimeOperator_inactiveToActive
    (R q : ℕ) (hq : q.Prime) (hRq : R < q)
    (t : PrimeActiveLabel) :
    (physicalCenteredDistinguishedPrimeOperator R q hq hRq).inactiveToActive t =
      physicalDistinguishedPrimeCenteredB R q hq hRq t := by
  change
    physicalDistinguishedPrimeRawKernel R q hq hRq none (some t) -
        (∑ u : PrimeActiveLabel,
          physicalDistinguishedPrimeRawKernel R q hq hRq none (some u)) / 6 =
      physicalDistinguishedPrimeCenteredB R q hq hRq t
  unfold physicalDistinguishedPrimeCenteredB physicalDistinguishedPrimeBMean
  rw [physicalDistinguishedPrimeRawKernel_none_some]
  simp_rw [physicalDistinguishedPrimeRawKernel_none_some]

/-- **Coefficient identification:** centering leaves every explicit arithmetic
`c_{R,q,s}` unchanged. -/
@[simp] theorem physicalCenteredDistinguishedPrimeOperator_activeToInactive
    (R q : ℕ) (hq : q.Prime) (hRq : R < q)
    (s : PrimeActiveLabel) :
    (physicalCenteredDistinguishedPrimeOperator R q hq hRq).activeToInactive s =
      physicalDistinguishedPrimeC R q hq hRq s := by
  change physicalDistinguishedPrimeRawKernel R q hq hRq (some s) none =
    physicalDistinguishedPrimeC R q hq hRq s
  exact physicalDistinguishedPrimeRawKernel_some_none R q hq hRq s

/-- The centered physical coefficient family has zero active-destination mean. -/
theorem sum_physicalDistinguishedPrimeCenteredB_eq_zero
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    (∑ t : PrimeActiveLabel,
      physicalDistinguishedPrimeCenteredB R q hq hRq t) = 0 := by
  unfold physicalDistinguishedPrimeCenteredB physicalDistinguishedPrimeBMean
  rw [Finset.sum_sub_distrib, sum_primeActiveLabel_const]
  ring

end RHLean.Analysis