import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery
import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Analysis.SquarePrefixMertensBridge

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-!
# Recovered square-root wheel as the exact Mertens criterion

The arithmetic layer proves that a square-root-covered prime wheel recovers the
joint signed quantity `raw - 2 * smooth` exactly as the Möbius prefix. This
module packages the canonical minimal square-root wheel and shows that a
critical energy estimate for that single signed quantity is exactly the existing
Mertens-energy criterion, hence exactly the square-prefix criterion already used
by the square-block route.

The physical section below additionally instantiates the actual signed
fixed-prime transition data from that same corrected wheel. It reconstructs the
raw physical kernel coefficientwise from the centered operator plus the exact
centering/support corrections, and restores the endpoint cells omitted by the
overlapping adjacent-cell transition representation.

No quantitative estimate is asserted here. No stochastic assumption, asymptotic
cutoff, new axiom, or RH input is used by the reconstruction layer.
-/

/-- The canonical minimal square-root wheel prefix at physical cutoff `X`.
Only prime coordinates through `sqrt X` are used, and the smooth-core correction
is retained inside the signed object. -/
def sqrtWheelRecoveredPrefix (X : ℕ) : ℤ :=
  primeWheelRawPositivePrefix (primesUpTo (Nat.sqrt X)) X -
    2 * primeWheelSmoothPositivePrefix (primesUpTo (Nat.sqrt X)) X X

/-- The canonical prime set through `sqrt X` has exactly the coverage required
by the pointwise prime-wheel recovery theorem. -/
theorem primesUpTo_sqrtCoverage (X : ℕ) :
    PrimeWheelSqrtCoverage (primesUpTo (Nat.sqrt X)) X := by
  intro p hp hple
  exact mem_primesUpTo.mpr ⟨hp, hple⟩

/-- Exact arithmetic recovery for the canonical minimal square-root wheel. -/
theorem sqrtWheelRecoveredPrefix_eq_moebiusPositivePrefix (X : ℕ) :
    sqrtWheelRecoveredPrefix X = moebiusPositivePrefix X := by
  unfold sqrtWheelRecoveredPrefix
  exact primeWheelRaw_sub_two_smooth_eq_moebiusPositivePrefix
    (primesUpTo (Nat.sqrt X)) X X
    (by
      intro p hp
      exact prime_of_mem_primesUpTo hp)
    (primesUpTo_sqrtCoverage X) le_rfl

/-- The canonical recovered wheel is exactly the repository's standard integer
Möbius prefix. -/
theorem sqrtWheelRecoveredPrefix_eq_moebiusPrefix (X : ℕ) :
    sqrtWheelRecoveredPrefix X =
      ∑ n ∈ Finset.range (X + 1), μ n := by
  rw [sqrtWheelRecoveredPrefix_eq_moebiusPositivePrefix,
    moebiusPositivePrefix_eq_moebiusPrefix]

/-- After the harmless integer-to-complex cast, the recovered wheel prefix is
literally the analytic Mertens summatory function used downstream. -/
theorem sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory (X : ℕ) :
    ((sqrtWheelRecoveredPrefix X : ℤ) : ℂ) = mertensSummatory X := by
  rw [sqrtWheelRecoveredPrefix_eq_moebiusPrefix]
  simp [mertensSummatory]

/-- At the exact complete-square endpoint, the recovered minimal square-root
wheel is literally the repository's square-prefix Mertens value. -/
theorem sqrtWheelRecoveredPrefix_cast_eq_squarePrefixMertens
    (n : ℕ) :
    ((sqrtWheelRecoveredPrefix (squarePrefixEndpoint n) : ℤ) : ℂ) =
      squarePrefixMertens n := by
  simpa [squarePrefixMertens] using
    sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory
      (squarePrefixEndpoint n)

/-! ## Exact wheel instantiation of the physical signed fibres -/

/-- Read one physical lower-cofactor weight directly from the corrected minimal
square-root prime wheel at the same physical cutoff. -/
def sqrtWheelCofactorWeight (R c : ℕ) : ℂ :=
  ((correctedPrimeWheelSite
      (primesUpTo (Nat.sqrt (squareRootEndpoint R)))
      (squareRootEndpoint R) c : ℤ) : ℂ)

/-- Every cofactor in the actual physical domain `1 <= c < R` is recovered
exactly as its canonical Möbius weight by the minimal square-root wheel. -/
theorem sqrtWheelCofactorWeight_eq_canonical
    {R c : ℕ}
    (hc : c ∈ Finset.Ico 1 R) :
    sqrtWheelCofactorWeight R c = canonicalMoebiusWeight c := by
  have hcData := Finset.mem_Ico.mp hc
  have hcPos : 0 < c := by omega
  have hR2 : 2 ≤ R := by omega
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hcX : c ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hmu :
      correctedPrimeWheelSite
          (primesUpTo (Nat.sqrt (squareRootEndpoint R)))
          (squareRootEndpoint R) c =
        μ c := by
    exact correctedPrimeWheelSite_eq_moebius
      (primesUpTo (Nat.sqrt (squareRootEndpoint R)))
      (by
        intro p hp
        exact prime_of_mem_primesUpTo hp)
      (primesUpTo_sqrtCoverage (squareRootEndpoint R))
      hcPos hcX
  simp [sqrtWheelCofactorWeight, canonicalMoebiusWeight, hmu]

/-- The physical cell fibre written with the actual corrected square-root wheel
instead of an already-named Möbius weight. -/
def sqrtWheelPhysicalCellFibreMass
    (R q k : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    if c * q ≤ squareRootEndpoint R ∧
        ∃ i : Fin 3, c * q = threeSlotValue k i then
      sqrtWheelCofactorWeight R c
    else
      0

/-- The wheel-explicit cell fibre is coefficient-for-coefficient the existing
physical signed cofactor fibre. -/
theorem sqrtWheelPhysicalCellFibreMass_eq_physical
    (R q k : ℕ) :
    sqrtWheelPhysicalCellFibreMass R q k =
      physicalDistinguishedPrimeCellFibreMass R q k := by
  classical
  unfold sqrtWheelPhysicalCellFibreMass
    physicalDistinguishedPrimeCellFibreMass
  apply Finset.sum_congr rfl
  intro c hc
  rw [sqrtWheelCofactorWeight_eq_canonical hc]

/-- The wheel-explicit signed mass on one adjacent six-site physical transition. -/
def sqrtWheelPhysicalLocalTransitionFibreMass
    (R q k : ℕ) : ℂ :=
  sqrtWheelPhysicalCellFibreMass R q k +
    sqrtWheelPhysicalCellFibreMass R q (k + 1)

/-- The local adjacent-transition mass is therefore exactly the physical one. -/
theorem sqrtWheelPhysicalLocalTransitionFibreMass_eq_physical
    (R q k : ℕ) :
    sqrtWheelPhysicalLocalTransitionFibreMass R q k =
      physicalDistinguishedPrimeLocalTransitionFibreMass R q k := by
  simp [sqrtWheelPhysicalLocalTransitionFibreMass,
    physicalDistinguishedPrimeLocalTransitionFibreMass,
    sqrtWheelPhysicalCellFibreMass_eq_physical]

/-- One fixed-prime transition class, with the actual physical signed state
labels but wheel-explicit cofactor weights. -/
def sqrtWheelPhysicalTransitionMass
    (R q : ℕ) (s t : SignedPrimeHitState) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    if physicalDistinguishedPrimeState R q k = s ∧
        physicalDistinguishedPrimeState R q (k + 1) = t then
      sqrtWheelPhysicalLocalTransitionFibreMass R q k
    else
      0

/-- Every wheel-explicit transition coefficient is exactly the corresponding
physical signed transition coefficient. -/
theorem sqrtWheelPhysicalTransitionMass_eq_physical
    (R q : ℕ) (s t : SignedPrimeHitState) :
    sqrtWheelPhysicalTransitionMass R q s t =
      physicalDistinguishedPrimeTransitionMass R q s t := by
  classical
  unfold sqrtWheelPhysicalTransitionMass
    physicalDistinguishedPrimeTransitionMass
  apply Finset.sum_congr rfl
  intro k hk
  rw [sqrtWheelPhysicalLocalTransitionFibreMass_eq_physical]

/-- Raw fixed-prime kernel instantiated directly from the minimal square-root
wheel and the actual physical signed-state field. -/
def sqrtWheelPhysicalRawKernel
    (R q : ℕ) : SignedPrimeHitState → SignedPrimeHitState → ℂ :=
  fun s t => sqrtWheelPhysicalTransitionMass R q s t

/-- The wheel-instantiated raw kernel is literally the repository's physical
raw kernel; primality and scale hypotheses are used only to match its API, not
to prove the arithmetic equality. -/
theorem sqrtWheelPhysicalRawKernel_eq_physical
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    sqrtWheelPhysicalRawKernel R q =
      physicalDistinguishedPrimeRawKernel R q hq hRq := by
  funext s t
  exact sqrtWheelPhysicalTransitionMass_eq_physical R q s t

/-! ## Coefficientwise restoration of the centered physical channel -/

/-- Restore exactly the information removed when the raw physical kernel is
packaged into the restricted centered operator.

The inactive-to-active row mean is reinserted coefficientwise. The
active-to-active entry is retained directly from the actual physical transition
mass, so this definition remains exact at the finitely many small scales where
the thirteen-entry support theorem is not available. -/
def physicalCenteredDistinguishedPrimeRestoredKernel
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    SignedPrimeHitState → SignedPrimeHitState → ℂ
  | none, none =>
      (physicalCenteredDistinguishedPrimeOperator R q hq hRq).inactiveInactive
  | none, some t =>
      (physicalCenteredDistinguishedPrimeOperator R q hq hRq).inactiveToActive t +
        physicalDistinguishedPrimeBMean R q hq hRq
  | some s, none =>
      (physicalCenteredDistinguishedPrimeOperator R q hq hRq).activeToInactive s
  | some s, some t =>
      physicalDistinguishedPrimeTransitionMass R q (some s) (some t)

/-- **Exact physical-state reconstruction at fixed prime.** The centered channel
plus its explicit deterministic corrections is coefficient-for-coefficient the
actual raw signed physical kernel. No support cutoff or estimate is used. -/
theorem physicalCenteredDistinguishedPrimeRestoredKernel_eq_raw
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    physicalCenteredDistinguishedPrimeRestoredKernel R q hq hRq =
      physicalDistinguishedPrimeRawKernel R q hq hRq := by
  funext s t
  rcases s with _ | s
  · rcases t with _ | t
    · simp [physicalCenteredDistinguishedPrimeRestoredKernel]
    · simp [physicalCenteredDistinguishedPrimeRestoredKernel,
        physicalDistinguishedPrimeCenteredB]
  · rcases t with _ | t
    · simp [physicalCenteredDistinguishedPrimeRestoredKernel]
    · rfl

/-! ## Global restoration over the actual distinguished-prime family -/

/-- Totalize the restored centered fixed-prime kernel by zero off the actual
square-root distinguished-prime set. -/
def physicalCenteredDistinguishedPrimeRestoredChannel
    (R q : ℕ) : SignedPrimeHitState → SignedPrimeHitState → ℂ :=
  if hq : q ∈ centeredDistinguishedPrimeSet R then
    let hfilter := Finset.mem_filter.mp hq
    let hIoc := Finset.mem_Ioc.mp hfilter.1
    physicalCenteredDistinguishedPrimeRestoredKernel
      R q hfilter.2 hIoc.1
  else
    fun _ _ => 0

/-- Totalize the actual raw physical fixed-prime kernel by zero off the same
square-root distinguished-prime set. -/
def physicalDistinguishedPrimeRawChannel
    (R q : ℕ) : SignedPrimeHitState → SignedPrimeHitState → ℂ :=
  if hq : q ∈ centeredDistinguishedPrimeSet R then
    let hfilter := Finset.mem_filter.mp hq
    let hIoc := Finset.mem_Ioc.mp hfilter.1
    physicalDistinguishedPrimeRawKernel R q hfilter.2 hIoc.1
  else
    fun _ _ => 0

/-- Every totalized restored centered channel is exactly the corresponding
actual raw physical channel. -/
theorem physicalCenteredDistinguishedPrimeRestoredChannel_eq_raw
    (R q : ℕ) :
    physicalCenteredDistinguishedPrimeRestoredChannel R q =
      physicalDistinguishedPrimeRawChannel R q := by
  classical
  by_cases hq : q ∈ centeredDistinguishedPrimeSet R
  · simp [physicalCenteredDistinguishedPrimeRestoredChannel,
      physicalDistinguishedPrimeRawChannel, hq,
      physicalCenteredDistinguishedPrimeRestoredKernel_eq_raw]
  · simp [physicalCenteredDistinguishedPrimeRestoredChannel,
      physicalDistinguishedPrimeRawChannel, hq]

/-- Global restored centered signed kernel, assembled over every actual upper
prime before any norm or Gram contraction is taken. -/
def globalPhysicalCenteredDistinguishedPrimeRestoredKernel
    (R : ℕ) : SignedPrimeHitState → SignedPrimeHitState → ℂ :=
  fun s t =>
    ∑ q ∈ centeredDistinguishedPrimeSet R,
      physicalCenteredDistinguishedPrimeRestoredChannel R q s t

/-- Global actual raw physical signed kernel on the same distinguished-prime
family. -/
def globalPhysicalDistinguishedPrimeRawKernel
    (R : ℕ) : SignedPrimeHitState → SignedPrimeHitState → ℂ :=
  fun s t =>
    ∑ q ∈ centeredDistinguishedPrimeSet R,
      physicalDistinguishedPrimeRawChannel R q s t

/-- **Exact global physical-state reconstruction.** The complete centered
prime-family together with the explicit centering/support corrections is exactly
the actual global raw physical signed state, coefficient by coefficient and
before any norm. -/
theorem globalPhysicalCenteredDistinguishedPrimeRestoredKernel_eq_raw
    (R : ℕ) :
    globalPhysicalCenteredDistinguishedPrimeRestoredKernel R =
      globalPhysicalDistinguishedPrimeRawKernel R := by
  classical
  funext s t
  unfold globalPhysicalCenteredDistinguishedPrimeRestoredKernel
    globalPhysicalDistinguishedPrimeRawKernel
  apply Finset.sum_congr rfl
  intro q hq
  rw [physicalCenteredDistinguishedPrimeRestoredChannel_eq_raw]

/-! ## Exact physical mass reconstruction before centering -/

/-- Total signed mass on all adjacent physical six-site transitions for one
fixed distinguished-prime coordinate. -/
def physicalDistinguishedPrimeTransitionLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    physicalDistinguishedPrimeLocalTransitionFibreMass R q k

/-- Inactive-to-inactive part of the same physical transition ledger. -/
def physicalDistinguishedPrimeInactiveInactiveLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    if physicalDistinguishedPrimeState R q k = none ∧
        physicalDistinguishedPrimeState R q (k + 1) = none then
      physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    else
      0

/-- Inactive-to-active part of the physical transition ledger, retaining the
actual destination state without splitting it into an abstract coefficient
family. -/
def physicalDistinguishedPrimeInactiveToActiveLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    match physicalDistinguishedPrimeState R q k,
        physicalDistinguishedPrimeState R q (k + 1) with
    | none, some _ => physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    | _, _ => 0

/-- Active-to-inactive part of the physical transition ledger. -/
def physicalDistinguishedPrimeActiveToInactiveLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    match physicalDistinguishedPrimeState R q k,
        physicalDistinguishedPrimeState R q (k + 1) with
    | some _, none => physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    | _, _ => 0

/-- Active-to-active mass discarded by the thirteen-coefficient restricted
projection. It vanishes automatically in the large-prime support range, but is
kept here so that the arithmetic reconstruction is exact at every scale. -/
def physicalDistinguishedPrimeActiveActiveLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    match physicalDistinguishedPrimeState R q k,
        physicalDistinguishedPrimeState R q (k + 1) with
    | some _, some _ => physicalDistinguishedPrimeLocalTransitionFibreMass R q k
    | _, _ => 0

/-- The four physical source/destination classes partition the signed adjacent
transition mass exactly, including the small-scale active-to-active defect. -/
theorem physicalDistinguishedPrimeTransitionLedger_partition
    (R q : ℕ) :
    physicalDistinguishedPrimeTransitionLedger R q =
      physicalDistinguishedPrimeInactiveInactiveLedger R q +
        physicalDistinguishedPrimeInactiveToActiveLedger R q +
        physicalDistinguishedPrimeActiveToInactiveLedger R q +
        physicalDistinguishedPrimeActiveActiveLedger R q := by
  classical
  unfold physicalDistinguishedPrimeTransitionLedger
    physicalDistinguishedPrimeInactiveInactiveLedger
    physicalDistinguishedPrimeInactiveToActiveLedger
    physicalDistinguishedPrimeActiveToInactiveLedger
    physicalDistinguishedPrimeActiveActiveLedger
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rcases hs : physicalDistinguishedPrimeState R q k with _ | s <;>
    rcases ht : physicalDistinguishedPrimeState R q (k + 1) with _ | t <;>
    simp

/-- Signed physical cell mass before adjacent cells are overlapped into
transitions. There is one more cell than transition. -/
def physicalDistinguishedPrimeCellLedger
    (R q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R + 1),
    physicalDistinguishedPrimeCellFibreMass R q k

/-- The two endpoint-cell masses needed to invert the adjacent-cell overlap.
When the transition carrier is empty these are the same unique physical cell,
which is intentionally counted twice before division by two. -/
def physicalDistinguishedPrimeBoundaryCellLedger
    (R q : ℕ) : ℂ :=
  physicalDistinguishedPrimeCellFibreMass R q 0 +
    physicalDistinguishedPrimeCellFibreMass R q
      (physicalDistinguishedPrimeCarrierLength R)

/-- **Exact de-overlap identity.** The transition ledger counts every interior
cell twice and each endpoint cell once. Restoring the two endpoint masses gives
twice the actual physical cell ledger. -/
theorem physicalDistinguishedPrimeTransitionLedger_add_boundary_eq_two_cellLedger
    (R q : ℕ) :
    physicalDistinguishedPrimeTransitionLedger R q +
        physicalDistinguishedPrimeBoundaryCellLedger R q =
      2 * physicalDistinguishedPrimeCellLedger R q := by
  let K := physicalDistinguishedPrimeCarrierLength R
  let f : ℕ → ℂ := fun k => physicalDistinguishedPrimeCellFibreMass R q k
  have htail :
      (∑ k ∈ Finset.range (K + 1), f k) =
        (∑ k ∈ Finset.range K, f k) + f K := by
    simpa using (Finset.sum_range_succ f K)
  have hhead :
      (∑ k ∈ Finset.range (K + 1), f k) =
        f 0 + ∑ k ∈ Finset.range K, f (k + 1) := by
    simpa [add_comm] using (Finset.sum_range_succ' f K)
  change
    (∑ k ∈ Finset.range K, (f k + f (k + 1))) + (f 0 + f K) =
      2 * ∑ k ∈ Finset.range (K + 1), f k
  rw [Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range K, f k) +
          (∑ k ∈ Finset.range K, f (k + 1)) + (f 0 + f K) =
        ((∑ k ∈ Finset.range K, f k) + f K) +
          (f 0 + ∑ k ∈ Finset.range K, f (k + 1)) := by ring
    _ = (∑ k ∈ Finset.range (K + 1), f k) +
          ∑ k ∈ Finset.range (K + 1), f k := by
      rw [← htail, ← hhead]
    _ = 2 * ∑ k ∈ Finset.range (K + 1), f k := by ring

/-- Boundary-complete signed mass recovered from the adjacent transition ledger. -/
def physicalDistinguishedPrimeBoundaryCompleteMass
    (R q : ℕ) : ℂ :=
  (physicalDistinguishedPrimeTransitionLedger R q +
      physicalDistinguishedPrimeBoundaryCellLedger R q) / 2

/-- The boundary-complete transition ledger is exactly the actual physical cell
mass; no approximation or normalization remains. -/
theorem physicalDistinguishedPrimeBoundaryCompleteMass_eq_cellLedger
    (R q : ℕ) :
    physicalDistinguishedPrimeBoundaryCompleteMass R q =
      physicalDistinguishedPrimeCellLedger R q := by
  rw [physicalDistinguishedPrimeBoundaryCompleteMass,
    physicalDistinguishedPrimeTransitionLedger_add_boundary_eq_two_cellLedger]
  ring

/-- At `R = 2` there are no adjacent transitions at all. This is the exact
small-scale obstruction to identifying the bare transition operator with the
physical signed state. -/
@[simp] theorem physicalDistinguishedPrimeTransitionLedger_two
    (q : ℕ) :
    physicalDistinguishedPrimeTransitionLedger 2 q = 0 := by
  norm_num [physicalDistinguishedPrimeTransitionLedger,
    physicalDistinguishedPrimeCarrierLength, squareRootEndpoint]

/-- Nevertheless the boundary-complete ledger retains the unique physical cell
at `R = 2`, so the exact signal is not lost. -/
@[simp] theorem physicalDistinguishedPrimeCellLedger_two
    (q : ℕ) :
    physicalDistinguishedPrimeCellLedger 2 q =
      physicalDistinguishedPrimeCellFibreMass 2 q 0 := by
  norm_num [physicalDistinguishedPrimeCellLedger,
    physicalDistinguishedPrimeCarrierLength, squareRootEndpoint]

/-! ## Exact physical fibre equals the prime-dilated transport fibre -/

/-- A cofactor divisible by `4` has zero canonical Möbius weight. -/
private theorem canonicalMoebiusWeight_eq_zero_of_four_dvd
    {c : ℕ} (h4 : 4 ∣ c) :
    canonicalMoebiusWeight c = 0 := by
  have hmu : μ c = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hsq
    have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
    apply hnot
    simpa using h4
  simp [canonicalMoebiusWeight, hmu]

/-- For an odd prime, a factor `4` in `c*q` must already occur in the cofactor. -/
private theorem four_dvd_cofactor_of_four_dvd_mul_prime
    {c q : ℕ} (hq : q.Prime) (hq2 : 2 < q)
    (h4 : 4 ∣ c * q) :
    4 ∣ c := by
  have hne : 2 ≠ q := by omega
  have hcop : Nat.Coprime 4 q := by
    simpa using
      (Nat.coprime_pow_primes (p := 2) (q := q) 2 1
        Nat.prime_two hq hne)
  exact hcop.dvd_of_dvd_mul_right h4

/-- Two active three-slot values can represent the same integer only when they
come from the same four-cell. -/
private theorem threeSlotValue_cell_index_unique
    {k l : ℕ} {i j : Fin 3}
    (h : threeSlotValue k i = threeSlotValue l j) :
    k = l := by
  unfold threeSlotValue at h
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- Every positive non-multiple of `4` below the square endpoint lies in exactly
one of the physical three-slot cells retained by the carrier. The proof uses the
fact that a square endpoint minus one has residue `0` or `3` modulo `4`. -/
private theorem exists_physical_threeSlot_of_le_endpoint_of_not_four_dvd
    {R n : ℕ}
    (hR : 2 ≤ R) (_hnPos : 0 < n)
    (hnX : n ≤ squareRootEndpoint R)
    (h4 : ¬4 ∣ n) :
    ∃ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R + 1),
      ∃ i : Fin 3, n = threeSlotValue k i := by
  have hmod0 : n % 4 ≠ 0 := by
    intro hz
    exact h4 (Nat.dvd_of_mod_eq_zero hz)
  have hmodlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  have hklt :
      n / 4 < physicalDistinguishedPrimeCarrierLength R + 1 := by
    rcases Nat.even_or_odd' R with ⟨a, hRa | hRa⟩
    · have ha : 1 ≤ a := by omega
      let A := a * a
      have hA : 1 ≤ A := by
        dsimp [A]
        nlinarith
      have hsquare : (2 * a) ^ 2 = 4 * A := by
        dsimp [A]
        ring
      have hcarrier :
          physicalDistinguishedPrimeCarrierLength R + 1 = A := by
        rw [hRa]
        unfold physicalDistinguishedPrimeCarrierLength squareRootEndpoint
        rw [hsquare]
        omega
      have hnlt : n < A * 4 := by
        rw [hRa] at hnX
        unfold squareRootEndpoint at hnX
        rw [hsquare] at hnX
        omega
      rw [hcarrier]
      exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).2 hnlt
    · have ha : 1 ≤ a := by omega
      let A := a * (a + 1)
      have hA : 1 ≤ A := by
        dsimp [A]
        nlinarith
      have hsquare : (2 * a + 1) ^ 2 = 4 * A + 1 := by
        dsimp [A]
        ring
      have hcarrier :
          physicalDistinguishedPrimeCarrierLength R + 1 = A := by
        rw [hRa]
        unfold physicalDistinguishedPrimeCarrierLength squareRootEndpoint
        rw [hsquare]
        omega
      have hnlt : n < A * 4 := by
        rw [hRa] at hnX
        unfold squareRootEndpoint at hnX
        rw [hsquare] at hnX
        have hne : n ≠ 4 * A := by
          intro heq
          apply h4
          exact ⟨A, heq⟩
        omega
      rw [hcarrier]
      exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).2 hnlt
  have hkMem :
      n / 4 ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R + 1) :=
    Finset.mem_range.mpr hklt
  have hdiv := Nat.div_add_mod n 4
  have hres : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hres with h1 | h2 | h3
  · refine ⟨n / 4, hkMem, (0 : Fin 3), ?_⟩
    unfold threeSlotValue
    omega
  · refine ⟨n / 4, hkMem, (1 : Fin 3), ?_⟩
    unfold threeSlotValue
    omega
  · refine ⟨n / 4, hkMem, (2 : Fin 3), ?_⟩
    unfold threeSlotValue
    omega

/-- For one actual distinguished prime and one lower cofactor, summing the cell
indicator over the physical carrier returns exactly the prime-dilated fibre
summand. Multiples of `4` are the only omitted sites, and their Möbius weight is
zero. -/
private theorem sum_physicalCellFibre_indicator_eq_primeDilated_summand
    (R q c : ℕ) (hq : q.Prime) (hRq : R < q)
    (hc : c ∈ Finset.Ico 1 R) :
    (∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R + 1),
      if c * q ≤ squareRootEndpoint R ∧
          ∃ i : Fin 3, c * q = threeSlotValue k i then
        canonicalMoebiusWeight c
      else
        0) =
      if c * q ≤ squareRootEndpoint R then canonicalMoebiusWeight c else 0 := by
  classical
  by_cases hmul : c * q ≤ squareRootEndpoint R
  · rw [if_pos hmul]
    by_cases hweight : canonicalMoebiusWeight c = 0
    · simp [hmul, hweight]
    · have hcData := Finset.mem_Ico.mp hc
      have hR2 : 2 ≤ R := by omega
      have hq2 : 2 < q := by omega
      have hfour : ¬4 ∣ c * q := by
        intro h4prod
        have h4c : 4 ∣ c :=
          four_dvd_cofactor_of_four_dvd_mul_prime hq hq2 h4prod
        exact hweight (canonicalMoebiusWeight_eq_zero_of_four_dvd h4c)
      have hnPos : 0 < c * q := by
        exact Nat.mul_pos (by omega) (by omega)
      rcases exists_physical_threeSlot_of_le_endpoint_of_not_four_dvd
          hR2 hnPos hmul hfour with ⟨k, hk, i, hi⟩
      have hexk : ∃ j : Fin 3, c * q = threeSlotValue k j := ⟨i, hi⟩
      rw [Finset.sum_eq_single k]
      · simp [hmul, hexk]
      · intro l hl hlk
        by_cases hexl : ∃ j : Fin 3, c * q = threeSlotValue l j
        · rcases hexl with ⟨j, hj⟩
          have hlk' : l = k :=
            threeSlotValue_cell_index_unique (hj.symm.trans hi)
          exact (hlk hlk').elim
        · simp [hmul, hexl]
      · exact (fun hk' => (hk' hk).elim)
  · simp [hmul]

/-- **Missing fixed-fibre equality.** For every actual distinguished prime
`q > R`, the boundary-complete physical cell ledger is exactly the existing
prime-dilated low-cofactor mass. -/
theorem physicalDistinguishedPrimeCellLedger_eq_primeDilatedLowCofactorMass
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    physicalDistinguishedPrimeCellLedger R q =
      primeDilatedLowCofactorMass R q := by
  classical
  unfold physicalDistinguishedPrimeCellLedger
    physicalDistinguishedPrimeCellFibreMass
    primeDilatedLowCofactorMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  exact sum_physicalCellFibre_indicator_eq_primeDilated_summand
    R q c hq hRq hc

/-- Boundary-complete transition mass is therefore literally the existing
prime-dilated transport fibre. -/
theorem physicalDistinguishedPrimeBoundaryCompleteMass_eq_primeDilatedLowCofactorMass
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    physicalDistinguishedPrimeBoundaryCompleteMass R q =
      primeDilatedLowCofactorMass R q := by
  rw [physicalDistinguishedPrimeBoundaryCompleteMass_eq_cellLedger]
  exact physicalDistinguishedPrimeCellLedger_eq_primeDilatedLowCofactorMass
    R q hq hRq

/-- The physical fixed-prime fibre is the boundary-complete signed mass. -/
def physicalDistinguishedPrimeFibre (R q : ℕ) : ℂ :=
  physicalDistinguishedPrimeBoundaryCompleteMass R q

/-- One actual physical fibre is exactly one prime-first transport fibre. -/
theorem physicalDistinguishedPrimeFibre_eq_primeDilatedLowCofactorMass
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    physicalDistinguishedPrimeFibre R q =
      primeDilatedLowCofactorMass R q := by
  exact physicalDistinguishedPrimeBoundaryCompleteMass_eq_primeDilatedLowCofactorMass
    R q hq hRq

/-- **Exact fibre sum.** Summing the boundary-complete physical fibres over the
actual distinguished-prime family is exactly the repository's prime-first
square-root transport term. -/
theorem sum_physicalDistinguishedPrimeFibre_eq_squareRootTransportPrimeFirst
    (R : ℕ) :
    (∑ q ∈ centeredDistinguishedPrimeSet R,
      physicalDistinguishedPrimeFibre R q) =
      squareRootTransportPrimeFirst R := by
  classical
  unfold centeredDistinguishedPrimeSet squareRootTransportPrimeFirst
    physicalDistinguishedPrimeFibre
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hqRange
  by_cases hq : q.Prime
  · have hRq : R < q := (Finset.mem_Ioc.mp hqRange).1
    simp [hq,
      physicalDistinguishedPrimeBoundaryCompleteMass_eq_primeDilatedLowCofactorMass
        R q hq hRq]
  · simp [hq]

/-- Global boundary-complete physical transport mass. -/
def globalPhysicalDistinguishedPrimeFibreMass (R : ℕ) : ℂ :=
  ∑ q ∈ centeredDistinguishedPrimeSet R,
    physicalDistinguishedPrimeFibre R q

/-- The global physical fibre mass is exactly the prime-first transport signal. -/
theorem globalPhysicalDistinguishedPrimeFibreMass_eq_squareRootTransportPrimeFirst
    (R : ℕ) :
    globalPhysicalDistinguishedPrimeFibreMass R =
      squareRootTransportPrimeFirst R := by
  exact sum_physicalDistinguishedPrimeFibre_eq_squareRootTransportPrimeFirst R

/-- **Completed exact physical reconstruction.** The centered distinguished-prime
family, after restoring only the explicitly removed deterministic pieces, is the
actual raw signed physical kernel; simultaneously its boundary-complete scalar
fibre mass is exactly the existing prime-first square-root transport signal.
Thus signal reconstruction is complete before any energy or Gram estimate. -/
theorem globalPhysicalCenteredDistinguishedPrime_exact_reconstruction
    (R : ℕ) :
    globalPhysicalCenteredDistinguishedPrimeRestoredKernel R =
        globalPhysicalDistinguishedPrimeRawKernel R ∧
      globalPhysicalDistinguishedPrimeFibreMass R =
        squareRootTransportPrimeFirst R := by
  exact ⟨globalPhysicalCenteredDistinguishedPrimeRestoredKernel_eq_raw R,
    globalPhysicalDistinguishedPrimeFibreMass_eq_squareRootTransportPrimeFirst R⟩

/-! ## Exact square-root wheel energy target -/

/-- The exact quantitative target for the canonical square-root wheel. This is
the squared form of the desired `X^(1/2+ε)` cancellation, expressed without
splitting raw and smooth mass. -/
def SqrtWheelRecoveredEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ,
        ‖((sqrtWheelRecoveredPrefix X : ℤ) : ℂ)‖ ^ 2 ≤
          C * Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)

/-- The recovered square-root wheel estimate is exactly the protected global
Mertens-energy criterion. Thus proving the former loses no cancellation and
requires no additional analytic transfer theorem. -/
theorem sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded :
    SqrtWheelRecoveredEnergyBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro X
    have hx := hbound X
    rw [sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory X] at hx
    exact hx
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro X
    rw [sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory X]
    exact hbound X

/-- The same target is therefore exactly equivalent to the repository's
square-prefix energy criterion. This is the formal square-block compatibility
statement for the recovered prime-wheel quantity. -/
theorem sqrtWheelRecoveredEnergyBounded_iff_squarePrefixEnergyBounded :
    SqrtWheelRecoveredEnergyBoundedStatement ↔
      SquarePrefixEnergyBoundedStatement := by
  exact sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded.trans
    mertensEnergyBounded_iff_squarePrefixEnergyBounded

/-- The existing Mertens continuation and completed-zeta reflection route turns
a proof of the recovered square-root wheel bound directly into RH. -/
theorem riemannHypothesis_of_sqrtWheelRecoveredEnergy
    (h : SqrtWheelRecoveredEnergyBoundedStatement) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  exact sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded.mp h

end RHLean.Analysis
