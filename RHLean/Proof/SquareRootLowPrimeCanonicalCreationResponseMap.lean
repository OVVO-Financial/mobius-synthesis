import Mathlib
import RHLean.Proof.SquareRootLowPrimeEulerCreationResponseEnergyGate

/-!
# Canonical fresh-prime creation-to-response map

A non-head creation state is matched when at least one actual fresh prime
`K < p <= U` sends its absolute response seat to the deep response carrier.
The canonical owner is the least such prime.

Every source cofactor has largest prime at most `K`, while every owner is a
prime strictly above `K`. Hence the owner is fresh and becomes the canonical
largest prime of the target cofactor `p*c`. Equality of two targets therefore
recovers the owner prime, then the source cofactor, and finally the tagged local
seat. The map is globally injective.

This discharges the map, sign, freshness, membership, and injectivity hypotheses
of the Eulerian energy gate. The only remaining quantitative input is an
`R`-by-`B` owner for the tagged unmatched creation and response frontiers.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Fresh primes that carry one creation state to an admitted deep response
seat. -/
def squareRootLowPrimeEligibleResponseOwners
    (R K j U : ℕ) (x : SquareRootLowPrimeCreationState) : Finset ℕ :=
  (squareRootLowPrimeFreshPrimeSet K U).filter fun p =>
    (p * squareRootLowPrimeCreationStateCofactor x,
      squareRootLowPrimeCreationStateAbsoluteSeat R x) ∈
        squareRootLowPrimeOwnedResponseSeatCarrier R K j U

/-- Least eligible fresh-prime owner, with the irrelevant default `1` on an
unmatched state. -/
def squareRootLowPrimeCanonicalResponseOwner
    (R K j U : ℕ) (x : SquareRootLowPrimeCreationState) : ℕ :=
  if h : (squareRootLowPrimeEligibleResponseOwners R K j U x).Nonempty then
    (squareRootLowPrimeEligibleResponseOwners R K j U x).min' h
  else 1

/-- Creation states having at least one admitted deep response extension. -/
def squareRootLowPrimeMatchedCreationStates
    (R K j U : ℕ) : Finset SquareRootLowPrimeCreationState :=
  (squareRootLowPrimeCreationCarrierExact R K j).filter fun x =>
    x ≠ none ∧
      (squareRootLowPrimeEligibleResponseOwners R K j U x).Nonempty

/-- Canonical creation-to-response map. -/
def squareRootLowPrimeCanonicalCreationToResponse
    (R K j U : ℕ) (x : SquareRootLowPrimeCreationState) : ℕ × ℕ :=
  squareRootLowPrimeCreationToResponseSeat R
    (squareRootLowPrimeCanonicalResponseOwner R K j U) x

@[simp] theorem mem_squareRootLowPrimeEligibleResponseOwners
    {R K j U p : ℕ} {x : SquareRootLowPrimeCreationState} :
    p ∈ squareRootLowPrimeEligibleResponseOwners R K j U x ↔
      p ∈ squareRootLowPrimeFreshPrimeSet K U ∧
        (p * squareRootLowPrimeCreationStateCofactor x,
          squareRootLowPrimeCreationStateAbsoluteSeat R x) ∈
            squareRootLowPrimeOwnedResponseSeatCarrier R K j U := by
  simp [squareRootLowPrimeEligibleResponseOwners]

@[simp] theorem mem_squareRootLowPrimeMatchedCreationStates
    {R K j U : ℕ} {x : SquareRootLowPrimeCreationState} :
    x ∈ squareRootLowPrimeMatchedCreationStates R K j U ↔
      x ∈ squareRootLowPrimeCreationCarrierExact R K j ∧
        x ≠ none ∧
          (squareRootLowPrimeEligibleResponseOwners R K j U x).Nonempty := by
  simp [squareRootLowPrimeMatchedCreationStates]

/-- Data carried by a born seat atom. -/
theorem squareRootLowPrimeShallowBornSeatAtom_data
    {R K : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeShallowBornSeatAtoms R K) :
    z.1 ∈ squareRootLowPrimeShallowBornCofactors R K ∧
      z.2 < squareRootBornPartnerCount R z.1 := by
  unfold squareRootLowPrimeShallowBornSeatAtoms at hz
  rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
  have hdata := mem_squareRootLowPrimeShallowBornSeatFiber.mp hzc
  rw [hdata.1]
  exact ⟨hc, hdata.2⟩

/-- Data carried by a high seat atom. -/
theorem squareRootLowPrimeShallowHighSeatAtom_data
    {R K j : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeShallowHighSeatAtoms R K j) :
    z.1 ∈ squareRootLowPrimeShallowHighCofactors R K ∧
      z.2 < squareRootBornPostTailHighResponse R K j z.1 := by
  unfold squareRootLowPrimeShallowHighSeatAtoms at hz
  rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
  have hdata := mem_squareRootLowPrimeShallowHighSeatFiber.mp hzc
  rw [hdata.1]
  exact ⟨hc, hdata.2⟩

/-- Non-head membership in the creation carrier is exactly a tagged born or
high seat. -/
theorem squareRootLowPrimeCreationCarrierExact_nonhead_cases
    {R K j : ℕ} {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ squareRootLowPrimeCreationCarrierExact R K j)
    (hnone : x ≠ none) :
    (∃ z ∈ squareRootLowPrimeShallowBornSeatAtoms R K,
        x = some (Sum.inl z)) ∨
      ∃ z ∈ squareRootLowPrimeShallowHighSeatAtoms R K j,
        x = some (Sum.inr z) := by
  unfold squareRootLowPrimeCreationCarrierExact at hx
  rcases Finset.mem_insert.mp hx with hxHead | hxSeats
  · exact (hnone hxHead).elim
  · rcases Finset.mem_union.mp hxSeats with hxBorn | hxHigh
    · rcases Finset.mem_image.mp hxBorn with ⟨z, hz, hzx⟩
      exact Or.inl ⟨z, hz, hzx.symm⟩
    · rcases Finset.mem_image.mp hxHigh with ⟨z, hz, hzx⟩
      exact Or.inr ⟨z, hz, hzx.symm⟩

/-- Every non-head creation cofactor is positive, has all prime factors at most
`K`, and has nonzero Möbius weight. -/
theorem squareRootLowPrimeCreationStateCofactor_data
    {R K j : ℕ} {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ squareRootLowPrimeCreationCarrierExact R K j)
    (hnone : x ≠ none) :
    0 < squareRootLowPrimeCreationStateCofactor x ∧
      canonicalLargestPrimeFactor
        (squareRootLowPrimeCreationStateCofactor x) ≤ K ∧
      μ (squareRootLowPrimeCreationStateCofactor x) ≠ 0 := by
  rcases squareRootLowPrimeCreationCarrierExact_nonhead_cases hx hnone with
    ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
  · have hdata := squareRootLowPrimeShallowBornSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    rcases Finset.mem_Icc.mp hc.1 with ⟨hcOne, _hcTop⟩
    change 0 < z.1 ∧ canonicalLargestPrimeFactor z.1 ≤ K ∧ μ z.1 ≠ 0
    exact ⟨by omega, hc.2.1, hc.2.2⟩
  · have hdata := squareRootLowPrimeShallowHighSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    rcases Finset.mem_Icc.mp hc.1 with ⟨hcOne, _hcTop⟩
    change 0 < z.1 ∧ canonicalLargestPrimeFactor z.1 ≤ K ∧ μ z.1 ≠ 0
    exact ⟨by omega, hc.2.1, hc.2.2⟩

/-- The pair `(source cofactor, absolute seat)` recovers every non-head creation
state. -/
theorem squareRootLowPrimeCreationState_cofactorSeat_injOn
    (R K j : ℕ) :
    Set.InjOn
      (fun x : SquareRootLowPrimeCreationState =>
        (squareRootLowPrimeCreationStateCofactor x,
          squareRootLowPrimeCreationStateAbsoluteSeat R x))
      ((squareRootLowPrimeCreationCarrierExact R K j).erase none) := by
  intro x hx y hy hxy
  have hxCarrier := (Finset.mem_erase.mp hx).2
  have hyCarrier := (Finset.mem_erase.mp hy).2
  have hxNone : x ≠ none := (Finset.mem_erase.mp hx).1
  have hyNone : y ≠ none := (Finset.mem_erase.mp hy).1
  rcases squareRootLowPrimeCreationCarrierExact_nonhead_cases
      hxCarrier hxNone with
    ⟨zx, hzx, rfl⟩ | ⟨zx, hzx, rfl⟩ <;>
  rcases squareRootLowPrimeCreationCarrierExact_nonhead_cases
      hyCarrier hyNone with
    ⟨zy, hzy, rfl⟩ | ⟨zy, hzy, rfl⟩
  · have hc : zx.1 = zy.1 := by
      simpa [squareRootLowPrimeCreationStateCofactor] using
        congrArg (fun w : ℕ × ℕ => w.1) hxy
    have hs : zx.2 = zy.2 := by
      simpa [squareRootLowPrimeCreationStateAbsoluteSeat] using
        congrArg (fun w : ℕ × ℕ => w.2) hxy
    exact congrArg (fun z => some (Sum.inl z)) (Prod.ext hc hs)
  · have hxData := squareRootLowPrimeShallowBornSeatAtom_data hzx
    have hc : zx.1 = zy.1 := by
      simpa [squareRootLowPrimeCreationStateCofactor] using
        congrArg (fun w : ℕ × ℕ => w.1) hxy
    have hs :
        zx.2 = squareRootBornPartnerCount R zy.1 + zy.2 := by
      simpa [squareRootLowPrimeCreationStateAbsoluteSeat] using
        congrArg (fun w : ℕ × ℕ => w.2) hxy
    have hzxBound := hxData.2
    rw [hc] at hzxBound
    omega
  · have hyData := squareRootLowPrimeShallowBornSeatAtom_data hzy
    have hc : zx.1 = zy.1 := by
      simpa [squareRootLowPrimeCreationStateCofactor] using
        congrArg (fun w : ℕ × ℕ => w.1) hxy
    have hs :
        squareRootBornPartnerCount R zx.1 + zx.2 = zy.2 := by
      simpa [squareRootLowPrimeCreationStateAbsoluteSeat] using
        congrArg (fun w : ℕ × ℕ => w.2) hxy
    have hzyBound := hyData.2
    rw [← hc] at hzyBound
    omega
  · have hc : zx.1 = zy.1 := by
      simpa [squareRootLowPrimeCreationStateCofactor] using
        congrArg (fun w : ℕ × ℕ => w.1) hxy
    have hs :
        squareRootBornPartnerCount R zx.1 + zx.2 =
          squareRootBornPartnerCount R zy.1 + zy.2 := by
      simpa [squareRootLowPrimeCreationStateAbsoluteSeat] using
        congrArg (fun w : ℕ × ℕ => w.2) hxy
    rw [hc] at hs
    have hseat : zx.2 = zy.2 := by omega
    exact congrArg (fun z => some (Sum.inr z)) (Prod.ext hc hseat)

/-- The canonical owner belongs to the eligible-prime set on every matched
creation state. -/
theorem squareRootLowPrimeCanonicalResponseOwner_mem_eligible
    {R K j U : ℕ} {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ squareRootLowPrimeMatchedCreationStates R K j U) :
    squareRootLowPrimeCanonicalResponseOwner R K j U x ∈
      squareRootLowPrimeEligibleResponseOwners R K j U x := by
  have hne := (mem_squareRootLowPrimeMatchedCreationStates.mp hx).2.2
  unfold squareRootLowPrimeCanonicalResponseOwner
  rw [dif_pos hne]
  exact Finset.min'_mem _ hne

/-- Canonical owner data. -/
theorem squareRootLowPrimeCanonicalResponseOwner_data
    {R K j U : ℕ} {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ squareRootLowPrimeMatchedCreationStates R K j U) :
    K < squareRootLowPrimeCanonicalResponseOwner R K j U x ∧
      squareRootLowPrimeCanonicalResponseOwner R K j U x ≤ U ∧
      (squareRootLowPrimeCanonicalResponseOwner R K j U x).Prime := by
  have hmem := squareRootLowPrimeCanonicalResponseOwner_mem_eligible hx
  have hfresh := (mem_squareRootLowPrimeEligibleResponseOwners.mp hmem).1
  have hdata := Finset.mem_filter.mp hfresh
  have hIoc := Finset.mem_Ioc.mp hdata.1
  exact ⟨hIoc.1, hIoc.2, hdata.2⟩

/-- A prime strictly above the largest prime factor of a positive cofactor does
not divide it. -/
theorem prime_not_dvd_of_canonicalLargestPrimeFactor_lt
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    ¬ p ∣ c := by
  intro hdiv
  by_cases hcOne : c = 1
  · subst c
    exact hp.not_dvd_one hdiv
  · have hcGt : 1 < c := by omega
    have hmem : p ∈ c.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdiv, by omega⟩
    have hle : p ≤ canonicalLargestPrimeFactor c := by
      unfold canonicalLargestPrimeFactor
      rw [dif_pos hcGt]
      exact Finset.le_max' c.primeFactors p hmem
    omega

/-- Every canonical owner is genuinely fresh for its source cofactor. -/
theorem squareRootLowPrimeCanonicalResponseOwner_fresh
    {R K j U : ℕ} {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ squareRootLowPrimeMatchedCreationStates R K j U) :
    ¬ squareRootLowPrimeCanonicalResponseOwner R K j U x ∣
      squareRootLowPrimeCreationStateCofactor x := by
  have hxData := mem_squareRootLowPrimeMatchedCreationStates.mp hx
  have hcData := squareRootLowPrimeCreationStateCofactor_data
    hxData.1 hxData.2.1
  have hpData := squareRootLowPrimeCanonicalResponseOwner_data hx
  apply prime_not_dvd_of_canonicalLargestPrimeFactor_lt
    hcData.1 hpData.2.2
  exact lt_of_le_of_lt hcData.2.1 hpData.1

/-- The canonical map lands in the deep response carrier by construction. -/
theorem squareRootLowPrimeCanonicalCreationToResponse_mem
    {R K j U : ℕ} {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ squareRootLowPrimeMatchedCreationStates R K j U) :
    squareRootLowPrimeCanonicalCreationToResponse R K j U x ∈
      squareRootLowPrimeOwnedResponseSeatCarrier R K j U := by
  have hmem := squareRootLowPrimeCanonicalResponseOwner_mem_eligible hx
  exact (mem_squareRootLowPrimeEligibleResponseOwners.mp hmem).2

/-- **Global injectivity of the canonical creation-to-response map.** -/
theorem squareRootLowPrimeCanonicalCreationToResponse_injOn
    {R K j U : ℕ} :
    Set.InjOn (squareRootLowPrimeCanonicalCreationToResponse R K j U)
      (squareRootLowPrimeMatchedCreationStates R K j U) := by
  intro x hx y hy hxy
  have hxData := mem_squareRootLowPrimeMatchedCreationStates.mp hx
  have hyData := mem_squareRootLowPrimeMatchedCreationStates.mp hy
  have hcx := squareRootLowPrimeCreationStateCofactor_data
    hxData.1 hxData.2.1
  have hcy := squareRootLowPrimeCreationStateCofactor_data
    hyData.1 hyData.2.1
  have hpx := squareRootLowPrimeCanonicalResponseOwner_data hx
  have hpy := squareRootLowPrimeCanonicalResponseOwner_data hy
  have hroughX :
      canonicalLargestPrimeFactor
          (squareRootLowPrimeCreationStateCofactor x) <
        squareRootLowPrimeCanonicalResponseOwner R K j U x :=
    lt_of_le_of_lt hcx.2.1 hpx.1
  have hroughY :
      canonicalLargestPrimeFactor
          (squareRootLowPrimeCreationStateCofactor y) <
        squareRootLowPrimeCanonicalResponseOwner R K j U y :=
    lt_of_le_of_lt hcy.2.1 hpy.1
  have hlpfX :
      canonicalLargestPrimeFactor
        (squareRootLowPrimeCanonicalResponseOwner R K j U x *
          squareRootLowPrimeCreationStateCofactor x) =
        squareRootLowPrimeCanonicalResponseOwner R K j U x := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        hcx.1 hpx.2.2 hroughX
  have hlpfY :
      canonicalLargestPrimeFactor
        (squareRootLowPrimeCanonicalResponseOwner R K j U y *
          squareRootLowPrimeCreationStateCofactor y) =
        squareRootLowPrimeCanonicalResponseOwner R K j U y := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        hcy.1 hpy.2.2 hroughY
  have hprod :
      squareRootLowPrimeCanonicalResponseOwner R K j U x *
          squareRootLowPrimeCreationStateCofactor x =
        squareRootLowPrimeCanonicalResponseOwner R K j U y *
          squareRootLowPrimeCreationStateCofactor y := by
    simpa [squareRootLowPrimeCanonicalCreationToResponse,
      squareRootLowPrimeCreationToResponseSeat] using
      congrArg (fun z : ℕ × ℕ => z.1) hxy
  have hpEq :
      squareRootLowPrimeCanonicalResponseOwner R K j U x =
        squareRootLowPrimeCanonicalResponseOwner R K j U y := by
    rw [← hlpfX, ← hlpfY]
    exact congrArg canonicalLargestPrimeFactor hprod
  have hcEq :
      squareRootLowPrimeCreationStateCofactor x =
        squareRootLowPrimeCreationStateCofactor y := by
    rw [hpEq] at hprod
    exact Nat.mul_left_cancel hpy.2.2.pos hprod
  have hsEq :
      squareRootLowPrimeCreationStateAbsoluteSeat R x =
        squareRootLowPrimeCreationStateAbsoluteSeat R y := by
    simpa [squareRootLowPrimeCanonicalCreationToResponse,
      squareRootLowPrimeCreationToResponseSeat] using
      congrArg (fun z : ℕ × ℕ => z.2) hxy
  have hxErase :
      x ∈ (squareRootLowPrimeCreationCarrierExact R K j).erase none :=
    Finset.mem_erase.mpr ⟨hxData.2.1, hxData.1⟩
  have hyErase :
      y ∈ (squareRootLowPrimeCreationCarrierExact R K j).erase none :=
    Finset.mem_erase.mpr ⟨hyData.2.1, hyData.1⟩
  exact squareRootLowPrimeCreationState_cofactorSeat_injOn R K j
    hxErase hyErase (Prod.ext hcEq hsEq)

/-- Pointwise cancellation for the canonical map. -/
theorem squareRootLowPrimeCanonicalCreationToResponse_weight_cancel
    {R K j U : ℕ} {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ squareRootLowPrimeMatchedCreationStates R K j U) :
    squareRootLowPrimeCreationWeightReal x +
      squareRootLowPrimeResponseSeatWeightReal
        (squareRootLowPrimeCanonicalCreationToResponse R K j U x) = 0 := by
  have hxData := mem_squareRootLowPrimeMatchedCreationStates.mp hx
  exact squareRootLowPrimeCreationToResponseSeat_weight_cancel
    hxData.2.1
    (squareRootLowPrimeCanonicalResponseOwner_data hx).2.2
    (squareRootLowPrimeCanonicalResponseOwner_fresh hx)

end RHLean.Proof
