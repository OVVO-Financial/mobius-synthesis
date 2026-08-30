import Mathlib
import RHLean.Proof.SquareRootLowPrimeCreationResponseEnergyGate
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren

/-!
# Literal shallow-creation and deep-response carriers

The energy gate requires actual finite carriers whose signed masses are

`T(K)` and `-sum_{K<p<=U} Delta_p`.

The shallow carrier consists of

* one distinguished head atom of weight `+1`; and
* one seat `(c,s)` for each unit of the complete combined response of a
  nonzero-Möbius cofactor with `P+(c) <= K`.

Each such seat has weight `-mu(c)`. Therefore its total mass is exactly

`1 - sum_{P+(c)<=K} mu(c) * CombinedResponse(c)`,

which is the shallow running imbalance.

The deep response carrier is the already-defined complete signed response-atom
set. Its atom `(c,q)` has the same weight `-mu(c)`. Thus the repository's
existing creation-to-response map can be stated directly between these two
unit-weight carriers before any norm is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Nonzero-Möbius cofactors already present at the shallow cutoff `K`. -/
def squareRootLowPrimeShallowSignedCofactors
    (R K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun c =>
    canonicalLargestPrimeFactor c ≤ K ∧ μ c ≠ 0

/-- Seat atoms attached to one shallow cofactor. -/
def squareRootLowPrimeCreationSeatFiber
    (R K j c : ℕ) : Finset (ℕ × ℕ) :=
  ({c} : Finset ℕ).product
    (Finset.range (squareRootLowPrimeCombinedFreshResponse R K j c))

/-- All non-head shallow creation seats. -/
def squareRootLowPrimeCreationSeatAtoms
    (R K j : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeShallowSignedCofactors R K).biUnion
    (squareRootLowPrimeCreationSeatFiber R K j)

/-- The literal shallow creation carrier, including the distinguished head. -/
def squareRootLowPrimeCreationCarrier
    (R K j : ℕ) : Finset (Option (ℕ × ℕ)) :=
  insert none
    ((squareRootLowPrimeCreationSeatAtoms R K j).image some)

/-- Integer weight of one shallow creation state. -/
def squareRootLowPrimeCreationWeight : Option (ℕ × ℕ) → ℤ
  | none => 1
  | some z => -μ z.1

/-- Integer weight of one deep response atom. -/
def squareRootLowPrimeResponseAtomWeight (z : ℕ × ℕ) : ℤ :=
  -μ z.1

@[simp] theorem mem_squareRootLowPrimeCreationSeatFiber
    {R K j c : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeCreationSeatFiber R K j c ↔
      z.1 = c ∧
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeCreationSeatFiber, eq_comm, and_comm]

/-- Distinct shallow-cofactor seat fibres are disjoint. -/
theorem squareRootLowPrimeCreationSeatFiber_pairwiseDisjoint
    (R K j : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeShallowSignedCofactors R K))
      (squareRootLowPrimeCreationSeatFiber R K j) := by
  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeCreationSeatFiber R K j c)
    (squareRootLowPrimeCreationSeatFiber R K j d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  have hcEq := (mem_squareRootLowPrimeCreationSeatFiber.mp hzc).1
  have hdEq := (mem_squareRootLowPrimeCreationSeatFiber.mp hzd).1
  exact hcd (hcEq.symm.trans hdEq)

/-- One cofactor fibre has the expected signed seat mass. -/
theorem squareRootLowPrimeCreationSeatFiber_weight_sum
    (R K j c : ℕ) :
    (∑ z ∈ squareRootLowPrimeCreationSeatFiber R K j c,
      -μ z.1) =
      -(μ c) * (squareRootLowPrimeCombinedFreshResponse R K j c : ℤ) := by
  unfold squareRootLowPrimeCreationSeatFiber
  simp
  ring

/-- The complete non-head creation-seat mass is the low-cofactor weighted
response. -/
theorem squareRootLowPrimeCreationSeatAtoms_weight_sum
    (R K j : ℕ) :
    (∑ z ∈ squareRootLowPrimeCreationSeatAtoms R K j, -μ z.1) =
      ∑ c ∈ squareRootLowPrimeShallowSignedCofactors R K,
        -(μ c) *
          (squareRootLowPrimeCombinedFreshResponse R K j c : ℤ) := by
  unfold squareRootLowPrimeCreationSeatAtoms
  rw [Finset.sum_biUnion
    (squareRootLowPrimeCreationSeatFiber_pairwiseDisjoint R K j)]
  apply Finset.sum_congr rfl
  intro c _hc
  exact squareRootLowPrimeCreationSeatFiber_weight_sum R K j c

/-- The head atom is not a seat atom. -/
theorem none_not_mem_creationSeatAtoms_image_some
    (R K j : ℕ) :
    none ∉ (squareRootLowPrimeCreationSeatAtoms R K j).image some := by
  simp

/-- **Exact integer mass of the literal shallow creation carrier.** -/
theorem squareRootLowPrimeCreationCarrier_weight_sum
    (R K j : ℕ) :
    (∑ x ∈ squareRootLowPrimeCreationCarrier R K j,
      squareRootLowPrimeCreationWeight x) =
      1 +
        ∑ c ∈ squareRootLowPrimeShallowSignedCofactors R K,
          -(μ c) *
            (squareRootLowPrimeCombinedFreshResponse R K j c : ℤ) := by
  unfold squareRootLowPrimeCreationCarrier
  rw [Finset.sum_insert
    (none_not_mem_creationSeatAtoms_image_some R K j)]
  have himage :
      (∑ x ∈ (squareRootLowPrimeCreationSeatAtoms R K j).image some,
        squareRootLowPrimeCreationWeight x) =
        ∑ z ∈ squareRootLowPrimeCreationSeatAtoms R K j, -μ z.1 := by
    apply Finset.sum_image
    intro a _ha b _hb hab
    simpa using hab
  rw [himage, squareRootLowPrimeCreationSeatAtoms_weight_sum]
  simp [squareRootLowPrimeCreationWeight]

/-- Every shallow creation state has unit-or-zero integer weight. -/
theorem abs_squareRootLowPrimeCreationWeight_le_one
    (x : Option (ℕ × ℕ)) :
    |squareRootLowPrimeCreationWeight x| ≤ 1 := by
  rcases x with _ | z
  · simp [squareRootLowPrimeCreationWeight]
  · simp [squareRootLowPrimeCreationWeight]
    exact ArithmeticFunction.abs_moebius_le_one

/-- Every deep response atom has unit-or-zero integer weight. -/
theorem abs_squareRootLowPrimeResponseAtomWeight_le_one
    (z : ℕ × ℕ) :
    |squareRootLowPrimeResponseAtomWeight z| ≤ 1 := by
  simp [squareRootLowPrimeResponseAtomWeight]
  exact ArithmeticFunction.abs_moebius_le_one

/-- The deep response-atom weight is exactly the Möbius weight of its arithmetic
child. -/
theorem squareRootLowPrimeResponseAtomWeight_eq_child_moebius
    {R K U : ℕ} {z : ℕ × ℕ} (hUR : U < R)
    (hz : z ∈ squareRootLowPrimeOwnedResponseAtoms R K U) :
    squareRootLowPrimeResponseAtomWeight z =
      μ (squareRootLowPrimeBadAtomChild z) := by
  have hflip := squareRootLowPrimeOwnedResponseAtomChild_moebiusWeight
    hUR hz
  have hcast := congrArg (fun w : ℂ => w.re) hflip
  have hcastReal :
      ((-μ z.1 : ℤ) : ℝ) =
        ((μ (squareRootLowPrimeBadAtomChild z) : ℤ) : ℝ) := by
    simpa [canonicalMoebiusWeight] using hcast.symm
  unfold squareRootLowPrimeResponseAtomWeight
  exact_mod_cast hcastReal

/-- Exact signed deep response mass on the literal atom carrier. -/
theorem squareRootLowPrimeOwnedResponseAtoms_weight_sum_eq_neg_freshIncrementReal
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    ((∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
      squareRootLowPrimeResponseAtomWeight z : ℤ) : ℝ) =
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) := by
  have hresponse :=
    squareRootLowPrimeFreshIncrementReal_sum_eq_neg_ownedResponseChildrenMass
      (R := R) (K := K) (j := j) (U := U) hR hUR
  have hatoms :=
    squareRootLowPrimeOwnedResponseChildren_moebiusMass_eq_atoms
      (R := R) (K := K) (U := U) hUR
  have hatomsRe := congrArg Complex.re hatoms
  have hweight :
      ((∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
        squareRootLowPrimeResponseAtomWeight z : ℤ) : ℝ) =
        ∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
          (canonicalMoebiusWeight
            (squareRootLowPrimeBadAtomChild z)).re := by
    push_cast
    apply Finset.sum_congr rfl
    intro z hz
    have h := squareRootLowPrimeResponseAtomWeight_eq_child_moebius
      hUR hz
    simpa [canonicalMoebiusWeight] using congrArg (fun a : ℤ => (a : ℝ)) h
  calc
    ((∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
      squareRootLowPrimeResponseAtomWeight z : ℤ) : ℝ) =
        ∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
          (canonicalMoebiusWeight
            (squareRootLowPrimeBadAtomChild z)).re := hweight
    _ = ∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
          (canonicalMoebiusWeight n).re := by
      simpa using hatomsRe.symm
    _ = -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
          squareRootLowPrimeFreshIncrementReal R K j p) := by
      linarith [hresponse]

end RHLean.Proof
