import Mathlib
import RHLean.Proof.SquareRootLowPrimeChannelCreationCarrier
import RHLean.Proof.SquareRootLowPrimeCanonicalChildCharacterization

/-!
# Native combined response-seat carrier

The complete deep response can be represented without exposing the partner
prime: a cofactor `c` carries

`CombinedFreshResponse(R,K,j,c)`

literal unit seats.  A response state is therefore `(c,s)` with `s` below that
count, and its weight is `-mu(c)`.

Over the owned signed cofactors in `(K,U]`, the total seat mass is exactly

`-sum_{K<p<=U} Delta_p`.

This is the natural target of the repository's sequential creation-to-response
map.  Adding one fresh prime changes `c` to `p*c`, preserves the absolute seat
index, and reverses the Möbius sign.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Combined response seats over one cofactor. -/
def squareRootLowPrimeCombinedSeatFiber
    (R K j c : ℕ) : Finset (ℕ × ℕ) :=
  ({c} : Finset ℕ).product
    (Finset.range (squareRootLowPrimeCombinedFreshResponse R K j c))

/-- Complete owned deep response-seat carrier. -/
def squareRootLowPrimeOwnedResponseSeatCarrier
    (R K j U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeOwnedSignedCofactors R K U).biUnion
    (squareRootLowPrimeCombinedSeatFiber R K j)

/-- Real weight of one combined response seat. -/
def squareRootLowPrimeResponseSeatWeightReal
    (z : ℕ × ℕ) : ℝ :=
  ((-μ z.1 : ℤ) : ℝ)

@[simp] theorem mem_squareRootLowPrimeCombinedSeatFiber
    {R K j c : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeCombinedSeatFiber R K j c ↔
      z.1 = c ∧
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeCombinedSeatFiber, eq_comm, and_comm]

/-- Distinct cofactor seat fibres are disjoint. -/
theorem squareRootLowPrimeCombinedSeatFiber_pairwiseDisjoint
    (R K j U : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeOwnedSignedCofactors R K U))
      (squareRootLowPrimeCombinedSeatFiber R K j) := by
  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeCombinedSeatFiber R K j c)
    (squareRootLowPrimeCombinedSeatFiber R K j d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
    ((mem_squareRootLowPrimeCombinedSeatFiber.mp hzc).1.symm.trans
      (mem_squareRootLowPrimeCombinedSeatFiber.mp hzd).1)

/-- Signed real mass of one response-seat fibre. -/
theorem squareRootLowPrimeCombinedSeatFiber_weight_sum
    (R K j c : ℕ) :
    (∑ z ∈ squareRootLowPrimeCombinedSeatFiber R K j c,
      squareRootLowPrimeResponseSeatWeightReal z) =
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCombinedFreshResponse R K j c : ℝ) := by
  unfold squareRootLowPrimeCombinedSeatFiber
    squareRootLowPrimeResponseSeatWeightReal
  simp
  ring

/-- Bad and deletion cofactor carriers are disjoint. -/
theorem squareRootLowPrimeOwnedBadCofactors_disjoint_deletionCofactors
    (R K U : ℕ) :
    Disjoint (squareRootLowPrimeOwnedBadCofactors R K U)
      (squareRootLowPrimeOwnedDeletionCofactors R K U) := by
  rw [Finset.disjoint_left]
  intro c hbad hdelete
  have hpos := (squareRootLowPrimeOwnedBadCofactor_data hbad).2.2.2
  have hneg :=
    (squareRootLowPrimeOwnedDeletionCofactor_data hdelete).2.2.2
  omega

/-- The signed cofactor carrier is exactly the disjoint bad/deletion union. -/
theorem squareRootLowPrimeOwnedSignedCofactors_eq_bad_union_deletion
    (R K U : ℕ) :
    squareRootLowPrimeOwnedSignedCofactors R K U =
      squareRootLowPrimeOwnedBadCofactors R K U ∪
        squareRootLowPrimeOwnedDeletionCofactors R K U := by
  rfl

/-- Weighted response-seat mass on the bad cofactor carrier. -/
theorem squareRootLowPrimeBadCofactor_responseSeatMass
    (R K j U : ℕ) :
    (∑ c ∈ squareRootLowPrimeOwnedBadCofactors R K U,
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCombinedFreshResponse R K j c : ℝ)) =
      -(squareRootLowPrimeGlobalBadMass R K j K U : ℝ) := by
  rw [squareRootLowPrimeGlobalBadMass_eq_ownedCofactorSum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hmu := (squareRootLowPrimeOwnedBadCofactor_data hc).2.2.2
  simp [hmu]

/-- Weighted response-seat mass on the deletion cofactor carrier. -/
theorem squareRootLowPrimeDeletionCofactor_responseSeatMass
    (R K j U : ℕ) :
    (∑ c ∈ squareRootLowPrimeOwnedDeletionCofactors R K U,
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCombinedFreshResponse R K j c : ℝ)) =
      (squareRootLowPrimeGlobalDeletionMass R K j K U : ℝ) := by
  rw [squareRootLowPrimeGlobalDeletionMass_eq_ownedCofactorSum]
  push_cast
  apply Finset.sum_congr rfl
  intro c hc
  have hmu :=
    (squareRootLowPrimeOwnedDeletionCofactor_data hc).2.2.2
  simp [hmu]

/-- **The literal response-seat carrier has mass exactly `-sum Delta_p`.** -/
theorem squareRootLowPrimeOwnedResponseSeatCarrier_weight_sum
    {R K j U : ℕ} (hR : 2 ≤ R) :
    (∑ z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U,
      squareRootLowPrimeResponseSeatWeightReal z) =
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) := by
  unfold squareRootLowPrimeOwnedResponseSeatCarrier
  rw [Finset.sum_biUnion
    (squareRootLowPrimeCombinedSeatFiber_pairwiseDisjoint R K j U)]
  rw [squareRootLowPrimeOwnedSignedCofactors_eq_bad_union_deletion,
    Finset.sum_union
      (squareRootLowPrimeOwnedBadCofactors_disjoint_deletionCofactors R K U)]
  simp_rw [squareRootLowPrimeCombinedSeatFiber_weight_sum]
  rw [squareRootLowPrimeBadCofactor_responseSeatMass,
    squareRootLowPrimeDeletionCofactor_responseSeatMass]
  have hinc :=
    squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_badMass
      (R := R) (K := K) (j := j) (L := K) (U := U) hR
  have hincRe := congrArg Complex.re hinc
  have hincReal :
      (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        -(squareRootLowPrimeGlobalDeletionMass R K j K U : ℝ) +
          (squareRootLowPrimeGlobalBadMass R K j K U : ℝ) := by
    simpa [squareRootLowPrimeFreshIncrementReal] using hincRe
  linarith [hincReal]

/-- Every response seat has unit real weight. -/
theorem abs_squareRootLowPrimeResponseSeatWeightReal_le_one
    (z : ℕ × ℕ) :
    |squareRootLowPrimeResponseSeatWeightReal z| ≤ 1 := by
  unfold squareRootLowPrimeResponseSeatWeightReal
  have hInt : |(-μ z.1 : ℤ)| ≤ 1 := by
    simpa using (ArithmeticFunction.abs_moebius_le_one (n := z.1))
  exact_mod_cast hInt

/-- Recover the cofactor of a non-head creation state. -/
def squareRootLowPrimeCreationStateCofactor :
    SquareRootLowPrimeCreationState → ℕ
  | none => 1
  | some (Sum.inl z) => z.1
  | some (Sum.inr z) => z.1

/-- Convert the born/high local seat coordinate to the combined absolute seat
index. -/
def squareRootLowPrimeCreationStateAbsoluteSeat
    (R : ℕ) : SquareRootLowPrimeCreationState → ℕ
  | none => 0
  | some (Sum.inl z) => z.2
  | some (Sum.inr z) => squareRootBornPartnerCount R z.1 + z.2

/-- Add the owner prime and preserve the combined seat. The value on the head
is irrelevant because the matched domain may exclude it. -/
def squareRootLowPrimeCreationToResponseSeat
    (R : ℕ) (ownerPrime : SquareRootLowPrimeCreationState → ℕ)
    (x : SquareRootLowPrimeCreationState) : ℕ × ℕ :=
  (ownerPrime x * squareRootLowPrimeCreationStateCofactor x,
    squareRootLowPrimeCreationStateAbsoluteSeat R x)

/-- Pointwise sign reversal under one genuinely fresh prime extension. -/
theorem squareRootLowPrimeCreationToResponseSeat_weight_cancel
    {R : ℕ} {ownerPrime : SquareRootLowPrimeCreationState → ℕ}
    {x : SquareRootLowPrimeCreationState}
    (hx : x ≠ none)
    (hp : (ownerPrime x).Prime)
    (hfresh : ¬ ownerPrime x ∣ squareRootLowPrimeCreationStateCofactor x) :
    squareRootLowPrimeCreationWeightReal x +
      squareRootLowPrimeResponseSeatWeightReal
        (squareRootLowPrimeCreationToResponseSeat R ownerPrime x) = 0 := by
  have hcop :
      Nat.Coprime (ownerPrime x)
        (squareRootLowPrimeCreationStateCofactor x) :=
    (hp.coprime_iff_not_dvd).2 hfresh
  have hmu :
      μ (ownerPrime x * squareRootLowPrimeCreationStateCofactor x) =
        -μ (squareRootLowPrimeCreationStateCofactor x) := by
    calc
      μ (ownerPrime x * squareRootLowPrimeCreationStateCofactor x) =
          μ (ownerPrime x) *
            μ (squareRootLowPrimeCreationStateCofactor x) :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      _ = (-1) * μ (squareRootLowPrimeCreationStateCofactor x) := by
        rw [ArithmeticFunction.moebius_apply_prime hp]
      _ = -μ (squareRootLowPrimeCreationStateCofactor x) := by ring
  rcases x with _ | x
  · exact (hx rfl).elim
  · rcases x with z | z
    · simp only [squareRootLowPrimeCreationStateCofactor] at hmu
      have hmuReal := congrArg (fun a : ℤ => (a : ℝ)) hmu
      push_cast at hmuReal
      change -((μ z.1 : ℤ) : ℝ) +
          ((-μ (ownerPrime (some (Sum.inl z)) * z.1) : ℤ) : ℝ) = 0
      push_cast
      linarith
    · simp only [squareRootLowPrimeCreationStateCofactor] at hmu
      have hmuReal := congrArg (fun a : ℤ => (a : ℝ)) hmu
      push_cast at hmuReal
      change -((μ z.1 : ℤ) : ℝ) +
          ((-μ (ownerPrime (some (Sum.inr z)) * z.1) : ℤ) : ℝ) = 0
      push_cast
      linarith

end RHLean.Proof
