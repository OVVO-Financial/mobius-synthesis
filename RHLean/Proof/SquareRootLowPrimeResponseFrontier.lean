import Mathlib
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren
import RHLean.Proof.SquareRootBornPostTailLowPrimeRemainder

/-!
# Root-scale frontier of the signed low-prime response forest

The complete signed response carrier consists of prime-extension atoms `(c,q)`.
At the terminal low-prime cutoff

`P_R = R - floor(sqrt R)`,

split the born atoms according to whether their new largest prime `q` has
already been processed.

If `P_R < q <= R` and `(c,q)` is a born atom, then `q <= c` and
`c*q <= R^2-1`.  Consequently both coordinates lie in the same near-root
rectangle

`P_R < q <= R`,
`P_R < c <= (R^2-1)/(P_R+1) <= R + floor(sqrt R)`.

The rectangle has at most

`floor(sqrt R) * 2*floor(sqrt R) <= 2R`

lattice sites.  This proves an actual linear global bound for every born child
that exits the processed prime interval.  It is a bound on the fully weighted
atom population, not merely on its cofactor support.

Post-root atoms are deliberately not included in this estimate: they are the
transport-root population already identified with the far-survivor channel.
No estimate for that signed channel or for the remaining internal response
forest is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Response atoms whose partner belongs to the born-smooth prime range. -/
def squareRootLowPrimeBornResponseAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeOwnedResponseAtoms R K U).filter fun z =>
    z.2 ∈ squareRootBornPartnerSet R z.1

/-- Born response atoms whose newly adjoined prime lies beyond the processed
prime interval. -/
def squareRootLowPrimeBornFrontierAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeBornResponseAtoms R K U).filter fun z => U < z.2

/-- Born response atoms whose newly adjoined prime remains inside the processed
prime interval. -/
def squareRootLowPrimeBornInternalAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeBornResponseAtoms R K U).filter fun z => z.2 ≤ U

@[simp] theorem mem_squareRootLowPrimeBornResponseAtoms
    {R K U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeBornResponseAtoms R K U ↔
      z ∈ squareRootLowPrimeOwnedResponseAtoms R K U ∧
        z.2 ∈ squareRootBornPartnerSet R z.1 := by
  simp [squareRootLowPrimeBornResponseAtoms]

@[simp] theorem mem_squareRootLowPrimeBornFrontierAtoms
    {R K U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeBornFrontierAtoms R K U ↔
      z ∈ squareRootLowPrimeOwnedResponseAtoms R K U ∧
        z.2 ∈ squareRootBornPartnerSet R z.1 ∧ U < z.2 := by
  simp [squareRootLowPrimeBornFrontierAtoms,
    squareRootLowPrimeBornResponseAtoms, and_assoc]

@[simp] theorem mem_squareRootLowPrimeBornInternalAtoms
    {R K U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeBornInternalAtoms R K U ↔
      z ∈ squareRootLowPrimeOwnedResponseAtoms R K U ∧
        z.2 ∈ squareRootBornPartnerSet R z.1 ∧ z.2 ≤ U := by
  simp [squareRootLowPrimeBornInternalAtoms,
    squareRootLowPrimeBornResponseAtoms, and_assoc]

/-- The born response carrier is the disjoint union of its internal and frontier
parts. -/
theorem squareRootLowPrimeBornResponseAtoms_eq_internal_union_frontier
    (R K U : ℕ) :
    squareRootLowPrimeBornResponseAtoms R K U =
      squareRootLowPrimeBornInternalAtoms R K U ∪
        squareRootLowPrimeBornFrontierAtoms R K U := by
  ext z
  constructor
  · intro hz
    have hbase := mem_squareRootLowPrimeBornResponseAtoms.mp hz
    by_cases hqU : z.2 ≤ U
    · exact Finset.mem_union.mpr <| Or.inl <|
        mem_squareRootLowPrimeBornInternalAtoms.mpr
          ⟨hbase.1, hbase.2, hqU⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        mem_squareRootLowPrimeBornFrontierAtoms.mpr
          ⟨hbase.1, hbase.2, Nat.lt_of_not_ge hqU⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have h := mem_squareRootLowPrimeBornInternalAtoms.mp hz
      exact mem_squareRootLowPrimeBornResponseAtoms.mpr ⟨h.1, h.2.1⟩
    · have h := mem_squareRootLowPrimeBornFrontierAtoms.mp hz
      exact mem_squareRootLowPrimeBornResponseAtoms.mpr ⟨h.1, h.2.1⟩

/-- The internal and frontier born carriers are disjoint. -/
theorem squareRootLowPrimeBornInternalAtoms_disjoint_frontier
    (R K U : ℕ) :
    Disjoint (squareRootLowPrimeBornInternalAtoms R K U)
      (squareRootLowPrimeBornFrontierAtoms R K U) := by
  rw [Finset.disjoint_left]
  intro z hzInt hzFront
  have hi := mem_squareRootLowPrimeBornInternalAtoms.mp hzInt
  have hf := mem_squareRootLowPrimeBornFrontierAtoms.mp hzFront
  omega

/-- Every born frontier atom lies in one explicit near-root rectangle. -/
theorem squareRootLowPrimeBornFrontierAtoms_subset_rootRectangle
    (R K U : ℕ) :
    squareRootLowPrimeBornFrontierAtoms R K U ⊆
      (Finset.Ioc U (squareRootEndpoint R / (U + 1))).product
        (Finset.Ioc U R) := by
  intro z hz
  rcases mem_squareRootLowPrimeBornFrontierAtoms.mp hz with
    ⟨_hzResponse, hzBorn, hUz⟩
  rcases Finset.mem_filter.mp hzBorn with
    ⟨hzRange, hzPrime, _hzRough, hzOrder, hzProduct⟩
  have hzU1 : U + 1 ≤ z.2 := by omega
  have hcDiv : z.1 ≤ squareRootEndpoint R / z.2 :=
    (Nat.le_div_iff_mul_le hzPrime.pos).2 hzProduct
  have hdivMono :
      squareRootEndpoint R / z.2 ≤
        squareRootEndpoint R / (U + 1) :=
    Nat.div_le_div_left hzU1 (by omega)
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_Ioc.mpr
      ⟨lt_of_lt_of_le hUz hzOrder, hcDiv.trans hdivMono⟩
  · exact Finset.mem_Ioc.mpr
      ⟨hUz, (Finset.mem_Icc.mp hzRange).2⟩

/-- General rectangle bound before specializing the terminal cutoff. -/
theorem squareRootLowPrimeBornFrontierAtoms_card_le_rectangle
    (R K U : ℕ) :
    (squareRootLowPrimeBornFrontierAtoms R K U).card ≤
      (squareRootEndpoint R / (U + 1) - U) * (R - U) := by
  have hsub :=
    squareRootLowPrimeBornFrontierAtoms_subset_rootRectangle R K U
  calc
    (squareRootLowPrimeBornFrontierAtoms R K U).card ≤
        ((Finset.Ioc U (squareRootEndpoint R / (U + 1))).product
          (Finset.Ioc U R)).card := Finset.card_le_card hsub
    _ = (squareRootEndpoint R / (U + 1) - U) * (R - U) := by
      simp [Nat.card_Ioc]

/-- At the canonical cutoff `P_R = R-floor(sqrt R)`, the reciprocal upper edge
of the born frontier is at most `R+floor(sqrt R)`. -/
theorem squareRootLowPrimeBornFrontier_reciprocalUpper_le_root_add_sqrt
    (R : ℕ) :
    squareRootEndpoint R /
        (squareRootBornPostTailLowPrimeCutoff R + 1) ≤
      R + Nat.sqrt R := by
  let s := Nat.sqrt R
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hsR : s ≤ R := by
    simpa [s] using Nat.sqrt_le_self R
  have hPs : P + s = R := by
    dsimp [P, squareRootBornPostTailLowPrimeCutoff, s]
    omega
  have hsSq : s ^ 2 ≤ R := by
    simpa [s] using Nat.sqrt_le' R
  have hden : 0 < P + 1 := Nat.succ_pos P
  have hidentity :
      (R + s + 1) * (P + 1) + s ^ 2 = (R + 1) ^ 2 := by
    rw [← hPs]
    ring
  have hprodLower :
      R ^ 2 + 1 ≤ (R + s + 1) * (P + 1) := by
    nlinarith [hidentity, hsSq]
  have hprod :
      squareRootEndpoint R < (R + s + 1) * (P + 1) := by
    calc
      squareRootEndpoint R < R ^ 2 + 1 := by
        unfold squareRootEndpoint
        omega
      _ ≤ (R + s + 1) * (P + 1) := hprodLower
  have hlt :
      squareRootEndpoint R / (P + 1) < R + s + 1 :=
    (Nat.div_lt_iff_lt_mul hden).2 hprod
  simpa [P, s] using (Nat.le_of_lt_succ hlt)

/-- **Linear terminal born-frontier bound.**  Every born response atom that
escapes the processed interval at `P_R` lies in a rectangle of at most `2R`
sites. -/
theorem squareRootLowPrimeBornFrontierAtoms_card_le_two_root
    (R K : ℕ) :
    (squareRootLowPrimeBornFrontierAtoms R K
      (squareRootBornPostTailLowPrimeCutoff R)).card ≤ 2 * R := by
  let s := Nat.sqrt R
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hsR : s ≤ R := by
    simpa [s] using Nat.sqrt_le_self R
  have hPs : P + s = R := by
    dsimp [P, squareRootBornPostTailLowPrimeCutoff, s]
    omega
  have hupper :=
    squareRootLowPrimeBornFrontier_reciprocalUpper_le_root_add_sqrt R
  have hupperP :
      squareRootEndpoint R / (P + 1) ≤ R + s := by
    simpa [P, s] using hupper
  have hwidthC :
      squareRootEndpoint R / (P + 1) - P ≤ 2 * s := by
    omega
  have hwidthQ : R - P = s := by omega
  have hrect :=
    squareRootLowPrimeBornFrontierAtoms_card_le_rectangle R K P
  calc
    (squareRootLowPrimeBornFrontierAtoms R K P).card ≤
        (squareRootEndpoint R / (P + 1) - P) * (R - P) := hrect
    _ ≤ (2 * s) * s := by
      rw [hwidthQ]
      exact Nat.mul_le_mul_right s hwidthC
    _ = 2 * (s ^ 2) := by ring
    _ ≤ 2 * R := by
      exact Nat.mul_le_mul_left 2 (Nat.sqrt_le' R)

/-- Signed Möbius mass carried by the terminal born-response frontier. -/
def squareRootLowPrimeBornFrontierChildMass
    (R K U : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeBornFrontierAtoms R K U,
    canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)

/-- Every response child has unit Möbius norm. -/
theorem norm_squareRootLowPrimeResponseAtomChild_eq_one
    {R K U : ℕ} (hUR : U < R) {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeOwnedResponseAtoms R K U) :
    ‖canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)‖ = 1 := by
  unfold squareRootLowPrimeOwnedResponseAtoms at hz
  rcases Finset.mem_union.mp hz with hzBad | hzDeletion
  · rw [squareRootLowPrimeOwnedBadAtomChild_moebiusWeight_eq_neg_one
      hUR hzBad]
    norm_num
  · rw [squareRootLowPrimeOwnedDeletionAtomChild_moebiusWeight_eq_one
      hUR hzDeletion]
    norm_num

/-- Taking the norm only after global frontier ownership costs at most the
frontier cardinality. -/
theorem norm_squareRootLowPrimeBornFrontierChildMass_le_card
    {R K U : ℕ} (hUR : U < R) :
    ‖squareRootLowPrimeBornFrontierChildMass R K U‖ ≤
      ((squareRootLowPrimeBornFrontierAtoms R K U).card : ℝ) := by
  unfold squareRootLowPrimeBornFrontierChildMass
  calc
    ‖∑ z ∈ squareRootLowPrimeBornFrontierAtoms R K U,
        canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)‖ ≤
      ∑ z ∈ squareRootLowPrimeBornFrontierAtoms R K U,
        ‖canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)‖ := by
          exact norm_sum_le _ _
    _ = ∑ _z ∈ squareRootLowPrimeBornFrontierAtoms R K U, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [norm_squareRootLowPrimeResponseAtomChild_eq_one hUR
        (mem_squareRootLowPrimeBornFrontierAtoms.mp hz).1]
    _ = ((squareRootLowPrimeBornFrontierAtoms R K U).card : ℝ) := by simp

/-- **Linear signed frontier bound.**  At the canonical terminal cutoff the
entire born exit frontier has norm at most `2R`. -/
theorem norm_squareRootLowPrimeBornFrontierChildMass_le_two_root
    (R K : ℕ) (hR : 2 ≤ R) :
    ‖squareRootLowPrimeBornFrontierChildMass R K
        (squareRootBornPostTailLowPrimeCutoff R)‖ ≤
      2 * (R : ℝ) := by
  have hcut : squareRootBornPostTailLowPrimeCutoff R < R := by
    unfold squareRootBornPostTailLowPrimeCutoff
    have hspos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 (by omega)
    omega
  have hnorm :=
    norm_squareRootLowPrimeBornFrontierChildMass_le_card
      (R := R) (K := K)
      (U := squareRootBornPostTailLowPrimeCutoff R) hcut
  have hcard := squareRootLowPrimeBornFrontierAtoms_card_le_two_root R K
  have hcardReal :
      ((squareRootLowPrimeBornFrontierAtoms R K
        (squareRootBornPostTailLowPrimeCutoff R)).card : ℝ) ≤
          2 * (R : ℝ) := by
    exact_mod_cast hcard
  exact hnorm.trans hcardReal

end RHLean.Proof
