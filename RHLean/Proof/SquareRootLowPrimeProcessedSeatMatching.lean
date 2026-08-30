import Mathlib
import RHLean.Proof.SquareRootLowPrimeProcessedSeatCarrier
import RHLean.Proof.SquareRootLowPrimeSignedResponseMatching
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierRootCharge

/-!
# Sequential fresh-prime matching on the complete processed seat carrier

The common processed carrier contains the distinguished head and every literal
response seat with largest cofactor prime at most the terminal cutoff `U`.
For each fresh prime `p` in `(K,U]`, pair

`some (c,s) <-> some (p*c,s)`

whenever both seats are present and `p` is fresh for `c`.

The two weights are opposite because adjoining the fresh prime reverses the
Möbius sign.  Removing all such pairs therefore preserves the complete signed
mass.  Iterating through every fresh prime gives a terminal frontier whose mass
is exactly the actual running imbalance `T(U)`.

This is the correct quantitative frontier: it includes shallow creation, deep
response, and all intermediate response cofactors before any absolute value is
taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Cofactor represented by a processed state. -/
def squareRootLowPrimeProcessedStateCofactor : Option (ℕ × ℕ) → ℕ
  | none => 1
  | some z => z.1

/-- Add one prime to a non-head cofactor and preserve the seat index. -/
def squareRootLowPrimeProcessedSeatExtend
    (p : ℕ) : Option (ℕ × ℕ) → Option (ℕ × ℕ)
  | none => none
  | some z => some (p * z.1, z.2)

/-- Lower endpoints of all available `p`-edges in a finite processed carrier. -/
def squareRootLowPrimeProcessedSeatPairLower
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  S.filter fun x =>
    x ≠ none ∧
      ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x ∧
      squareRootLowPrimeProcessedSeatExtend p x ∈ S

/-- Upper endpoints of the available `p`-edges. -/
def squareRootLowPrimeProcessedSeatPairUpper
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  (squareRootLowPrimeProcessedSeatPairLower S p).image
    (squareRootLowPrimeProcessedSeatExtend p)

/-- Complete population removed at one fresh-prime coordinate. -/
def squareRootLowPrimeProcessedSeatPaired
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  squareRootLowPrimeProcessedSeatPairLower S p ∪
    squareRootLowPrimeProcessedSeatPairUpper S p

/-- Frontier after one fresh-prime coordinate. -/
def squareRootLowPrimeProcessedSeatFrontierStep
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  S \ squareRootLowPrimeProcessedSeatPaired S p

@[simp] theorem mem_squareRootLowPrimeProcessedSeatPairLower
    {S : Finset (Option (ℕ × ℕ))} {p : ℕ}
    {x : Option (ℕ × ℕ)} :
    x ∈ squareRootLowPrimeProcessedSeatPairLower S p ↔
      x ∈ S ∧ x ≠ none ∧
        ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x ∧
        squareRootLowPrimeProcessedSeatExtend p x ∈ S := by
  simp [squareRootLowPrimeProcessedSeatPairLower]

/-- Lower endpoints lie in the original carrier. -/
theorem squareRootLowPrimeProcessedSeatPairLower_subset
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    squareRootLowPrimeProcessedSeatPairLower S p ⊆ S := by
  intro x hx
  exact (mem_squareRootLowPrimeProcessedSeatPairLower.mp hx).1

/-- Upper endpoints lie in the original carrier. -/
theorem squareRootLowPrimeProcessedSeatPairUpper_subset
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    squareRootLowPrimeProcessedSeatPairUpper S p ⊆ S := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  exact (mem_squareRootLowPrimeProcessedSeatPairLower.mp hy).2.2.2

/-- The complete paired population lies in the original carrier. -/
theorem squareRootLowPrimeProcessedSeatPaired_subset
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    squareRootLowPrimeProcessedSeatPaired S p ⊆ S := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact squareRootLowPrimeProcessedSeatPairLower_subset S p hx
  · exact squareRootLowPrimeProcessedSeatPairUpper_subset S p hx

/-- Lower and upper endpoints of one fresh-prime coordinate are disjoint. -/
theorem squareRootLowPrimeProcessedSeatPairLower_disjoint_upper
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    Disjoint (squareRootLowPrimeProcessedSeatPairLower S p)
      (squareRootLowPrimeProcessedSeatPairUpper S p) := by
  rw [Finset.disjoint_left]
  intro x hxLower hxUpper
  have hxData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower
  rcases Finset.mem_image.mp hxUpper with ⟨y, _hy, hyx⟩
  rcases x with _ | z
  · exact hxData.2.1 rfl
  · rcases y with _ | w
    · simp [squareRootLowPrimeProcessedSeatExtend] at hyx
    · simp only [squareRootLowPrimeProcessedSeatExtend,
        Option.some.injEq] at hyx
      have hfirst := congrArg Prod.fst hyx
      apply hxData.2.2.1
      change p ∣ z.1
      exact ⟨w.1, hfirst.symm⟩

/-- Fresh-prime extension is injective on non-head lower endpoints. -/
theorem squareRootLowPrimeProcessedSeatExtend_injOn
    {S : Finset (Option (ℕ × ℕ))} {p : ℕ} (hp : 0 < p) :
    Set.InjOn (squareRootLowPrimeProcessedSeatExtend p)
      (squareRootLowPrimeProcessedSeatPairLower S p) := by
  intro x hx y hy hxy
  have hxNone := (mem_squareRootLowPrimeProcessedSeatPairLower.mp hx).2.1
  have hyNone := (mem_squareRootLowPrimeProcessedSeatPairLower.mp hy).2.1
  rcases x with _ | z
  · exact (hxNone rfl).elim
  · rcases y with _ | w
    · exact (hyNone rfl).elim
    · simp only [squareRootLowPrimeProcessedSeatExtend,
        Option.some.injEq, Prod.mk.injEq] at hxy
      have hc : z.1 = w.1 := Nat.mul_left_cancel hp hxy.1
      exact congrArg some (Prod.ext hc hxy.2)

/-- One fresh-prime extension reverses the processed seat weight. -/
theorem squareRootLowPrimeProcessedSeatExtend_weight_eq_neg
    {S : Finset (Option (ℕ × ℕ))} {p : ℕ} (hp : p.Prime)
    {x : Option (ℕ × ℕ)}
    (hx : x ∈ squareRootLowPrimeProcessedSeatPairLower S p) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatExtend p x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  have hxData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hx
  rcases x with _ | z
  · exact (hxData.2.1 rfl).elim
  · have hnot : ¬ p ∣ z.1 := by
      simpa [squareRootLowPrimeProcessedStateCofactor] using hxData.2.2.1
    have hmu : μ (p * z.1) = -μ z.1 :=
      moebius_prime_mul_eq_neg_of_not_dvd hp hnot
    change (((-μ (p * z.1) : ℤ) : ℝ)) =
      - (((-μ z.1 : ℤ) : ℝ))
    rw [hmu]
    push_cast
    ring

/-- Upper-endpoint mass is the negative lower-endpoint mass. -/
theorem squareRootLowPrimeProcessedSeatPairUpper_weight_sum_eq_neg_lower
    (S : Finset (Option (ℕ × ℕ))) {p : ℕ} (hp : p.Prime) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatPairUpper S p,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      -∑ x ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  unfold squareRootLowPrimeProcessedSeatPairUpper
  calc
    (∑ x ∈ (squareRootLowPrimeProcessedSeatPairLower S p).image
        (squareRootLowPrimeProcessedSeatExtend p),
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatWeightReal
          (squareRootLowPrimeProcessedSeatExtend p x) := by
      apply Finset.sum_image
      intro a ha b hb hab
      exact squareRootLowPrimeProcessedSeatExtend_injOn hp.pos ha hb hab
    _ = ∑ x ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        -squareRootLowPrimeProcessedSeatWeightReal x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp hx
    _ = -∑ x ∈ squareRootLowPrimeProcessedSeatPairLower S p,
        squareRootLowPrimeProcessedSeatWeightReal x := by
      rw [Finset.sum_neg_distrib]

/-- One complete fresh-prime matching has zero total weight. -/
theorem squareRootLowPrimeProcessedSeatPaired_weight_sum_eq_zero
    (S : Finset (Option (ℕ × ℕ))) {p : ℕ} (hp : p.Prime) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatPaired S p,
      squareRootLowPrimeProcessedSeatWeightReal x) = 0 := by
  unfold squareRootLowPrimeProcessedSeatPaired
  rw [Finset.sum_union
      (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p),
    squareRootLowPrimeProcessedSeatPairUpper_weight_sum_eq_neg_lower S hp]
  ring

/-- The complement of the one-step frontier is exactly the paired population. -/
theorem squareRootLowPrimeProcessedSeat_sdiff_frontierStep_eq_paired
    (S : Finset (Option (ℕ × ℕ))) (p : ℕ) :
    S \ squareRootLowPrimeProcessedSeatFrontierStep S p =
      squareRootLowPrimeProcessedSeatPaired S p := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxNotFrontier⟩
    by_contra hxNotPaired
    apply hxNotFrontier
    exact Finset.mem_sdiff.mpr ⟨hxS, hxNotPaired⟩
  · intro hxPaired
    have hxS := squareRootLowPrimeProcessedSeatPaired_subset S p hxPaired
    apply Finset.mem_sdiff.mpr
    refine ⟨hxS, ?_⟩
    intro hxFrontier
    exact (Finset.mem_sdiff.mp hxFrontier).2 hxPaired

/-- One fresh-prime matching step preserves the complete processed mass. -/
theorem squareRootLowPrimeProcessedSeat_weight_sum_eq_frontierStep
    (S : Finset (Option (ℕ × ℕ))) {p : ℕ} (hp : p.Prime) :
    (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  have hsubset :
      squareRootLowPrimeProcessedSeatFrontierStep S p ⊆ S := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  have hsplit :
      (∑ x ∈ S \ squareRootLowPrimeProcessedSeatFrontierStep S p,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        ∑ x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p,
          squareRootLowPrimeProcessedSeatWeightReal x =
        ∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x :=
    Finset.sum_sdiff hsubset
  rw [squareRootLowPrimeProcessedSeat_sdiff_frontierStep_eq_paired,
    squareRootLowPrimeProcessedSeatPaired_weight_sum_eq_zero S hp] at hsplit
  simpa using hsplit.symm

/-- Iterate processed-seat matching through an explicit prime list. -/
def squareRootLowPrimeProcessedSeatMatchingFrontier :
    List ℕ → Finset (Option (ℕ × ℕ)) → Finset (Option (ℕ × ℕ))
  | [], S => S
  | p :: ps, S =>
      squareRootLowPrimeProcessedSeatMatchingFrontier ps
        (squareRootLowPrimeProcessedSeatFrontierStep S p)

/-- Iterating fresh-prime matchings preserves the complete processed mass. -/
theorem squareRootLowPrimeProcessedSeat_weight_sum_eq_matchingFrontier
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ)))
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeProcessedSeatMatchingFrontier]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hrest : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      calc
        (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
          ∑ x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p,
            squareRootLowPrimeProcessedSeatWeightReal x :=
          squareRootLowPrimeProcessedSeat_weight_sum_eq_frontierStep S hp
        _ = ∑ x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p),
            squareRootLowPrimeProcessedSeatWeightReal x :=
          ih (squareRootLowPrimeProcessedSeatFrontierStep S p) hrest
        _ = ∑ x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
              (p :: ps) S,
            squareRootLowPrimeProcessedSeatWeightReal x := by rfl

/-- Complete sequential frontier at terminal cutoff `U`. -/
def squareRootLowPrimeProcessedSeatTerminalFrontier
    (R K j U : ℕ) : Finset (Option (ℕ × ℕ)) :=
  squareRootLowPrimeProcessedSeatMatchingFrontier
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- **The terminal frontier has signed mass exactly `T(U)`.** -/
theorem squareRootLowPrimeProcessedSeatTerminalFrontier_weight_sum
    {R K j U : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatTerminalFrontier R K j U,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  have hmatch := squareRootLowPrimeProcessedSeat_weight_sum_eq_matchingFrontier
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
    (fun p hp => prime_of_mem_squareRootLowPrimeFreshPrimeList hp)
  rw [squareRootLowPrimeProcessedSeatCarrier_mass_eq_runningImbalanceReal hR]
    at hmatch
  exact hmatch.symm

/-- Terminal absolute value is bounded by the complete sequential frontier. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_processedSeatFrontierCard
    {R K j U : ℕ} (hR : 2 ≤ R) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      (squareRootLowPrimeProcessedSeatTerminalFrontier R K j U).card := by
  rw [← squareRootLowPrimeProcessedSeatTerminalFrontier_weight_sum hR]
  calc
    |∑ x ∈ squareRootLowPrimeProcessedSeatTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x| ≤
      ∑ x ∈ squareRootLowPrimeProcessedSeatTerminalFrontier R K j U,
        |squareRootLowPrimeProcessedSeatWeightReal x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ squareRootLowPrimeProcessedSeatTerminalFrontier R K j U,
        (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _hx
      exact abs_squareRootLowPrimeProcessedSeatWeightReal_le_one x
    _ = (squareRootLowPrimeProcessedSeatTerminalFrontier R K j U).card := by
      simp

/-- **Final root-seat quantitative gate on the complete sequential frontier.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_processedFrontier
    {R K j U B : ℕ}
    (encode : Option (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R)
    (hinj : Set.InjOn encode
      (squareRootLowPrimeProcessedSeatTerminalFrontier R K j U))
    (hbox : ∀ x ∈ squareRootLowPrimeProcessedSeatTerminalFrontier R K j U,
      encode x ∈ squareRootLowPrimeRootSeatBox R B) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      (R * B : ℕ) := by
  have himage :
      (squareRootLowPrimeProcessedSeatTerminalFrontier R K j U).image encode ⊆
        squareRootLowPrimeRootSeatBox R B := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hbox x hx
  have hcardImage :
      ((squareRootLowPrimeProcessedSeatTerminalFrontier R K j U).image
        encode).card =
        (squareRootLowPrimeProcessedSeatTerminalFrontier R K j U).card :=
    Finset.card_image_iff.mpr hinj
  have hcard :
      (squareRootLowPrimeProcessedSeatTerminalFrontier R K j U).card ≤
        R * B := by
    rw [← hcardImage, ← card_squareRootLowPrimeRootSeatBox R B]
    exact Finset.card_le_card himage
  exact
    (abs_squareRootLowPrimeRunningImbalanceReal_le_processedSeatFrontierCard
      (R := R) (K := K) (j := j) (U := U) hR).trans
      (by exact_mod_cast hcard)

/-- **Processed-frontier energy-decrement acceptance gate.** -/
theorem squareRootLowPrimeProcessedSeat_energyDecrement_ge
    {R K j U B : ℕ}
    (encode : Option (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R)
    (hinj : Set.InjOn encode
      (squareRootLowPrimeProcessedSeatTerminalFrontier R K j U))
    (hbox : ∀ x ∈ squareRootLowPrimeProcessedSeatTerminalFrontier R K j U,
      encode x ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        ((R * B : ℕ) : ℝ) ^ 2 := by
  have habs :=
    abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_processedFrontier
      encode hR hinj hbox
  have hnonneg : (0 : ℝ) ≤ (R * B : ℕ) := by positivity
  rcases abs_le.mp habs with ⟨hlow, hupp⟩
  nlinarith

end RHLean.Proof
