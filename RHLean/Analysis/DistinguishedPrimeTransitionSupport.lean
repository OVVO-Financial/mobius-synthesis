import Mathlib
import RHLean.Arithmetic.PrimeSquareCollisionKernel
import RHLean.Analysis.TwoABPrimeDilation

/-!
# Distinguished-prime transition support

This module records exact forced-zero laws for one distinguished large-prime
coordinate across two consecutive physical three-slot cells.

The physical six sites are

* `4*k+1`, `4*k+2`, `4*k+3`,
* `4*k+5`, `4*k+6`, `4*k+7`.

If `q > 6`, divisibility by `q` can occur at at most one of these six sites.
Consequently a fixed distinguished transport-prime fibre has no active-to-active
source/destination transition.  After retaining an arbitrary sign bit on an
active slot, the nominal `7 x 7 = 49` signed transition class contracts exactly
to the `13` states consisting of inactive-to-inactive, active-to-inactive, and
inactive-to-active transitions.

The module also records the reciprocal-fibre cofactor bound
`c <= floor((R^2-1)/q)` and its extreme fibre-one consequences.  The final
section packages the exact `13`-entry support as a restricted operator, proves
its active Gram block is rank-one, and derives the exact weighted Lyapunov
identity with the signed active recombination kept inside one norm.

No analytic estimate, stochastic model, or RH-scale contraction is asserted
here: these are finite arithmetic and linear-algebra support theorems intended
to shrink the admissible operator class for a later restricted Gram or Lyapunov
argument.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- A divisor larger than `2` can hit at most one active slot inside a physical
three-slot four-cell. -/
theorem largeDivisor_threeSlotValue_slot_unique
    (q k i j : ℕ)
    (hq : 2 < q)
    (hi : i < 3) (hj : j < 3)
    (hqi : q ∣ threeSlotValue k i)
    (hqj : q ∣ threeSlotValue k j) :
    i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hdiff : q ∣ threeSlotValue k j - threeSlotValue k i :=
      Nat.dvd_sub hqj hqi
    have hgap : threeSlotValue k j - threeSlotValue k i = j - i := by
      unfold threeSlotValue
      omega
    rw [hgap] at hdiff
    have hpos : 0 < j - i := by omega
    have hqle : q ≤ j - i := Nat.le_of_dvd hpos hdiff
    omega
  · have hdiff : q ∣ threeSlotValue k i - threeSlotValue k j :=
      Nat.dvd_sub hqi hqj
    have hgap : threeSlotValue k i - threeSlotValue k j = i - j := by
      unfold threeSlotValue
      omega
    rw [hgap] at hdiff
    have hpos : 0 < i - j := by omega
    have hqle : q ≤ i - j := Nat.le_of_dvd hpos hdiff
    omega

/-- A divisor larger than `6` cannot hit one source slot and one destination
slot in two consecutive physical three-slot cells. -/
theorem largeDivisor_current_next_threeSlot_impossible
    (q k i j : ℕ)
    (hq : 6 < q)
    (hi : i < 3) (hj : j < 3)
    (hcur : q ∣ threeSlotValue k i)
    (hnext : q ∣ threeSlotValue (k + 1) j) :
    False := by
  have hdiff : q ∣ threeSlotValue (k + 1) j - threeSlotValue k i :=
    Nat.dvd_sub hnext hcur
  have hgap :
      threeSlotValue (k + 1) j - threeSlotValue k i = 4 + j - i := by
    unfold threeSlotValue
    omega
  rw [hgap] at hdiff
  have hpos : 0 < 4 + j - i := by omega
  have hle : 4 + j - i ≤ 6 := by omega
  have hqle : q ≤ 4 + j - i := Nat.le_of_dvd hpos hdiff
  omega

/-- Physical support consisting of the three source sites and the three sites in
the immediately following destination cell. -/
def IsAdjacentDistinguishedPrimeSite (k n : ℕ) : Prop :=
  ∃ j : ℕ, j < 3 ∧
    (n = threeSlotValue k j ∨ n = threeSlotValue (k + 1) j)

/-- Any two adjacent-cell physical sites divisible by the same `q > 6` are the
same integer.  Thus one distinguished large-prime fibre has at most one active
site in the entire six-site source/destination support. -/
theorem distinguishedPrime_adjacent_site_unique
    (q k n m : ℕ)
    (hq : 6 < q)
    (hn : IsAdjacentDistinguishedPrimeSite k n)
    (hm : IsAdjacentDistinguishedPrimeSite k m)
    (hqn : q ∣ n)
    (hqm : q ∣ m) :
    n = m := by
  rcases hn with ⟨i, hi, hni | hni⟩
  · rcases hm with ⟨j, hj, hmj | hmj⟩
    · subst n
      subst m
      have hij := largeDivisor_threeSlotValue_slot_unique
        q k i j (by omega) hi hj hqn hqm
      rw [hij]
    · subst n
      subst m
      exact (largeDivisor_current_next_threeSlot_impossible
        q k i j hq hi hj hqn hqm).elim
  · rcases hm with ⟨j, hj, hmj | hmj⟩
    · subst n
      subst m
      exact (largeDivisor_current_next_threeSlot_impossible
        q k j i hq hj hi hqm hqn).elim
    · subst n
      subst m
      have hij := largeDivisor_threeSlotValue_slot_unique
        q (k + 1) i j (by omega) hi hj hqn hqm
      rw [hij]

/-- A fixed prime/divisor is active in the source physical three-slot cell. -/
def fixedPrimeSourceActive (q k : ℕ) : Prop :=
  ∃ i : ℕ, i < 3 ∧ q ∣ threeSlotValue k i

/-- A fixed prime/divisor is active in the immediately following destination
physical three-slot cell. -/
def fixedPrimeDestinationActive (q k : ℕ) : Prop :=
  ∃ j : ℕ, j < 3 ∧ q ∣ threeSlotValue (k + 1) j

/-- **Forced-zero law.**  For `q > 6`, the same distinguished prime/divisor
cannot be active in both the source and destination cells. -/
theorem fixedPrime_source_destination_not_both
    (q k : ℕ) (hq : 6 < q) :
    ¬(fixedPrimeSourceActive q k ∧ fixedPrimeDestinationActive q k) := by
  rintro ⟨⟨i, hi, hcur⟩, ⟨j, hj, hnext⟩⟩
  exact largeDivisor_current_next_threeSlot_impossible
    q k i j hq hi hj hcur hnext

/-- Signed support state for one fixed distinguished prime in one three-slot
cell. `none` means inactive; `some (i, sign)` means active in slot `i`, retaining
one arbitrary sign bit. -/
abbrev SignedPrimeHitState := Option (Fin 3 × Bool)

/-- The exact support relation forced by six-site uniqueness: at least one side
of a source/destination transition must be inactive. -/
def FixedPrimeTransitionAdmissible
    (s t : SignedPrimeHitState) : Prop :=
  s = none ∨ t = none

instance fixedPrimeTransitionAdmissibleDecidable
    (s t : SignedPrimeHitState) :
    Decidable (FixedPrimeTransitionAdmissible s t) := by
  unfold FixedPrimeTransitionAdmissible
  infer_instance

/-- Nominal signed source state count: one inactive state plus `3 * 2` active
slot/sign states. -/
theorem signedPrimeHitState_card :
    Fintype.card SignedPrimeHitState = 7 := by
  native_decide

/-- All admissible fixed-prime source/destination signed transitions. -/
def fixedPrimeAdmissibleTransitions :
    Finset (SignedPrimeHitState × SignedPrimeHitState) :=
  Finset.univ.filter fun st =>
    FixedPrimeTransitionAdmissible st.1 st.2

/-- The nominal `7 x 7 = 49` transition class has exactly `13` admissible
entries once the arithmetic active-to-active forced zero is imposed. -/
theorem fixedPrimeAdmissibleTransitions_card :
    fixedPrimeAdmissibleTransitions.card = 13 := by
  native_decide

/-- Equivalently, `36` of the `49` nominal signed entries are forced zero. -/
theorem fixedPrimeForcedZeroTransitions_card :
    Fintype.card (SignedPrimeHitState × SignedPrimeHitState) -
        fixedPrimeAdmissibleTransitions.card = 36 := by
  native_decide

/-- Source compatibility only records the arithmetic support of an active
signed label.  The sign bit is deliberately unconstrained here. -/
def SourcePrimeHitCompatible
    (q k : ℕ) : SignedPrimeHitState → Prop
  | none => True
  | some a => q ∣ threeSlotValue k a.1

/-- Destination analogue of `SourcePrimeHitCompatible`. -/
def DestinationPrimeHitCompatible
    (q k : ℕ) : SignedPrimeHitState → Prop
  | none => True
  | some a => q ∣ threeSlotValue (k + 1) a.1

/-- Every physically compatible fixed-`q` signed transition lies in the exact
`13`-entry admissible class. -/
theorem compatible_fixedPrime_transition_admissible
    (q k : ℕ) (hq : 6 < q)
    (s t : SignedPrimeHitState)
    (hs : SourcePrimeHitCompatible q k s)
    (ht : DestinationPrimeHitCompatible q k t) :
    FixedPrimeTransitionAdmissible s t := by
  rcases s with _ | ⟨i, sign⟩
  · exact Or.inl rfl
  rcases t with _ | ⟨j, sign'⟩
  · exact Or.inr rfl
  have hcur : q ∣ threeSlotValue k i := by
    simpa [SourcePrimeHitCompatible] using hs
  have hnext : q ∣ threeSlotValue (k + 1) j := by
    simpa [DestinationPrimeHitCompatible] using ht
  exact (largeDivisor_current_next_threeSlot_impossible
    q k i j hq i.isLt j.isLt hcur hnext).elim

/-- Reciprocal quotient attached to one square-root transport prime fibre. -/
def transportReciprocalFibre (R q : ℕ) : ℕ :=
  squareRootEndpoint R / q

/-- Every transport cofactor lies below its reciprocal quotient fibre. -/
theorem transportCofactor_le_reciprocalFibre
    {R q c : ℕ}
    (hq : 0 < q)
    (hprod : c * q ≤ squareRootEndpoint R) :
    c ≤ transportReciprocalFibre R q := by
  unfold transportReciprocalFibre
  exact (Nat.le_div_iff_mul_le hq).2 hprod

/-- In reciprocal fibre `1`, every positive admissible cofactor is exactly the
unit cofactor. -/
theorem transportCofactor_eq_one_of_fibre_one
    {R q c : ℕ}
    (hq : 0 < q)
    (hc : 1 ≤ c)
    (hprod : c * q ≤ squareRootEndpoint R)
    (hfibre : transportReciprocalFibre R q = 1) :
    c = 1 := by
  have hcle := transportCofactor_le_reciprocalFibre
    (R := R) (q := q) (c := c) hq hprod
  rw [hfibre] at hcle
  omega

/-- Fibre-one transport sources have Möbius sign `-1`: the source is the prime
`q` itself. -/
theorem moebius_transportProduct_eq_neg_one_of_fibre_one
    {R q c : ℕ}
    (hqPrime : q.Prime)
    (hc : 1 ≤ c)
    (hprod : c * q ≤ squareRootEndpoint R)
    (hfibre : transportReciprocalFibre R q = 1) :
    μ (c * q) = -1 := by
  have hc1 := transportCofactor_eq_one_of_fibre_one
    (R := R) (q := q) (c := c) hqPrime.pos hc hprod hfibre
  subst c
  simp [ArithmeticFunction.moebius_apply_prime hqPrime]

/-- The physical middle slot cannot occur in reciprocal fibre `1` for an odd
prime.  Thus the top prime fibre is supported only on the four outer positions
of the six-site transition. -/
theorem fibre_one_middle_threeSlot_impossible
    {R q c k : ℕ}
    (hqPrime : q.Prime)
    (hq2 : 2 < q)
    (hc : 1 ≤ c)
    (hprod : c * q ≤ squareRootEndpoint R)
    (hfibre : transportReciprocalFibre R q = 1)
    (hmiddle : c * q = threeSlotValue k 1) :
    False := by
  have hc1 := transportCofactor_eq_one_of_fibre_one
    (R := R) (q := q) (c := c) hqPrime.pos hc hprod hfibre
  subst c
  simp only [one_mul] at hmiddle
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
  rcases hqOdd with ⟨a, ha⟩
  unfold threeSlotValue at hmiddle
  omega

/-- The same fibre-one middle-slot exclusion holds in the destination cell. -/
theorem fibre_one_destination_middle_impossible
    {R q c k : ℕ}
    (hqPrime : q.Prime)
    (hq2 : 2 < q)
    (hc : 1 ≤ c)
    (hprod : c * q ≤ squareRootEndpoint R)
    (hfibre : transportReciprocalFibre R q = 1)
    (hmiddle : c * q = threeSlotValue (k + 1) 1) :
    False := by
  exact fibre_one_middle_threeSlot_impossible
    hqPrime hq2 hc hprod hfibre hmiddle

/-! ## Exact restricted operator and Gram class -/

/-- The six active slot/sign labels in a fixed distinguished-prime fibre. -/
abbrev PrimeActiveLabel := Fin 3 × Bool

/-- There are exactly six active slot/sign labels. -/
theorem primeActiveLabel_card : Fintype.card PrimeActiveLabel = 6 := by
  native_decide

/-- Exact `13`-coefficient operator class forced by the distinguished-prime
support theorem.  The absent active-to-active block is not a hypothesis: it is
removed from the data structure itself. -/
structure RestrictedPrimeTransitionOperator where
  inactiveInactive : ℂ
  inactiveToActive : PrimeActiveLabel → ℂ
  activeToInactive : PrimeActiveLabel → ℂ

namespace RestrictedPrimeTransitionOperator

/-- Matrix coefficient of the restricted operator. -/
def coeff (A : RestrictedPrimeTransitionOperator) :
    SignedPrimeHitState → SignedPrimeHitState → ℂ
  | none, none => A.inactiveInactive
  | none, some t => A.inactiveToActive t
  | some s, none => A.activeToInactive s
  | some _, some _ => 0

@[simp] theorem coeff_none_none (A : RestrictedPrimeTransitionOperator) :
    A.coeff none none = A.inactiveInactive := rfl

@[simp] theorem coeff_none_some
    (A : RestrictedPrimeTransitionOperator) (t : PrimeActiveLabel) :
    A.coeff none (some t) = A.inactiveToActive t := rfl

@[simp] theorem coeff_some_none
    (A : RestrictedPrimeTransitionOperator) (s : PrimeActiveLabel) :
    A.coeff (some s) none = A.activeToInactive s := rfl

@[simp] theorem coeff_some_some
    (A : RestrictedPrimeTransitionOperator) (s t : PrimeActiveLabel) :
    A.coeff (some s) (some t) = 0 := rfl

/-- Every coefficient outside the arithmetic `13`-entry support vanishes. -/
theorem coeff_eq_zero_of_not_admissible
    (A : RestrictedPrimeTransitionOperator)
    (s t : SignedPrimeHitState)
    (h : ¬FixedPrimeTransitionAdmissible s t) :
    A.coeff s t = 0 := by
  rcases s with _ | s
  · exact (h (Or.inl rfl)).elim
  rcases t with _ | t
  · exact (h (Or.inr rfl)).elim
  rfl

/-- A raw kernel has the distinguished-prime restricted support exactly when its
active-to-active block vanishes. -/
def IsRestrictedPrimeKernel
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ) : Prop :=
  ∀ s t : PrimeActiveLabel, K (some s) (some t) = 0

/-- Package any raw kernel into its three surviving coefficient families. -/
def ofKernel
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ) :
    RestrictedPrimeTransitionOperator where
  inactiveInactive := K none none
  inactiveToActive := fun t => K none (some t)
  activeToInactive := fun s => K (some s) none

/-- The restricted structure represents every raw kernel with the certified
support, coefficient-for-coefficient. -/
theorem coeff_ofKernel_eq
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (hK : IsRestrictedPrimeKernel K)
    (s t : SignedPrimeHitState) :
    (ofKernel K).coeff s t = K s t := by
  rcases s with _ | s
  · rcases t with _ | t <;> rfl
  rcases t with _ | t
  · rfl
  · exact (hK s t).symm

/-- Signed active input recombination feeding the unique inactive output. -/
def activeInputForm
    (A : RestrictedPrimeTransitionOperator)
    (x : SignedPrimeHitState → ℂ) : ℂ :=
  ∑ t : PrimeActiveLabel, A.inactiveToActive t * x (some t)

/-- Squared coefficient energy feeding the six active outputs from the unique
inactive input. -/
def activeOutputEnergy (A : RestrictedPrimeTransitionOperator) : ℝ :=
  ∑ s : PrimeActiveLabel, ‖A.activeToInactive s‖ ^ 2

/-- Exact action of the restricted operator.  All active input coordinates are
recombined before the norm at the inactive output. -/
def action
    (A : RestrictedPrimeTransitionOperator)
    (x : SignedPrimeHitState → ℂ) : SignedPrimeHitState → ℂ
  | none => A.inactiveInactive * x none + A.activeInputForm x
  | some s => A.activeToInactive s * x none

@[simp] theorem action_none
    (A : RestrictedPrimeTransitionOperator)
    (x : SignedPrimeHitState → ℂ) :
    A.action x none = A.inactiveInactive * x none + A.activeInputForm x := rfl

@[simp] theorem action_some
    (A : RestrictedPrimeTransitionOperator)
    (x : SignedPrimeHitState → ℂ)
    (s : PrimeActiveLabel) :
    A.action x (some s) = A.activeToInactive s * x none := rfl

/-- Exact active-output energy.  Because the active-to-active block is zero, all
six active outputs depend on the same scalar inactive input. -/
theorem sum_norm_action_active_sq
    (A : RestrictedPrimeTransitionOperator)
    (x : SignedPrimeHitState → ℂ) :
    (∑ s : PrimeActiveLabel, ‖A.action x (some s)‖ ^ 2) =
      ‖x none‖ ^ 2 * A.activeOutputEnergy := by
  calc
    (∑ s : PrimeActiveLabel, ‖A.action x (some s)‖ ^ 2) =
        ∑ s : PrimeActiveLabel,
          ‖A.activeToInactive s‖ ^ 2 * ‖x none‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [mul_pow]
    _ = (∑ s : PrimeActiveLabel, ‖A.activeToInactive s‖ ^ 2) *
        ‖x none‖ ^ 2 := by
      rw [Finset.sum_mul]
    _ = ‖x none‖ ^ 2 * A.activeOutputEnergy := by
      unfold activeOutputEnergy
      ring

end RestrictedPrimeTransitionOperator

/-- Nonnegative weights for the inactive scalar and the six active coordinates. -/
structure RestrictedPrimeLyapunovWeights where
  inactive : ℝ
  active : ℝ
  inactive_nonneg : 0 ≤ inactive
  active_nonneg : 0 ≤ active

/-- Weighted energy on the certified seven-state fixed-prime space. -/
def restrictedPrimeLyapunov
    (w : RestrictedPrimeLyapunovWeights)
    (x : SignedPrimeHitState → ℂ) : ℝ :=
  w.inactive * ‖x none‖ ^ 2 +
    w.active * ∑ s : PrimeActiveLabel, ‖x (some s)‖ ^ 2

/-- The restricted Lyapunov energy is nonnegative. -/
theorem restrictedPrimeLyapunov_nonneg
    (w : RestrictedPrimeLyapunovWeights)
    (x : SignedPrimeHitState → ℂ) :
    0 ≤ restrictedPrimeLyapunov w x := by
  unfold restrictedPrimeLyapunov
  apply add_nonneg
  · exact mul_nonneg w.inactive_nonneg (sq_nonneg _)
  · exact mul_nonneg w.active_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **Exact restricted Lyapunov identity.**  The only active-input interaction is
its fully signed linear form feeding the inactive output; the active outputs
carry only the inactive input.  No channelwise absolute values are introduced. -/
theorem restrictedPrimeLyapunov_action_exact
    (w : RestrictedPrimeLyapunovWeights)
    (A : RestrictedPrimeTransitionOperator)
    (x : SignedPrimeHitState → ℂ) :
    restrictedPrimeLyapunov w (A.action x) =
      w.inactive *
          ‖A.inactiveInactive * x none + A.activeInputForm x‖ ^ 2 +
        w.active *
          (‖x none‖ ^ 2 * A.activeOutputEnergy) := by
  unfold restrictedPrimeLyapunov
  rw [RestrictedPrimeTransitionOperator.sum_norm_action_active_sq]
  rfl

/-- The still-open analytic obligation on this exact sparse class. -/
def RestrictedPrimeLyapunovContraction
    (w : RestrictedPrimeLyapunovWeights)
    (A : RestrictedPrimeTransitionOperator)
    (rho : ℝ) : Prop :=
  ∀ x : SignedPrimeHitState → ℂ,
    restrictedPrimeLyapunov w (A.action x) ≤
      rho * restrictedPrimeLyapunov w x

/-- The contraction problem is exactly the reduced signed inequality exposed by
the sparse action formula.  This theorem introduces no estimate. -/
theorem restrictedPrimeLyapunovContraction_iff_reduced
    (w : RestrictedPrimeLyapunovWeights)
    (A : RestrictedPrimeTransitionOperator)
    (rho : ℝ) :
    RestrictedPrimeLyapunovContraction w A rho ↔
      ∀ x : SignedPrimeHitState → ℂ,
        w.inactive *
            ‖A.inactiveInactive * x none + A.activeInputForm x‖ ^ 2 +
          w.active *
            (‖x none‖ ^ 2 * A.activeOutputEnergy) ≤
          rho * restrictedPrimeLyapunov w x := by
  unfold RestrictedPrimeLyapunovContraction
  constructor
  · intro h x
    rw [← restrictedPrimeLyapunov_action_exact w A x]
    exact h x
  · intro h x
    rw [restrictedPrimeLyapunov_action_exact]
    exact h x

/-- Finite Hermitian pairing written in the inactive/active decomposition. -/
def restrictedPrimeStateInner
    (x y : SignedPrimeHitState → ℂ) : ℂ :=
  star (x none) * y none +
    ∑ s : PrimeActiveLabel, star (x (some s)) * y (some s)

/-- Basis vector of one active slot/sign coordinate. -/
def restrictedPrimeActiveBasis
    (i : PrimeActiveLabel) : SignedPrimeHitState → ℂ
  | none => 0
  | some j => if j = i then 1 else 0

/-- Basis vector of the unique inactive coordinate. -/
def restrictedPrimeInactiveBasis : SignedPrimeHitState → ℂ
  | none => 1
  | some _ => 0

@[simp] theorem action_restrictedPrimeActiveBasis_none
    (A : RestrictedPrimeTransitionOperator)
    (i : PrimeActiveLabel) :
    A.action (restrictedPrimeActiveBasis i) none = A.inactiveToActive i := by
  classical
  simp [RestrictedPrimeTransitionOperator.action,
    RestrictedPrimeTransitionOperator.activeInputForm,
    restrictedPrimeActiveBasis]

@[simp] theorem action_restrictedPrimeActiveBasis_some
    (A : RestrictedPrimeTransitionOperator)
    (i s : PrimeActiveLabel) :
    A.action (restrictedPrimeActiveBasis i) (some s) = 0 := by
  simp [RestrictedPrimeTransitionOperator.action, restrictedPrimeActiveBasis]

@[simp] theorem action_restrictedPrimeInactiveBasis_none
    (A : RestrictedPrimeTransitionOperator) :
    A.action restrictedPrimeInactiveBasis none = A.inactiveInactive := by
  classical
  simp [RestrictedPrimeTransitionOperator.action,
    RestrictedPrimeTransitionOperator.activeInputForm,
    restrictedPrimeInactiveBasis]

@[simp] theorem action_restrictedPrimeInactiveBasis_some
    (A : RestrictedPrimeTransitionOperator)
    (s : PrimeActiveLabel) :
    A.action restrictedPrimeInactiveBasis (some s) = A.activeToInactive s := by
  simp [RestrictedPrimeTransitionOperator.action, restrictedPrimeInactiveBasis]

/-- Active-active Gram entry of the restricted operator. -/
def restrictedPrimeActiveGramEntry
    (A : RestrictedPrimeTransitionOperator)
    (i j : PrimeActiveLabel) : ℂ :=
  restrictedPrimeStateInner
    (A.action (restrictedPrimeActiveBasis i))
    (A.action (restrictedPrimeActiveBasis j))

/-- **Rank-one active Gram block.**  All six-by-six active Gram interactions
factor through the single inactive output coordinate. -/
theorem restrictedPrimeActiveGramEntry_eq_outer
    (A : RestrictedPrimeTransitionOperator)
    (i j : PrimeActiveLabel) :
    restrictedPrimeActiveGramEntry A i j =
      star (A.inactiveToActive i) * A.inactiveToActive j := by
  unfold restrictedPrimeActiveGramEntry restrictedPrimeStateInner
  rw [action_restrictedPrimeActiveBasis_none A i,
    action_restrictedPrimeActiveBasis_none A j]
  simp only [action_restrictedPrimeActiveBasis_some, star_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- Inactive-to-active Gram entry. -/
def restrictedPrimeInactiveActiveGramEntry
    (A : RestrictedPrimeTransitionOperator)
    (j : PrimeActiveLabel) : ℂ :=
  restrictedPrimeStateInner
    (A.action restrictedPrimeInactiveBasis)
    (A.action (restrictedPrimeActiveBasis j))

/-- Every inactive-to-active Gram entry also factors through the inactive scalar
coefficient. -/
theorem restrictedPrimeInactiveActiveGramEntry_eq
    (A : RestrictedPrimeTransitionOperator)
    (j : PrimeActiveLabel) :
    restrictedPrimeInactiveActiveGramEntry A j =
      star A.inactiveInactive * A.inactiveToActive j := by
  unfold restrictedPrimeInactiveActiveGramEntry restrictedPrimeStateInner
  rw [action_restrictedPrimeInactiveBasis_none,
    action_restrictedPrimeActiveBasis_none A j]
  simp only [action_restrictedPrimeActiveBasis_some, mul_zero,
    Finset.sum_const_zero, add_zero]

/-- Active-to-inactive Gram entry. -/
def restrictedPrimeActiveInactiveGramEntry
    (A : RestrictedPrimeTransitionOperator)
    (i : PrimeActiveLabel) : ℂ :=
  restrictedPrimeStateInner
    (A.action (restrictedPrimeActiveBasis i))
    (A.action restrictedPrimeInactiveBasis)

/-- Adjoint cross block of the restricted Gram form. -/
theorem restrictedPrimeActiveInactiveGramEntry_eq
    (A : RestrictedPrimeTransitionOperator)
    (i : PrimeActiveLabel) :
    restrictedPrimeActiveInactiveGramEntry A i =
      star (A.inactiveToActive i) * A.inactiveInactive := by
  unfold restrictedPrimeActiveInactiveGramEntry restrictedPrimeStateInner
  rw [action_restrictedPrimeActiveBasis_none A i,
    action_restrictedPrimeInactiveBasis_none]
  simp only [action_restrictedPrimeActiveBasis_some, star_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- Inactive-inactive Gram entry. -/
def restrictedPrimeInactiveGramEntry
    (A : RestrictedPrimeTransitionOperator) : ℂ :=
  restrictedPrimeStateInner
    (A.action restrictedPrimeInactiveBasis)
    (A.action restrictedPrimeInactiveBasis)

/-- Exact inactive Gram entry: the scalar self-term plus all six outgoing
inactive-to-active coefficient squares, with no other terms. -/
theorem restrictedPrimeInactiveGramEntry_eq
    (A : RestrictedPrimeTransitionOperator) :
    restrictedPrimeInactiveGramEntry A =
      star A.inactiveInactive * A.inactiveInactive +
        ∑ s : PrimeActiveLabel,
          star (A.activeToInactive s) * A.activeToInactive s := by
  unfold restrictedPrimeInactiveGramEntry restrictedPrimeStateInner
  rw [action_restrictedPrimeInactiveBasis_none]
  simp only [action_restrictedPrimeInactiveBasis_some]

/-! ## Real-pair representation of the reduced complex channel -/

/-- The paper's real-pair coordinate space for one complex number. -/
abbrev ComplexRealPair := ℝ × ℝ

/-- Exact real-pair map `phi(a+bi) = (a-b, a+b)`. -/
def complexRealPair (z : ℂ) : ComplexRealPair :=
  (z.re - z.im, z.re + z.im)

/-- Explicit inverse of `complexRealPair`. -/
def complexOfRealPair (p : ComplexRealPair) : ℂ :=
  ⟨(p.1 + p.2) / 2, (p.2 - p.1) / 2⟩

@[simp] theorem complexOfRealPair_complexRealPair (z : ℂ) :
    complexOfRealPair (complexRealPair z) = z := by
  apply Complex.ext
  · simp [complexOfRealPair, complexRealPair]
  · simp [complexOfRealPair, complexRealPair]

@[simp] theorem complexRealPair_complexOfRealPair (p : ComplexRealPair) :
    complexRealPair (complexOfRealPair p) = p := by
  rcases p with ⟨x, y⟩
  ext <;> simp [complexOfRealPair, complexRealPair] <;> ring

/-- Euclidean square in the paper's real-pair coordinates. -/
def complexRealPairEnergy (p : ComplexRealPair) : ℝ :=
  p.1 ^ 2 + p.2 ^ 2

/-- The real-pair map is a scaled isometry: pair energy is twice complex norm
square. -/
theorem complexRealPairEnergy_complexRealPair (z : ℂ) :
    complexRealPairEnergy (complexRealPair z) = 2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold complexRealPairEnergy complexRealPair
  ring

open ComplexConjugate

/-- Complex conjugation is coordinate swap in real-pair coordinates. -/
@[simp] theorem complexRealPair_conj (z : ℂ) :
    complexRealPair (conj z) =
      ((complexRealPair z).2, (complexRealPair z).1) := by
  ext <;> simp [complexRealPair, sub_eq_add_neg]

/-- Componentwise pair addition. -/
def complexRealPairAdd (p q : ComplexRealPair) : ComplexRealPair :=
  (p.1 + q.1, p.2 + q.2)

/-- Real scalar multiplication in pair coordinates. -/
def complexRealPairScale (r : ℝ) (p : ComplexRealPair) : ComplexRealPair :=
  (r * p.1, r * p.2)

/-- Multiplication transported to real-pair coordinates, in the explicit form
from the real-pair representation. -/
def complexRealPairMul (p q : ComplexRealPair) : ComplexRealPair :=
  let realPart := (p.1 * q.2 + p.2 * q.1) / 2
  let imagPart := (p.2 * q.2 - p.1 * q.1) / 2
  (realPart - imagPart, realPart + imagPart)

@[simp] theorem complexRealPair_add (z w : ℂ) :
    complexRealPair (z + w) =
      complexRealPairAdd (complexRealPair z) (complexRealPair w) := by
  ext <;> simp [complexRealPair, complexRealPairAdd] <;> ring

@[simp] theorem complexRealPair_real_mul (r : ℝ) (z : ℂ) :
    complexRealPair ((r : ℂ) * z) =
      complexRealPairScale r (complexRealPair z) := by
  ext <;> simp [complexRealPair, complexRealPairScale] <;> ring

@[simp] theorem complexRealPair_mul (z w : ℂ) :
    complexRealPair (z * w) =
      complexRealPairMul (complexRealPair z) (complexRealPair w) := by
  ext <;> simp [complexRealPair, complexRealPairMul] <;> ring

/-- The two-complex-scalar input energy after the rank-one active reduction. -/
def restrictedPrimeTwoScalarInputEnergy
    (r : ℝ) (u v : ℂ) : ℝ :=
  ‖u‖ ^ 2 + r * ‖v‖ ^ 2

/-- The corresponding output energy.  `beta` and `gamma` are the Euclidean
lengths of the two six-coordinate coefficient families. -/
def restrictedPrimeTwoScalarOutputEnergy
    (a : ℂ) (beta gamma r : ℝ) (u v : ℂ) : ℝ :=
  ‖a * u + (beta : ℂ) * v‖ ^ 2 +
    r * gamma ^ 2 * ‖u‖ ^ 2

/-- The inactive output coordinate written purely in real-pair arithmetic. -/
def restrictedPrimeRealPairInactive
    (aPair : ComplexRealPair) (beta : ℝ)
    (uPair vPair : ComplexRealPair) : ComplexRealPair :=
  complexRealPairAdd
    (complexRealPairMul aPair uPair)
    (complexRealPairScale beta vPair)

/-- Real-pair input energy.  It is exactly twice the complex input energy under
`complexRealPair`. -/
def restrictedPrimeRealPairInputEnergy
    (r : ℝ) (uPair vPair : ComplexRealPair) : ℝ :=
  complexRealPairEnergy uPair + r * complexRealPairEnergy vPair

/-- Real-pair output energy for the reduced fixed-prime channel. -/
def restrictedPrimeRealPairOutputEnergy
    (aPair : ComplexRealPair) (beta gamma r : ℝ)
    (uPair vPair : ComplexRealPair) : ℝ :=
  complexRealPairEnergy
      (restrictedPrimeRealPairInactive aPair beta uPair vPair) +
    r * gamma ^ 2 * complexRealPairEnergy uPair

@[simp] theorem restrictedPrimeRealPairInactive_complexRealPair
    (a u v : ℂ) (beta : ℝ) :
    restrictedPrimeRealPairInactive
        (complexRealPair a) beta (complexRealPair u) (complexRealPair v) =
      complexRealPair (a * u + (beta : ℂ) * v) := by
  rw [complexRealPair_add, complexRealPair_mul a u,
    complexRealPair_real_mul beta v]
  rfl

/-- Exact scaling relation for the reduced input energy. -/
theorem restrictedPrimeRealPairInputEnergy_complexRealPair
    (r : ℝ) (u v : ℂ) :
    restrictedPrimeRealPairInputEnergy r (complexRealPair u) (complexRealPair v) =
      2 * restrictedPrimeTwoScalarInputEnergy r u v := by
  unfold restrictedPrimeRealPairInputEnergy restrictedPrimeTwoScalarInputEnergy
  rw [complexRealPairEnergy_complexRealPair, complexRealPairEnergy_complexRealPair]
  ring

/-- Exact scaling relation for the reduced output energy. -/
theorem restrictedPrimeRealPairOutputEnergy_complexRealPair
    (a u v : ℂ) (beta gamma r : ℝ) :
    restrictedPrimeRealPairOutputEnergy
        (complexRealPair a) beta gamma r (complexRealPair u) (complexRealPair v) =
      2 * restrictedPrimeTwoScalarOutputEnergy a beta gamma r u v := by
  unfold restrictedPrimeRealPairOutputEnergy restrictedPrimeTwoScalarOutputEnergy
  rw [restrictedPrimeRealPairInactive_complexRealPair,
    complexRealPairEnergy_complexRealPair,
    complexRealPairEnergy_complexRealPair]
  ring

/-- Complex form of the reduced two-scalar contraction problem. -/
def RestrictedPrimeTwoScalarContraction
    (a : ℂ) (beta gamma r rho : ℝ) : Prop :=
  ∀ u v : ℂ,
    restrictedPrimeTwoScalarOutputEnergy a beta gamma r u v ≤
      rho * restrictedPrimeTwoScalarInputEnergy r u v

/-- Purely real-pair form of the same reduced contraction problem. -/
def RestrictedPrimeRealPairContraction
    (a : ℂ) (beta gamma r rho : ℝ) : Prop :=
  ∀ uPair vPair : ComplexRealPair,
    restrictedPrimeRealPairOutputEnergy
        (complexRealPair a) beta gamma r uPair vPair ≤
      rho * restrictedPrimeRealPairInputEnergy r uPair vPair

/-- **Exact real-pair bridge.**  The reduced complex contraction problem is
logically equivalent to a four-real-variable quadratic inequality. -/
theorem restrictedPrimeTwoScalarContraction_iff_realPair
    (a : ℂ) (beta gamma r rho : ℝ) :
    RestrictedPrimeTwoScalarContraction a beta gamma r rho ↔
      RestrictedPrimeRealPairContraction a beta gamma r rho := by
  constructor
  · intro h uPair vPair
    have hc := h (complexOfRealPair uPair) (complexOfRealPair vPair)
    have hout :
        restrictedPrimeRealPairOutputEnergy
            (complexRealPair a) beta gamma r uPair vPair =
          2 * restrictedPrimeTwoScalarOutputEnergy
            a beta gamma r (complexOfRealPair uPair) (complexOfRealPair vPair) := by
      simpa using restrictedPrimeRealPairOutputEnergy_complexRealPair
        a (complexOfRealPair uPair) (complexOfRealPair vPair) beta gamma r
    have hin :
        restrictedPrimeRealPairInputEnergy r uPair vPair =
          2 * restrictedPrimeTwoScalarInputEnergy
            r (complexOfRealPair uPair) (complexOfRealPair vPair) := by
      simpa using restrictedPrimeRealPairInputEnergy_complexRealPair
        r (complexOfRealPair uPair) (complexOfRealPair vPair)
    rw [hout, hin]
    nlinarith
  · intro h u v
    have hr := h (complexRealPair u) (complexRealPair v)
    rw [restrictedPrimeRealPairOutputEnergy_complexRealPair,
      restrictedPrimeRealPairInputEnergy_complexRealPair] at hr
    nlinarith

end RHLean.Analysis
