import Mathlib
import RHLean.Proof.SquareRootLowPrimeHorizontalTerminalCoverage

/-!
# Canonical prime liberties for finite processed-seat matching

Every state removed by the processed-seat matching is removed in one concrete
fresh-prime pair.  The only states without such an owned prime stage are the
states in the final matching frontier.

For the horizontal first-owner cut, intrinsic child absence in the original
processed carrier is also opened here.  Once the proposed owner `p` is prime,
within the terminal owner cutoff, fresh for the parent, and above the parent's
canonical largest prime, all arithmetic legality of the child is automatic.
Consequently an intrinsically missing child can fail only at one of the two
literal carrier walls:

* its cofactor `p*c` lies beyond the square endpoint; or
* the fixed seat index lies beyond the child's combined response fibre.

The second alternative is the existing parent/child response-window boundary,
not a mutable-row matching skip.

Finally, the quantitative matcher is restricted to genuine Euler-oriented
edges `P⁺(c) < p`.  This is a second zero-mass representation of the same
running state, not a change to the arithmetic response.  A canonical child
owned by `p` cannot be consumed by an earlier canonical coordinate `q < p`.
Therefore the first scheduled owner above `P⁺(c)` either removes the parent or
its child is intrinsically absent from the original carrier.  The resulting
terminal support is exactly the disjoint intrinsic first-owner fallout fibres
plus the explicit head/no-later-owner population.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A concrete prime liberty, together with its chronological location in the
matching list. -/
def SquareRootLowPrimePrimeLibertyData
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ)))
    (x : Option (ℕ × ℕ)) : Prop :=
  ∃ pre p post,
    ps = pre ++ p :: post ∧
      x ∈ squareRootLowPrimeProcessedSeatPaired
        (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p

/-- The exposed no-liberty boundary after every listed prime has been
processed. -/
def squareRootLowPrimeNoLibertyBoundary
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ))) :
    Finset (Option (ℕ × ℕ)) :=
  squareRootLowPrimeProcessedSeatMatchingFrontier ps S

/-- **Canonical-liberty dichotomy.** -/
theorem squareRootLowPrime_mem_noLibertyBoundary_or_primeLiberty
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ)))
    {x : Option (ℕ × ℕ)} (hx : x ∈ S) :
    x ∈ squareRootLowPrimeNoLibertyBoundary ps S ∨
      SquareRootLowPrimePrimeLibertyData ps S x := by
  by_cases hterminal :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S
  · exact Or.inl hterminal
  · exact Or.inr
      (squareRootLowPrimeProcessedSeat_removed_has_owner
        ps S hx hterminal)

/-- **Intrinsic processed-seat fallout has only genuine carrier obstructions.**

Suppose `some (c,s)` is canonical fallout at owner `p` relative to the original
processed carrier at cutoff `U`.  If `p` is prime and `p ≤ U`, then freshness
and `P⁺(c) < p` force the child cofactor `p*c` to have largest prime `p` and
nonzero Möbius weight.  Therefore the child can be absent from the original
carrier only because

`X_R < p*c`

or because its response fibre is too short for the inherited seat index:

`CombinedResponse(p*c) ≤ s`.

In particular, disappearance from a mutable matching row is not one of the
intrinsic obstruction cases. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_carrierObstruction
    {R K j U p c s : ℕ}
    (hp : p.Prime) (hpU : p ≤ U)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootEndpoint R < p * c ∨
      squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s := by
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hparent, _hhead, hpFresh0, hchildMissing0, hrough0⟩
  have hpFresh : ¬ p ∣ c := by
    simpa [squareRootLowPrimeProcessedStateCofactor] using hpFresh0
  have hrough : canonicalLargestPrimeFactor c < p := by
    simpa [squareRootLowPrimeProcessedStateCofactor] using hrough0
  have hchildMissing :
      some (p * c, s) ∉ squareRootLowPrimeProcessedSeatCarrier R K j U := by
    simpa [squareRootLowPrimeProcessedSeatExtend] using hchildMissing0
  have hparentAtom :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
  have hcSigned : c ∈ squareRootLowPrimeProcessedSignedCofactors R U :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).1
  rcases Finset.mem_filter.mp hcSigned with
    ⟨hcRange, _hcOwner, hcMu⟩
  have hcPos : 0 < c := by
    have hcOne : 1 ≤ c := (Finset.mem_Icc.mp hcRange).1
    omega
  by_cases hwall : squareRootEndpoint R < p * c
  · exact Or.inl hwall
  by_cases hseat :
      squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s
  · exact Or.inr hseat
  exfalso
  apply hchildMissing
  have hpcX : p * c ≤ squareRootEndpoint R := Nat.le_of_not_gt hwall
  have hsChild :
      s < squareRootLowPrimeCombinedFreshResponse R K j (p * c) :=
    Nat.lt_of_not_ge hseat
  have hlpfChild : canonicalLargestPrimeFactor (p * c) = p := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hp hrough
    simpa [Nat.mul_comm] using h
  have hmuChild : μ (p * c) ≠ 0 := by
    rw [moebius_prime_mul_eq_neg_of_not_dvd hp hpFresh]
    exact neg_ne_zero.mpr hcMu
  have hchildSigned :
      p * c ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
    unfold squareRootLowPrimeProcessedSignedCofactors
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hpcX⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hp.ne_zero (Nat.ne_of_gt hcPos))
    · exact ⟨by rw [hlpfChild]; exact hpU, hmuChild⟩
  have hchildAtom :
      (p * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hchildSigned, hsChild⟩
  unfold squareRootLowPrimeProcessedSeatCarrier
  exact Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨(p * c, s), hchildAtom, rfl⟩)

/-! ## First scheduled owner above the canonical cofactor owner -/

/-- First listed owner strictly above a numerical cutoff. -/
def squareRootLowPrimeFirstOwnerAbove : List ℕ → ℕ → Option ℕ
  | [], _L => none
  | p :: ps, L =>
      if L < p then some p else squareRootLowPrimeFirstOwnerAbove ps L

/-- There is no later owner exactly when every listed owner is at or below the
cutoff. -/
theorem squareRootLowPrimeFirstOwnerAbove_eq_none_iff
    (ps : List ℕ) (L : ℕ) :
    squareRootLowPrimeFirstOwnerAbove ps L = none ↔
      ∀ p ∈ ps, p ≤ L := by
  induction ps with
  | nil => simp [squareRootLowPrimeFirstOwnerAbove]
  | cons p ps ih =>
      by_cases hLp : L < p
      · simp [squareRootLowPrimeFirstOwnerAbove, hLp]
      · have hpL : p ≤ L := Nat.le_of_not_gt hLp
        simp [squareRootLowPrimeFirstOwnerAbove, hLp, hpL, ih]

/-- If a first owner above `L` exists, the list splits at it and every earlier
coordinate is at or below `L`. -/
theorem squareRootLowPrimeFirstOwnerAbove_some_split
    {ps : List ℕ} {L p : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove ps L = some p) :
    ∃ pre post,
      ps = pre ++ p :: post ∧
        (∀ q ∈ pre, q ≤ L) ∧
        L < p := by
  induction ps with
  | nil =>
      simp [squareRootLowPrimeFirstOwnerAbove] at hfirst
  | cons q qs ih =>
      by_cases hLq : L < q
      · have hqp : q = p := by
          apply Option.some.inj
          simpa [squareRootLowPrimeFirstOwnerAbove, hLq] using hfirst
        subst p
        exact ⟨[], qs, by simp, by simp, hLq⟩
      · have hqL : q ≤ L := Nat.le_of_not_gt hLq
        have htail : squareRootLowPrimeFirstOwnerAbove qs L = some p := by
          simpa [squareRootLowPrimeFirstOwnerAbove, hLq] using hfirst
        rcases ih htail with ⟨pre, post, hsplit, hpre, hLp⟩
        refine ⟨q :: pre, post, ?_, ?_, hLp⟩
        · simp [hsplit]
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hqL
          · exact hpre r hr

/-- Positive processed-seat cofactors really are positive arithmetic states. -/
private theorem squareRootLowPrimeProcessedSeatCofactor_pos_of_mem_carrier
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hxHead : x ≠ none) :
    0 < squareRootLowPrimeProcessedStateCofactor x := by
  rcases x with _ | z
  · exact (hxHead rfl).elim
  · have hzAtom : z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hx
    have hcSigned := (mem_squareRootLowPrimeProcessedSeatAtoms.mp hzAtom).1
    have hcRange := (Finset.mem_filter.mp hcSigned).1
    have hcOne := (Finset.mem_Icc.mp hcRange).1
    change 0 < z.1
    omega

/-- A prime strictly above the largest prime factor of a positive cofactor is
fresh for that cofactor. -/
private theorem squareRootLowPrimePrime_not_dvd_of_lpf_lt
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

/-- **First-later-owner skip lands immediately on the low-owner boundary.**

This theorem records what happens for the older unrestricted-fresh matcher.  It
is retained as a diagnostic; the canonical Euler matcher below eliminates this
skip population entirely. -/
theorem squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_firstOwnerAbove_blocker
    {R K j U p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxResidual :
      x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U))
    (hfirst :
      squareRootLowPrimeFirstOwnerAbove
          (squareRootLowPrimeFreshPrimeList K U)
          (canonicalLargestPrimeFactor
            (squareRootLowPrimeProcessedStateCofactor x)) = some p) :
    ∃ pre post pre' q post' z,
      squareRootLowPrimeFreshPrimeList K U = pre ++ p :: post ∧
        pre = pre' ++ q :: post' ∧
        p.Prime ∧ q.Prime ∧
        q ≤ canonicalLargestPrimeFactor
          (squareRootLowPrimeProcessedStateCofactor x) ∧
        q < p ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre'
          (squareRootLowPrimeProcessedSeatCarrier R K j U) ∧
        ((squareRootLowPrimeProcessedSeatExtend p x ∈
              squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre'
                  (squareRootLowPrimeProcessedSeatCarrier R K j U)) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q
              (squareRootLowPrimeProcessedSeatExtend p x)) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre'
                (squareRootLowPrimeProcessedSeatCarrier R K j U)) q ∧
            squareRootLowPrimeProcessedSeatExtend p x =
              squareRootLowPrimeProcessedSeatExtend q z)) := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, hpre, hLp⟩
  have hpMem : p ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hsplit]
    simp
  have hpPrime : p.Prime := prime_of_mem_squareRootLowPrimeFreshPrimeList hpMem
  have hxResidualData :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp hxResidual
  have hxTargetData := Finset.mem_erase.mp hxResidualData.1
  have hxHead : x ≠ none := hxTargetData.1
  have hxTerminal := hxTargetData.2
  have hxCarrier :
      x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset'
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U) hxTerminal
  have hcPos := squareRootLowPrimeProcessedSeatCofactor_pos_of_mem_carrier
    hxCarrier hxHead
  have hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x :=
    squareRootLowPrimePrime_not_dvd_of_lpf_lt hcPos hpPrime hLp
  have hpreLt : ∀ q ∈ pre, q < p := by
    intro q hq
    exact lt_of_le_of_lt (hpre q hq) hLp
  rcases
      squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_has_earlier_blocker
        (squareRootLowPrimeFreshPrimeList K U) pre post
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        hxResidual hsplit hpFresh hLp hpreLt with
    ⟨pre', q, post', z, hpreSplit, hqp, hz, hedge⟩
  have hqPre : q ∈ pre := by
    rw [hpreSplit]
    simp
  have hqLe := hpre q hqPre
  have hqMem : q ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hsplit]
    simp [hqPre]
  have hqPrime : q.Prime := prime_of_mem_squareRootLowPrimeFreshPrimeList hqMem
  exact ⟨pre, post, pre', q, post', z, hsplit, hpreSplit,
    hpPrime, hqPrime, hqLe, hqp, hz, hedge⟩

/-- Diagnostic residual classification for the older unrestricted-fresh
matcher. -/
theorem squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_noLaterOwner_or_lowBlocker
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxResidual :
      x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)) :
    (∀ p ∈ squareRootLowPrimeFreshPrimeList K U,
        p ≤ canonicalLargestPrimeFactor
          (squareRootLowPrimeProcessedStateCofactor x)) ∨
      ∃ p pre post pre' q post' z,
        squareRootLowPrimeFreshPrimeList K U = pre ++ p :: post ∧
          pre = pre' ++ q :: post' ∧
          p.Prime ∧ q.Prime ∧
          q ≤ canonicalLargestPrimeFactor
            (squareRootLowPrimeProcessedStateCofactor x) ∧
          q < p ∧
          z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre'
            (squareRootLowPrimeProcessedSeatCarrier R K j U) ∧
          ((squareRootLowPrimeProcessedSeatExtend p x ∈
                squareRootLowPrimeProcessedSeatPairLower
                  (squareRootLowPrimeProcessedSeatMatchingFrontier pre'
                    (squareRootLowPrimeProcessedSeatCarrier R K j U)) q ∧
              z = squareRootLowPrimeProcessedSeatExtend q
                (squareRootLowPrimeProcessedSeatExtend p x)) ∨
            (z ∈ squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre'
                  (squareRootLowPrimeProcessedSeatCarrier R K j U)) q ∧
              squareRootLowPrimeProcessedSeatExtend p x =
                squareRootLowPrimeProcessedSeatExtend q z)) := by
  let L := canonicalLargestPrimeFactor
    (squareRootLowPrimeProcessedStateCofactor x)
  cases hfirst :
      squareRootLowPrimeFirstOwnerAbove
        (squareRootLowPrimeFreshPrimeList K U) L with
  | none =>
      left
      simpa [L] using
        (squareRootLowPrimeFirstOwnerAbove_eq_none_iff
          (squareRootLowPrimeFreshPrimeList K U) L).mp hfirst
  | some p =>
      right
      have hblock :=
        squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_firstOwnerAbove_blocker
          hxResidual (by simpa [L] using hfirst)
      rcases hblock with
        ⟨pre, post, pre', q, post', z, hsplit, hpreSplit,
          hpPrime, hqPrime, hqLe, hqp, hz, hedge⟩
      exact ⟨p, pre, post, pre', q, post', z, hsplit, hpreSplit,
        hpPrime, hqPrime, hqLe, hqp, hz, hedge⟩

/-! ## Canonical Euler matching -/

open scoped BigOperators

/-- Lower endpoints of genuine Euler-oriented `p` edges.  This is the ordinary
processed lower-endpoint set, filtered by the condition `P⁺(c) < p`. -/
def squareRootLowPrimeProcessedSeatCanonicalPairLower
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatPairLower S p).filter fun x =>
    canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p

@[simp] theorem mem_squareRootLowPrimeProcessedSeatCanonicalPairLower
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p ↔
      x ∈ squareRootLowPrimeProcessedSeatPairLower S p ∧
        canonicalLargestPrimeFactor
          (squareRootLowPrimeProcessedStateCofactor x) < p := by
  simp [squareRootLowPrimeProcessedSeatCanonicalPairLower]

/-- Upper endpoints of genuine Euler-oriented `p` edges. -/
def squareRootLowPrimeProcessedSeatCanonicalPairUpper
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatCanonicalPairLower S p).image
    (squareRootLowPrimeProcessedSeatExtend p)

/-- Complete canonical population removed at owner `p`. -/
def squareRootLowPrimeProcessedSeatCanonicalPaired
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatCanonicalPairLower S p ∪
    squareRootLowPrimeProcessedSeatCanonicalPairUpper S p

/-- Frontier after removing only genuine Euler-oriented `p` pairs. -/
def squareRootLowPrimeProcessedSeatCanonicalFrontierStep
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  S \ squareRootLowPrimeProcessedSeatCanonicalPaired S p

/-- Canonical lower endpoints are ordinary lower endpoints. -/
theorem squareRootLowPrimeProcessedSeatCanonicalPairLower_subset
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatCanonicalPairLower S p ⊆
      squareRootLowPrimeProcessedSeatPairLower S p := by
  intro x hx
  exact (mem_squareRootLowPrimeProcessedSeatCanonicalPairLower.mp hx).1

/-- Canonical upper endpoints are ordinary upper endpoints. -/
theorem squareRootLowPrimeProcessedSeatCanonicalPairUpper_subset
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatCanonicalPairUpper S p ⊆
      squareRootLowPrimeProcessedSeatPairUpper S p := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨y,
    squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hy, rfl⟩

/-- Canonical lower and upper endpoints are disjoint. -/
theorem squareRootLowPrimeProcessedSeatCanonicalPairLower_disjoint_upper
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Disjoint (squareRootLowPrimeProcessedSeatCanonicalPairLower S p)
      (squareRootLowPrimeProcessedSeatCanonicalPairUpper S p) := by
  rw [Finset.disjoint_left]
  intro x hxLower hxUpper
  exact (Finset.disjoint_left.mp
    (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
    (squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hxLower)
    (squareRootLowPrimeProcessedSeatCanonicalPairUpper_subset S p hxUpper)

/-- Canonical paired populations lie in the current row. -/
theorem squareRootLowPrimeProcessedSeatCanonicalPaired_subset
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatCanonicalPaired S p ⊆ S := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxLower | hxUpper
  · exact squareRootLowPrimeProcessedSeatPairLower_subset S p
      (squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hxLower)
  · exact squareRootLowPrimeProcessedSeatPairUpper_subset S p
      (squareRootLowPrimeProcessedSeatCanonicalPairUpper_subset S p hxUpper)

/-- Canonical upper-endpoint mass is the negative canonical lower-endpoint
mass. -/
theorem squareRootLowPrimeProcessedSeatCanonicalPairUpper_weight_sum_eq_neg_lower
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : p.Prime) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalPairUpper S p,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      -∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  unfold squareRootLowPrimeProcessedSeatCanonicalPairUpper
  calc
    (∑ x ∈ (squareRootLowPrimeProcessedSeatCanonicalPairLower S p).image
        (squareRootLowPrimeProcessedSeatExtend p),
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        squareRootLowPrimeProcessedSeatWeightReal
          (squareRootLowPrimeProcessedSeatExtend p x) := by
      apply Finset.sum_image
      intro a ha b hb hab
      exact squareRootLowPrimeProcessedSeatExtend_injOn hp.pos
        (squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p ha)
        (squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hb) hab
    _ = ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        -squareRootLowPrimeProcessedSeatWeightReal x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp
        (squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hx)
    _ = -∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        squareRootLowPrimeProcessedSeatWeightReal x := by
      rw [Finset.sum_neg_distrib]

/-- Only the canonical paired population receives a zero-mass theorem. -/
theorem squareRootLowPrimeProcessedSeatCanonicalPaired_weight_sum_eq_zero
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : p.Prime) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p,
      squareRootLowPrimeProcessedSeatWeightReal x) = 0 := by
  unfold squareRootLowPrimeProcessedSeatCanonicalPaired
  rw [Finset.sum_union
      (squareRootLowPrimeProcessedSeatCanonicalPairLower_disjoint_upper S p),
    squareRootLowPrimeProcessedSeatCanonicalPairUpper_weight_sum_eq_neg_lower
      S hp]
  ring

/-- One canonical Euler matching step only removes states. -/
theorem squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p ⊆ S := by
  intro x hx
  exact (Finset.mem_sdiff.mp hx).1

/-- The complement of one canonical frontier is exactly its canonical paired
population. -/
theorem squareRootLowPrimeProcessedSeat_sdiff_canonicalFrontierStep_eq_paired
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    S \ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p =
      squareRootLowPrimeProcessedSeatCanonicalPaired S p := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxNotFrontier⟩
    by_contra hxNotPaired
    apply hxNotFrontier
    exact Finset.mem_sdiff.mpr ⟨hxS, hxNotPaired⟩
  · intro hxPaired
    have hxS := squareRootLowPrimeProcessedSeatCanonicalPaired_subset S p hxPaired
    apply Finset.mem_sdiff.mpr
    refine ⟨hxS, ?_⟩
    intro hxFrontier
    exact (Finset.mem_sdiff.mp hxFrontier).2 hxPaired

/-- One canonical Euler matching step preserves signed mass. -/
theorem squareRootLowPrimeProcessedSeat_weight_sum_eq_canonicalFrontierStep
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : p.Prime) :
    (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  have hsubset := squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset S p
  have hsplit :
      (∑ x ∈ S \ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p,
          squareRootLowPrimeProcessedSeatWeightReal x =
        ∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x :=
    Finset.sum_sdiff hsubset
  rw [squareRootLowPrimeProcessedSeat_sdiff_canonicalFrontierStep_eq_paired,
    squareRootLowPrimeProcessedSeatCanonicalPaired_weight_sum_eq_zero S hp]
    at hsplit
  simpa using hsplit.symm

/-- Iterate only genuine Euler-oriented matching edges. -/
def squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState
  | [], S => S
  | p :: ps, S =>
      squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier ps
        (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p)

/-- Canonical matching only removes states. -/
theorem squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_subset
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier ps S ⊆ S := by
  induction ps generalizing S with
  | nil =>
      intro x hx
      simpa [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier] using hx
  | cons p ps ih =>
      exact
        (ih (S := squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p)).trans
          (squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset S p)

/-- Canonical matching respects list concatenation. -/
theorem squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_append
    (pre post : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier (pre ++ post) S =
      squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier post
        (squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre S) := by
  induction pre generalizing S with
  | nil => rfl
  | cons p pre ih =>
      simp only [List.cons_append,
        squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier]
      exact ih (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p)

/-- Iterated canonical matching preserves the complete signed mass. -/
theorem squareRootLowPrimeProcessedSeat_weight_sum_eq_canonicalMatchingFrontier
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier ps S,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hrest : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      calc
        (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
          ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p,
            squareRootLowPrimeProcessedSeatWeightReal x :=
          squareRootLowPrimeProcessedSeat_weight_sum_eq_canonicalFrontierStep S hp
        _ = ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier ps
              (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p),
            squareRootLowPrimeProcessedSeatWeightReal x :=
          ih (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) hrest
        _ = ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier
              (p :: ps) S,
            squareRootLowPrimeProcessedSeatWeightReal x := by rfl

/-- Terminal frontier of the Euler-oriented quantitative matcher. -/
def squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- The canonical terminal frontier is a second exact representation of the
same running imbalance `T(U)`. -/
theorem squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum
    {R K j U : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  have hmatch :=
    squareRootLowPrimeProcessedSeat_weight_sum_eq_canonicalMatchingFrontier
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U)
      (fun p hp => prime_of_mem_squareRootLowPrimeFreshPrimeList hp)
  rw [squareRootLowPrimeProcessedSeatCarrier_mass_eq_runningImbalanceReal hR]
    at hmatch
  exact hmatch.symm

/-- The largest prime of a genuine `p`-extension is exactly `p`. -/
private theorem squareRootLowPrimeProcessedSeatExtend_lpf_of_rough
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxHead : x ≠ none)
    (hcPos : 0 < squareRootLowPrimeProcessedStateCofactor x)
    (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p) :
    canonicalLargestPrimeFactor
        (squareRootLowPrimeProcessedStateCofactor
          (squareRootLowPrimeProcessedSeatExtend p x)) = p := by
  rcases x with _ | z
  · exact (hxHead rfl).elim
  · change canonicalLargestPrimeFactor (p * z.1) = p
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hp hrough
    simpa [Nat.mul_comm] using h

/-- A canonical child owned by `p` cannot be consumed at an earlier canonical
owner `q < p`.  Lower ownership would force `p < q`; upper ownership would give
the same child two distinct canonical largest-prime owners. -/
theorem squareRootLowPrimeProcessedSeatCanonicalChild_not_paired_before_owner
    {S : Finset SquareRootLowPrimeProcessedState}
    {p q : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxHead : x ≠ none)
    (hcPos : 0 < squareRootLowPrimeProcessedStateCofactor x)
    (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p)
    (hqp : q < p)
    (hpositive : ∀ y ∈ S, y ≠ none →
      0 < squareRootLowPrimeProcessedStateCofactor y) :
    squareRootLowPrimeProcessedSeatExtend p x ∉
      squareRootLowPrimeProcessedSeatCanonicalPaired S q := by
  have hlpfP := squareRootLowPrimeProcessedSeatExtend_lpf_of_rough
    hxHead hcPos hp hrough
  intro hpaired
  rcases Finset.mem_union.mp hpaired with hlower | hupper
  · have hqRough :=
      (mem_squareRootLowPrimeProcessedSeatCanonicalPairLower.mp hlower).2
    rw [hlpfP] at hqRough
    omega
  · rcases Finset.mem_image.mp hupper with ⟨y, hyLower, hyEq⟩
    have hyCanonical :=
      mem_squareRootLowPrimeProcessedSeatCanonicalPairLower.mp hyLower
    have hyGeneric := mem_squareRootLowPrimeProcessedSeatPairLower.mp hyCanonical.1
    have hyPos := hpositive y hyGeneric.1 hyGeneric.2.1
    have hlpfQ := squareRootLowPrimeProcessedSeatExtend_lpf_of_rough
      hyGeneric.2.1 hyPos hq hyCanonical.2
    have hEq := congrArg
      (fun t => canonicalLargestPrimeFactor
        (squareRootLowPrimeProcessedStateCofactor t)) hyEq
    change canonicalLargestPrimeFactor
        (squareRootLowPrimeProcessedStateCofactor
          (squareRootLowPrimeProcessedSeatExtend q y)) =
      canonicalLargestPrimeFactor
        (squareRootLowPrimeProcessedStateCofactor
          (squareRootLowPrimeProcessedSeatExtend p x)) at hEq
    rw [hlpfQ, hlpfP] at hEq
    omega

/-- A canonical child survives every earlier canonical owner. -/
theorem squareRootLowPrimeProcessedSeatCanonicalChild_survives_prefix
    (pre : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxHead : x ≠ none)
    (hcPos : 0 < squareRootLowPrimeProcessedStateCofactor x)
    (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p)
    (hprime : ∀ q ∈ pre, q.Prime)
    (hlt : ∀ q ∈ pre, q < p)
    (hpositive : ∀ y ∈ S, y ≠ none →
      0 < squareRootLowPrimeProcessedStateCofactor y)
    (hchild : squareRootLowPrimeProcessedSeatExtend p x ∈ S) :
    squareRootLowPrimeProcessedSeatExtend p x ∈
      squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre S := by
  induction pre generalizing S with
  | nil =>
      simpa [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier] using hchild
  | cons q qs ih =>
      have hqPrime : q.Prime := hprime q (by simp)
      have hqLt : q < p := hlt q (by simp)
      have hnotPaired :=
        squareRootLowPrimeProcessedSeatCanonicalChild_not_paired_before_owner
          hxHead hcPos hp hqPrime hrough hqLt hpositive
      have hstep :
          squareRootLowPrimeProcessedSeatExtend p x ∈
            squareRootLowPrimeProcessedSeatCanonicalFrontierStep S q := by
        unfold squareRootLowPrimeProcessedSeatCanonicalFrontierStep
        exact Finset.mem_sdiff.mpr ⟨hchild, hnotPaired⟩
      have hpositiveStep :
          ∀ y ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S q,
            y ≠ none → 0 < squareRootLowPrimeProcessedStateCofactor y := by
        intro y hy hyHead
        exact hpositive y
          (squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset S q hy)
          hyHead
      have hrestPrime : ∀ r ∈ qs, r.Prime := by
        intro r hr
        exact hprime r (by simp [hr])
      have hrestLt : ∀ r ∈ qs, r < p := by
        intro r hr
        exact hlt r (by simp [hr])
      exact ih
        (S := squareRootLowPrimeProcessedSeatCanonicalFrontierStep S q)
        hrestPrime hrestLt hpositiveStep hstep

/-- **First scheduled owner gives intrinsic fallout for every non-head canonical
terminal survivor.**

Let `p` be the first scheduled prime above `P⁺(x)`.  If the canonical child
`p*x` belonged to the original carrier, it could not be removed by any earlier
canonical owner and therefore would still be present when `p` is processed.
The parent would then be a canonical lower endpoint and could not survive.
Thus terminal survival forces `p*x` to be intrinsically absent, i.e. `x ∈ U_p`.
-/
theorem squareRootLowPrimeProcessedSeatCanonicalTerminal_firstOwnerAbove_mem_falloff
    {R K j U p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxTerminal :
      x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U)
    (hxHead : x ≠ none)
    (hfirst :
      squareRootLowPrimeFirstOwnerAbove
          (squareRootLowPrimeFreshPrimeList K U)
          (canonicalLargestPrimeFactor
            (squareRootLowPrimeProcessedStateCofactor x)) = some p) :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, hpreLe, hLp⟩
  have hpMem : p ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hsplit]
    simp
  have hpPrime : p.Prime := prime_of_mem_squareRootLowPrimeFreshPrimeList hpMem
  have hxCarrier :
      x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_subset
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U) hxTerminal
  have hcPos := squareRootLowPrimeProcessedSeatCofactor_pos_of_mem_carrier
    hxCarrier hxHead
  have hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x :=
    squareRootLowPrimePrime_not_dvd_of_lpf_lt hcPos hpPrime hLp
  have hxSplit :
      x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier
        (pre ++ p :: post)
        (squareRootLowPrimeProcessedSeatCarrier R K j U) := by
    simpa [squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier, hsplit] using
      hxTerminal
  rw [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_append] at hxSplit
  have hxAfterP :
      x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier post
        (squareRootLowPrimeProcessedSeatCanonicalFrontierStep
          (squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre
            (squareRootLowPrimeProcessedSeatCarrier R K j U)) p) := by
    simpa [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier] using hxSplit
  have hxStep :
      x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep
        (squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre
          (squareRootLowPrimeProcessedSeatCarrier R K j U)) p :=
    squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_subset post _ hxAfterP
  have hxPre :
      x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre
        (squareRootLowPrimeProcessedSeatCarrier R K j U) :=
    squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset _ p hxStep
  have hprePrime : ∀ q ∈ pre, q.Prime := by
    intro q hq
    apply prime_of_mem_squareRootLowPrimeFreshPrimeList
    rw [hsplit]
    simp [hq]
  have hpreLt : ∀ q ∈ pre, q < p := by
    intro q hq
    exact lt_of_le_of_lt (hpreLe q hq) hLp
  have hpositiveCarrier :
      ∀ y ∈ squareRootLowPrimeProcessedSeatCarrier R K j U,
        y ≠ none → 0 < squareRootLowPrimeProcessedStateCofactor y := by
    intro y hy hyHead
    exact squareRootLowPrimeProcessedSeatCofactor_pos_of_mem_carrier hy hyHead
  have hchildMissing :
      squareRootLowPrimeProcessedSeatExtend p x ∉
        squareRootLowPrimeProcessedSeatCarrier R K j U := by
    intro hchildCarrier
    have hchildPre :=
      squareRootLowPrimeProcessedSeatCanonicalChild_survives_prefix
        pre (squareRootLowPrimeProcessedSeatCarrier R K j U)
        hxHead hcPos hpPrime hLp hprePrime hpreLt hpositiveCarrier hchildCarrier
    have hxGenericLower :
        x ∈ squareRootLowPrimeProcessedSeatPairLower
          (squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre
            (squareRootLowPrimeProcessedSeatCarrier R K j U)) p :=
      mem_squareRootLowPrimeProcessedSeatPairLower.mpr
        ⟨hxPre, hxHead, hpFresh, hchildPre⟩
    have hxCanonicalLower :
        x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower
          (squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre
            (squareRootLowPrimeProcessedSeatCarrier R K j U)) p :=
      mem_squareRootLowPrimeProcessedSeatCanonicalPairLower.mpr
        ⟨hxGenericLower, hLp⟩
    have hxStepData :
        x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre
              (squareRootLowPrimeProcessedSeatCarrier R K j U) \
            squareRootLowPrimeProcessedSeatCanonicalPaired
              (squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier pre
                (squareRootLowPrimeProcessedSeatCarrier R K j U)) p := by
      simpa [squareRootLowPrimeProcessedSeatCanonicalFrontierStep] using hxStep
    exact (Finset.mem_sdiff.mp hxStepData).2
      (Finset.mem_union.mpr (Or.inl hxCanonicalLower))
  exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
    ⟨hxCarrier, hxHead, hpFresh, hchildMissing, hLp⟩

/-- Explicit terminal heads: the distinguished head and terminal states for
which the schedule contains no owner strictly above their canonical largest
prime. -/
def squareRootLowPrimeProcessedSeatCanonicalTerminalHeads
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U).filter
    fun x =>
      x = none ∨
        squareRootLowPrimeFirstOwnerAbove
          (squareRootLowPrimeFreshPrimeList K U)
          (canonicalLargestPrimeFactor
            (squareRootLowPrimeProcessedStateCofactor x)) = none

/-- Everything outside the explicit heads is the terminal population requiring
an intrinsic owner. -/
def squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U \
    squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U

/-- The head population really is a subset of the canonical terminal frontier. -/
theorem squareRootLowPrimeProcessedSeatCanonicalTerminalHeads_subset
    (R K j U : ℕ) :
    squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U ⊆
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- Assigned terminals and explicit heads are disjoint. -/
theorem squareRootLowPrimeProcessedSeatCanonicalAssigned_disjoint_heads
    (R K j U : ℕ) :
    Disjoint
      (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U)
      (squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U) := by
  rw [Finset.disjoint_left]
  intro x hxAssigned hxHead
  exact (Finset.mem_sdiff.mp hxAssigned).2 hxHead

/-- **No hidden residual.**  Assigned terminals plus the explicit heads are
exactly the canonical terminal frontier. -/
theorem squareRootLowPrimeProcessedSeatCanonicalAssigned_union_heads
    (R K j U : ℕ) :
    squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U ∪
        squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U =
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxAssigned | hxHead
    · exact (Finset.mem_sdiff.mp hxAssigned).1
    · exact squareRootLowPrimeProcessedSeatCanonicalTerminalHeads_subset
        R K j U hxHead
  · intro hxTerminal
    by_cases hxHead :
        x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U
    · exact Finset.mem_union.mpr (Or.inr hxHead)
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_sdiff.mpr ⟨hxTerminal, hxHead⟩))

/-- Every assigned canonical terminal has an actual intrinsic owner `U_p` in
the original carrier. -/
theorem squareRootLowPrimeProcessedSeatCanonicalAssigned_covered
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) :
    ∃ p ∈ squareRootLowPrimeFreshPrimeList K U,
      x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p := by
  have hxData := Finset.mem_sdiff.mp hx
  have hxTerminal := hxData.1
  have hxNotHeads := hxData.2
  have hxHead : x ≠ none := by
    intro hnone
    apply hxNotHeads
    exact Finset.mem_filter.mpr ⟨hxTerminal, Or.inl hnone⟩
  let L := canonicalLargestPrimeFactor
    (squareRootLowPrimeProcessedStateCofactor x)
  cases hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L with
  | none =>
      exfalso
      apply hxNotHeads
      exact Finset.mem_filter.mpr
        ⟨hxTerminal, Or.inr (by simpa [L] using hfirst)⟩
  | some p =>
      have hfall :=
        squareRootLowPrimeProcessedSeatCanonicalTerminal_firstOwnerAbove_mem_falloff
          hxTerminal hxHead (by simpa [L] using hfirst)
      rcases squareRootLowPrimeFirstOwnerAbove_some_split
          (by simpa [L] using hfirst) with
        ⟨pre, post, hsplit, _hpre, _hLp⟩
      refine ⟨p, ?_, hfall⟩
      rw [hsplit]
      simp

/-- **Unique first-owner assignment.**  Every non-head/nonterminal-head state
has exactly one chronological intrinsic owner fibre. -/
theorem squareRootLowPrimeProcessedSeatCanonicalAssigned_existsUnique_firstOwner
    {R K j U : ℕ} :
    ∀ x ∈ squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U,
      ∃! p : ℕ,
        p ∈ squareRootLowPrimeFreshPrimeList K U ∧
          x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice
            (squareRootLowPrimeFreshPrimeList K U)
            (squareRootLowPrimeProcessedSeatCarrier R K j U)
            (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) p := by
  apply squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_unique_of_covered
  intro x hx
  exact squareRootLowPrimeProcessedSeatCanonicalAssigned_covered hx

/-- **Exact mass of the assigned terminal population.**  This is the requested
horizontal cut: only the disjoint `U_p` first-owner fibres remain, with their
actual signed mass retained. -/
theorem squareRootLowPrimeProcessedSeatCanonicalAssigned_weight_sum_eq_firstOwnerMass
    {R K j U : ℕ} :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) := by
  apply
    squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_intrinsicFirstOwnerMass_of_covered
  intro x hx
  exact squareRootLowPrimeProcessedSeatCanonicalAssigned_covered hx

/-- The canonical terminal mass is exactly owner-fallout mass plus the explicit
heads.  There is no ordinary high-terminal residual left in the bookkeeping. -/
theorem squareRootLowPrimeProcessedSeatCanonicalTerminal_weight_sum_eq_firstOwnerMass_add_heads
    {R K j U : ℕ} :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) +
      ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  have hpart := squareRootLowPrimeProcessedSeatCanonicalAssigned_union_heads
    R K j U
  have hdisj := squareRootLowPrimeProcessedSeatCanonicalAssigned_disjoint_heads
    R K j U
  calc
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈
        (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U ∪
          squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U),
        squareRootLowPrimeProcessedSeatWeightReal x := by rw [hpart]
    _ =
      (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) +
      ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x :=
      Finset.sum_union hdisj
    _ =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) +
      ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x := by
      rw [squareRootLowPrimeProcessedSeatCanonicalAssigned_weight_sum_eq_firstOwnerMass]

/-- **Final bookkeeping identity before any estimate.**  The actual running
imbalance is the disjoint intrinsic owner-fallout mass plus the explicit
head/no-later-owner mass.  This is deliberately an identity, not a bound. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_firstOwnerMass_add_heads
    {R K j U : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) +
      ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  rw [← squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum hR]
  exact
    squareRootLowPrimeProcessedSeatCanonicalTerminal_weight_sum_eq_firstOwnerMass_add_heads

end RHLean.Proof
