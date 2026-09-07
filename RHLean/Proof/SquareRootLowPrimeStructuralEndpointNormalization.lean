import Mathlib
import RHLean.Proof.SquareRootLowPrimeStructuralKey
import RHLean.Proof.SquareRootLowPrimeHorizontalTerminalCoverage
import RHLean.Proof.SquareRootLowPrimeFirstOwnerFalloutWidth

/-!
# Well-founded structural endpoint normalization

A terminal processed seat can fail to use an apparently eligible prime because
its proposed neighbour was consumed at an earlier stage.  The displacement
owner theorem makes that obstruction structural: the blocker belongs to a
strict prefix of the current schedule.

This file turns that observation into a well-founded normalization.  Every
recursive blocker flip shortens the actual prime schedule and preserves the
canonical `(shallowBase, seat)` key.  The endpoint predicate here is only a
normalization stop condition; the final no-liberty classifier subsequently
refines normalized states into Head, Partial, BornExit, with RootEquality as the
forced residual.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Schedule-generic displacement: if a terminal state still has its `p`-neighbor
in the original carrier, that neighbor was consumed at one concrete coordinate
in the strict prefix before `p`.  No numeric ordering of the prime labels is
needed here; the structural decrease is the shortening of the prefix. -/
theorem squareRootLowPrimeProcessedSeatTerminal_neighbor_has_prefix_blocker
    (pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
      (pre ++ p :: post) S)
    (hxHead : x ≠ none)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hneighbor : squareRootLowPrimeProcessedSeatExtend p x ∈ S) :
    ∃ pre' q post' z,
      pre = pre' ++ q :: post' ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre' S ∧
        ((squareRootLowPrimeProcessedSeatExtend p x ∈
              squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q
              (squareRootLowPrimeProcessedSeatExtend p x)) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            squareRootLowPrimeProcessedSeatExtend p x =
              squareRootLowPrimeProcessedSeatExtend q z)) := by
  have hxRewritten :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier post
        (squareRootLowPrimeProcessedSeatFrontierStep
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p) := by
    rw [squareRootLowPrimeProcessedSeatMatchingFrontier_append] at hx
    simpa [squareRootLowPrimeProcessedSeatMatchingFrontier] using hx
  have hxStep :
      x ∈ squareRootLowPrimeProcessedSeatFrontierStep
        (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' post _ hxRewritten
  have hneighborLost :
      squareRootLowPrimeProcessedSeatExtend p x ∉
        squareRootLowPrimeProcessedSeatMatchingFrontier pre S := by
    intro hneighborPre
    have hxPre := (Finset.mem_sdiff.mp hxStep).1
    have hxLower :
        x ∈ squareRootLowPrimeProcessedSeatPairLower
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
      mem_squareRootLowPrimeProcessedSeatPairLower.mpr
        ⟨hxPre, hxHead, hpFresh, hneighborPre⟩
    exact (Finset.mem_sdiff.mp hxStep).2
      (Finset.mem_union.mpr (Or.inl hxLower))
  rcases squareRootLowPrimeProcessedSeat_removed_has_owner
      pre S hneighbor hneighborLost with
    ⟨pre', q, post', hpreSplit, hpaired⟩
  rcases squareRootLowPrimeProcessedSeatPaired_has_partner hpaired with
    ⟨z, hz, hedge⟩
  exact ⟨pre', q, post', z, hpreSplit, hz, hedge⟩

/-- The same prefix-blocker statement for a genuine intrinsic terminal residual.
If the proposed child were absent from the original carrier, `p` would already
be its intrinsic first owner; therefore residuality forces the neighbor to be
present and the schedule-generic displacement theorem applies. -/
theorem squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_has_prefix_blocker
    (ps pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxResidual :
      x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual ps S)
    (hps : ps = pre ++ p :: post)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hlpf : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p) :
    ∃ pre' q post' z,
      pre = pre' ++ q :: post' ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre' S ∧
        ((squareRootLowPrimeProcessedSeatExtend p x ∈
              squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q
              (squareRootLowPrimeProcessedSeatExtend p x)) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            squareRootLowPrimeProcessedSeatExtend p x =
              squareRootLowPrimeProcessedSeatExtend q z)) := by
  have hxResidual' :
      x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S
        (squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S) := by
    simpa [squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual] using
      hxResidual
  have hxResidualData :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp hxResidual'
  have hxTargetData :
      x ≠ none ∧
        x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S :=
    Finset.mem_erase.mp hxResidualData.1
  have hxHead : x ≠ none := hxTargetData.1
  have hxTerminal :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S :=
    hxTargetData.2
  have hxS : x ∈ S :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps S hxTerminal
  have hpList : p ∈ ps := by
    rw [hps]
    simp
  have hnone :=
    (squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_none_iff ps S x).mp
      hxResidualData.2
  have hneighbor : squareRootLowPrimeProcessedSeatExtend p x ∈ S := by
    by_contra hmissing
    have hfall :
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p :=
      mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
        ⟨hxS, hxHead, hpFresh, hmissing, hlpf⟩
    exact hnone p hpList hfall
  have hxStage :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
        (pre ++ p :: post) S := by
    rw [← hps]
    exact hxTerminal
  exact squareRootLowPrimeProcessedSeatTerminal_neighbor_has_prefix_blocker
    pre post S hxStage hxHead hpFresh hneighbor

/-- A blocker found in the prefix has strictly smaller structural schedule rank.
This is the well-founded measure used by the terminal traversal. -/
theorem squareRootLowPrimeProcessedSeat_prefixBlocker_length_lt
    {pre pre' post' : List ℕ} {q : ℕ}
    (hsplit : pre = pre' ++ q :: post') :
    pre'.length < pre.length := by
  rw [hsplit, List.length_append, List.length_cons]
  omega

/-- Every blocker partner in a fresh-prime schedule remains in the same
`(shallowBase, seat)` fibre as the terminal state that exposed it. -/
theorem squareRootLowPrimeProcessedSeat_prefixBlocker_structuralKey
    {K U p q : ℕ} {pre post pre' post' : List ℕ}
    {x z : SquareRootLowPrimeProcessedState}
    (hps : squareRootLowPrimeFreshPrimeList K U = pre ++ p :: post)
    (hpre : pre = pre' ++ q :: post')
    (hedge :
      (z = squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x)) ∨
        (squareRootLowPrimeProcessedSeatExtend p x =
          squareRootLowPrimeProcessedSeatExtend q z)) :
    squareRootLowPrimeProcessedSeatStructuralKey K z =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  have hpMem : p ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hps]
    simp
  have hqPre : q ∈ pre := by
    rw [hpre]
    simp
  have hqMem : q ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hps]
    simp [hqPre]
  have hpData := squareRootLowPrimeFreshPrimeList_prime_and_above hpMem
  have hqData := squareRootLowPrimeFreshPrimeList_prime_and_above hqMem
  rcases hedge with hforward | hback
  · rw [hforward,
      squareRootLowPrimeProcessedSeatStructuralKey_extend hqData.1 hqData.2,
      squareRootLowPrimeProcessedSeatStructuralKey_extend hpData.1 hpData.2]
  · have hkey := congrArg
      (squareRootLowPrimeProcessedSeatStructuralKey K) hback
    rw [squareRootLowPrimeProcessedSeatStructuralKey_extend hpData.1 hpData.2,
      squareRootLowPrimeProcessedSeatStructuralKey_extend hqData.1 hqData.2]
      at hkey
    exact hkey.symm

/-- Normalization stop condition.  This is deliberately broader than the final
three explicit classifier branches; RootEquality will be the complement after
Head, Partial and BornExit have been discharged. -/
def SquareRootLowPrimeStructuralEndpointStop
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (x : SquareRootLowPrimeProcessedState) : Prop :=
  x = none ∨
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x ≠ none ∨
      squareRootLowPrimeFirstOwnerAbove ps
        (canonicalLargestPrimeFactor
          (squareRootLowPrimeProcessedStateCofactor x)) = none

/-- **Well-founded alternating blocker normalization.**

Starting from any terminal state of a schedule consisting of actual fresh-prime
coordinates, repeatedly expose the first still-eligible owner.  If its child is
intrinsically absent, stop.  Otherwise terminality forces that child to have
been consumed by an owner in a strict prefix; flip to the blocker partner and
recurse on that prefix.  Hence schedule length decreases at every genuine
displacement.  The endpoint stays in the same `(shallowBase, seat)` fibre. -/
theorem squareRootLowPrimeProcessedSeat_exists_structuralEndpoint
    {R K j U : ℕ}
    (ps : List ℕ) (x : SquareRootLowPrimeProcessedState)
    (hsub : ∀ p ∈ ps, p ∈ squareRootLowPrimeFreshPrimeList K U)
    (hx : x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps
      (squareRootLowPrimeProcessedSeatCarrier R K j U)) :
    ∃ qs y,
      qs.length ≤ ps.length ∧
        (∀ p ∈ qs, p ∈ squareRootLowPrimeFreshPrimeList K U) ∧
        y ∈ squareRootLowPrimeProcessedSeatMatchingFrontier qs
          (squareRootLowPrimeProcessedSeatCarrier R K j U) ∧
        SquareRootLowPrimeStructuralEndpointStop qs
          (squareRootLowPrimeProcessedSeatCarrier R K j U) y ∧
        squareRootLowPrimeProcessedSeatStructuralKey K y =
          squareRootLowPrimeProcessedSeatStructuralKey K x := by
  by_cases hxHead : x = none
  · exact ⟨ps, x, le_rfl, hsub, hx, Or.inl hxHead, rfl⟩
  cases howner : squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps
      (squareRootLowPrimeProcessedSeatCarrier R K j U) x with
  | some p =>
      refine ⟨ps, x, le_rfl, hsub, hx, ?_, rfl⟩
      exact Or.inr (Or.inl (by simp [howner]))
  | none =>
      let L := canonicalLargestPrimeFactor
        (squareRootLowPrimeProcessedStateCofactor x)
      cases hfirst : squareRootLowPrimeFirstOwnerAbove ps L with
      | none =>
          refine ⟨ps, x, le_rfl, hsub, hx, ?_, rfl⟩
          exact Or.inr (Or.inr (by simpa [L] using hfirst))
      | some p =>
          rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
            ⟨pre, post, hps, _hpre, hLp⟩
          have hpPs : p ∈ ps := by
            rw [hps]
            simp
          have hpFreshList : p ∈ squareRootLowPrimeFreshPrimeList K U :=
            hsub p hpPs
          have hpData :=
            squareRootLowPrimeFreshPrimeList_prime_and_above hpFreshList
          have hxCarrier :
              x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
            squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps _ hx
          have hcPos :
              0 < squareRootLowPrimeProcessedStateCofactor x := by
            rcases x with _ | z
            · exact (hxHead rfl).elim
            · have hzAtom :
                  z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
                simpa [squareRootLowPrimeProcessedSeatCarrier] using hxCarrier
              have hcSigned :=
                (mem_squareRootLowPrimeProcessedSeatAtoms.mp hzAtom).1
              have hcRange := (Finset.mem_filter.mp hcSigned).1
              have hcOne := (Finset.mem_Icc.mp hcRange).1
              change 0 < z.1
              omega
          have hpFresh :
              ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x :=
            squareRootLowPrimePrime_fresh_of_lpf_lt hcPos hpData.1
              (by simpa [L] using hLp)
          have hxTarget :
              x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps
                (squareRootLowPrimeProcessedSeatCarrier R K j U) := by
            exact Finset.mem_erase.mpr ⟨hxHead, hx⟩
          have hxResidual :
              x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual ps
                (squareRootLowPrimeProcessedSeatCarrier R K j U) := by
            unfold squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual
            exact
              mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mpr
                ⟨hxTarget, howner⟩
          rcases
              squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_has_prefix_blocker
                ps pre post (squareRootLowPrimeProcessedSeatCarrier R K j U)
                hxResidual hps hpFresh (by simpa [L] using hLp) with
            ⟨pre', q, post', z, hpreSplit, hz, hedge⟩
          have hpreLt : pre'.length < ps.length := by
            have h₁ := squareRootLowPrimeProcessedSeat_prefixBlocker_length_lt
              hpreSplit
            rw [hps, List.length_append, List.length_cons]
            omega
          have hsubPre :
              ∀ r ∈ pre', r ∈ squareRootLowPrimeFreshPrimeList K U := by
            intro r hr
            have hrPre : r ∈ pre := by
              rw [hpreSplit]
              simp [hr]
            have hrPs : r ∈ ps := by
              rw [hps]
              simp [hrPre]
            exact hsub r hrPs
          have hqPre : q ∈ pre := by
            rw [hpreSplit]
            simp
          have hqPs : q ∈ ps := by
            rw [hps]
            simp [hqPre]
          have hqFreshList : q ∈ squareRootLowPrimeFreshPrimeList K U :=
            hsub q hqPs
          have hqData :=
            squareRootLowPrimeFreshPrimeList_prime_and_above hqFreshList
          have hedgeEq :
              z = squareRootLowPrimeProcessedSeatExtend q
                    (squareRootLowPrimeProcessedSeatExtend p x) ∨
                squareRootLowPrimeProcessedSeatExtend p x =
                  squareRootLowPrimeProcessedSeatExtend q z := by
            rcases hedge with hedge | hedge
            · exact Or.inl hedge.2
            · exact Or.inr hedge.2
          have hkeyZX :
              squareRootLowPrimeProcessedSeatStructuralKey K z =
                squareRootLowPrimeProcessedSeatStructuralKey K x := by
            rcases hedgeEq with hforward | hback
            · rw [hforward,
                squareRootLowPrimeProcessedSeatStructuralKey_extend
                  hqData.1 hqData.2,
                squareRootLowPrimeProcessedSeatStructuralKey_extend
                  hpData.1 hpData.2]
            · have hkey := congrArg
                (squareRootLowPrimeProcessedSeatStructuralKey K) hback
              rw [squareRootLowPrimeProcessedSeatStructuralKey_extend
                    hpData.1 hpData.2,
                  squareRootLowPrimeProcessedSeatStructuralKey_extend
                    hqData.1 hqData.2] at hkey
              exact hkey.symm
          rcases squareRootLowPrimeProcessedSeat_exists_structuralEndpoint
              (R := R) (K := K) (j := j) (U := U)
              pre' z hsubPre hz with
            ⟨qs, y, hlen, hsubQs, hy, hstop, hkeyYZ⟩
          refine ⟨qs, y, ?_, hsubQs, hy, hstop, ?_⟩
          · exact hlen.trans (Nat.le_of_lt hpreLt)
          · exact hkeyYZ.trans hkeyZX
termination_by ps.length

decreasing_by
  exact hpreLt

end RHLean.Proof
