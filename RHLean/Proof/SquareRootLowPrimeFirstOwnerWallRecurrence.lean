import Mathlib
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity
import RHLean.Proof.LowPrimeParentChildWindowDifference
import RHLean.Proof.SquareRootLowPrimeFirstOwnerFalloutWidth
import RHLean.Proof.SquareRootLowPrimeDescendingPivotStability
import RHLean.Proof.PrimeCombVisualizationDynamics

/-!
# First-owner wall fallout is terminal and has one fresh owner

The exact fallout-width theorem separates intrinsic missing-child states into a
square-wall part and a response-fibre tail.  This file finishes the purely
combinatorial reduction of the square-wall part before any estimate.

A canonical fallout state already survives its own owner step: its child is
missing, so it is not a lower endpoint, and freshness prevents it from being an
upper endpoint.  On a first-owner square wall the parent canonical owner is at
most the shallow cutoff `K`.  Hence there are no scheduled coordinates before
its first owner.  Every later scheduled prime `r` is at least that first owner,
so `X_R < p*c` implies `X_R < r*c`; the `r`-child is intrinsically absent as
well.  The state therefore survives every later canonical matching step.

There is a second collapse.  Since every scheduled prime is strictly above
`K`, the first scheduled owner above any `L <= K` is simply the first element of
the same fresh-prime list.  Thus all first-owner wall states share one fresh
owner.  The wall is not a sum of independent fresh-prime defects.

The final section opens the resulting old-prime Fubini window.  For one old
partner `q`, the cofactor interval is the exact frozen-prime difference

`F_{q^-}(X_R/q) - F_{q^-}(X_R/p)`.

It then proves the literal wall-pair set equality between the cofactor-first and
old-prime-first enumerations.  Summing the moving upper column over old primes
uses the same fresh-prime recurrence and telescopes exactly, leaving only one
fixed-cutoff unfinished-cube column.  Completed predecessor cubes are deleted
pointwise.  No estimate is introduced.

No norm, cardinality estimate, PNT input, Mertens bound, or RH-equivalent input
is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Intrinsic canonical fallout automatically survives the matching step at its
own owner. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_mem_frontierStep
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hfall : x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p := by
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hxS, _hxHead, hpFresh, hchildMissing, _hrough⟩
  unfold squareRootLowPrimeProcessedSeatCanonicalFrontierStep
  apply Finset.mem_sdiff.mpr
  refine ⟨hxS, ?_⟩
  intro hpaired
  rcases Finset.mem_union.mp hpaired with hlower | hupper
  · have hlower' :=
      squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hlower
    exact hchildMissing
      (mem_squareRootLowPrimeProcessedSeatPairLower.mp hlower').2.2.2
  · have hupper' :=
      squareRootLowPrimeProcessedSeatCanonicalPairUpper_subset S p hupper
    exact
      (squareRootLowPrimeProcessedSeat_not_mem_pairUpper_of_fresh hpFresh)
        hupper'

/-- A square-wall `p`-child remains beyond the square endpoint after replacing
`p` by any larger coordinate `r`. -/
theorem squareRootLowPrimeWall_mono
    {R p r c : ℕ} (hpr : p ≤ r)
    (hwall : squareRootEndpoint R < p * c) :
    squareRootEndpoint R < r * c := by
  have hmul : p * c ≤ r * c := Nat.mul_le_mul_right c hpr
  exact hwall.trans_le hmul

/-- Once `r*c` is beyond the square endpoint, no processed seat with that
cofactor can belong to the original carrier. -/
theorem squareRootLowPrimeWall_child_not_mem_processedCarrier
    {R K j U r c s : ℕ}
    (hwall : squareRootEndpoint R < r * c) :
    some (r * c, s) ∉ squareRootLowPrimeProcessedSeatCarrier R K j U := by
  intro hchild
  have hchildAtom :
      (r * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hchild
  have hrcSigned :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hchildAtom).1
  have hrcRange := (Finset.mem_filter.mp hrcSigned).1
  have hrcUpper := (Finset.mem_Icc.mp hrcRange).2
  omega

/-- If the first-owner cutoff `L` is already at most `K`, its split has an empty
prefix because every scheduled coordinate lies in `(K,U]`. -/
theorem squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff
    {K U L p : ℕ} (hLK : L ≤ K)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L = some p) :
    ∃ post,
      squareRootLowPrimeFreshPrimeList K U = p :: post := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, hpre, _hLp⟩
  have hpreNil : pre = [] := by
    cases pre with
    | nil => rfl
    | cons q qs =>
        have hqPre : q ∈ q :: qs := by simp
        have hqLeL := hpre q hqPre
        have hqList : q ∈ squareRootLowPrimeFreshPrimeList K U := by
          rw [hsplit]
          simp
        have hqSet : q ∈ squareRootLowPrimeFreshPrimeSet K U := by
          simpa [squareRootLowPrimeFreshPrimeList] using hqList
        have hKq := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hqSet).1).1
        omega
  subst pre
  refine ⟨post, ?_⟩
  simpa using hsplit

/-- Therefore first owners above any two cutoffs already below `K` coincide.
This is the precise single-fresh-owner statement used for the wall population. -/
theorem squareRootLowPrimeFirstOwnerAbove_unique_below_shallowCutoff
    {K U L₁ L₂ p q : ℕ}
    (hL₁K : L₁ ≤ K) (hL₂K : L₂ ≤ K)
    (hp : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L₁ = some p)
    (hq : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L₂ = some q) :
    p = q := by
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff hL₁K hp with
    ⟨ps, hps⟩
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff hL₂K hq with
    ⟨qs, hqs⟩
  have hhead : p :: ps = q :: qs := hps.symm.trans hqs
  exact List.cons.inj hhead |>.1

/-- A later fresh coordinate sees a first-owner wall state as intrinsic fallout
again.  The current row may have shrunk, but it remains a subset of the original
carrier, and the later child is beyond the same square wall. -/
theorem squareRootLowPrimeFirstOwnerWall_mem_laterFalloff
    {R K j U p r c s : ℕ}
    {S : Finset SquareRootLowPrimeProcessedState}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hlow : canonicalLargestPrimeFactor c ≤ K)
    (hwall : squareRootEndpoint R < p * c)
    (hrList : r ∈ squareRootLowPrimeFreshPrimeList K U)
    (hS : S ⊆ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hxS : some (c, s) ∈ S)
    (hcPos : 0 < c) :
    some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S r := by
  have hrSet : r ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hrList
  have hrData := Finset.mem_filter.mp hrSet
  have hrPrime : r.Prime := hrData.2
  have hKr : K < r := (Finset.mem_Ioc.mp hrData.1).1
  have hrough : canonicalLargestPrimeFactor c < r := hlow.trans_lt hKr
  have hpr : p ≤ r :=
    squareRootLowPrimeFirstOwnerAbove_le_of_mem hfirst hrList hrough
  have hrFresh : ¬ r ∣ c :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hcPos hrPrime hrough
  have hchildMissing :
      squareRootLowPrimeProcessedSeatExtend r (some (c, s)) ∉ S := by
    intro hchildS
    have hchildCarrier := hS hchildS
    have hwallR : squareRootEndpoint R < r * c :=
      squareRootLowPrimeWall_mono hpr hwall
    apply squareRootLowPrimeWall_child_not_mem_processedCarrier hwallR
    simpa [squareRootLowPrimeProcessedSeatExtend] using hchildCarrier
  exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
    ⟨hxS, by simp,
      by simpa [squareRootLowPrimeProcessedStateCofactor] using hrFresh,
      hchildMissing,
      by simpa [squareRootLowPrimeProcessedStateCofactor] using hrough⟩

/-- Once the first wall owner has been processed, the wall state survives every
remaining canonical Euler coordinate. -/
theorem squareRootLowPrimeFirstOwnerWall_survives_tail
    {R K j U p c s : ℕ}
    (post : List ℕ)
    (hpost : ∀ r ∈ post, r ∈ squareRootLowPrimeFreshPrimeList K U)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hlow : canonicalLargestPrimeFactor c ≤ K)
    (hwall : squareRootEndpoint R < p * c)
    (hcPos : 0 < c)
    (S : Finset SquareRootLowPrimeProcessedState)
    (hS : S ⊆ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hxS : some (c, s) ∈ S) :
    some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier post S := by
  induction post generalizing S with
  | nil =>
      simpa [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier] using hxS
  | cons r rs ih =>
      have hrList : r ∈ squareRootLowPrimeFreshPrimeList K U :=
        hpost r (by simp)
      have hfallR := squareRootLowPrimeFirstOwnerWall_mem_laterFalloff
        hfirst hlow hwall hrList hS hxS hcPos
      have hxStep :=
        squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_mem_frontierStep
          hfallR
      have hstepSubset :
          squareRootLowPrimeProcessedSeatCanonicalFrontierStep S r ⊆
            squareRootLowPrimeProcessedSeatCarrier R K j U :=
        (squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset S r).trans hS
      have hrest :
          ∀ q ∈ rs, q ∈ squareRootLowPrimeFreshPrimeList K U := by
        intro q hq
        exact hpost q (by simp [hq])
      exact ih hrest
        (S := squareRootLowPrimeProcessedSeatCanonicalFrontierStep S r)
        hstepSubset hxStep

/-- **First-owner square-wall fallout is already terminal.**

This removes the last subset loss on the wall component: a state assigned to
its first intrinsic owner and lost because `p*c` crosses the square endpoint
survives the complete canonical Euler schedule. -/
theorem squareRootLowPrimeFirstOwnerWall_mem_canonicalTerminal
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hwall : squareRootEndpoint R < p * c) :
    some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U := by
  have hlow := squareRootLowPrimeFirstOwnerFalloff_productWall_forces_lowOwner
    (R := R) (K := K) (j := j) (U := U) (p := p) (c := c) (s := s)
    (by omega) hUR hfirst hfall hwall
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff hlow hfirst with
    ⟨post, hsplit⟩
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hxCarrier, hxHead, _hpFresh, _hchildMissing, _hrough⟩
  have hxAtom :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hxCarrier
  have hcSigned := (mem_squareRootLowPrimeProcessedSeatAtoms.mp hxAtom).1
  have hcRange := (Finset.mem_filter.mp hcSigned).1
  have hcOne := (Finset.mem_Icc.mp hcRange).1
  have hcPos : 0 < c := by omega
  have hxStep :=
    squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_mem_frontierStep hfall
  have hstepSubset :
      squareRootLowPrimeProcessedSeatCanonicalFrontierStep
          (squareRootLowPrimeProcessedSeatCarrier R K j U) p ⊆
        squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset _ p
  have hpost :
      ∀ r ∈ post, r ∈ squareRootLowPrimeFreshPrimeList K U := by
    intro r hr
    rw [hsplit]
    simp [hr]
  have htail := squareRootLowPrimeFirstOwnerWall_survives_tail
    (R := R) (K := K) (j := j) (U := U) (p := p) (c := c) (s := s)
    post hpost hfirst hlow hwall hcPos
    (squareRootLowPrimeProcessedSeatCanonicalFrontierStep
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    hstepSubset hxStep
  unfold squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
  rw [hsplit]
  simpa [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier] using htail

/-- A first-owner wall state is not one of the explicit terminal heads. -/
theorem squareRootLowPrimeFirstOwnerWall_mem_assignedTerminal
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hwall : squareRootEndpoint R < p * c) :
    some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U := by
  have hterminal := squareRootLowPrimeFirstOwnerWall_mem_canonicalTerminal
    hR hUR hfirst hfall hwall
  unfold squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal
  apply Finset.mem_sdiff.mpr
  refine ⟨hterminal, ?_⟩
  intro hhead
  have hheadData := Finset.mem_filter.mp hhead
  rcases hheadData.2 with hnone | hnoOwner
  · simp at hnone
  · simp [squareRootLowPrimeProcessedStateCofactor, hfirst] at hnoOwner

/-- **Wall first-owner state lies in the actual terminal first-owner fibre.** -/
theorem squareRootLowPrimeFirstOwnerWall_mem_intrinsicFirstOwnerSlice
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hwall : squareRootEndpoint R < p * c) :
    some (c, s) ∈
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) p := by
  have hlow := squareRootLowPrimeFirstOwnerFalloff_productWall_forces_lowOwner
    (R := R) (K := K) (j := j) (U := U) (p := p) (c := c) (s := s)
    (by omega) hUR hfirst hfall hwall
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff hlow hfirst with
    ⟨post, hsplit⟩
  have hassigned := squareRootLowPrimeFirstOwnerWall_mem_assignedTerminal
    hR hUR hfirst hfall hwall
  apply mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mpr
  refine ⟨hassigned, ?_⟩
  rw [hsplit]
  simp only [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner]
  simp [hfall]

/-! ## Frozen old-prime cofactor windows -/

open RHLean.Arithmetic

/-- Boolean faces in one open/closed prime-product window. -/
def frozenPrimeUniverseWindowFaces
    (S : Finset ℕ) (A B : ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter fun t =>
    A < primeFaceProduct t ∧ primeFaceProduct t ≤ B

@[simp] theorem mem_frozenPrimeUniverseWindowFaces
    {S : Finset ℕ} {A B : ℕ} {t : Finset ℕ} :
    t ∈ frozenPrimeUniverseWindowFaces S A B ↔
      t ∈ S.powerset ∧ A < primeFaceProduct t ∧ primeFaceProduct t ≤ B := by
  simp [frozenPrimeUniverseWindowFaces]

/-- Signed alternating mass of one frozen product window. -/
def frozenPrimeUniverseWindowMass
    (S : Finset ℕ) (A B : ℕ) : ℤ :=
  ∑ t ∈ frozenPrimeUniverseWindowFaces S A B, booleanCubeSign t

/-- **Frozen mass difference = exact open/closed face window.** -/
theorem frozenPrimeUniverseWindowMass_eq_sub
    {S : Finset ℕ} {A B : ℕ} (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass S A B =
      frozenPrimeUniverseMass S B - frozenPrimeUniverseMass S A := by
  unfold frozenPrimeUniverseWindowMass frozenPrimeUniverseWindowFaces
  rw [Finset.sum_filter,
    frozenPrimeUniverseMass_eq_cutoffSum,
    frozenPrimeUniverseMass_eq_cutoffSum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hA : primeFaceProduct t ≤ A
  · have hB : primeFaceProduct t ≤ B := hA.trans hAB
    have hnot : ¬ A < primeFaceProduct t := Nat.not_lt.mpr hA
    simp [hA, hB, hnot]
  · have hAt : A < primeFaceProduct t := Nat.lt_of_not_ge hA
    by_cases hB : primeFaceProduct t ≤ B
    · simp [hA, hAt, hB]
    · simp [hA, hAt, hB]

/-- Square-root wall faces at old partner `q` and fresh wall owner `p`. -/
def squareRootLowPrimeOldPrimeWallWindowFaces
    (R p q : ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces
    (primesUpTo (q - 1))
    (squareRootEndpoint R / p)
    (squareRootEndpoint R / q)

/-- Signed mass of the old-prime wall window. -/
def squareRootLowPrimeOldPrimeWallWindowMass
    (R p q : ℕ) : ℤ :=
  frozenPrimeUniverseWindowMass
    (primesUpTo (q - 1))
    (squareRootEndpoint R / p)
    (squareRootEndpoint R / q)

/-- **The wall cofactor window is an exact frozen `F_{q^-}` difference.** -/
theorem squareRootLowPrimeOldPrimeWallWindowMass_eq_frozenDifference
    {R p q : ℕ} (hq : q.Prime) (hqp : q ≤ p) :
    squareRootLowPrimeOldPrimeWallWindowMass R p q =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / p) := by
  unfold squareRootLowPrimeOldPrimeWallWindowMass
  apply frozenPrimeUniverseWindowMass_eq_sub
  exact Nat.div_le_div_left hqp hq.pos

/-- Squarefree cofactors represented by the frozen wall window. -/
def squareRootLowPrimeOldPrimeWallWindowCofactors
    (R p q : ℕ) : Finset ℕ :=
  (squareRootLowPrimeOldPrimeWallWindowFaces R p q).image primeFaceProduct

/-- Prime-face products are injective on one frozen wall window. -/
theorem squareRootLowPrimeOldPrimeWallWindow_primeFaceProduct_injOn
    (R p q : ℕ) :
    Set.InjOn primeFaceProduct
      (↑(squareRootLowPrimeOldPrimeWallWindowFaces R p q)) := by
  intro t ht u hu hprod
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp ht).1
  have huPow := (mem_frozenPrimeUniverseWindowFaces.mp hu).1
  have htSub := Finset.mem_powerset.mp htPow
  have huSub := Finset.mem_powerset.mp huPow
  exact (primeFaceProduct_eq_iff
    (fun r hr => prime_of_mem_primesUpTo (htSub hr))
    (fun r hr => prime_of_mem_primesUpTo (huSub hr))).mp hprod

/-- Möbius on a represented rough cofactor is its Boolean face sign. -/
theorem squareRootLowPrimeOldPrimeWallWindow_moebius_eq_sign
    {R p q : ℕ} {t : Finset ℕ}
    (ht : t ∈ squareRootLowPrimeOldPrimeWallWindowFaces R p q) :
    μ (primeFaceProduct t) = booleanCubeSign t := by
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp ht).1
  have htSub := Finset.mem_powerset.mp htPow
  exact moebius_primeFaceProduct_eq_booleanCubeSign t
    (fun r hr => prime_of_mem_primesUpTo (htSub hr))

/-- The ordinary Möbius sum of the represented cofactors is the face mass. -/
theorem squareRootLowPrimeOldPrimeWallWindowCofactors_moebiusSum
    (R p q : ℕ) :
    (∑ c ∈ squareRootLowPrimeOldPrimeWallWindowCofactors R p q, μ c) =
      squareRootLowPrimeOldPrimeWallWindowMass R p q := by
  unfold squareRootLowPrimeOldPrimeWallWindowCofactors
    squareRootLowPrimeOldPrimeWallWindowMass
    frozenPrimeUniverseWindowMass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    exact squareRootLowPrimeOldPrimeWallWindow_moebius_eq_sign ht
  · intro a ha b hb hab
    exact squareRootLowPrimeOldPrimeWallWindow_primeFaceProduct_injOn
      R p q ha hb hab

/-- **Integer rough-cofactor form of the horizontal recurrence window.** -/
theorem squareRootLowPrimeOldPrimeWallWindowCofactors_moebiusSum_eq_frozenDifference
    {R p q : ℕ} (hq : q.Prime) (hqp : q ≤ p) :
    (∑ c ∈ squareRootLowPrimeOldPrimeWallWindowCofactors R p q, μ c) =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / p) := by
  rw [squareRootLowPrimeOldPrimeWallWindowCofactors_moebiusSum,
    squareRootLowPrimeOldPrimeWallWindowMass_eq_frozenDifference hq hqp]

/-! ## One literal wall-pair carrier with two readings -/

/-- The old-prime coordinates available below the shallow cutoff. -/
def squareRootLowPrimeWallOldPrimeSet (K : ℕ) : Finset ℕ :=
  (Finset.Icc 2 K).filter Nat.Prime

@[simp] theorem mem_squareRootLowPrimeWallOldPrimeSet
    {K q : ℕ} :
    q ∈ squareRootLowPrimeWallOldPrimeSet K ↔ q.Prime ∧ q ≤ K := by
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqPrime⟩
    exact ⟨hqPrime, (Finset.mem_Icc.mp hqIcc).2⟩
  · rintro ⟨hqPrime, hqK⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqK⟩, hqPrime⟩

/-- The old-prime set is exactly the ordinary prime prefix through `K`. -/
theorem squareRootLowPrimeWallOldPrimeSet_eq_primesUpTo (K : ℕ) :
    squareRootLowPrimeWallOldPrimeSet K = primesUpTo K := by
  ext q
  rw [mem_squareRootLowPrimeWallOldPrimeSet, mem_primesUpTo]

/-- Integer characterization of the face-defined cofactor window.  This is the
surjectivity step which prevents the old-prime reading from being only an
auxiliary Boolean-face carrier. -/
theorem mem_squareRootLowPrimeOldPrimeWallWindowCofactors_iff
    {R p q c : ℕ} (hq : q.Prime) :
    c ∈ squareRootLowPrimeOldPrimeWallWindowCofactors R p q ↔
      Squarefree c ∧
        canonicalLargestPrimeFactor c < q ∧
        squareRootEndpoint R / p < c ∧
        c ≤ squareRootEndpoint R / q := by
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨t, ht, rfl⟩
    have htData := mem_frozenPrimeUniverseWindowFaces.mp ht
    have hmuNe : μ (primeFaceProduct t) ≠ 0 := by
      rw [squareRootLowPrimeOldPrimeWallWindow_moebius_eq_sign ht]
      simp [booleanCubeSign]
    have hsq : Squarefree (primeFaceProduct t) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    have hlpf :=
      canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hq htData.1
    exact ⟨hsq, hlpf, htData.2.1, htData.2.2⟩
  · rintro ⟨hsq, hlpf, hlow, hupp⟩
    let t := squarefreePrimeFace c
    have hprod : primeFaceProduct t = c := by
      simpa [t] using primeFaceProduct_squarefreePrimeFace hsq
    have htSub : t ⊆ primesUpTo (q - 1) := by
      intro r hr
      have hrData := Nat.mem_primeFactors.mp (by simpa [t, squarefreePrimeFace] using hr)
      have hrPrime : r.Prime := hrData.1
      have hrDvd : r ∣ c := hrData.2.1
      have hcPos : 0 < c := Nat.pos_of_ne_zero hsq.ne_zero
      have hrLeC : r ≤ c := Nat.le_of_dvd hcPos hrDvd
      have hcGt : 1 < c := by
        have hrTwo := hrPrime.two_le
        omega
      have hrLeLpf : r ≤ canonicalLargestPrimeFactor c := by
        unfold canonicalLargestPrimeFactor
        rw [dif_pos hcGt]
        exact Finset.le_max' c.primeFactors r (by simpa [t, squarefreePrimeFace] using hr)
      exact mem_primesUpTo.mpr ⟨hrPrime, by omega⟩
    have htWin : t ∈ squareRootLowPrimeOldPrimeWallWindowFaces R p q := by
      apply mem_frozenPrimeUniverseWindowFaces.mpr
      refine ⟨Finset.mem_powerset.mpr htSub, ?_, ?_⟩
      · simpa [hprod] using hlow
      · simpa [hprod] using hupp
    exact Finset.mem_image.mpr ⟨t, htWin, hprod⟩

/-- Cofactors whose first-fresh-owner child crosses the square wall. -/
def squareRootLowPrimeWallCofactors
    (R K p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeProcessedSignedCofactors R K).filter fun c =>
    squareRootEndpoint R < p * c

/-- Cofactor-first reading: one pair `(c,q)` for every old born partner of a
wall cofactor. -/
def squareRootLowPrimeWallPairCarrierCofactorFirst
    (R K p : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeWallCofactors R K p).biUnion fun c =>
    ((squareRootBornPartnerSet R c).filter fun q => q ≤ K).image
      fun q => (c, q)

/-- Old-prime-first reading: one pair `(c,q)` for every cofactor in the frozen
`q^-` wall window. -/
def squareRootLowPrimeWallPairCarrierOldPrimeFirst
    (R K p : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeWallOldPrimeSet K).biUnion fun q =>
    (squareRootLowPrimeOldPrimeWallWindowCofactors R p q).image
      fun c => (c, q)

/-- A wall crossing at an owner below the root forces the parent cofactor to
have reached the root.  This is the owner-only form of the earlier first-owner
lemma and is what makes the born condition `q <= c` automatic in the window
reading. -/
theorem squareRootLowPrimeWall_forces_root_le_cofactor_of_owner_lt_root
    {R p c : ℕ} (hR : 2 ≤ R) (hpR : p < R)
    (hwall : squareRootEndpoint R < p * c) :
    R ≤ c := by
  by_contra hnot
  have hcR : c < R := Nat.lt_of_not_ge hnot
  have hcPos : 0 < c := by
    by_contra hc0
    have hcZero : c = 0 := Nat.eq_zero_of_not_pos hc0
    rw [hcZero, Nat.mul_zero] at hwall
    omega
  have hprod : p * c < R * R := by
    calc
      p * c < R * c := Nat.mul_lt_mul_of_pos_right hpR hcPos
      _ < R * R := Nat.mul_lt_mul_of_pos_left hcR (by omega)
  have hprod' : p * c < R ^ 2 := by
    simpa [pow_two] using hprod
  unfold squareRootEndpoint at hwall
  omega

/-- **Literal partition bridge.**  The cofactor-first born-partner enumeration
and the old-prime-first frozen-window enumeration are the same finite subset of
arithmetic pairs.  In particular there is no hidden obstruction family between
the two readings. -/
theorem squareRootLowPrimeWallPairCarrierCofactorFirst_eq_oldPrimeFirst
    {R K p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hKp : K < p) (hpR : p < R) :
    squareRootLowPrimeWallPairCarrierCofactorFirst R K p =
      squareRootLowPrimeWallPairCarrierOldPrimeFirst R K p := by
  ext z
  rcases z with ⟨c, q⟩
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨d, hd, hzPair⟩
    rcases Finset.mem_image.mp hzPair with ⟨r, hr, hpair⟩
    have hdc : d = c := congrArg Prod.fst hpair
    have hrq : r = q := congrArg Prod.snd hpair
    subst d
    subst r
    have hcWall := Finset.mem_filter.mp hd
    have hcSigned := hcWall.1
    have hwall := hcWall.2
    have hqFiltered := Finset.mem_filter.mp hr
    have hqBorn := hqFiltered.1
    have hqK := hqFiltered.2
    rcases Finset.mem_filter.mp hqBorn with
      ⟨hqRange, hqPrime, hrough, _hqc, hproduct⟩
    have hqTwo := (Finset.mem_Icc.mp hqRange).1
    have hcData := Finset.mem_filter.mp hcSigned
    have hsq : Squarefree c :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hcData.2.2
    have hlow : squareRootEndpoint R / p < c := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      simpa [Nat.mul_comm] using hwall
    have hupp : c ≤ squareRootEndpoint R / q := by
      exact (Nat.le_div_iff_mul_le hqPrime.pos).2 hproduct
    apply Finset.mem_biUnion.mpr
    refine ⟨q, mem_squareRootLowPrimeWallOldPrimeSet.mpr ⟨hqPrime, hqK⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨c, ?_, rfl⟩
    exact (mem_squareRootLowPrimeOldPrimeWallWindowCofactors_iff hqPrime).2
      ⟨hsq, hrough, hlow, hupp⟩
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨r, hr, hzPair⟩
    rcases Finset.mem_image.mp hzPair with ⟨d, hd, hpair⟩
    have hdc : d = c := congrArg Prod.fst hpair
    have hrq : r = q := congrArg Prod.snd hpair
    subst d
    subst r
    have hqData := mem_squareRootLowPrimeWallOldPrimeSet.mp hr
    have hqPrime := hqData.1
    have hqK := hqData.2
    rcases (mem_squareRootLowPrimeOldPrimeWallWindowCofactors_iff hqPrime).1 hd with
      ⟨hsq, hrough, hlow, hupp⟩
    have hwall' := (Nat.div_lt_iff_lt_mul hp.pos).1 hlow
    have hwall : squareRootEndpoint R < p * c := by
      simpa [Nat.mul_comm] using hwall'
    have hcR := squareRootLowPrimeWall_forces_root_le_cofactor_of_owner_lt_root
      hR hpR hwall
    have hcPos : 0 < c := by omega
    have hmu : μ c ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
    have hcLeX : c ≤ squareRootEndpoint R :=
      hupp.trans (Nat.div_le_self _ q)
    have hcSigned : c ∈ squareRootLowPrimeProcessedSignedCofactors R K := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, hcLeX⟩, ?_, hmu⟩
      omega
    have hqLeC : q ≤ c := by omega
    have hcq : c * q ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hqPrime.pos).1 hupp
    have hqBorn : q ∈ squareRootBornPartnerSet R c := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, ?_⟩,
        hqPrime, hrough, hqLeC, hcq⟩
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨hcSigned, hwall⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ⟨hqBorn, hqK⟩, rfl⟩

/-- Every arithmetic wall pair is a genuinely fresh old-prime extension on its
cofactor coordinate. -/
theorem squareRootLowPrimeWallPairCarrier_fresh
    {R K p c q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p) :
    ¬ q ∣ c := by
  rcases Finset.mem_biUnion.mp hz with ⟨d, hd, hzPair⟩
  rcases Finset.mem_image.mp hzPair with ⟨r, hr, hpair⟩
  have hdc : d = c := congrArg Prod.fst hpair
  have hrq : r = q := congrArg Prod.snd hpair
  subst d
  subst r
  have hqBorn := (Finset.mem_filter.mp hr).1
  rcases Finset.mem_filter.mp hqBorn with
    ⟨_hqRange, hqPrime, hrough, hqc, _hproduct⟩
  have hcPos : 0 < c := lt_of_lt_of_le hqPrime.pos hqc
  exact squareRootLowPrimePrime_fresh_of_lpf_lt hcPos hqPrime hrough

/-- The old-prime fibres in the second reading are pairwise disjoint because
the second coordinate remembers the owner `q`. -/
theorem squareRootLowPrimeOldPrimeWallPairFibers_pairwiseDisjoint
    (R K p : ℕ) :
    Set.PairwiseDisjoint (↑(squareRootLowPrimeWallOldPrimeSet K))
      (fun q =>
        (squareRootLowPrimeOldPrimeWallWindowCofactors R p q).image
          fun c => (c, q)) := by
  intro q _hq r _hr hqr
  change Disjoint
    ((squareRootLowPrimeOldPrimeWallWindowCofactors R p q).image
      fun c => (c, q))
    ((squareRootLowPrimeOldPrimeWallWindowCofactors R p r).image
      fun c => (c, r))
  rw [Finset.disjoint_left]
  intro z hzq hzr
  rcases Finset.mem_image.mp hzq with ⟨c, _hc, hcz⟩
  rcases Finset.mem_image.mp hzr with ⟨d, _hd, hdz⟩
  have hsnd : q = r := by
    have h := congrArg Prod.snd (hcz.trans hdz.symm)
    simpa using h
  exact hqr hsnd

/-- The signed mass of the literal pair carrier is exactly the sum of its
old-prime frozen windows. -/
theorem squareRootLowPrimeWallPairCarrierOldPrimeFirst_moebiusSum
    (R K p : ℕ) :
    (∑ z ∈ squareRootLowPrimeWallPairCarrierOldPrimeFirst R K p, μ z.1) =
      ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
        squareRootLowPrimeOldPrimeWallWindowMass R p q := by
  unfold squareRootLowPrimeWallPairCarrierOldPrimeFirst
  rw [Finset.sum_biUnion
    (squareRootLowPrimeOldPrimeWallPairFibers_pairwiseDisjoint R K p)]
  apply Finset.sum_congr rfl
  intro q _hq
  calc
    (∑ z ∈ (squareRootLowPrimeOldPrimeWallWindowCofactors R p q).image
        (fun c => (c, q)), μ z.1) =
      ∑ c ∈ squareRootLowPrimeOldPrimeWallWindowCofactors R p q, μ c := by
        rw [Finset.sum_image]
        intro a _ha b _hb hab
        exact congrArg Prod.fst hab
    _ = squareRootLowPrimeOldPrimeWallWindowMass R p q :=
      squareRootLowPrimeOldPrimeWallWindowCofactors_moebiusSum R p q

/-! ## Contract the wall sum to one fixed-cutoff column -/

/-- Composite successor cutoffs do not change the frozen prime universe. -/
theorem primesUpTo_succ_eq_of_not_prime_public
    (n : ℕ) (hnot : ¬ (n + 1).Prime) :
    primesUpTo (n + 1) = primesUpTo n := by
  ext q
  simp only [mem_primesUpTo]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    refine ⟨hqPrime, ?_⟩
    have hqne : q ≠ n + 1 := by
      intro hEq
      subst q
      exact hnot hqPrime
    omega
  · rintro ⟨hqPrime, hqle⟩
    exact ⟨hqPrime, by omega⟩

/-- **Upper-column telescope.**  At a fixed endpoint `X`, each prime `q`
contributes exactly the decrement from the predecessor frozen universe to the
universe after adjoining `q`.  Summing all old primes therefore removes the
entire moving `X/q` column. -/
theorem frozenPrimeUniverse_upperColumn_telescope
    (X K : ℕ) (hX : 1 ≤ X) :
    (∑ q ∈ primesUpTo K,
      frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / q)) =
      1 - frozenPrimeUniverseMass (primesUpTo K) X := by
  induction K with
  | zero =>
      have hzero : primesUpTo 0 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        have hdata := mem_primesUpTo.mp hq
        have htwo := hdata.1.two_le
        omega
      rw [hzero]
      simp [frozenPrimeUniverseMass_eq_cutoffSum,
        primeFaceProduct, booleanCubeSign, hX]
  | succ K ih =>
      by_cases hq : (K + 1).Prime
      · have hnotMem : K + 1 ∉ primesUpTo K := by
          simp
        have hpred : K + 1 - 1 = K := by omega
        have hset : primesUpTo (K + 1) = insert (K + 1) (primesUpTo K) := by
          simpa [hpred] using primesUpTo_eq_insert_pred_of_prime hq
        calc
          (∑ q ∈ primesUpTo (K + 1),
              frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / q)) =
            frozenPrimeUniverseMass (primesUpTo K) (X / (K + 1)) +
              ∑ q ∈ primesUpTo K,
                frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / q) := by
                  rw [hset, Finset.sum_insert hnotMem, hpred]
          _ = frozenPrimeUniverseMass (primesUpTo K) (X / (K + 1)) +
              (1 - frozenPrimeUniverseMass (primesUpTo K) X) := by rw [ih]
          _ = 1 - frozenPrimeUniverseMass (primesUpTo (K + 1)) X := by
              rw [hset,
                frozenPrimeUniverseMass_insert hnotMem hq]
              ring
      · have hset := primesUpTo_succ_eq_of_not_prime_public K hq
        rw [hset, ih]

/-- Square-root specialization of the exact upper-column telescope. -/
theorem squareRootLowPrimeWallUpperColumn_telescope
    {R K : ℕ} (hR : 2 ≤ R) :
    (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
      frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / q)) =
      1 - frozenPrimeUniverseMass (primesUpTo K) (squareRootEndpoint R) := by
  rw [squareRootLowPrimeWallOldPrimeSet_eq_primesUpTo]
  apply frozenPrimeUniverse_upperColumn_telescope
  unfold squareRootEndpoint
  have hsq : 2 ≤ R ^ 2 := by nlinarith
  omega

/-- Old-prime window mass after the moving upper column has telescoped.  Only
one common lower-cutoff column remains. -/
theorem squareRootLowPrimeOldPrimeWallWindowMassSum_eq_fixedColumn
    {R K p : ℕ} (hR : 2 ≤ R) (hKp : K < p) :
    (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
      squareRootLowPrimeOldPrimeWallWindowMass R p q) =
      (1 - frozenPrimeUniverseMass (primesUpTo K) (squareRootEndpoint R)) -
        ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / p) := by
  calc
    (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
        squareRootLowPrimeOldPrimeWallWindowMass R p q) =
      ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
        (frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q) -
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / p)) := by
              apply Finset.sum_congr rfl
              intro q hq
              have hqData := mem_squareRootLowPrimeWallOldPrimeSet.mp hq
              exact squareRootLowPrimeOldPrimeWallWindowMass_eq_frozenDifference
                hqData.1 (by omega)
    _ = (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q)) -
        ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / p) := by
              rw [Finset.sum_sub_distrib]
    _ = (1 - frozenPrimeUniverseMass (primesUpTo K) (squareRootEndpoint R)) -
        ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / p) := by
              rw [squareRootLowPrimeWallUpperColumn_telescope hR]

/-- Old-prime coordinates whose whole predecessor Boolean cube already fits
under the common wall cutoff.  Nonemptiness is explicit because the empty cube
has mass `1`, not `0`. -/
def squareRootLowPrimeCompletedWallOldPrimeSet
    (R K p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeWallOldPrimeSet K).filter fun q =>
    (primesUpTo (q - 1)).Nonempty ∧
      primeFaceProduct (primesUpTo (q - 1)) ≤ squareRootEndpoint R / p

/-- Complementary old-prime coordinates: these are exactly the unfinished
predecessor cubes at the common cutoff. -/
def squareRootLowPrimeUnfinishedWallOldPrimeSet
    (R K p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeWallOldPrimeSet K).filter fun q =>
    ¬ ((primesUpTo (q - 1)).Nonempty ∧
      primeFaceProduct (primesUpTo (q - 1)) ≤ squareRootEndpoint R / p)

/-- A completed predecessor cube contributes exactly zero to the common column. -/
theorem squareRootLowPrimeCompletedWallOldPrime_mass_eq_zero
    {R K p q : ℕ}
    (hq : q ∈ squareRootLowPrimeCompletedWallOldPrimeSet R K p) :
    frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / p) = 0 := by
  have hqData := Finset.mem_filter.mp hq
  exact frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
    hqData.2.1
    (fun r hr => prime_of_mem_primesUpTo hr)
    hqData.2.2

/-- Exact deletion of every genuinely completed small-owner layer. -/
theorem squareRootLowPrimeWallFixedColumn_eq_unfinished
    (R K p : ℕ) :
    (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
      frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / p)) =
      ∑ q ∈ squareRootLowPrimeUnfinishedWallOldPrimeSet R K p,
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / p) := by
  unfold squareRootLowPrimeUnfinishedWallOldPrimeSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hdone :
      (primesUpTo (q - 1)).Nonempty ∧
        primeFaceProduct (primesUpTo (q - 1)) ≤ squareRootEndpoint R / p
  · have hzero :
        frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / p) = 0 :=
      frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
        hdone.1 (fun r hr => prime_of_mem_primesUpTo hr) hdone.2
    simp [hdone, hzero]
  · simp [hdone]

/-- **Contracted arithmetic wall sum.**  After literal set identification, the
moving `X_R/q` column telescopes and every fitted predecessor cube vanishes.
The only remaining wall target is one fixed-cutoff sum over unfinished old-prime
cubes.  This is an identity, not an estimate. -/
theorem squareRootLowPrimeWallPairCarrier_moebiusSum_eq_unfinishedFixedColumn
    {R K p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hKp : K < p) (hpR : p < R) :
    (∑ z ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p, μ z.1) =
      (1 - frozenPrimeUniverseMass (primesUpTo K) (squareRootEndpoint R)) -
        ∑ q ∈ squareRootLowPrimeUnfinishedWallOldPrimeSet R K p,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / p) := by
  rw [squareRootLowPrimeWallPairCarrierCofactorFirst_eq_oldPrimeFirst
      hR hp hKp hpR,
    squareRootLowPrimeWallPairCarrierOldPrimeFirst_moebiusSum,
    squareRootLowPrimeOldPrimeWallWindowMassSum_eq_fixedColumn hR hKp,
    squareRootLowPrimeWallFixedColumn_eq_unfinished]

end RHLean.Proof
