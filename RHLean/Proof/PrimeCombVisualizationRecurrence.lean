import Mathlib
import RHLean.Proof.PrimeCombVisualizationDynamics

/-!
# Ordered-prime recurrence for the visualization frames

`PrimeCombVisualizationDynamics` records the literal operational masks used by
the animation: kill, first hit, and later-touch flip.  This file proves that
those operational updates are not a second model.  When `S` consists of primes
strictly smaller than the fresh prime `p`, one animation step is exactly the
closed-form frame obtained by adjoining `p` to the processed prime set.

Thus the visualization really is a prime-by-prime recurrence on the frame
state, while the closed form remains available for global geometric arguments.
No estimate occurs here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Before the fresh prime `p`, ordinary selected-divisor touch and proper-
multiple touch coincide on every site strictly beyond `p`. -/
theorem primeCombFrameProperTouched_iff_touched_of_beforePrime
    (S : Finset ℕ) {p n : ℕ}
    (hSlt : ∀ q ∈ S, q < p) (hpn : p < n) :
    PrimeCombFrameProperTouched S n ↔ PrimeCombFrameTouched S n := by
  constructor
  · rintro ⟨q, hqS, _hqn, hqdiv⟩
    unfold PrimeCombFrameTouched primeCombFrameDivisors
    exact ⟨q, Finset.mem_filter.mpr ⟨hqS, hqdiv⟩⟩
  · rintro ⟨q, hq⟩
    have hqData := Finset.mem_filter.mp hq
    exact ⟨q, hqData.1, (hSlt q hqData.1).trans hpn, hqData.2⟩

private theorem primeCombFrameAlive_of_no_square
    {S : Finset ℕ} {n : ℕ}
    (hn0 : n ≠ 0) (hn1 : n ≠ 1)
    (hnoSquare : ¬ PrimeCombFrameSquareHit S n) :
    PrimeCombFrameAlive S n := by
  unfold PrimeCombFrameAlive primeCombFrameSite
  rw [if_neg hn0, if_neg hn1, if_neg hnoSquare]
  dsimp
  by_cases hdiv : primeCombFrameDivisors S n = ∅
  · rw [if_pos (Finset.card_eq_zero.mpr hdiv)]
    norm_num
  · have hcard : (primeCombFrameDivisors S n).card ≠ 0 :=
      Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hdiv)
    rw [if_neg hcard]
    exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)

private theorem primeCombFrameDivisors_prime_eq_empty
    (S : Finset ℕ) {p : ℕ}
    (hpPrime : p.Prime)
    (hSPrime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    primeCombFrameDivisors S p = ∅ := by
  classical
  ext q
  simp only [primeCombFrameDivisors, Finset.mem_filter, Finset.notMem_empty,
    iff_false]
  intro h
  rcases h with ⟨hqS, hqdiv⟩
  have hqPrime := hSPrime q hqS
  rcases (Nat.dvd_prime hpPrime).mp hqdiv with hq1 | hqp
  · exact hqPrime.ne_one hq1
  · subst q
    exact (Nat.lt_irrefl p) (hSlt p hqS)

/-- **Operational recurrence equals the closed frame.**  If `S` contains only
primes smaller than the fresh prime `p`, the literal kill/first-hit/flip step
is exactly the frame obtained from the processed coordinate set `insert p S`.
This is the frame-by-frame correctness theorem for the animation. -/
theorem primeCombAnimationStepSite_eq_insert
    (S : Finset ℕ) (p n : ℕ)
    (hpPrime : p.Prime)
    (hSPrime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    primeCombAnimationStepSite S p n =
      primeCombFrameSite (insert p S) n := by
  classical
  have hpS : p ∉ S := by
    intro hpMem
    exact (Nat.lt_irrefl p) (hSlt p hpMem)
  by_cases hn0 : n = 0
  · subst n
    simp [primeCombAnimationStepSite, PrimeCombFrameKilled,
      PrimeCombFrameFlipped, PrimeCombFrameAlive]
  by_cases hn1 : n = 1
  · subst n
    have hNotProper : ¬ PrimeCombFrameProperMultiple p 1 := by
      intro h
      unfold PrimeCombFrameProperMultiple at h
      have hp2 : 2 ≤ p := hpPrime.two_le
      omega
    have hNotKilled : ¬ PrimeCombFrameKilled S p 1 := by
      intro h
      exact hNotProper h.2.1
    have hNotFlipped : ¬ PrimeCombFrameFlipped S p 1 := by
      intro h
      exact hNotProper h.2.1
    simp [primeCombAnimationStepSite, hNotKilled, hNotFlipped]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hOldSquare : PrimeCombFrameSquareHit S n
  · have hOldZero : primeCombFrameSite S n = 0 := by
      simp [primeCombFrameSite, hn0, hn1, hOldSquare]
    have hNotAlive : ¬ PrimeCombFrameAlive S n := by
      simp [PrimeCombFrameAlive, hOldZero]
    have hNotKilled : ¬ PrimeCombFrameKilled S p n := by
      intro h
      exact hNotAlive h.1
    have hNotFlipped : ¬ PrimeCombFrameFlipped S p n := by
      intro h
      exact hNotAlive h.1
    have hNewSquare : PrimeCombFrameSquareHit (insert p S) n :=
      (primeCombFrameSquareHit_insert S p n).2 (Or.inr hOldSquare)
    rw [show primeCombAnimationStepSite S p n = 0 by
      simp [primeCombAnimationStepSite, hNotKilled, hNotFlipped, hOldZero]]
    simp [primeCombFrameSite, hn0, hn1, hNewSquare]
  have hAlive : PrimeCombFrameAlive S n :=
    primeCombFrameAlive_of_no_square hn0 hn1 hOldSquare
  by_cases hPSquare : p ^ 2 ∣ n
  · have hpdiv : p ∣ n := by
      rcases hPSquare with ⟨k, hk⟩
      refine ⟨p * k, ?_⟩
      simpa [pow_two, Nat.mul_assoc] using hk
    have hp2le : p ^ 2 ≤ n := Nat.le_of_dvd hnpos hPSquare
    have hplt : p < n := by
      have hpp : p < p ^ 2 := by
        nlinarith [hpPrime.two_le]
      exact hpp.trans_le hp2le
    have hproper : PrimeCombFrameProperMultiple p n := ⟨hplt, hpdiv⟩
    have hkilled : PrimeCombFrameKilled S p n :=
      ⟨hAlive, hproper, hPSquare⟩
    have hNewSquare : PrimeCombFrameSquareHit (insert p S) n :=
      (primeCombFrameSquareHit_insert S p n).2 (Or.inl hPSquare)
    rw [primeCombAnimationStepSite_eq_zero_of_killed S hkilled]
    simp [primeCombFrameSite, hn0, hn1, hNewSquare]
  have hNewNoSquare : ¬ PrimeCombFrameSquareHit (insert p S) n := by
    rw [primeCombFrameSquareHit_insert]
    simp [hPSquare, hOldSquare]
  by_cases hpdiv : p ∣ n
  · by_cases hplt : p < n
    · have hproper : PrimeCombFrameProperMultiple p n := ⟨hplt, hpdiv⟩
      have hpNotOldDivisor : p ∉ primeCombFrameDivisors S n := by
        simp [primeCombFrameDivisors, hpS]
      by_cases hProperTouched : PrimeCombFrameProperTouched S n
      · have hflipped : PrimeCombFrameFlipped S p n :=
          ⟨hAlive, hproper, hProperTouched, hPSquare⟩
        have hTouched : PrimeCombFrameTouched S n :=
          (primeCombFrameProperTouched_iff_touched_of_beforePrime
            S hSlt hplt).1 hProperTouched
        have hOldCardNe : (primeCombFrameDivisors S n).card ≠ 0 :=
          Finset.card_ne_zero.mpr hTouched
        have hOld :
            primeCombFrameSite S n =
              (-1 : ℤ) ^ (primeCombFrameDivisors S n).card := by
          unfold primeCombFrameSite
          rw [if_neg hn0, if_neg hn1, if_neg hOldSquare]
          dsimp
          rw [if_neg hOldCardNe]
        have hNewCard :
            (primeCombFrameDivisors (insert p S) n).card =
              (primeCombFrameDivisors S n).card + 1 := by
          rw [primeCombFrameDivisors_insert S p n, if_pos hpdiv,
            Finset.card_insert_of_notMem hpNotOldDivisor]
        have hNew :
            primeCombFrameSite (insert p S) n =
              (-1 : ℤ) ^ ((primeCombFrameDivisors S n).card + 1) := by
          unfold primeCombFrameSite
          rw [if_neg hn0, if_neg hn1, if_neg hNewNoSquare]
          dsimp
          rw [hNewCard, if_neg (by omega)]
        rw [primeCombAnimationStepSite_eq_neg_of_flipped S hflipped,
          hOld, hNew, pow_succ]
        ring
      · have hNotTouched : ¬ PrimeCombFrameTouched S n := by
          intro htouched
          exact hProperTouched
            ((primeCombFrameProperTouched_iff_touched_of_beforePrime
              S hSlt hplt).2 htouched)
        have hOldCardZero : (primeCombFrameDivisors S n).card = 0 := by
          by_contra hcard
          exact hNotTouched (Finset.card_ne_zero.mp hcard)
        have hfirst : PrimeCombFrameFirstHit S p n :=
          ⟨hAlive, hproper, hProperTouched, hPSquare⟩
        have hOld : primeCombFrameSite S n = -1 := by
          unfold primeCombFrameSite
          rw [if_neg hn0, if_neg hn1, if_neg hOldSquare]
          dsimp
          rw [if_pos hOldCardZero]
        have hNewCard :
            (primeCombFrameDivisors (insert p S) n).card = 1 := by
          rw [primeCombFrameDivisors_insert S p n, if_pos hpdiv,
            Finset.card_insert_of_notMem hpNotOldDivisor, hOldCardZero]
        have hNew : primeCombFrameSite (insert p S) n = -1 := by
          unfold primeCombFrameSite
          rw [if_neg hn0, if_neg hn1, if_neg hNewNoSquare]
          dsimp
          rw [hNewCard]
          norm_num
        rw [primeCombAnimationStepSite_eq_of_firstHit S hfirst, hOld, hNew]
    · have hpLeN : p ≤ n := Nat.le_of_dvd hnpos hpdiv
      have hnLeP : n ≤ p := Nat.le_of_not_gt hplt
      have hnp : n = p := Nat.le_antisymm hnLeP hpLeN
      subst n
      have hOldDivisors : primeCombFrameDivisors S p = ∅ :=
        primeCombFrameDivisors_prime_eq_empty S hpPrime hSPrime hSlt
      have hNotProper : ¬ PrimeCombFrameProperMultiple p p := by
        intro h
        exact (Nat.lt_irrefl p) h.1
      have hNotKilled : ¬ PrimeCombFrameKilled S p p := by
        intro h
        exact hNotProper h.2.1
      have hNotFlipped : ¬ PrimeCombFrameFlipped S p p := by
        intro h
        exact hNotProper h.2.1
      have hOld : primeCombFrameSite S p = -1 := by
        unfold primeCombFrameSite
        rw [if_neg hpPrime.ne_zero, if_neg hpPrime.ne_one,
          if_neg hOldSquare]
        dsimp
        rw [hOldDivisors]
        norm_num
      have hNewCard :
          (primeCombFrameDivisors (insert p S) p).card = 1 := by
        rw [primeCombFrameDivisors_insert S p p, if_pos (dvd_refl p),
          hOldDivisors]
        simp
      have hNew : primeCombFrameSite (insert p S) p = -1 := by
        unfold primeCombFrameSite
        rw [if_neg hpPrime.ne_zero, if_neg hpPrime.ne_one,
          if_neg hNewNoSquare]
        dsimp
        rw [hNewCard]
        norm_num
      simp [primeCombAnimationStepSite, hNotKilled, hNotFlipped, hOld, hNew]
  · have hNotProper : ¬ PrimeCombFrameProperMultiple p n := by
      intro h
      exact hpdiv h.2
    have hNotKilled : ¬ PrimeCombFrameKilled S p n := by
      intro h
      exact hNotProper h.2.1
    have hNotFlipped : ¬ PrimeCombFrameFlipped S p n := by
      intro h
      exact hNotProper h.2.1
    have hFrameEq :
        primeCombFrameSite (insert p S) n = primeCombFrameSite S n := by
      simp only [primeCombFrameSite, hn0, hn1, if_false,
        hNewNoSquare, hOldSquare, primeCombFrameDivisors_insert,
        hpdiv]
    rw [hFrameEq]
    simp [primeCombAnimationStepSite, hNotKilled, hNotFlipped]

/-! ## Literal ordered-prime corollaries -/

/-- The animation's `hit |= proper_multiple` assignment, as an exact logical
recurrence for the hit mask. -/
theorem primeCombFrameProperTouched_insert_iff
    (S : Finset ℕ) (p n : ℕ) :
    PrimeCombFrameProperTouched (insert p S) n ↔
      PrimeCombFrameProperTouched S n ∨ PrimeCombFrameProperMultiple p n := by
  unfold PrimeCombFrameProperTouched PrimeCombFrameProperMultiple
  constructor
  · rintro ⟨q, hq, hqn, hqdiv⟩
    rcases Finset.mem_insert.mp hq with hqp | hqS
    · subst q
      exact Or.inr ⟨hqn, hqdiv⟩
    · exact Or.inl ⟨q, hqS, hqn, hqdiv⟩
  · rintro (⟨q, hqS, hqn, hqdiv⟩ | ⟨hpn, hpdiv⟩)
    · exact ⟨q, Finset.mem_insert_of_mem hqS, hqn, hqdiv⟩
    · exact ⟨p, Finset.mem_insert_self p S, hpn, hpdiv⟩

/-- **Each successive rake can touch no more multiplier seats.**  Increasing
the prime coordinate shrinks the hyperbolic multiplier bunch. -/
theorem primeCombProperMultiplierSet_antitone
    {W p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    primeCombProperMultiplierSet q W ⊆ primeCombProperMultiplierSet p W := by
  intro k hk
  have hq : 0 < q := hp.trans_le hpq
  have hkData := (mem_primeCombProperMultiplierSet_iff hq).1 hk
  apply (mem_primeCombProperMultiplierSet_iff hp).2
  exact ⟨hkData.1, (Nat.mul_le_mul_left k hpq).trans hkData.2⟩

/-- Cardinal form of the shrinking-rake law. -/
theorem card_primeCombProperMultiplierSet_antitone
    {W p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    (primeCombProperMultiplierSet q W).card ≤
      (primeCombProperMultiplierSet p W).card :=
  Finset.card_le_card (primeCombProperMultiplierSet_antitone hp hpq)

/-- At a prime coordinate, the full ambient prime set is exactly the previous
prime frame plus the fresh coordinate. -/
theorem primesUpTo_eq_insert_pred_of_prime
    {p : ℕ} (hp : p.Prime) :
    primesUpTo p = insert p (primesUpTo (p - 1)) := by
  classical
  ext q
  simp only [mem_primesUpTo, Finset.mem_insert]
  constructor
  · rintro ⟨hqPrime, hqp⟩
    by_cases hqpEq : q = p
    · exact Or.inl hqpEq
    · exact Or.inr ⟨hqPrime, by omega⟩
  · rintro (hqp | ⟨hqPrime, hqPred⟩)
    · subst q
      exact ⟨hp, le_rfl⟩
    · exact ⟨hqPrime, by omega⟩

/-- The abstract insertion recurrence is therefore the literal increasing-prime
animation when the old frame is `primesUpTo (p-1)`. -/
theorem primeCombAnimationStepSite_primesUpTo_pred_eq
    (p n : ℕ) (hp : p.Prime) :
    primeCombAnimationStepSite (primesUpTo (p - 1)) p n =
      primeCombFrameSite (primesUpTo p) n := by
  have hSPrime : ∀ q ∈ primesUpTo (p - 1), q.Prime := by
    intro q hq
    exact prime_of_mem_primesUpTo hq
  have hSlt : ∀ q ∈ primesUpTo (p - 1), q < p := by
    intro q hq
    have hqPred := (mem_primesUpTo.mp hq).2
    have hp2 : 2 ≤ p := hp.two_le
    omega
  calc
    primeCombAnimationStepSite (primesUpTo (p - 1)) p n =
        primeCombFrameSite (insert p (primesUpTo (p - 1))) n :=
      primeCombAnimationStepSite_eq_insert
        (primesUpTo (p - 1)) p n hp hSPrime hSlt
    _ = primeCombFrameSite (primesUpTo p) n := by
      rw [primesUpTo_eq_insert_pred_of_prime hp]

/-! ## Fresh-face channels before aggregation -/

/-- Signed contribution of the child created from one old parent face `t` by
adjoining the fresh coordinate `p`.  The child is present only when its product
fits below `X`. -/
def frozenFreshPrimeChildContribution
    (p X : ℕ) (t : Finset ℕ) : ℤ :=
  if p * primeFaceProduct t ≤ X then
    booleanCubeSign (insert p t)
  else
    0

/-- The empty parent is the first-hit prime seat itself.  Its child sign is
`-1`; if the prime is already beyond the cutoff the boundary contribution is
zero. -/
def frozenPrimeUniverseFirstHitBoundaryMass (p X : ℕ) : ℤ :=
  if p ≤ X then -1 else 0

/-- Parentwise first-hit contribution.  Exactly the empty parent carries the
first-hit boundary seat. -/
def frozenFreshPrimeFirstHitContribution
    (p X : ℕ) (t : Finset ℕ) : ℤ :=
  if t = ∅ then frozenPrimeUniverseFirstHitBoundaryMass p X else 0

/-- Signed old-parent contribution on the genuine later-touch channel.  The
parent must be nonempty and its fresh `p`-child must fit below the cutoff. -/
def frozenFreshPrimeReachableParentContribution
    (p X : ℕ) (t : Finset ℕ) : ℤ :=
  if t ≠ ∅ ∧ p * primeFaceProduct t ≤ X then
    booleanCubeSign t
  else
    0

/-- **Local sequential child law.**  For one old parent face, the fresh child
is either the first-hit prime seat (empty parent), or the opposite-signed child
of one reachable nonempty parent.  This is the pointwise statement that must be
preserved before summing over the frame. -/
theorem frozenFreshPrimeChildContribution_eq_firstHit_sub_reachableParent
    {S t : Finset ℕ} {p X : ℕ}
    (hp : p ∉ S) (ht : t ∈ S.powerset) :
    frozenFreshPrimeChildContribution p X t =
      frozenFreshPrimeFirstHitContribution p X t -
        frozenFreshPrimeReachableParentContribution p X t := by
  classical
  have hpt : p ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht hp
  have hsign :
      booleanCubeSign (insert p t) = -booleanCubeSign t := by
    unfold booleanCubeSign
    rw [Finset.card_insert_of_notMem hpt, pow_succ]
    ring
  by_cases ht0 : t = ∅
  · subst t
    by_cases hpX : p ≤ X
    · simp [frozenFreshPrimeChildContribution,
        frozenFreshPrimeFirstHitContribution,
        frozenFreshPrimeReachableParentContribution,
        frozenPrimeUniverseFirstHitBoundaryMass,
        primeFaceProduct, hpX]
      norm_num [booleanCubeSign]
    · simp [frozenFreshPrimeChildContribution,
        frozenFreshPrimeFirstHitContribution,
        frozenFreshPrimeReachableParentContribution,
        frozenPrimeUniverseFirstHitBoundaryMass,
        primeFaceProduct, hpX]
  · by_cases hfit : p * primeFaceProduct t ≤ X
    · simp [frozenFreshPrimeChildContribution,
        frozenFreshPrimeFirstHitContribution,
        frozenFreshPrimeReachableParentContribution,
        ht0, hfit, hsign]
    · simp [frozenFreshPrimeChildContribution,
        frozenFreshPrimeFirstHitContribution,
        frozenFreshPrimeReachableParentContribution,
        ht0, hfit]

/-- Total signed mass of the fresh `p`-face, still indexed by the old parents
that generated its children. -/
def frozenPrimeUniverseFreshPrimeFaceMass
    (S : Finset ℕ) (p X : ℕ) : ℤ :=
  ∑ t ∈ S.powerset, frozenFreshPrimeChildContribution p X t

/-- Total signed old-state mass on nonempty parents whose fresh `p`-children
are actually reachable below the cutoff. -/
def frozenPrimeUniverseReachableProperParentMass
    (S : Finset ℕ) (p X : ℕ) : ℤ :=
  ∑ t ∈ S.powerset,
    frozenFreshPrimeReachableParentContribution p X t

/-- The fresh face is exactly the first-hit boundary seat minus the reachable
proper-parent mass.  This is the aggregate corollary of the local child law,
not its replacement. -/
theorem frozenPrimeUniverseFreshPrimeFaceMass_eq_firstHit_sub_reachableParent
    {S : Finset ℕ} {p X : ℕ} (hp : p ∉ S) :
    frozenPrimeUniverseFreshPrimeFaceMass S p X =
      frozenPrimeUniverseFirstHitBoundaryMass p X -
        frozenPrimeUniverseReachableProperParentMass S p X := by
  classical
  unfold frozenPrimeUniverseFreshPrimeFaceMass
    frozenPrimeUniverseReachableProperParentMass
  calc
    (∑ t ∈ S.powerset, frozenFreshPrimeChildContribution p X t) =
        ∑ t ∈ S.powerset,
          (frozenFreshPrimeFirstHitContribution p X t -
            frozenFreshPrimeReachableParentContribution p X t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact
        frozenFreshPrimeChildContribution_eq_firstHit_sub_reachableParent
          hp ht
    _ = (∑ t ∈ S.powerset,
          frozenFreshPrimeFirstHitContribution p X t) -
        ∑ t ∈ S.powerset,
          frozenFreshPrimeReachableParentContribution p X t := by
      rw [Finset.sum_sub_distrib]
    _ = frozenPrimeUniverseFirstHitBoundaryMass p X -
        ∑ t ∈ S.powerset,
          frozenFreshPrimeReachableParentContribution p X t := by
      simp [frozenFreshPrimeFirstHitContribution]

/-- Splitting the inserted powerset into its old face and its fresh `p`-face
without collapsing the fresh face to a lower-cutoff mass. -/
theorem frozenPrimeUniverseMass_insert_eq_old_add_freshPrimeFace
    {S : Finset ℕ} {p X : ℕ} (hp : p ∉ S) :
    frozenPrimeUniverseMass (insert p S) X =
      frozenPrimeUniverseMass S X +
        frozenPrimeUniverseFreshPrimeFaceMass S p X := by
  classical
  rw [frozenPrimeUniverseMass_eq_cutoffSum,
    frozenPrimeUniverseMass_eq_cutoffSum]
  rw [Finset.sum_powerset_insert hp]
  congr 1
  unfold frozenPrimeUniverseFreshPrimeFaceMass
    frozenFreshPrimeChildContribution
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht hp
  have hprod :
      primeFaceProduct (insert p t) = p * primeFaceProduct t := by
    simp [primeFaceProduct, hpt]
  rw [hprod]

/-- **Sequential fresh-prime state transition.**  The state after adjoining
`p` is the old state, minus the signed mass of genuine reachable parents, plus
the first-hit boundary prime seat.

This is deliberately stronger in structure than the collapsed recurrence
`F_(S insert p)(X) = F_S(X) - F_S(X/p)`: it remembers which part is the
first-hit seat and which part comes from opposite-signed parent-child flips. -/
theorem frozenPrimeUniverseMass_insert_eq_old_sub_reachableParent_add_firstHit
    {S : Finset ℕ} {p X : ℕ} (hp : p ∉ S) :
    frozenPrimeUniverseMass (insert p S) X =
      frozenPrimeUniverseMass S X -
        frozenPrimeUniverseReachableProperParentMass S p X +
          frozenPrimeUniverseFirstHitBoundaryMass p X := by
  rw [frozenPrimeUniverseMass_insert_eq_old_add_freshPrimeFace hp,
    frozenPrimeUniverseFreshPrimeFaceMass_eq_firstHit_sub_reachableParent hp]
  ring

/-! ## Literal one-prime animation state -/

/-- Summing the already-proved pointwise operational recurrence gives the
prefix state after one literal animation step. -/
theorem primeCombAnimationStepPrefixMass_eq_insert
    (S : Finset ℕ) (p W : ℕ)
    (hpPrime : p.Prime)
    (hSPrime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    primeCombAnimationStepPrefixMass S p W =
      primeCombFramePrefixMass (insert p S) W := by
  unfold primeCombAnimationStepPrefixMass primeCombFramePrefixMass
  apply Finset.sum_congr rfl
  intro n _hn
  exact primeCombAnimationStepSite_eq_insert S p n hpPrime hSPrime hSlt

/-- **Displayed one-prime state recurrence.**  In the literal animation,
first-hit proper multiples are score-neutral, square collisions remove their
old score, and later touches reverse their old score.  Hence after one fresh
prime arrives,

`new prefix = old prefix - killed old mass - 2 * flipped old mass`.

No prime interval has been summed and no averaging has been performed. -/
theorem primeCombFramePrefixMass_insert_eq_old_sub_channels
    (S : Finset ℕ) (p W : ℕ)
    (hpPrime : p.Prime)
    (hSPrime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    primeCombFramePrefixMass (insert p S) W =
      primeCombFramePrefixMass S W -
        primeCombFrameKillChannelMass S p W -
          2 * primeCombFrameFlipChannelMass S p W := by
  have hdelta := primeCombAnimationStepDelta_eq_channels S p W
  unfold primeCombAnimationStepDelta at hdelta
  rw [primeCombAnimationStepPrefixMass_eq_insert
    S p W hpPrime hSPrime hSlt] at hdelta
  linear_combination hdelta

/-- The preceding theorem specialized to the actual increasing-prime walk.
This is the exact recurrence from the frame immediately before `p` to the frame
immediately after `p`. -/
theorem primeCombFramePrefixMass_primesUpTo_step
    (p W : ℕ) (hp : p.Prime) :
    primeCombFramePrefixMass (primesUpTo p) W =
      primeCombFramePrefixMass (primesUpTo (p - 1)) W -
        primeCombFrameKillChannelMass (primesUpTo (p - 1)) p W -
          2 * primeCombFrameFlipChannelMass (primesUpTo (p - 1)) p W := by
  have hSPrime : ∀ q ∈ primesUpTo (p - 1), q.Prime := by
    intro q hq
    exact prime_of_mem_primesUpTo hq
  have hSlt : ∀ q ∈ primesUpTo (p - 1), q < p := by
    intro q hq
    have hqPred := (mem_primesUpTo.mp hq).2
    have hp2 : 2 ≤ p := hp.two_le
    omega
  rw [primesUpTo_eq_insert_pred_of_prime hp]
  exact primeCombFramePrefixMass_insert_eq_old_sub_channels
    (primesUpTo (p - 1)) p W hp hSPrime hSlt

end RHLean.Proof
