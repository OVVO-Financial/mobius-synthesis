import Mathlib
import RHLean.Proof.LowWheelCanonicalOrientedRunFibres
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence
import RHLean.Proof.SquareRootLowPrimeGoHyperbolicStripRecursion

/-!
# Square-root contraction of predecessor-dense frozen cubes

The ordered dense-divisibility split becomes quantitative at the root scale.
Let `s = Nat.sqrt R`.  If a face has product at most `R` and is triply
predecessor-dense above the smooth threshold `s`, then every prime coordinate
of that face is already at most `s`.

Indeed, a hypothetical coordinate `p > s` would satisfy

`p^4 <= s * primeFaceProduct t <= s * R`,

while `R < (s+1)^2` and `s+1 <= p` force

`s * R < (s+1)^4 <= p^4`.

Consequently the dense part of every frozen predecessor window with upper
product cutoff at most `R` collapses *exactly* to the smaller Boolean cube
`primesUpTo (Nat.sqrt R)`.  The complementary first-jump mass is left signed.
Thus a high-owner frozen window admits the exact contraction

`F_{q^-} = F_{sqrt R} + J_{q,sqrt R}`

before any norm or triangle inequality.

The next step is stronger than a recursive tail estimate.  At the same physical
cutoff `B <= R`, a first jump `p > sqrt R` cannot have any later prime
coordinate at all: two primes larger than `sqrt R` already have product larger
than `R`.  Hence the nominal decomposition

`t = u union {p} union v`

has `v = empty` identically.  The first-jump residual is therefore an exact
one-dimensional high-prime ledger with a completed lower-scale Mertens gap at
each prime.  No fixed-prime absolute value is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Elementary clock inequality behind the contraction. -/
theorem sqrt_mul_root_lt_succ_fourth (R : ℕ) :
    Nat.sqrt R * R < (Nat.sqrt R + 1) ^ 4 := by
  let s := Nat.sqrt R
  have hR : R < (s + 1) ^ 2 := by
    dsimp [s]
    exact Nat.lt_succ_sqrt' R
  by_cases hs : s = 0
  · subst s
    simp [hs]
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    have hleft : s * R < s * (s + 1) ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hR hspos
    have hsle : s ≤ (s + 1) ^ 2 := by
      nlinarith
    have hright :
        s * (s + 1) ^ 2 ≤ (s + 1) ^ 2 * (s + 1) ^ 2 :=
      Nat.mul_le_mul_right ((s + 1) ^ 2) hsle
    calc
      Nat.sqrt R * R = s * R := by rfl
      _ < s * (s + 1) ^ 2 := hleft
      _ ≤ (s + 1) ^ 2 * (s + 1) ^ 2 := hright
      _ = (s + 1) ^ 4 := by ring
      _ = (Nat.sqrt R + 1) ^ 4 := by rfl

/-- A triply predecessor-dense prime face of product at most `R` contains no
prime above `sqrt R`.  This is the strict multiplicative contraction. -/
theorem predecessorDensePrimeFace_subset_primesUpTo_sqrt
    {R : ℕ} {t : Finset ℕ}
    (hprime : ∀ p ∈ t, p.Prime)
    (hdense : PredecessorDenseFace 3 (Nat.sqrt R) t)
    (hprod : primeFaceProduct t ≤ R) :
    t ⊆ primesUpTo (Nat.sqrt R) := by
  intro p hpt
  have hpPrime := hprime p hpt
  apply mem_primesUpTo.mpr
  refine ⟨hpPrime, ?_⟩
  by_contra hnot
  have hsp : Nat.sqrt R < p := Nat.lt_of_not_ge hnot
  have hp4 : p ^ 4 ≤ Nat.sqrt R * primeFaceProduct t := by
    have h :=
      predecessorDenseFace_coordinate_power_succ_le_of_large
        hprime hdense hpt hsp
    simpa using h
  have hp4R : p ^ 4 ≤ Nat.sqrt R * R :=
    hp4.trans (Nat.mul_le_mul_left (Nat.sqrt R) hprod)
  have hclock := sqrt_mul_root_lt_succ_fourth R
  have hsucc : Nat.sqrt R + 1 ≤ p := by omega
  have hpow : (Nat.sqrt R + 1) ^ 4 ≤ p ^ 4 :=
    Nat.pow_le_pow_left hsucc 4
  have : p ^ 4 < p ^ 4 := hp4R.trans_lt (hclock.trans_le hpow)
  exact (Nat.lt_irrefl _ this)

/-- Dense faces in an old owner window are already supported on the square-root
prime universe as soon as the window product is bounded by `R`. -/
theorem predecessorDenseFrozenWindowFace_subset_sqrt
    {R q A B : ℕ} {t : Finset ℕ}
    (hBR : B ≤ R)
    (ht : t ∈ predecessorDenseFrozenWindowFaces 3 (Nat.sqrt R)
      (primesUpTo (q - 1)) A B) :
    t ∈ (primesUpTo (Nat.sqrt R)).powerset := by
  rcases mem_predecessorDenseFrozenWindowFaces.mp ht with
    ⟨hwindow, hdense⟩
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htOld, _hlo, hup⟩
  have hOldSub := Finset.mem_powerset.mp htOld
  have hprime : ∀ p ∈ t, p.Prime := by
    intro p hpt
    exact prime_of_mem_primesUpTo (hOldSub hpt)
  have hprod : primeFaceProduct t ≤ R := hup.trans hBR
  exact Finset.mem_powerset.mpr
    (predecessorDensePrimeFace_subset_primesUpTo_sqrt
      hprime hdense hprod)

/-- **Exact dense-face contraction.**  If the old owner lies above `sqrt R`,
the predecessor-dense portion of its frozen window is literally the same face
set as the full frozen window in the smaller prime universe through `sqrt R`. -/
theorem predecessorDenseFrozenWindowFaces_sqrt_eq
    (R q A B : ℕ)
    (hqroot : Nat.sqrt R < q)
    (hBR : B ≤ R) :
    predecessorDenseFrozenWindowFaces 3 (Nat.sqrt R)
        (primesUpTo (q - 1)) A B =
      frozenPrimeUniverseWindowFaces
        (primesUpTo (Nat.sqrt R)) A B := by
  ext t
  constructor
  · intro ht
    have htSmall :=
      predecessorDenseFrozenWindowFace_subset_sqrt hBR ht
    rcases mem_predecessorDenseFrozenWindowFaces.mp ht with
      ⟨hwindow, _hdense⟩
    rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
      ⟨_htOld, hlo, hup⟩
    exact mem_frozenPrimeUniverseWindowFaces.mpr
      ⟨htSmall, hlo, hup⟩
  · intro ht
    rcases mem_frozenPrimeUniverseWindowFaces.mp ht with
      ⟨htSmall, hlo, hup⟩
    have hSmallSub := Finset.mem_powerset.mp htSmall
    have htOld : t ∈ (primesUpTo (q - 1)).powerset := by
      apply Finset.mem_powerset.mpr
      intro p hpt
      rcases mem_primesUpTo.mp (hSmallSub hpt) with ⟨hpPrime, hpLe⟩
      apply mem_primesUpTo.mpr
      refine ⟨hpPrime, ?_⟩
      omega
    have hdense : PredecessorDenseFace 3 (Nat.sqrt R) t := by
      intro p hpt hlarge
      have hpLe := (mem_primesUpTo.mp (hSmallSub hpt)).2
      omega
    exact mem_predecessorDenseFrozenWindowFaces.mpr
      ⟨mem_frozenPrimeUniverseWindowFaces.mpr ⟨htOld, hlo, hup⟩,
        hdense⟩

/-- Signed version of the exact dense-face contraction. -/
theorem predecessorDenseFrozenWindowMass_sqrt_eq
    (R q A B : ℕ)
    (hqroot : Nat.sqrt R < q)
    (hBR : B ≤ R) :
    predecessorDenseFrozenWindowMass 3 (Nat.sqrt R)
        (primesUpTo (q - 1)) A B =
      frozenPrimeUniverseWindowMass
        (primesUpTo (Nat.sqrt R)) A B := by
  unfold predecessorDenseFrozenWindowMass frozenPrimeUniverseWindowMass
  rw [predecessorDenseFrozenWindowFaces_sqrt_eq R q A B hqroot hBR]

/-- **Square-root signed contraction of one high-owner frozen window.**
The dense contribution is exactly the lower prime universe; all unresolved
arithmetic is confined to the signed first-jump residual. -/
theorem frozenPrimeUniverseWindowMass_eq_sqrtContraction_add_firstJump
    (R q A B : ℕ)
    (hqroot : Nat.sqrt R < q)
    (hBR : B ≤ R) :
    frozenPrimeUniverseWindowMass (primesUpTo (q - 1)) A B =
      frozenPrimeUniverseWindowMass (primesUpTo (Nat.sqrt R)) A B +
        predecessorFirstJumpFrozenWindowMass
          3 (Nat.sqrt R) (primesUpTo (q - 1)) A B := by
  rw [frozenPrimeUniverseWindowMass_eq_dense_add_firstJump
      3 (Nat.sqrt R) (primesUpTo (q - 1)) A B,
    predecessorDenseFrozenWindowMass_sqrt_eq R q A B hqroot hBR]

/-- The predecessor cube attached to the canonical first high jump is itself
entirely supported below `sqrt R`. -/
theorem firstJumpFrozenWindowFace_sqrt_exists_highPrime_lowPredecessor
    {R q A B : ℕ} {t : Finset ℕ}
    (hqroot : Nat.sqrt R < q)
    (hBR : B ≤ R)
    (ht : t ∈ predecessorFirstJumpFrozenWindowFaces 3 (Nat.sqrt R)
      (primesUpTo (q - 1)) A B) :
    ∃ p ∈ t,
      Nat.sqrt R < p ∧ p < q ∧
      Nat.sqrt R * predecessorPrimeFaceProduct t p < p ^ 3 ∧
      predecessorPrimeFace t p ∈
        (primesUpTo (Nat.sqrt R)).powerset := by
  rcases mem_predecessorFirstJumpFrozenWindowFaces.mp ht with
    ⟨hwindow, hnotDense⟩
  rcases exists_first_predecessorDenseFailure_with_densePredecessor hnotDense with
    ⟨p, hpt, hsp, hfail, hpredDense⟩
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htOld, _hlo, hup⟩
  have hOldSub := Finset.mem_powerset.mp htOld
  have hpOld := hOldSub hpt
  rcases mem_primesUpTo.mp hpOld with ⟨hpPrime, hpLeOld⟩
  have hpLtQ : p < q := by omega
  have hprimePred : ∀ r ∈ predecessorPrimeFace t p, r.Prime := by
    intro r hr
    exact prime_of_mem_primesUpTo
      (hOldSub (mem_predecessorPrimeFace.mp hr).1)
  have hprefix :=
    prime_mul_predecessorPrimeFaceProduct_le
      (fun r hr => prime_of_mem_primesUpTo (hOldSub hr)) hpt
  have hpredLeMul :
      predecessorPrimeFaceProduct t p ≤
        p * predecessorPrimeFaceProduct t p := by
    have hpOne : 1 ≤ p := hpPrime.one_le
    simpa [one_mul, Nat.mul_comm] using
      Nat.mul_le_mul_right (predecessorPrimeFaceProduct t p) hpOne
  have hpredLeR : predecessorPrimeFaceProduct t p ≤ R :=
    (hpredLeMul.trans hprefix).trans (hup.trans hBR)
  have hpredSmall :
      predecessorPrimeFace t p ⊆ primesUpTo (Nat.sqrt R) :=
    predecessorDensePrimeFace_subset_primesUpTo_sqrt
      hprimePred hpredDense hpredLeR
  exact ⟨p, hpt, hsp, hpLtQ, hfail,
    Finset.mem_powerset.mpr hpredSmall⟩

/-- **Oriented-state specialization.**  Every oriented state whose fresh owner
is above `sqrt R` has its signed Boolean mass split into an exact square-root
frozen cube plus a signed first-high-jump residual. -/
theorem sum_booleanCubeSign_orientedChargingFaces_eq_sqrtFrozen_add_firstJump
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty)
    (hqroot : Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k)) :
    (∑ t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k),
        booleanCubeSign t) =
      frozenPrimeUniverseWindowMass
        (primesUpTo (Nat.sqrt R))
        (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) +
      predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R)
        (primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1))
        (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) := by
  have hupper : lowWheelCanonicalDowncrossOwnershipUpper R c k ≤ R := by
    unfold lowWheelCanonicalDowncrossOwnershipUpper
    exact (min_le_left _ _).trans (Nat.div_le_self _ _)
  rw [sum_booleanCubeSign_orientedChargingFaces_eq_frozenWindowMass hne,
    frozenPrimeUniverseWindowMass_eq_sqrtContraction_add_firstJump
      R (lowWheelCanonicalDowncrossPivot (c, k))
      (R / k) (lowWheelCanonicalDowncrossOwnershipUpper R c k)
      hqroot hupper]

/-! ## The first-jump residual has no later tail at square-root scale -/

/-- `p` is the canonical first large predecessor-density failure of `t`. -/
def IsPredecessorFirstJumpAt
    (d Y : ℕ) (t : Finset ℕ) (p : ℕ) : Prop :=
  p ∈ t ∧
    Y < p ∧
    Y * predecessorPrimeFaceProduct t p < p ^ d ∧
    ∀ r ∈ t, r < p → Y < r →
      r ^ d ≤ Y * predecessorPrimeFaceProduct t r

/-- The canonical first predecessor jump is unique. -/
theorem isPredecessorFirstJumpAt_unique
    {d Y : ℕ} {t : Finset ℕ} {p q : ℕ}
    (hp : IsPredecessorFirstJumpAt d Y t p)
    (hq : IsPredecessorFirstJumpAt d Y t q) :
    p = q := by
  rcases hp with ⟨hpt, hYp, hpfail, hprevP⟩
  rcases hq with ⟨hqt, hYq, hqfail, hprevQ⟩
  by_cases hpq : p = q
  · exact hpq
  · by_cases hpLtQ : p < q
    · have hgood := hprevQ p hpt hpLtQ hYp
      omega
    · have hqLtP : q < p := by omega
      have hgood := hprevP q hqt hqLtP hYq
      omega

/-- Every first-jump frozen face has its canonical first failure. -/
theorem firstJumpFrozenWindowFace_exists_isPredecessorFirstJumpAt
    {d Y : ℕ} {S : Finset ℕ} {A B : ℕ} {t : Finset ℕ}
    (ht : t ∈ predecessorFirstJumpFrozenWindowFaces d Y S A B) :
    ∃ p, IsPredecessorFirstJumpAt d Y t p := by
  rcases firstJumpFrozenWindowFace_exists_firstFailure ht with
    ⟨p, hpt, hYp, hfail, hprev⟩
  exact ⟨p, hpt, hYp, hfail, hprev⟩

/-- The slice of the first-jump residual whose canonical jump is `p`. -/
def predecessorFirstJumpFrozenWindowSlice
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) : Finset (Finset ℕ) :=
  (predecessorFirstJumpFrozenWindowFaces d Y S A B).filter fun t =>
    IsPredecessorFirstJumpAt d Y t p

@[simp] theorem mem_predecessorFirstJumpFrozenWindowSlice
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {t : Finset ℕ} :
    t ∈ predecessorFirstJumpFrozenWindowSlice d Y S A B p ↔
      t ∈ predecessorFirstJumpFrozenWindowFaces d Y S A B ∧
        IsPredecessorFirstJumpAt d Y t p := by
  simp [predecessorFirstJumpFrozenWindowSlice]

/-- The canonical first-jump slices are pairwise disjoint. -/
theorem predecessorFirstJumpFrozenWindowSlice_pairwise
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    Set.PairwiseDisjoint (↑S)
      (predecessorFirstJumpFrozenWindowSlice d Y S A B) := by
  intro p _hpS q _hqS hpq
  change Disjoint
    (predecessorFirstJumpFrozenWindowSlice d Y S A B p)
    (predecessorFirstJumpFrozenWindowSlice d Y S A B q)
  rw [Finset.disjoint_left]
  intro t htp htq
  have hpFirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp htp).2
  have hqFirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp htq).2
  exact hpq (isPredecessorFirstJumpAt_unique hpFirst hqFirst)

/-- The full first-jump residual is the disjoint union of its canonical
prime-indexed slices. -/
theorem predecessorFirstJumpFrozenWindowFaces_eq_biUnion_slices
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    predecessorFirstJumpFrozenWindowFaces d Y S A B =
      S.biUnion (predecessorFirstJumpFrozenWindowSlice d Y S A B) := by
  ext t
  constructor
  · intro ht
    rcases firstJumpFrozenWindowFace_exists_isPredecessorFirstJumpAt ht with
      ⟨p, hpFirst⟩
    have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp ht).1
    have htPow := (mem_frozenPrimeUniverseWindowFaces.mp hwindow).1
    have hpS := (Finset.mem_powerset.mp htPow) hpFirst.1
    exact Finset.mem_biUnion.mpr
      ⟨p, hpS,
        mem_predecessorFirstJumpFrozenWindowSlice.mpr ⟨ht, hpFirst⟩⟩
  · intro ht
    rcases Finset.mem_biUnion.mp ht with ⟨p, _hpS, htp⟩
    exact (mem_predecessorFirstJumpFrozenWindowSlice.mp htp).1

/-- Signed mass of one canonical first-jump slice. -/
def predecessorFirstJumpFrozenWindowSliceMass
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) : ℤ :=
  ∑ t ∈ predecessorFirstJumpFrozenWindowSlice d Y S A B p,
    booleanCubeSign t

/-- Exact signed Fubini over the canonical first jump. -/
theorem predecessorFirstJumpFrozenWindowMass_eq_sum_slices
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    predecessorFirstJumpFrozenWindowMass d Y S A B =
      ∑ p ∈ S,
        predecessorFirstJumpFrozenWindowSliceMass d Y S A B p := by
  unfold predecessorFirstJumpFrozenWindowMass
    predecessorFirstJumpFrozenWindowSliceMass
  rw [predecessorFirstJumpFrozenWindowFaces_eq_biUnion_slices]
  exact Finset.sum_biUnion
    (predecessorFirstJumpFrozenWindowSlice_pairwise d Y S A B)

/-- Coordinates strictly after the canonical first jump. -/
def firstJumpTailFace (t : Finset ℕ) (p : ℕ) : Finset ℕ :=
  t.filter fun r => p < r

@[simp] theorem mem_firstJumpTailFace
    {t : Finset ℕ} {p r : ℕ} :
    r ∈ firstJumpTailFace t p ↔ r ∈ t ∧ p < r := by
  simp [firstJumpTailFace]

/-- **No later tail at the square-root wall.**  In a product window with
`B <= R`, once the first jump satisfies `p > sqrt R`, a second later prime
would force the face product above `R`. -/
theorem sqrtFirstJumpSlice_tail_eq_empty
    {R q A B p : ℕ} {t : Finset ℕ}
    (hBR : B ≤ R)
    (ht : t ∈ predecessorFirstJumpFrozenWindowSlice
      3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p) :
    firstJumpTailFace t p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hslice := mem_predecessorFirstJumpFrozenWindowSlice.mp ht
  have hfirst := hslice.2
  have hjump := hslice.1
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hjump).1
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htPow, _hlo, hup⟩
  have htSub := Finset.mem_powerset.mp htPow
  have hrt := (mem_firstJumpTailFace.mp hr).1
  have hpr := (mem_firstJumpTailFace.mp hr).2
  have hsub : insert p {r} ⊆ t := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · subst z
      exact hfirst.1
    · subst z
      exact hrt
  have hprodLower : p * r ≤ primeFaceProduct t := by
    unfold primeFaceProduct
    have hle := Finset.prod_le_prod_of_subset_of_one_le' hsub (by
      intro z hzt _hzsmall
      exact (prime_of_mem_primesUpTo (htSub hzt)).one_le)
    have hne : p ≠ r := by omega
    simpa [hne, Nat.mul_comm] using hle
  have hRnext : R < (Nat.sqrt R + 1) ^ 2 := Nat.lt_succ_sqrt' R
  have hrootLt : Nat.sqrt R < p := hfirst.2.1
  have hsp : Nat.sqrt R + 1 ≤ p := by omega
  have hsr : Nat.sqrt R + 1 ≤ r := by omega
  have hnextLe : (Nat.sqrt R + 1) ^ 2 ≤ p * r := by
    rw [pow_two]
    exact Nat.mul_le_mul hsp hsr
  have hRpr : R < p * r := hRnext.trans_le hnextLe
  have hprR : p * r ≤ R := hprodLower.trans (hup.trans hBR)
  omega

/-- Thus a square-root first-jump face is exactly its completed predecessor
with the single high prime adjoined; the nominal later cube is empty. -/
theorem sqrtFirstJumpSlice_face_eq_insert_predecessor
    {R q A B p : ℕ} {t : Finset ℕ}
    (hBR : B ≤ R)
    (ht : t ∈ predecessorFirstJumpFrozenWindowSlice
      3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p) :
    t = insert p (predecessorPrimeFace t p) := by
  have htail := sqrtFirstJumpSlice_tail_eq_empty hBR ht
  have hfirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp ht).2
  ext r
  constructor
  · intro hrt
    by_cases hrp : r = p
    · subst r
      simp
    · have hrlt : r < p := by
        by_contra hnot
        have hpr : p < r := by omega
        have hrTail : r ∈ firstJumpTailFace t p :=
          mem_firstJumpTailFace.mpr ⟨hrt, hpr⟩
        rw [htail] at hrTail
        simp at hrTail
      exact Finset.mem_insert_of_mem
        (mem_predecessorPrimeFace.mpr ⟨hrt, hrlt⟩)
  · intro hr
    rcases Finset.mem_insert.mp hr with hEq | hpred
    · subst r
      exact hfirst.1
    · exact (mem_predecessorPrimeFace.mp hpred).1

/-- The predecessor attached to a canonical square-root first jump is entirely
supported on the lower prime universe through `sqrt R`. -/
theorem sqrtFirstJumpSlice_predecessor_subset_sqrt
    {R q A B p : ℕ} {t : Finset ℕ}
    (hBR : B ≤ R)
    (ht : t ∈ predecessorFirstJumpFrozenWindowSlice
      3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p) :
    predecessorPrimeFace t p ∈ (primesUpTo (Nat.sqrt R)).powerset := by
  have hslice := mem_predecessorFirstJumpFrozenWindowSlice.mp ht
  have hfirst := hslice.2
  have hjump := hslice.1
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hjump).1
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htPow, _hlo, hup⟩
  have htSub := Finset.mem_powerset.mp htPow
  have hprimePred : ∀ r ∈ predecessorPrimeFace t p, r.Prime := by
    intro r hr
    exact prime_of_mem_primesUpTo
      (htSub (mem_predecessorPrimeFace.mp hr).1)
  have hpredDense :
      PredecessorDenseFace 3 (Nat.sqrt R) (predecessorPrimeFace t p) :=
    predecessorPrimeFace_dense_of_previous hfirst.2.2.2
  have hpPrime := prime_of_mem_primesUpTo (htSub hfirst.1)
  have hprefix :=
    prime_mul_predecessorPrimeFaceProduct_le
      (fun r hr => prime_of_mem_primesUpTo (htSub hr)) hfirst.1
  have hpredLeMul :
      predecessorPrimeFaceProduct t p ≤
        p * predecessorPrimeFaceProduct t p := by
    simpa [one_mul, Nat.mul_comm] using
      Nat.mul_le_mul_right (predecessorPrimeFaceProduct t p) hpPrime.one_le
  have hpredLeR : predecessorPrimeFaceProduct t p ≤ R :=
    (hpredLeMul.trans hprefix).trans (hup.trans hBR)
  exact Finset.mem_powerset.mpr
    (predecessorDensePrimeFace_subset_primesUpTo_sqrt
      hprimePred hpredDense hpredLeR)

/-! ## Exact high-prime telescope of the first-jump residual -/

/-- Prime coordinates added between two prefix universes. -/
def frozenPrimeUniverseHighPrimeSet (s K : ℕ) : Finset ℕ :=
  primesUpTo K \ primesUpTo s

@[simp] theorem mem_frozenPrimeUniverseHighPrimeSet
    {s K p : ℕ} :
    p ∈ frozenPrimeUniverseHighPrimeSet s K ↔
      p.Prime ∧ s < p ∧ p ≤ K := by
  constructor
  · intro hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpK, hpNotS⟩
    rcases mem_primesUpTo.mp hpK with ⟨hpPrime, hpLeK⟩
    have hsp : s < p := by
      by_contra hnot
      have hpLeS : p ≤ s := Nat.le_of_not_gt hnot
      exact hpNotS (mem_primesUpTo.mpr ⟨hpPrime, hpLeS⟩)
    exact ⟨hpPrime, hsp, hpLeK⟩
  · rintro ⟨hpPrime, hsp, hpLeK⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_primesUpTo.mpr ⟨hpPrime, hpLeK⟩, ?_⟩
    intro hpS
    have hpLeS := (mem_primesUpTo.mp hpS).2
    omega

/-- Monotonicity of the finite prime prefix. -/
theorem primesUpTo_subset_of_le
    {s K : ℕ} (hsK : s ≤ K) : primesUpTo s ⊆ primesUpTo K := by
  intro p hp
  rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpLeS⟩
  exact mem_primesUpTo.mpr ⟨hpPrime, hpLeS.trans hsK⟩

/-- A genuine prime universe has no face product at cutoff zero. -/
theorem frozenPrimeUniverseMass_primesUpTo_zero (K : ℕ) :
    frozenPrimeUniverseMass (primesUpTo K) 0 = 0 := by
  rw [frozenPrimeUniverseMass_eq_cutoffSum]
  apply Finset.sum_eq_zero
  intro t ht
  have htSub := Finset.mem_powerset.mp ht
  have hprodPos : 0 < primeFaceProduct t := by
    unfold primeFaceProduct
    exact Finset.prod_pos fun p hp =>
      (prime_of_mem_primesUpTo (htSub hp)).pos
  have hnot : ¬ primeFaceProduct t ≤ 0 := by omega
  simp [hnot]

/-- **High-prime upper-column telescope.**  The contribution of the primes
inserted after `s` is exactly the difference between the two frozen prefixes.
This version includes cutoff zero. -/
theorem frozenPrimeUniverse_highUpperColumn_telescope
    (X s K : ℕ) (hsK : s ≤ K) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
      frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      frozenPrimeUniverseMass (primesUpTo s) X -
        frozenPrimeUniverseMass (primesUpTo K) X := by
  have hsub : primesUpTo s ⊆ primesUpTo K := primesUpTo_subset_of_le hsK
  by_cases hX0 : X = 0
  · subst X
    calc
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (0 / p)) = 0 := by
        apply Finset.sum_eq_zero
        intro p _hp
        simpa using frozenPrimeUniverseMass_primesUpTo_zero (p - 1)
      _ = frozenPrimeUniverseMass (primesUpTo s) 0 -
          frozenPrimeUniverseMass (primesUpTo K) 0 := by
        rw [frozenPrimeUniverseMass_primesUpTo_zero,
          frozenPrimeUniverseMass_primesUpTo_zero]
        ring
  · have hX : 1 ≤ X := by omega
    have hK := frozenPrimeUniverse_upperColumn_telescope X K hX
    have hs := frozenPrimeUniverse_upperColumn_telescope X s hX
    have hsplit :
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
            frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) +
          (∑ p ∈ primesUpTo s,
            frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
          ∑ p ∈ primesUpTo K,
            frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) := by
      unfold frozenPrimeUniverseHighPrimeSet
      exact Finset.sum_sdiff hsub
    calc
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
        (∑ p ∈ primesUpTo K,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) -
        ∑ p ∈ primesUpTo s,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) :=
        (eq_sub_iff_add_eq).2 hsplit
      _ = (1 - frozenPrimeUniverseMass (primesUpTo K) X) -
          (1 - frozenPrimeUniverseMass (primesUpTo s) X) := by
        rw [hK, hs]
      _ = frozenPrimeUniverseMass (primesUpTo s) X -
          frozenPrimeUniverseMass (primesUpTo K) X := by ring

/-- Window form of the high-prime telescope.  The whole signed high-prime
column is retained before any norm is taken. -/
theorem frozenPrimeUniverse_highWindow_telescope
    (s K A B : ℕ) (hsK : s ≤ K) (hAB : A ≤ B) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
      frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
        (A / p) (B / p)) =
      frozenPrimeUniverseWindowMass (primesUpTo s) A B -
        frozenPrimeUniverseWindowMass (primesUpTo K) A B := by
  calc
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
        frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
          (A / p) (B / p)) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
        (frozenPrimeUniverseMass (primesUpTo (p - 1)) (B / p) -
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (A / p)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [frozenPrimeUniverseWindowMass_eq_sub (Nat.div_le_div_right hAB)]
    _ = (∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (B / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (A / p) := by
      rw [Finset.sum_sub_distrib]
    _ = (frozenPrimeUniverseMass (primesUpTo s) B -
          frozenPrimeUniverseMass (primesUpTo K) B) -
        (frozenPrimeUniverseMass (primesUpTo s) A -
          frozenPrimeUniverseMass (primesUpTo K) A) := by
      rw [frozenPrimeUniverse_highUpperColumn_telescope B s K hsK,
        frozenPrimeUniverse_highUpperColumn_telescope A s K hsK]
    _ = frozenPrimeUniverseWindowMass (primesUpTo s) A B -
        frozenPrimeUniverseWindowMass (primesUpTo K) A B := by
      rw [frozenPrimeUniverseWindowMass_eq_sub hAB,
        frozenPrimeUniverseWindowMass_eq_sub hAB]
      ring

/-- The first-jump residual is exactly the negative high-prime column.
Thus the canonical `u,p,v` decomposition has already telescoped the complete
later-prime geometry into one signed sum indexed only by the first high prime. -/
theorem sqrtFirstJumpResidual_eq_neg_highPrimeWindows
    {R q A B : ℕ}
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B =
      -(∑ p ∈ frozenPrimeUniverseHighPrimeSet (Nat.sqrt R) (q - 1),
        frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
          (A / p) (B / p)) := by
  have hsK : Nat.sqrt R ≤ q - 1 := by omega
  have hcontract :=
    frozenPrimeUniverseWindowMass_eq_sqrtContraction_add_firstJump
      R q A B hqroot hBR
  have htelescope :=
    frozenPrimeUniverse_highWindow_telescope
      (Nat.sqrt R) (q - 1) A B hsK hAB
  have hJ :
      predecessorFirstJumpFrozenWindowMass
          3 (Nat.sqrt R) (primesUpTo (q - 1)) A B =
        frozenPrimeUniverseWindowMass (primesUpTo (q - 1)) A B -
          frozenPrimeUniverseWindowMass (primesUpTo (Nat.sqrt R)) A B := by
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using hcontract.symm
  calc
    predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B =
      frozenPrimeUniverseWindowMass (primesUpTo (q - 1)) A B -
        frozenPrimeUniverseWindowMass (primesUpTo (Nat.sqrt R)) A B := hJ
    _ = -(frozenPrimeUniverseWindowMass (primesUpTo (Nat.sqrt R)) A B -
        frozenPrimeUniverseWindowMass (primesUpTo (q - 1)) A B) := by ring
    _ = -(∑ p ∈ frozenPrimeUniverseHighPrimeSet (Nat.sqrt R) (q - 1),
        frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
          (A / p) (B / p)) := by rw [← htelescope]

/-- Above `sqrt R`, every reciprocal cutoff `B/p` is already below its owner
`p`, so the predecessor frozen window is a complete ordinary Mertens gap. -/
theorem sqrtHighPrimePredecessorWindow_eq_mertensGap
    {R A B p : ℕ} (hBR : B ≤ R) (hAB : A ≤ B)
    (hp : p.Prime) (hsp : Nat.sqrt R < p) :
    frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
        (A / p) (B / p) =
      mertensSummatoryInt (B / p) - mertensSummatoryInt (A / p) := by
  have hRnext : R < (Nat.sqrt R + 1) ^ 2 := Nat.lt_succ_sqrt' R
  have hsucc : Nat.sqrt R + 1 ≤ p := by omega
  have hnextLe : (Nat.sqrt R + 1) ^ 2 ≤ p * p := by
    rw [pow_two]
    exact Nat.mul_le_mul hsucc hsucc
  have hBlt : B < p * p := hBR.trans_lt (hRnext.trans_le hnextLe)
  have hBdiv : B / p < p := by
    apply (Nat.div_lt_iff_lt_mul hp.pos).2
    simpa [Nat.mul_comm] using hBlt
  have hAdiv : A / p < p :=
    (Nat.div_le_div_right hAB).trans_lt hBdiv
  rw [frozenPrimeUniverseWindowMass_eq_sub (Nat.div_le_div_right hAB),
    frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner hp hBdiv,
    frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner hp hAdiv]

/-- **Final exact first-jump form.**  The residual is one signed high-prime
sum of lower-scale Mertens gaps.  There is no later tail cube left to estimate. -/
theorem sqrtFirstJumpResidual_eq_neg_sum_mertensGaps
    {R q A B : ℕ}
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B =
      -(∑ p ∈ frozenPrimeUniverseHighPrimeSet (Nat.sqrt R) (q - 1),
        (mertensSummatoryInt (B / p) - mertensSummatoryInt (A / p))) := by
  rw [sqrtFirstJumpResidual_eq_neg_highPrimeWindows hqroot hBR hAB]
  congr 1
  apply Finset.sum_congr rfl
  intro p hpSet
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hpSet
  exact sqrtHighPrimePredecessorWindow_eq_mertensGap
    hBR hAB hpData.1 hpData.2.1

end RHLean.Proof
