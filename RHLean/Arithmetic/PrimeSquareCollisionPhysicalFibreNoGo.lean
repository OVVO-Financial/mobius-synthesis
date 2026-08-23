import Mathlib
import RHLean.Arithmetic.PrimeWheelCorrectedLocalFlip

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# No-go theorem for the literal physical collision-site fibre

The nine CRT collision labels record actual prime-square hits.  If a label is
weighted on that same physical square-hit site, the corrected prime-wheel field
is identically zero there.  Thus the current literal collision-site fibre cannot
carry a nonzero corrected-field quotient.

The immediate adjacent-cell escape is unavailable as well.  For `p >= 7`, a
`p^2` hit in the current three-slot cell leaves only exponent states `0` and `2`
throughout the current and next active cells: the hit slot is state `2`, every
other current slot is a genuine miss, and every next-cell slot is a genuine
miss.  Since `primeCombExponentFlip` exchanges `0` and `1` while fixing `2`, any
realized exponent flip inside those two physical cells is forced to be the
trivial `2 -> 2` square state, where both corrected weights vanish.

Consequently a viable quotient must transport collision labels outside the
literal current/next-cell site fibre and separately justify that transport.
-/

@[simp] theorem localPrimeExponentState_eq_two_of_square_hit
    (p n : ℕ) (hsq : p ^ 2 ∣ n) :
    localPrimeExponentState p n = 2 := by
  simp [localPrimeExponentState, hsq]

@[simp] theorem localPrimeExponentState_eq_zero_of_not_dvd
    (p n : ℕ) (hnot : ¬ p ∣ n) :
    localPrimeExponentState p n = 0 := by
  have hsq : ¬ p ^ 2 ∣ n := by
    intro h
    apply hnot
    exact dvd_trans (dvd_pow_self p (by norm_num)) h
  simp [localPrimeExponentState, hsq, hnot]

/-- Exponent state `2` is not merely a symbolic label: it forces an actual
selected-prime square hit. -/
theorem square_hit_of_localPrimeExponentState_eq_two
    (p n : ℕ)
    (hstate : localPrimeExponentState p n = 2) :
    p ^ 2 ∣ n := by
  by_contra hsq
  by_cases hp : p ∣ n <;>
    simp [localPrimeExponentState, hsq, hp] at hstate

/-- A literal adjacent-cell continuation of the square-hit site itself cannot
implement `primeCombExponentFlip` for any selected prime `p >= 7`. -/
theorem adjacent_threeSlot_exponentFlip_impossible_of_square_hit
    (p k i j : ℕ)
    (hp : 6 < p)
    (hi : i < 3) (hj : j < 3)
    (hsq : p ^ 2 ∣ threeSlotValue k i) :
    localPrimeExponentState p (threeSlotValue (k + 1) j) ≠
      primeCombExponentFlip
        (localPrimeExponentState p (threeSlotValue k i)) := by
  have hnext : ¬ p ∣ threeSlotValue (k + 1) j :=
    prime_not_dvd_next_threeSlotValue_of_square_hit
      p k i j hp hi hj hsq
  rw [localPrimeExponentState_eq_zero_of_not_dvd p _ hnext,
    localPrimeExponentState_eq_two_of_square_hit p _ hsq]
  native_decide

/-- Physical support consisting of the three current active sites and the three
active sites in the immediately following four-cell. -/
def IsAdjacentThreeSlotSite (k n : ℕ) : Prop :=
  ∃ j : ℕ, j < 3 ∧
    (n = threeSlotValue k j ∨ n = threeSlotValue (k + 1) j)

/-- A current `p^2` collision with `p >= 7` eliminates exponent state `1` from
all six active sites in the current/next-cell physical support. -/
theorem adjacent_threeSlot_exponentState_ne_one_of_square_hit
    (p k i n : ℕ)
    (hp : 6 < p)
    (hi : i < 3)
    (hsq : p ^ 2 ∣ threeSlotValue k i)
    (hn : IsAdjacentThreeSlotSite k n) :
    localPrimeExponentState p n ≠ 1 := by
  rcases hn with ⟨j, hj, hcur | hnext⟩
  · subst n
    by_cases hij : i = j
    · subst j
      rw [localPrimeExponentState_eq_two_of_square_hit p _ hsq]
      native_decide
    · have hmiss : ¬ p ∣ threeSlotValue k j :=
        prime_not_dvd_other_threeSlotValue_of_square_hit
          p k i j (by omega) hi hj hij hsq
      rw [localPrimeExponentState_eq_zero_of_not_dvd p _ hmiss]
      native_decide
  · subst n
    have hmiss : ¬ p ∣ threeSlotValue (k + 1) j :=
      prime_not_dvd_next_threeSlotValue_of_square_hit
        p k i j hp hi hj hsq
    rw [localPrimeExponentState_eq_zero_of_not_dvd p _ hmiss]
    native_decide

/-- **Adjacent two-cell flip no-go.**  If two sites both lie in the literal
current/next-cell physical support and nevertheless satisfy the required
exponent-state flip, both sites must be square-hit state `2`.  Thus the only
possible local flip in this coordinate fibre is the trivial zero-weight square
state. -/
theorem adjacent_threeSlot_exponentFlip_forces_square_hits
    (p k i n m : ℕ)
    (hp : 6 < p)
    (hi : i < 3)
    (hsq : p ^ 2 ∣ threeSlotValue k i)
    (hn : IsAdjacentThreeSlotSite k n)
    (hm : IsAdjacentThreeSlotSite k m)
    (hflip : localPrimeExponentState p m =
      primeCombExponentFlip (localPrimeExponentState p n)) :
    p ^ 2 ∣ n ∧ p ^ 2 ∣ m := by
  have hn1 : localPrimeExponentState p n ≠ 1 :=
    adjacent_threeSlot_exponentState_ne_one_of_square_hit
      p k i n hp hi hsq hn
  have hm1 : localPrimeExponentState p m ≠ 1 :=
    adjacent_threeSlot_exponentState_ne_one_of_square_hit
      p k i m hp hi hsq hm
  have hn2 : localPrimeExponentState p n = 2 := by
    by_contra hn2
    have hn0 : localPrimeExponentState p n = 0 := by
      apply Fin.ext
      have hlt := (localPrimeExponentState p n).isLt
      have hne1v : (localPrimeExponentState p n).val ≠ 1 := by
        intro hv
        apply hn1
        apply Fin.ext
        exact hv
      have hne2v : (localPrimeExponentState p n).val ≠ 2 := by
        intro hv
        apply hn2
        apply Fin.ext
        exact hv
      omega
    have hmstate : localPrimeExponentState p m = 1 := by
      simpa [hn0, primeCombExponentFlip] using hflip
    exact hm1 hmstate
  have hm2 : localPrimeExponentState p m = 2 := by
    simpa [hn2, primeCombExponentFlip] using hflip
  exact ⟨
    square_hit_of_localPrimeExponentState_eq_two p n hn2,
    square_hit_of_localPrimeExponentState_eq_two p m hm2⟩

/-- Hence any corrected-field pair that realizes the exponent flip entirely
inside the literal current/next-cell support is the zero pair. -/
theorem correctedPrimeWheelSite_pair_eq_zero_of_adjacent_exponentFlip
    (S : Finset ℕ) (upper p k i n m : ℕ)
    (hpS : p ∈ S)
    (hp : 6 < p)
    (hi : i < 3)
    (hsq : p ^ 2 ∣ threeSlotValue k i)
    (hn : IsAdjacentThreeSlotSite k n)
    (hm : IsAdjacentThreeSlotSite k m)
    (hflip : localPrimeExponentState p m =
      primeCombExponentFlip (localPrimeExponentState p n)) :
    correctedPrimeWheelSite S upper n = 0 ∧
      correctedPrimeWheelSite S upper m = 0 := by
  rcases adjacent_threeSlot_exponentFlip_forces_square_hits
      p k i n m hp hi hsq hn hm hflip with ⟨hnsq, hmsq⟩
  exact ⟨
    correctedPrimeWheelSite_eq_zero_of_square_hit
      S upper p n hpS hnsq,
    correctedPrimeWheelSite_eq_zero_of_square_hit
      S upper p m hpS hmsq⟩

/-- A collision label weighted on a literal selected-prime square-hit site has
zero corrected prime-wheel weight. -/
theorem correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (s : TwoPrimeCollisionState)
    (hsquare : p ^ 2 ∣ site s) :
    correctedCollisionSiteWeight S upper site s = 0 := by
  unfold correctedCollisionSiteWeight
  exact correctedPrimeWheelSite_eq_zero_of_square_hit
    S upper p (site s) hpS hsquare

/-- Hence the corrected-field mass of every finite literal collision frontier is
zero, independently of the pairing involution and cutoff. -/
theorem sum_correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (F : Finset TwoPrimeCollisionState)
    (hsquare : ∀ s ∈ F, p ^ 2 ∣ site s) :
    (∑ s ∈ F, correctedCollisionSiteWeight S upper site s) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s hs
  exact correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    S upper p site hpS s (hsquare s hs)

end RHLean.Arithmetic
