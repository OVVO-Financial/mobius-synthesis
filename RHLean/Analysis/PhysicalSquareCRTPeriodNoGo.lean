import Mathlib
import RHLean.Analysis.PhysicalSquareCRTTransfer

/-!
# The complete-CRT core is empty once the period exceeds the square block

`PhysicalSquareCRTTransfer` partitions the physical zero-free transition
population of one square block into cells lying on complete aligned CRT periods
and the incomplete square-clock boundary:

`physicalT R = crtT P R + boundaryT P R`.

That partition is exact for every `P` and `R`.  This module records the
geometric constraint that decides whether it carries any content.

The square-block transition window `threeSlotSquareBlockTransitionCells R`
consists of `k` with `R^2 <= 4*k+1` and `4*k+7 < (R+1)^2`, so the injection
`k ↦ 4*k+1` lands it inside `Icc (R^2) ((R+1)^2)` and its cardinality is at most
`2*R+2`.  An aligned CRT period has cardinality exactly
`finitePrimeCRTPeriod P = max 1 (prod_{p in P} p^2)`.  A complete period can
therefore sit inside the window only if

`prod_{p in P} p^2 <= 2*R + 2`.

When that fails the complete-period core is *empty*, `crtT P R = 0`, and
`boundaryT P R = physicalT R`: the partition degenerates to
`physicalT = 0 + physicalT` and the CRT interior carries nothing.

The constraint bites immediately, because `FinitePrimeTMixing` only gives strict
Walsh contraction for `p >= 11`.  Taking the selected primes from `11` upward:

```text
P = {11}              period          121   needs R >=            60
P = {11,13}           period       20 449   needs R >=        10 224
P = {11,13,17}        period    5 909 761   needs R >=     2 954 880
P = {11,13,17,19}     period 2 133 423 721  needs R >= 1 066 711 860
```

The period is a product of squares, so it grows doubly exponentially in the
number of selected primes while the window grows linearly in `R`.  The number of
usable primes is therefore `O(log R)`, and the total available Walsh contraction
`prod_{p in P} (1 - 2*s*(p-1)/(p^2-6))` over such a set is a bounded factor, not
a power saving.

This module proves only the emptiness statement and its two immediate
consequences.  It proves no bound on `boundaryT`, no lower bound on the window
cardinality, and asserts nothing about whether the complete-period contribution
would satisfy the finite-prime law if it were nonempty.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- An aligned CRT period has exactly the period's cardinality. -/
theorem card_finitePrimeCRTOrbit (P : Finset ℕ) (k : ℕ) :
    (finitePrimeCRTOrbit P k).card = finitePrimeCRTPeriod P := by
  have hEq : finitePrimeCRTOrbit P k =
      Finset.Ico ((k / finitePrimeCRTPeriod P) * finitePrimeCRTPeriod P)
        ((k / finitePrimeCRTPeriod P + 1) * finitePrimeCRTPeriod P) := rfl
  rw [hEq, Nat.card_Ico]
  have hmul :
      (k / finitePrimeCRTPeriod P + 1) * finitePrimeCRTPeriod P =
        (k / finitePrimeCRTPeriod P) * finitePrimeCRTPeriod P +
          finitePrimeCRTPeriod P := by
    ring
  omega

/-- The square-block transition window holds at most `2*R+2` cells.  The active
sites `4*k+1` of distinct cells are distinct and all lie in `Icc (R^2) ((R+1)^2)`. -/
theorem card_threeSlotSquareBlockTransitionCells_le (R : ℕ) :
    (threeSlotSquareBlockTransitionCells R).card ≤ 2 * R + 2 := by
  classical
  have hmaps : ∀ k ∈ threeSlotSquareBlockTransitionCells R,
      4 * k + 1 ∈ Finset.Icc (R ^ 2) ((R + 1) ^ 2) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨_hrange, hlo, hhi⟩
    exact Finset.mem_Icc.mpr ⟨hlo, by omega⟩
  have hinj : Set.InjOn (fun k => 4 * k + 1)
      (threeSlotSquareBlockTransitionCells R : Set ℕ) := by
    intro a _ha b _hb hab
    have hab' : 4 * a + 1 = 4 * b + 1 := hab
    omega
  have hcard :=
    Finset.card_le_card_of_injOn (fun k => 4 * k + 1) hmaps hinj
  have hIcc : (Finset.Icc (R ^ 2) ((R + 1) ^ 2)).card = 2 * R + 2 := by
    rw [Nat.card_Icc]
    have hexp : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    omega
  omega

/-- **Vacuity threshold.**  If the CRT period exceeds the square-block window,
no complete aligned period fits and the core is empty. -/
theorem physicalSquareCompleteCRTCells_eq_empty_of_period_gt
    (P : Finset ℕ) (R : ℕ) (h : 2 * R + 2 < finitePrimeCRTPeriod P) :
    physicalSquareCompleteCRTCells P R = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hsub := finitePrimeCRTOrbit_subset_squareBlock_of_mem_complete hk
  have hle := Finset.card_le_card hsub
  rw [card_finitePrimeCRTOrbit] at hle
  have hbound := card_threeSlotSquareBlockTransitionCells_le R
  omega

/-- Contrapositive: a nonempty complete-period core forces the CRT period below
the square-block window. -/
theorem finitePrimeCRTPeriod_le_of_complete_nonempty
    {P : Finset ℕ} {R : ℕ}
    (hne : (physicalSquareCompleteCRTCells P R).Nonempty) :
    finitePrimeCRTPeriod P ≤ 2 * R + 2 := by
  by_contra hcon
  have hempty :=
    physicalSquareCompleteCRTCells_eq_empty_of_period_gt P R (by omega)
  rw [hempty] at hne
  exact absurd hne (by simp)

/-- Above the threshold the CRT interior carries no mass at all. -/
theorem crtT_eq_zero_of_period_gt
    (P : Finset ℕ) (R : ℕ) (h : 2 * R + 2 < finitePrimeCRTPeriod P) :
    crtT P R = 0 := by
  unfold crtT
  rw [physicalSquareCompleteCRTCells_eq_empty_of_period_gt P R h]
  simp

/-- Above the threshold the exact partition degenerates: the whole physical mass
is the square-clock boundary. -/
theorem boundaryT_eq_physicalT_of_period_gt
    (P : Finset ℕ) (R : ℕ) (h : 2 * R + 2 < finitePrimeCRTPeriod P) :
    boundaryT P R = physicalT R := by
  have hpart := physicalTransport_is_crtTransport_add_boundary P R
  rw [crtT_eq_zero_of_period_gt P R h] at hpart
  omega

end RHLean.Analysis
