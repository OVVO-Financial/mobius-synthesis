import Mathlib
import RHLean.Proof.DeathShellCardinalityAndCentering

/-!
# Complete Fermat sieve by terminal digit

This module formalizes the corrected, verified terminal-digit sieve for

`N = a^2 - b^2 = (a - b)(a + b)`.

The primitive classification is by `N mod 20`, because this records both the
mod-four parity lane and the decimal terminal digit. The complete tables by
`N mod 10` are then unions of the two compatible mod-twenty lanes.

All finite classifications are proved by evaluation inside Lean. No
asymptotic cardinality claim is made here.
-/

noncomputable section

namespace RHLean.Proof

/-- Parity lane determined by an odd residue modulo twenty. -/
def fermatParityAdmissibleMod20 (n20 a b : ℕ) : Bool :=
  if n20 % 4 = 1 then
    (a % 2 == 1) && (b % 2 == 0)
  else if n20 % 4 = 3 then
    (a % 2 == 0) && (b % 2 == 1)
  else
    false

/-- Decimal terminal digit of `a^2 - b^2`. -/
def fermatDifferenceDigit (a b : ℕ) : ℕ :=
  let ar := a % 10
  let br := b % 10
  let a2 := ar * ar % 10
  let b2 := br * br % 10
  (a2 + 10 - b2) % 10

/-- Exact mod-twenty admissibility predicate for Fermat terminal digits. -/
def fermatDigitAdmissibleMod20 (n20 a b : ℕ) : Bool :=
  fermatParityAdmissibleMod20 (n20 % 20) a b &&
    (fermatDifferenceDigit a b == n20 % 10)

/-- All terminal pairs `(a mod 10, b mod 10)` admitted by a residue modulo
twenty. -/
def fermatDigitPairsMod20 (n20 : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range 10).product (Finset.range 10)).filter fun p =>
    fermatDigitAdmissibleMod20 n20 p.1 p.2

/-- Complete terminal table for a residue modulo ten: the union of its two
compatible mod-twenty lanes. -/
def fermatDigitPairsMod10 (n10 : ℕ) : Finset (ℕ × ℕ) :=
  fermatDigitPairsMod20 (n10 % 10) ∪
    fermatDigitPairsMod20 (n10 % 10 + 10)

/-- `N ≡ 1 (mod 20)`: Lane A, `a` odd and `b` even. -/
theorem fermatDigitPairsMod20_one :
    fermatDigitPairsMod20 1 =
      ([(1, 0), (5, 2), (5, 8), (9, 0)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 3 (mod 20)`: Lane B, `a` even and `b` odd. -/
theorem fermatDigitPairsMod20_three :
    fermatDigitPairsMod20 3 =
      ([(2, 1), (2, 9), (8, 1), (8, 9)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 5 (mod 20)`: the exceptional factor-five part of Lane A. -/
theorem fermatDigitPairsMod20_five :
    fermatDigitPairsMod20 5 =
      ([(1, 4), (1, 6), (3, 2), (3, 8), (5, 0),
        (7, 2), (7, 8), (9, 4), (9, 6)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 7 (mod 20)`: Lane B. -/
theorem fermatDigitPairsMod20_seven :
    fermatDigitPairsMod20 7 =
      ([(4, 3), (4, 7), (6, 3), (6, 7)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 9 (mod 20)`: Lane A. -/
theorem fermatDigitPairsMod20_nine :
    fermatDigitPairsMod20 9 =
      ([(3, 0), (5, 4), (5, 6), (7, 0)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 11 (mod 20)`: Lane B. -/
theorem fermatDigitPairsMod20_eleven :
    fermatDigitPairsMod20 11 =
      ([(0, 3), (0, 7), (4, 5), (6, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 13 (mod 20)`: Lane A. -/
theorem fermatDigitPairsMod20_thirteen :
    fermatDigitPairsMod20 13 =
      ([(3, 4), (3, 6), (7, 4), (7, 6)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 15 (mod 20)`: the exceptional factor-five part of Lane B. -/
theorem fermatDigitPairsMod20_fifteen :
    fermatDigitPairsMod20 15 =
      ([(0, 5), (2, 3), (2, 7), (4, 1), (4, 9),
        (6, 1), (6, 9), (8, 3), (8, 7)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 17 (mod 20)`: Lane A. -/
theorem fermatDigitPairsMod20_seventeen :
    fermatDigitPairsMod20 17 =
      ([(1, 2), (1, 8), (9, 2), (9, 8)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- `N ≡ 19 (mod 20)`: Lane B. -/
theorem fermatDigitPairsMod20_nineteen :
    fermatDigitPairsMod20 19 =
      ([(0, 1), (0, 9), (2, 5), (8, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete `N ≡ 1 (mod 10)` table: eight pairs from residues `1` and `11`
modulo twenty. -/
theorem fermatDigitPairsMod10_one :
    fermatDigitPairsMod10 1 =
      ([(0, 3), (0, 7), (1, 0), (4, 5),
        (5, 2), (5, 8), (6, 5), (9, 0)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete `N ≡ 3 (mod 10)` table. -/
theorem fermatDigitPairsMod10_three :
    fermatDigitPairsMod10 3 =
      ([(2, 1), (2, 9), (3, 4), (3, 6),
        (7, 4), (7, 6), (8, 1), (8, 9)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete exceptional `N ≡ 5 (mod 10)` table: eighteen pairs from residues
`5` and `15` modulo twenty. -/
theorem fermatDigitPairsMod10_five :
    fermatDigitPairsMod10 5 =
      ([(0, 5), (1, 4), (1, 6), (2, 3), (2, 7),
        (3, 2), (3, 8), (4, 1), (4, 9), (5, 0),
        (6, 1), (6, 9), (7, 2), (7, 8), (8, 3),
        (8, 7), (9, 4), (9, 6)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete `N ≡ 7 (mod 10)` table. -/
theorem fermatDigitPairsMod10_seven :
    fermatDigitPairsMod10 7 =
      ([(1, 2), (1, 8), (4, 3), (4, 7),
        (6, 3), (6, 7), (9, 2), (9, 8)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Complete `N ≡ 9 (mod 10)` table. -/
theorem fermatDigitPairsMod10_nine :
    fermatDigitPairsMod10 9 =
      ([(0, 1), (0, 9), (2, 5), (3, 0),
        (5, 4), (5, 6), (7, 0), (8, 5)] : List (ℕ × ℕ)).toFinset := by
  native_decide

/-- Uniform cardinality classification for all residues modulo twenty. -/
theorem fermatDigitPairsMod20_card (r : Fin 20) :
    (fermatDigitPairsMod20 r.val).card =
      if r.val % 2 = 0 then 0 else if r.val % 5 = 0 then 9 else 4 := by
  fin_cases r <;> native_decide

/-- Uniform cardinality classification for all residues modulo ten. -/
theorem fermatDigitPairsMod10_card (r : Fin 10) :
    (fermatDigitPairsMod10 r.val).card =
      if r.val % 2 = 0 then 0 else if r.val = 5 then 18 else 8 := by
  fin_cases r <;> native_decide

/-- Finite mod-four classification for Lane A. -/
theorem fermatParity_one_mod_four
    (a b : Fin 4) :
    ((a.val : ZMod 4) ^ 2 - (b.val : ZMod 4) ^ 2 = 1) →
      a.val % 2 = 1 ∧ b.val % 2 = 0 := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- Finite mod-four classification for Lane B. -/
theorem fermatParity_three_mod_four
    (a b : Fin 4) :
    ((a.val : ZMod 4) ^ 2 - (b.val : ZMod 4) ^ 2 = 3) →
      a.val % 2 = 0 ∧ b.val % 2 = 1 := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- In either odd Fermat lane, `4` divides the doubled product `2ab`. -/
theorem four_dvd_two_mul_of_fermatParity
    {a b : ℕ}
    (h : (Odd a ∧ Even b) ∨ (Even a ∧ Odd b)) :
    4 ∣ 2 * a * b := by
  rcases h with ⟨_, hb⟩ | ⟨ha, _⟩
  · rcases hb with ⟨k, hk⟩
    refine ⟨a * k, ?_⟩
    rw [hk]
    ring
  · rcases ha with ⟨k, hk⟩
    refine ⟨k * b, ?_⟩
    rw [hk]
    ring

/-- Fermat midpoint coordinate for a prime-cofactor pair. -/
def deathFermatA (q c : ℕ) : ℕ :=
  (q + c) / 2

/-- Natural absolute difference, avoiding any dependence on an unavailable
`Nat.absDiff` API. -/
def fermatNatAbsDiff (q c : ℕ) : ℕ :=
  (q - c) + (c - q)

/-- Fermat half-difference coordinate for a prime-cofactor pair. -/
def deathFermatB (q c : ℕ) : ℕ :=
  fermatNatAbsDiff q c / 2

/-- Apply the complete mod-twenty sieve to a death-shell prime-cofactor pair. -/
def deathFermatDigitAdmissible (N q c : ℕ) : Bool :=
  fermatDigitAdmissibleMod20 (N % 20)
    (deathFermatA q c) (deathFermatB q c)

/-- Regression witness from the verified table:
`551 = 24^2 - 5^2 = 19 * 29 ≡ 11 (mod 20)`. -/
theorem fermat_551_regression :
    24 ^ 2 - 5 ^ 2 = 551 ∧
      19 * 29 = 551 ∧
        deathFermatA 29 19 = 24 ∧
          deathFermatB 29 19 = 5 ∧
            (4, 5) ∈ fermatDigitPairsMod20 11 := by
  native_decide

end RHLean.Proof
