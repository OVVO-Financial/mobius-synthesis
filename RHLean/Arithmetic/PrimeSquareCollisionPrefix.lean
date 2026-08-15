import Mathlib.Data.Int.CardIntervalMod
import RHLean.Arithmetic.PrimeSquareCollisionCRT

noncomputable section

namespace RHLean.Arithmetic

/-!
# Exact finite-prefix ledger for prime-square CRT collision residues

A complete CRT period is not assumed.  Instead, each residue class contributes
exactly its full-period count plus one possible remainder hit.  Summing over a
finite residue set turns the incomplete period into an explicit finite frontier
finset.
-/

/-- Number of representatives below `K` lying in a finite set of residue
classes modulo `Q`. -/
def residuePrefixCount
    (Q K : ℕ) [NeZero Q] (A : Finset (ZMod Q)) : ℕ :=
  ∑ a ∈ A, K.count (· ≡ a.val [MOD Q])

/-- Residue classes whose canonical representative lies in the incomplete
remainder after the last complete period. -/
def residuePrefixFrontier
    (Q K : ℕ) [NeZero Q] (A : Finset (ZMod Q)) : Finset (ZMod Q) :=
  A.filter (fun a => a.val < K % Q)

/-- Exact prefix decomposition for any finite residue set:

`prefix = |A| * floor(K/Q) + frontier`.

There is no asymptotic error term. -/
theorem residuePrefixCount_eq_fullPeriods_add_frontier
    (Q K : ℕ) [NeZero Q] (hQ : 0 < Q)
    (A : Finset (ZMod Q)) :
    residuePrefixCount Q K A =
      A.card * (K / Q) + (residuePrefixFrontier Q K A).card := by
  classical
  unfold residuePrefixCount residuePrefixFrontier
  calc
    (∑ a ∈ A, K.count (· ≡ a.val [MOD Q])) =
        ∑ a ∈ A, (K / Q + if a.val < K % Q then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Nat.count_modEq_card K hQ a.val]
      rw [Nat.mod_eq_of_lt a.val_lt]
    _ = A.card * (K / Q) + (A.filter (fun a => a.val < K % Q)).card := by
      simp [Finset.sum_add_distrib]

/-- The incomplete frontier never has more entries than the full residue set. -/
theorem residuePrefixFrontier_card_le
    (Q K : ℕ) [NeZero Q] (A : Finset (ZMod Q)) :
    (residuePrefixFrontier Q K A).card ≤ A.card := by
  exact Finset.card_filter_le _ _

/-- The positive joint collision modulus for odd primes. -/
theorem collisionModulus_pos
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    0 < (p ^ 2) * (q ^ 2) := by
  exact Nat.mul_pos (pow_pos hp.pos 2) (pow_pos hq.pos 2)

/-- Specialization to the nine complete-period collision residues.  The
physical prefix is exactly nine full-period copies plus a frontier containing
at most nine residue classes. -/
theorem collisionCRT_prefix_eq_nine_fullPeriods_add_frontier
    (p q K : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpgt : 2 < p) (hqgt : 2 < q)
    (hpq : p ≠ q) :
    let Q := (p ^ 2) * (q ^ 2)
    let hcop := primeSquare_coprime_primeSquare p q hp hq hpq
    letI : NeZero Q := ⟨(collisionModulus_pos p q hp hq).ne'⟩
    residuePrefixCount Q K (collisionCRTResidues p q hcop) =
      9 * (K / Q) +
        (residuePrefixFrontier Q K (collisionCRTResidues p q hcop)).card := by
  dsimp only
  letI : NeZero ((p ^ 2) * (q ^ 2)) :=
    ⟨(collisionModulus_pos p q hp hq).ne'⟩
  rw [residuePrefixCount_eq_fullPeriods_add_frontier
    ((p ^ 2) * (q ^ 2)) K (collisionModulus_pos p q hp hq)]
  rw [collisionCRTResidues_card p q hp hq hpgt hqgt hpq]

/-- Consequently the exact remainder ledger for one distinct-prime pair has
cardinality at most nine. -/
theorem collisionCRT_frontier_card_le_nine
    (p q K : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpgt : 2 < p) (hqgt : 2 < q)
    (hpq : p ≠ q) :
    let Q := (p ^ 2) * (q ^ 2)
    let hcop := primeSquare_coprime_primeSquare p q hp hq hpq
    letI : NeZero Q := ⟨(collisionModulus_pos p q hp hq).ne'⟩
    (residuePrefixFrontier Q K (collisionCRTResidues p q hcop)).card ≤ 9 := by
  dsimp only
  letI : NeZero ((p ^ 2) * (q ^ 2)) :=
    ⟨(collisionModulus_pos p q hp hq).ne'⟩
  calc
    (residuePrefixFrontier ((p ^ 2) * (q ^ 2)) K
      (collisionCRTResidues p q
        (primeSquare_coprime_primeSquare p q hp hq hpq))).card ≤
        (collisionCRTResidues p q
          (primeSquare_coprime_primeSquare p q hp hq hpq)).card :=
      residuePrefixFrontier_card_le _ _ _
    _ = 9 := collisionCRTResidues_card p q hp hq hpgt hqgt hpq

end RHLean.Arithmetic
