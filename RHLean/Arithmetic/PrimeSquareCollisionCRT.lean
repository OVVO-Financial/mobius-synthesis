import Mathlib
import RHLean.Arithmetic.PrimeSquareCollisionKernel

noncomputable section

open scoped Pointwise

namespace RHLean.Arithmetic

/-!
# Complete-period CRT count for prime-square collision transitions

For an odd prime square modulus, each of the three active slots gives one
residue class of the four-cell index.  For distinct primes `p` and `q`, the
Chinese remainder theorem pairs the three current `p^2` collision residues
with the three next-cell `q^2` collision residues.  Hence the complete joint
period modulo `p^2*q^2` contains exactly nine labelled slot-pair residues.

This is a complete-period theorem only.  It does not replace the finite-prefix
analysis required for the physical interval.
-/

/-- The residue solving `4*k + r = 0` modulo `m`, when `4` is a unit modulo
`m`.  The definition is total; coprimality is used only in its lemmas. -/
def collisionRoot (m r : ℕ) : ZMod m :=
  -(r : ZMod m) * (4 : ZMod m)⁻¹

/-- Multiplying a collision root by `4` recovers its defining residue. -/
theorem four_mul_collisionRoot
    (m r : ℕ) (h4 : Nat.Coprime 4 m) :
    (4 : ZMod m) * collisionRoot m r = -(r : ZMod m) := by
  unfold collisionRoot
  have hunit : (4 : ZMod m) * (4 : ZMod m)⁻¹ = 1 := by
    exact ZMod.coe_mul_inv_eq_one 4 h4
  calc
    (4 : ZMod m) * (-(r : ZMod m) * (4 : ZMod m)⁻¹) =
        -(r : ZMod m) * ((4 : ZMod m) * (4 : ZMod m)⁻¹) := by ring
    _ = -(r : ZMod m) := by rw [hunit, mul_one]

/-- Distinct small offsets give distinct collision roots. -/
theorem collisionRoot_injective_of_lt
    (m a b : ℕ) (h4 : Nat.Coprime 4 m)
    (ha : a < m) (hb : b < m)
    (h : collisionRoot m a = collisionRoot m b) :
    a = b := by
  have hneg : (-(a : ZMod m)) = -(b : ZMod m) := by
    calc
      -(a : ZMod m) = (4 : ZMod m) * collisionRoot m a :=
        (four_mul_collisionRoot m a h4).symm
      _ = (4 : ZMod m) * collisionRoot m b := by rw [h]
      _ = -(b : ZMod m) := four_mul_collisionRoot m b h4
  have hcast : (a : ZMod m) = (b : ZMod m) := by
    exact neg_injective hneg
  have hmod := (ZMod.natCast_eq_natCast_iff' a b m).mp hcast
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hmod

/-- Four is coprime to the square of every odd prime. -/
theorem four_coprime_primeSquare
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    Nat.Coprime 4 (p ^ 2) := by
  have hpne : p ≠ 2 := by omega
  have h2p : Nat.Coprime 2 p := (hp.odd_of_ne_two hpne).coprime_two_left
  have hpow : Nat.Coprime (2 ^ 2) (p ^ 2) := h2p.pow 2 2
  norm_num at hpow ⊢
  exact hpow

/-- The three current-cell collision residues modulo `p^2`. -/
def currentCollisionRoots (p : ℕ) : Finset (ZMod (p ^ 2)) :=
  {collisionRoot (p ^ 2) 1,
   collisionRoot (p ^ 2) 2,
   collisionRoot (p ^ 2) 3}

/-- The three next-cell collision residues modulo `q^2`; the active values in
the following cell are `4*k+5`, `4*k+6`, `4*k+7`. -/
def nextCollisionRoots (q : ℕ) : Finset (ZMod (q ^ 2)) :=
  {collisionRoot (q ^ 2) 5,
   collisionRoot (q ^ 2) 6,
   collisionRoot (q ^ 2) 7}

/-- There are exactly three current collision residues for an odd prime. -/
theorem currentCollisionRoots_card
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    (currentCollisionRoots p).card = 3 := by
  have h4 := four_coprime_primeSquare p hp hpgt
  have hm : 9 ≤ p ^ 2 := by nlinarith
  have h12 : collisionRoot (p ^ 2) 1 ≠ collisionRoot (p ^ 2) 2 := by
    intro h
    have heq := collisionRoot_injective_of_lt (p ^ 2) 1 2 h4 (by omega) (by omega) h
    omega
  have h13 : collisionRoot (p ^ 2) 1 ≠ collisionRoot (p ^ 2) 3 := by
    intro h
    have heq := collisionRoot_injective_of_lt (p ^ 2) 1 3 h4 (by omega) (by omega) h
    omega
  have h23 : collisionRoot (p ^ 2) 2 ≠ collisionRoot (p ^ 2) 3 := by
    intro h
    have heq := collisionRoot_injective_of_lt (p ^ 2) 2 3 h4 (by omega) (by omega) h
    omega
  simp [currentCollisionRoots, h12, h13, h23]

/-- There are exactly three next-cell collision residues for an odd prime. -/
theorem nextCollisionRoots_card
    (q : ℕ) (hq : Nat.Prime q) (hqgt : 2 < q) :
    (nextCollisionRoots q).card = 3 := by
  have h4 := four_coprime_primeSquare q hq hqgt
  have hm : 9 ≤ q ^ 2 := by nlinarith
  have h56 : collisionRoot (q ^ 2) 5 ≠ collisionRoot (q ^ 2) 6 := by
    intro h
    have heq := collisionRoot_injective_of_lt (q ^ 2) 5 6 h4 (by omega) (by omega) h
    omega
  have h57 : collisionRoot (q ^ 2) 5 ≠ collisionRoot (q ^ 2) 7 := by
    intro h
    have heq := collisionRoot_injective_of_lt (q ^ 2) 5 7 h4 (by omega) (by omega) h
    omega
  have h67 : collisionRoot (q ^ 2) 6 ≠ collisionRoot (q ^ 2) 7 := by
    intro h
    have heq := collisionRoot_injective_of_lt (q ^ 2) 6 7 h4 (by omega) (by omega) h
    omega
  simp [nextCollisionRoots, h56, h57, h67]

/-- Distinct prime squares are coprime. -/
theorem primeSquare_coprime_primeSquare
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Nat.Coprime (p ^ 2) (q ^ 2) := by
  exact Nat.coprime_pow_primes 2 2 hp hq hpq

/-- The complete-period joint collision residue set: three current `p^2`
roots paired by CRT with three next `q^2` roots. -/
def collisionCRTResidues
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2)) :
    Finset (ZMod ((p ^ 2) * (q ^ 2))) :=
  ((currentCollisionRoots p) ×ˢ (nextCollisionRoots q)).image
    (ZMod.chineseRemainder hcop).symm

/-- **Exact complete-period off-diagonal count.**  For distinct odd primes
`p,q`, exactly nine residues modulo `p^2*q^2` encode a `p^2` collision in the
current three-slot cell and a `q^2` collision in the next three-slot cell. -/
theorem collisionCRTResidues_card
    (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpgt : 2 < p) (hqgt : 2 < q)
    (hpq : p ≠ q) :
    (collisionCRTResidues p q
      (primeSquare_coprime_primeSquare p q hp hq hpq)).card = 9 := by
  let hcop := primeSquare_coprime_primeSquare p q hp hq hpq
  unfold collisionCRTResidues
  rw [Finset.card_image_of_injective _ (ZMod.chineseRemainder hcop).symm.injective]
  rw [Finset.card_product, currentCollisionRoots_card p hp hpgt,
    nextCollisionRoots_card q hq hqgt]

end RHLean.Arithmetic
