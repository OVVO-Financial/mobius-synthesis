import Mathlib

/-!
# Finite-prime T-sector mixing

This module isolates the exact finite-prime spectral statement behind the observed
8-state zero-free transition matrix.

The ternary three-coordinate Mobius state has `3^3 = 27` states.  The zero-free
sector `T` has `2^3 = 8` sign states; the complementary zero-containing sector
`A` therefore has `19` states.

For one transition from the three active forms

* `4*k + 1`,
* `2*k + 1`,
* `4*k + 3`

to the same three forms at `k+1`, there are six sign coordinates.  For a prime
`p > 7`, the six roots modulo `p` are distinct.  After conditioning away the six
square-zero residue classes modulo `p^2`, the exact local count law is:

* zero-free total: `p^2 - 6`;
* no sign flip: `p^2 - 6*p`;
* each of the six singleton flips: `p - 1`.

The present file formalizes the algebraic and spectral consequences of that exact
count law.  In particular, a Walsh mode of Hamming weight `s` has eigenvalue

`1 - 2*s*(p-1)/(p^2-6)`.

Every nonconstant mode `1 <= s <= 6` is strictly contracted for `p >= 11`, and
finite prime layers multiply their contractions exactly.

This file deliberately does *not* identify the finite-prime product with the
true Mobius process.  The rough-prime transfer needed for that passage remains a
separate theorem obligation and is not introduced as a premise here.
-/

open scoped BigOperators

namespace RHLean.Analysis

/-- Number of zero-free sign states in one three-coordinate Mobius block. -/
def tStateCount : Nat := 2 ^ 3

/-- Number of ternary states in one three-coordinate Mobius block. -/
def fullStateCount : Nat := 3 ^ 3

/-- Number of zero-containing states, the `A` sector. -/
def aStateCount : Nat := fullStateCount - tStateCount

/-- Number of zero-free source-destination sign transitions. -/
def tTransitionCount : Nat := tStateCount ^ 2

@[simp] theorem tStateCount_eq_eight : tStateCount = 8 := by
  norm_num [tStateCount]

@[simp] theorem fullStateCount_eq_twenty_seven : fullStateCount = 27 := by
  norm_num [fullStateCount]

@[simp] theorem aStateCount_eq_nineteen : aStateCount = 19 := by
  norm_num [aStateCount, fullStateCount, tStateCount]

@[simp] theorem tTransitionCount_eq_sixty_four : tTransitionCount = 64 := by
  norm_num [tTransitionCount, tStateCount]

/-- The three active affine forms in one complete four-slot cell. -/
def tActiveForm (i : Fin 3) (k : Nat) : Nat :=
  if i.1 = 0 then 4 * k + 1
  else if i.1 = 1 then 2 * k + 1
  else 4 * k + 3

@[simp] theorem tActiveForm_zero (k : Nat) :
    tActiveForm (0 : Fin 3) k = 4 * k + 1 := by
  simp [tActiveForm]

@[simp] theorem tActiveForm_one (k : Nat) :
    tActiveForm (1 : Fin 3) k = 2 * k + 1 := by
  simp [tActiveForm]

@[simp] theorem tActiveForm_two (k : Nat) :
    tActiveForm (2 : Fin 3) k = 4 * k + 3 := by
  simp [tActiveForm]

/-- The destination triple is the same affine family at the next cell. -/
def tDestinationForm (i : Fin 3) (k : Nat) : Nat :=
  tActiveForm i (k + 1)

@[simp] theorem tDestinationForm_zero (k : Nat) :
    tDestinationForm (0 : Fin 3) k = 4 * k + 5 := by
  simp [tDestinationForm, tActiveForm]
  omega

@[simp] theorem tDestinationForm_one (k : Nat) :
    tDestinationForm (1 : Fin 3) k = 2 * k + 3 := by
  simp [tDestinationForm, tActiveForm]
  omega

@[simp] theorem tDestinationForm_two (k : Nat) :
    tDestinationForm (2 : Fin 3) k = 4 * k + 7 := by
  simp [tDestinationForm, tActiveForm]
  omega

/-! ## Exact first generic residue certificate at `p = 11` -/

/-- The six affine coordinates in one source-destination `T` transition. -/
def tTransitionForm (i : Fin 6) (k : Nat) : Nat :=
  if i.1 = 0 then 4 * k + 1
  else if i.1 = 1 then 2 * k + 1
  else if i.1 = 2 then 4 * k + 3
  else if i.1 = 3 then 4 * k + 5
  else if i.1 = 4 then 2 * k + 3
  else 4 * k + 7

/-- No coordinate is killed by the square of `p`. -/
def tSquareZeroFreeAt (p k : Nat) : Prop :=
  ∀ i : Fin 6, ¬ p ^ 2 ∣ tTransitionForm i k

/-- No coordinate is even flipped by `p`. -/
def tNoFlipAt (p k : Nat) : Prop :=
  ∀ i : Fin 6, ¬ p ∣ tTransitionForm i k

/-- Exactly the prescribed coordinate is divisible by `p`. -/
def tSingletonFlipAt (p : Nat) (i : Fin 6) (k : Nat) : Prop :=
  p ∣ tTransitionForm i k ∧
    ∀ j : Fin 6, j ≠ i → ¬ p ∣ tTransitionForm j k

/-! Each of the three predicates above is a bounded quantifier over `Fin 6`
composed with `Nat` divisibility, so each is decidable.  Instance synthesis does
not unfold a plain `def`, though, so without these the `Finset.filter`s below
cannot find `DecidablePred` and every `native_decide` certificate fails with
"uses 'sorry' and/or contains errors".  `inferInstanceAs` states the unfolded
form explicitly and keeps the instance definitionally transparent, so the
certificates still evaluate. -/

instance tSquareZeroFreeAt_decidable (p k : Nat) : Decidable (tSquareZeroFreeAt p k) :=
  inferInstanceAs (Decidable (∀ i : Fin 6, ¬ p ^ 2 ∣ tTransitionForm i k))

instance tNoFlipAt_decidable (p k : Nat) : Decidable (tNoFlipAt p k) :=
  inferInstanceAs (Decidable (∀ i : Fin 6, ¬ p ∣ tTransitionForm i k))

instance tSingletonFlipAt_decidable (p : Nat) (i : Fin 6) (k : Nat) :
    Decidable (tSingletonFlipAt p i k) :=
  inferInstanceAs
    (Decidable (p ∣ tTransitionForm i k ∧
      ∀ j : Fin 6, j ≠ i → ¬ p ∣ tTransitionForm j k))

/-- Zero-free residues for the first generic prime layer, represented modulo `11^2`. -/
def elevenZeroFreeResidues : Finset (Fin 121) :=
  Finset.univ.filter fun k => tSquareZeroFreeAt 11 k.1

/-- Residues with no sign flip at the first generic prime layer. -/
def elevenNoFlipResidues : Finset (Fin 121) :=
  Finset.univ.filter fun k =>
    tSquareZeroFreeAt 11 k.1 ∧ tNoFlipAt 11 k.1

/-- Residues with exactly one prescribed sign flip at the first generic prime layer. -/
def elevenSingletonFlipResidues (i : Fin 6) : Finset (Fin 121) :=
  Finset.univ.filter fun k =>
    tSquareZeroFreeAt 11 k.1 ∧ tSingletonFlipAt 11 i k.1

/-- Direct finite certificate: exactly six of the `121` residue classes are square-zero. -/
theorem elevenZeroFreeResidues_card :
    elevenZeroFreeResidues.card = 115 := by
  native_decide

/-- Direct finite certificate: exactly `55` zero-free residues have no sign flip. -/
theorem elevenNoFlipResidues_card :
    elevenNoFlipResidues.card = 55 := by
  native_decide

/-- Direct finite certificate: every one of the six singleton-flip classes has size `10`. -/
theorem elevenSingletonFlipResidues_card (i : Fin 6) :
    (elevenSingletonFlipResidues i).card = 10 := by
  fin_cases i <;> native_decide

/-- The certified classes exhaust the `115` zero-free residues numerically. -/
theorem elevenCertifiedPartition_card :
    elevenNoFlipResidues.card +
        ∑ i : Fin 6, (elevenSingletonFlipResidues i).card = 115 := by
  rw [elevenNoFlipResidues_card]
  simp [elevenSingletonFlipResidues_card]

/-! ## Algebra of the exact one-prime zero-free count law

The three weights below are the exact residue counts obtained once the six affine
root fibres modulo `p` and their unique square-zero lifts modulo `p^2` have been
counted.  This module proves all algebraic and spectral consequences of those
counts.  The repository integration should discharge the finite residue-count
bridge directly from the affine forms above before using this module as the
prime-arithmetic implementation theorem.
-/

/-- Exact zero-free residue weight after removing the six `p^2` roots. -/
def onePrimeZeroFreeWeight (p : Nat) : ℚ :=
  (p : ℚ) ^ 2 - 6

/-- Exact weight of residues on which none of the six coordinates flips. -/
def onePrimeNoFlipWeight (p : Nat) : ℚ :=
  (p : ℚ) ^ 2 - 6 * (p : ℚ)

/-- Exact weight of each one-coordinate flip class. -/
def onePrimeSingleFlipWeight (p : Nat) : ℚ :=
  (p : ℚ) - 1

/-- At `p = 11`, the abstract zero-free weight is the directly certified residue count. -/
theorem onePrimeZeroFreeWeight_eleven_eq_card :
    onePrimeZeroFreeWeight 11 = (elevenZeroFreeResidues.card : ℚ) := by
  rw [elevenZeroFreeResidues_card]
  norm_num [onePrimeZeroFreeWeight]

/-- At `p = 11`, the abstract no-flip weight is the directly certified residue count. -/
theorem onePrimeNoFlipWeight_eleven_eq_card :
    onePrimeNoFlipWeight 11 = (elevenNoFlipResidues.card : ℚ) := by
  rw [elevenNoFlipResidues_card]
  norm_num [onePrimeNoFlipWeight]

/-- At `p = 11`, every singleton-flip weight is the directly certified residue count. -/
theorem onePrimeSingleFlipWeight_eleven_eq_card (i : Fin 6) :
    onePrimeSingleFlipWeight 11 = ((elevenSingletonFlipResidues i).card : ℚ) := by
  rw [elevenSingletonFlipResidues_card]
  norm_num [onePrimeSingleFlipWeight]

/-- The local weights partition the zero-free residue classes exactly. -/
theorem onePrimeWeight_partition (p : Nat) :
    onePrimeNoFlipWeight p + 6 * onePrimeSingleFlipWeight p =
      onePrimeZeroFreeWeight p := by
  unfold onePrimeNoFlipWeight onePrimeSingleFlipWeight onePrimeZeroFreeWeight
  ring

/-- For every prime-sized layer used here, the zero-free denominator is positive. -/
theorem onePrimeZeroFreeWeight_pos {p : Nat} (hp : 11 <= p) :
    0 < onePrimeZeroFreeWeight p := by
  unfold onePrimeZeroFreeWeight
  have hpq : (11 : ℚ) <= (p : ℚ) := by
    exact_mod_cast hp
  nlinarith

/-- The no-flip class has nonnegative weight for `p >= 11`. -/
theorem onePrimeNoFlipWeight_nonneg {p : Nat} (hp : 11 <= p) :
    0 <= onePrimeNoFlipWeight p := by
  unfold onePrimeNoFlipWeight
  have hpq : (11 : ℚ) <= (p : ℚ) := by
    exact_mod_cast hp
  nlinarith

/-- Every singleton-flip class has positive weight for `p >= 11`. -/
theorem onePrimeSingleFlipWeight_pos {p : Nat} (hp : 11 <= p) :
    0 < onePrimeSingleFlipWeight p := by
  unfold onePrimeSingleFlipWeight
  have hpq : (11 : ℚ) <= (p : ℚ) := by
    exact_mod_cast hp
  linarith

/-- Conditional probability of no sign flip in the zero-free six-coordinate law. -/
def onePrimeNoFlipProb (p : Nat) : ℚ :=
  onePrimeNoFlipWeight p / onePrimeZeroFreeWeight p

/-- Conditional probability of any prescribed singleton sign flip. -/
def onePrimeSingleFlipProb (p : Nat) : ℚ :=
  onePrimeSingleFlipWeight p / onePrimeZeroFreeWeight p

/-- The conditional local law has total mass one. -/
theorem onePrimeProbability_partition {p : Nat} (hp : 11 <= p) :
    onePrimeNoFlipProb p + 6 * onePrimeSingleFlipProb p = 1 := by
  have hden : onePrimeZeroFreeWeight p ≠ 0 :=
    ne_of_gt (onePrimeZeroFreeWeight_pos hp)
  unfold onePrimeNoFlipProb onePrimeSingleFlipProb
  calc
    onePrimeNoFlipWeight p / onePrimeZeroFreeWeight p +
          6 * (onePrimeSingleFlipWeight p / onePrimeZeroFreeWeight p)
        = (onePrimeNoFlipWeight p + 6 * onePrimeSingleFlipWeight p) /
            onePrimeZeroFreeWeight p := by ring
    _ = onePrimeZeroFreeWeight p / onePrimeZeroFreeWeight p := by
          rw [onePrimeWeight_partition]
    _ = 1 := div_self hden

/-! ## Walsh spectrum of one prime layer -/

/--
Walsh eigenvalue of a character depending on `s` of the six transition signs.

The no-flip residue contributes `+1`.  Of the six singleton flips, `s` flip a
coordinate seen by the character and contribute `-1`, while `6-s` contribute
`+1`.  Hence the signed singleton coefficient is `6 - 2*s`.
-/
def onePrimeWalshFactor (p s : Nat) : ℚ :=
  onePrimeNoFlipProb p +
    (6 - 2 * (s : ℚ)) * onePrimeSingleFlipProb p

/-- Closed form for the one-prime Walsh factor. -/
theorem onePrimeWalshFactor_eq {p s : Nat} (hp : 11 <= p) :
    onePrimeWalshFactor p s =
      1 - (2 * (s : ℚ) * ((p : ℚ) - 1)) /
        ((p : ℚ) ^ 2 - 6) := by
  have hden : onePrimeZeroFreeWeight p ≠ 0 :=
    ne_of_gt (onePrimeZeroFreeWeight_pos hp)
  unfold onePrimeWalshFactor onePrimeNoFlipProb onePrimeSingleFlipProb
  -- `hden` mentions only `onePrimeZeroFreeWeight`, and `unfold` fails outright
  -- at any location where one of its arguments does not occur, so the goal and
  -- the hypothesis are unfolded separately rather than in one `at hden ⊢`.
  unfold onePrimeNoFlipWeight onePrimeSingleFlipWeight onePrimeZeroFreeWeight
  unfold onePrimeZeroFreeWeight at hden
  field_simp [hden]
  ring

/-- Every nonconstant Walsh mode lies strictly below `1`. -/
theorem onePrimeWalshFactor_lt_one
    {p s : Nat} (hp : 11 <= p) (hs : 1 <= s) :
    onePrimeWalshFactor p s < 1 := by
  rw [onePrimeWalshFactor_eq hp]
  have hden : (0 : ℚ) < (p : ℚ) ^ 2 - 6 := by
    simpa [onePrimeZeroFreeWeight] using onePrimeZeroFreeWeight_pos hp
  have hsq : (0 : ℚ) < (s : ℚ) := by
    exact_mod_cast (show 0 < s by omega)
  have hpq : (1 : ℚ) < (p : ℚ) := by
    have : (11 : ℚ) <= (p : ℚ) := by exact_mod_cast hp
    linarith
  have hnum : (0 : ℚ) < 2 * (s : ℚ) * ((p : ℚ) - 1) := by
    exact mul_pos (mul_pos (by norm_num) hsq) (sub_pos.mpr hpq)
  have hquot :
      (0 : ℚ) <
        (2 * (s : ℚ) * ((p : ℚ) - 1)) /
          ((p : ℚ) ^ 2 - 6) :=
    div_pos hnum hden
  linarith

/-- For weights `1` through `6`, every one-prime Walsh factor lies above `-1`. -/
theorem neg_one_lt_onePrimeWalshFactor
    {p s : Nat} (hp : 11 <= p) (_hs1 : 1 <= s) (hs6 : s <= 6) :
    (-1 : ℚ) < onePrimeWalshFactor p s := by
  rw [onePrimeWalshFactor_eq hp]
  have hpq : (11 : ℚ) <= (p : ℚ) := by
    exact_mod_cast hp
  have hsq : (s : ℚ) <= 6 := by
    exact_mod_cast hs6
  have hpm1 : (0 : ℚ) <= (p : ℚ) - 1 := by
    linarith
  have hlinear :
      (s : ℚ) * ((p : ℚ) - 1) <=
        6 * ((p : ℚ) - 1) :=
    mul_le_mul_of_nonneg_right hsq hpm1
  have hquad :
      6 * ((p : ℚ) - 1) < (p : ℚ) ^ 2 - 6 := by
    nlinarith
  have hden : (0 : ℚ) < (p : ℚ) ^ 2 - 6 := by
    nlinarith
  have hnum :
      2 * (s : ℚ) * ((p : ℚ) - 1) <
        2 * ((p : ℚ) ^ 2 - 6) := by
    nlinarith
  have hquot :
      (2 * (s : ℚ) * ((p : ℚ) - 1)) /
          ((p : ℚ) ^ 2 - 6) < 2 := by
    exact (div_lt_iff₀ hden).2 hnum
  linarith

/-- Strict contraction of every nonconstant six-coordinate Walsh mode. -/
theorem abs_onePrimeWalshFactor_lt_one
    {p s : Nat} (hp : 11 <= p) (hs1 : 1 <= s) (hs6 : s <= 6) :
    |onePrimeWalshFactor p s| < 1 := by
  rw [abs_lt]
  exact ⟨neg_one_lt_onePrimeWalshFactor hp hs1 hs6,
    onePrimeWalshFactor_lt_one hp hs1⟩

/-- At the first generic prime `11`, the six nonconstant factors are all bounded
by the explicit spectral radius `19/23`. -/
theorem abs_onePrimeWalshFactor_eleven_le
    {s : Nat} (hs1 : 1 <= s) (hs6 : s <= 6) :
    |onePrimeWalshFactor 11 s| <= (19 : ℚ) / 23 := by
  interval_cases s <;> norm_num [onePrimeWalshFactor, onePrimeNoFlipProb,
    onePrimeSingleFlipProb, onePrimeNoFlipWeight, onePrimeSingleFlipWeight,
    onePrimeZeroFreeWeight]

/-- Exact first-generic-prime spectral radius. -/
def firstGenericTRadius : ℚ := (19 : ℚ) / 23

@[simp] theorem onePrimeWalshFactor_eleven_one :
    onePrimeWalshFactor 11 1 = (19 : ℚ) / 23 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

@[simp] theorem onePrimeWalshFactor_eleven_two :
    onePrimeWalshFactor 11 2 = (15 : ℚ) / 23 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

@[simp] theorem onePrimeWalshFactor_eleven_three :
    onePrimeWalshFactor 11 3 = (11 : ℚ) / 23 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

@[simp] theorem onePrimeWalshFactor_eleven_four :
    onePrimeWalshFactor 11 4 = (7 : ℚ) / 23 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

@[simp] theorem onePrimeWalshFactor_eleven_five :
    onePrimeWalshFactor 11 5 = (3 : ℚ) / 23 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

@[simp] theorem onePrimeWalshFactor_eleven_six :
    onePrimeWalshFactor 11 6 = -(1 : ℚ) / 23 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

/-- The explicit first-layer radius is strictly contractive. -/
theorem firstGenericTRadius_lt_one :
    firstGenericTRadius < 1 := by
  norm_num [firstGenericTRadius]

/-! ## Finite products of independent prime layers -/

/-- Exact Walsh multiplier for a finite collection of prime layers. -/
def finitePrimeWalshProduct (P : Finset Nat) (s : Nat) : ℚ :=
  ∏ p ∈ P, onePrimeWalshFactor p s

/-- Adjoining one prime multiplies every Walsh mode by its one-prime factor. -/
theorem finitePrimeWalshProduct_insert
    {P : Finset Nat} {a s : Nat} (ha : a ∉ P) :
    finitePrimeWalshProduct (insert a P) s =
      onePrimeWalshFactor a s * finitePrimeWalshProduct P s := by
  simp [finitePrimeWalshProduct, ha]

/-- Disjoint prime families compose by multiplication.  In the arithmetic
application, CRT supplies exactly this disjoint local-factor composition. -/
theorem finitePrimeWalshProduct_union
    {P Q : Finset Nat} (hPQ : Disjoint P Q) (s : Nat) :
    finitePrimeWalshProduct (P ∪ Q) s =
      finitePrimeWalshProduct P s * finitePrimeWalshProduct Q s := by
  unfold finitePrimeWalshProduct
  exact Finset.prod_union hPQ

/-- A finite product of admissible prime layers has absolute value at most one. -/
theorem abs_finitePrimeWalshProduct_le_one
    (P : Finset Nat) {s : Nat}
    (hP : ∀ p ∈ P, 11 <= p) (hs1 : 1 <= s) (hs6 : s <= 6) :
    |finitePrimeWalshProduct P s| <= 1 := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty =>
      intro hP
      simp [finitePrimeWalshProduct]
  | @insert a P ha ih =>
      intro hP
      have ha11 : 11 <= a := hP a (by simp)
      have hPrest : ∀ p ∈ P, 11 <= p := by
        intro p hpP
        exact hP p (by simp [hpP])
      have htail : |finitePrimeWalshProduct P s| <= 1 :=
        ih hPrest
      have hhead : |onePrimeWalshFactor a s| <= 1 :=
        le_of_lt (abs_onePrimeWalshFactor_lt_one ha11 hs1 hs6)
      rw [finitePrimeWalshProduct_insert ha, abs_mul]
      calc
        |onePrimeWalshFactor a s| * |finitePrimeWalshProduct P s|
            <= |onePrimeWalshFactor a s| * 1 := by
              exact mul_le_mul_of_nonneg_left htail (abs_nonneg _)
        _ = |onePrimeWalshFactor a s| := by ring
        _ <= 1 := hhead


/-- If the finite prime set contains `11`, every nonconstant Walsh mode is
uniformly bounded by the concrete radius `19/23`, independently of how many
additional admissible prime layers are present. -/
theorem abs_finitePrimeWalshProduct_le_firstGenericTRadius
    (P : Finset Nat) (h11 : 11 ∈ P) {s : Nat}
    (hP : ∀ p ∈ P, 11 <= p) (hs1 : 1 <= s) (hs6 : s <= 6) :
    |finitePrimeWalshProduct P s| <= firstGenericTRadius := by
  classical
  have hPrest : ∀ p ∈ P.erase 11, 11 <= p := by
    intro p hp
    exact hP p (Finset.mem_erase.mp hp).2
  have htail : |finitePrimeWalshProduct (P.erase 11) s| <= 1 :=
    abs_finitePrimeWalshProduct_le_one (P.erase 11) hPrest hs1 hs6
  have hhead : |onePrimeWalshFactor 11 s| <= firstGenericTRadius := by
    simpa [firstGenericTRadius] using abs_onePrimeWalshFactor_eleven_le hs1 hs6
  have h11erase : 11 ∉ P.erase 11 := Finset.notMem_erase 11 P
  have hprod := finitePrimeWalshProduct_insert (s := s) h11erase
  rw [Finset.insert_erase h11] at hprod
  rw [hprod, abs_mul]
  calc
    |onePrimeWalshFactor 11 s| * |finitePrimeWalshProduct (P.erase 11) s|
        <= |onePrimeWalshFactor 11 s| * 1 := by
          exact mul_le_mul_of_nonneg_left htail (abs_nonneg _)
    _ = |onePrimeWalshFactor 11 s| := by ring
    _ <= firstGenericTRadius := hhead

/-- Every nonempty finite collection of admissible prime layers strictly contracts
all nonconstant six-coordinate Walsh modes. -/
theorem abs_finitePrimeWalshProduct_lt_one
    (P : Finset Nat) (hPnonempty : P.Nonempty) {s : Nat}
    (hP : ∀ p ∈ P, 11 <= p) (hs1 : 1 <= s) (hs6 : s <= 6) :
    |finitePrimeWalshProduct P s| < 1 := by
  classical
  rcases hPnonempty with ⟨a, haP⟩
  have ha11 : 11 <= a := hP a haP
  have hPrest : ∀ p ∈ P.erase a, 11 <= p := by
    intro p hp
    exact hP p (Finset.mem_erase.mp hp).2
  have htail : |finitePrimeWalshProduct (P.erase a) s| <= 1 :=
    abs_finitePrimeWalshProduct_le_one (P.erase a) hPrest hs1 hs6
  have hhead : |onePrimeWalshFactor a s| < 1 :=
    abs_onePrimeWalshFactor_lt_one ha11 hs1 hs6
  have haerase : a ∉ P.erase a := Finset.notMem_erase a P
  have hprod := finitePrimeWalshProduct_insert (s := s) haerase
  rw [Finset.insert_erase haP] at hprod
  rw [hprod, abs_mul]
  calc
    |onePrimeWalshFactor a s| * |finitePrimeWalshProduct (P.erase a) s|
        <= |onePrimeWalshFactor a s| * 1 := by
          exact mul_le_mul_of_nonneg_left htail (abs_nonneg _)
    _ = |onePrimeWalshFactor a s| := by ring
    _ < 1 := hhead

/-- The first seven generic odd prime layers after the exceptional small primes. -/
def firstSevenGenericPrimes : Finset Nat :=
  {11, 13, 17, 19, 23, 29, 31}

/-- A concrete finite numerical contraction: the first seven generic layers cut
every nonconstant six-coordinate Walsh mode by more than one half. -/
theorem firstSevenGenericPrimes_half_contraction
    {s : Nat} (hs1 : 1 <= s) (hs6 : s <= 6) :
    |finitePrimeWalshProduct firstSevenGenericPrimes s| < (1 : ℚ) / 2 := by
  interval_cases s <;> norm_num [firstSevenGenericPrimes, finitePrimeWalshProduct,
    onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

/-- The finite-prime `T` sector is spectrally contractive exactly when every
nonconstant Walsh weight is contracted.  This is a finite numerical property,
not an RH-equivalent criterion. -/
def FinitePrimeTContractive (P : Finset Nat) : Prop :=
  ∀ s : Nat, 1 <= s -> s <= 6 -> |finitePrimeWalshProduct P s| < 1

/-- Every nonempty finite prime set with all primes at least `11` gives a strict
`T`-sector contraction. -/
theorem finitePrimeTContractive_of_ge_eleven
    (P : Finset Nat) (hPnonempty : P.Nonempty)
    (hP : ∀ p ∈ P, 11 <= p) :
    FinitePrimeTContractive P := by
  intro s hs1 hs6
  exact abs_finitePrimeWalshProduct_lt_one P hPnonempty hP hs1 hs6

/-- The singleton first generic layer already gives a literal finite numerical
`T`-sector contraction. -/
theorem finitePrimeTContractive_singleton_eleven :
    FinitePrimeTContractive ({11} : Finset Nat) := by
  apply finitePrimeTContractive_of_ge_eleven
  · simp
  · intro p hp
    simp at hp
    omega

end RHLean.Analysis
