import Mathlib
import RHLean.Arithmetic.PrimeCombComplementSmoothInversion
import RHLean.Arithmetic.PrimeWheelThreeSlotRecovery
import RHLean.Analysis.PrimeWheelRecoveredMertensCriterion

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-!
# Exact three-slot Mertens degree-one projection

This module turns the empirical three-slot state diagnostic into an exact finite
identity.  For each complete four-cell indexed by `k`, the active state is

```text
(mu(4k+1), mu(4k+2), mu(4k+3)) in {-1,0,1}^3.
```

The three coordinates are encoded by the mixed-radix index

```text
(a+1) * 9 + (b+1) * 3 + (c+1) in {0,...,26}.
```

For the first `K` cells, `threeSlotStateCount K i` is the exact population of
state `i`.  Regrouping the three degree-one Mobius sums by these finite fibers
gives the corresponding Walsh projections.  Their sum is exactly `M(4K)`.

The same degree-one object is then identified with the repository's physical
prime-wheel signed field `R - 2H`: raw seeded mass minus twice the smooth-core
correction.  No transition probability, asymptotic estimate, or probabilistic
independence statement is used here.
-/

/-- Code a Mobius value `-1, 0, 1` as the trit `0, 1, 2`. -/
def moebiusTrit (n : ℕ) : Fin 3 :=
  if μ n = -1 then 0 else if μ n = 0 then 1 else 2

/-- Decode a trit back to its signed value `-1, 0, 1`. -/
def tritSign (t : Fin 3) : ℤ :=
  (t.1 : ℤ) - 1

@[simp] theorem tritSign_moebiusTrit (n : ℕ) :
    tritSign (moebiusTrit n) = μ n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [moebiusTrit, tritSign, h]

/-- Mixed-radix encoding of three trits into the `27 = 3^3` state space. -/
def encodeThreeTrits (a b c : Fin 3) : Fin 27 :=
  ⟨9 * a.1 + 3 * b.1 + c.1, by omega⟩

/-- The exact three-slot Mobius state of the `k`th complete four-cell. -/
def threeSlotState (k : ℕ) : Fin 27 :=
  encodeThreeTrits
    (moebiusTrit (4 * k + 1))
    (moebiusTrit (4 * k + 2))
    (moebiusTrit (4 * k + 3))

/-- Degree-one character selecting the first coordinate. -/
def chiA (i : Fin 27) : ℤ :=
  ((i.1 / 9 : ℕ) : ℤ) - 1

/-- Degree-one character selecting the second coordinate. -/
def chiB (i : Fin 27) : ℤ :=
  ((((i.1 / 3) % 3 : ℕ)) : ℤ) - 1

/-- Degree-one character selecting the third coordinate. -/
def chiC (i : Fin 27) : ℤ :=
  ((i.1 % 3 : ℕ) : ℤ) - 1

@[simp] theorem chiA_encodeThreeTrits (a b c : Fin 3) :
    chiA (encodeThreeTrits a b c) = tritSign a := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [chiA, encodeThreeTrits, tritSign]

@[simp] theorem chiB_encodeThreeTrits (a b c : Fin 3) :
    chiB (encodeThreeTrits a b c) = tritSign b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [chiB, encodeThreeTrits, tritSign]

@[simp] theorem chiC_encodeThreeTrits (a b c : Fin 3) :
    chiC (encodeThreeTrits a b c) = tritSign c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [chiC, encodeThreeTrits, tritSign]

@[simp] theorem chiA_threeSlotState (k : ℕ) :
    chiA (threeSlotState k) = μ (4 * k + 1) := by
  simp [threeSlotState]

@[simp] theorem chiB_threeSlotState (k : ℕ) :
    chiB (threeSlotState k) = μ (4 * k + 2) := by
  simp [threeSlotState]

@[simp] theorem chiC_threeSlotState (k : ℕ) :
    chiC (threeSlotState k) = μ (4 * k + 3) := by
  simp [threeSlotState]

/-- The exact empirical count `C_i(K)` of state `i` among the first `K` cells. -/
def threeSlotStateCount (K : ℕ) (i : Fin 27) : ℕ :=
  ((Finset.range K).filter fun k => threeSlotState k = i).card

/-- Generic finite-fiber regrouping identity behind every degree-one projection. -/
theorem degreeOneProjection_fiberwise
    (K : ℕ) (χ : Fin 27 → ℤ) :
    (∑ i : Fin 27, χ i * (threeSlotStateCount K i : ℤ)) =
      ∑ k ∈ Finset.range K, χ (threeSlotState k) := by
  classical
  have hmaps :
      ∀ k ∈ Finset.range K,
        threeSlotState k ∈ (Finset.univ : Finset (Fin 27)) := by
    intro k hk
    simp
  unfold threeSlotStateCount
  calc
    (∑ i : Fin 27,
        χ i *
          (((Finset.range K).filter fun k => threeSlotState k = i).card : ℤ)) =
      ∑ i ∈ (Finset.univ : Finset (Fin 27)),
        ∑ _k ∈ Finset.range K with threeSlotState _k = i, χ i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [mul_comm]
    _ = ∑ k ∈ Finset.range K, χ (threeSlotState k) := by
      simpa using
        (Finset.sum_fiberwise_of_maps_to'
          (s := Finset.range K)
          (t := (Finset.univ : Finset (Fin 27)))
          (g := threeSlotState)
          hmaps
          χ)

/-- First degree-one Walsh sum `W_a(K)`. -/
def threeSlotWa (K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, μ (4 * k + 1)

/-- Second degree-one Walsh sum `W_b(K)`. -/
def threeSlotWb (K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, μ (4 * k + 2)

/-- Third degree-one Walsh sum `W_c(K)`. -/
def threeSlotWc (K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, μ (4 * k + 3)

/-- Exact first-coordinate projection `W_a(K) = sum_i chi_a(i) C_i(K)`. -/
theorem threeSlotWa_eq_degreeOneProjection (K : ℕ) :
    threeSlotWa K =
      ∑ i : Fin 27, chiA i * (threeSlotStateCount K i : ℤ) := by
  rw [degreeOneProjection_fiberwise (K := K) (χ := chiA)]
  simp [threeSlotWa]

/-- Exact second-coordinate projection `W_b(K) = sum_i chi_b(i) C_i(K)`. -/
theorem threeSlotWb_eq_degreeOneProjection (K : ℕ) :
    threeSlotWb K =
      ∑ i : Fin 27, chiB i * (threeSlotStateCount K i : ℤ) := by
  rw [degreeOneProjection_fiberwise (K := K) (χ := chiB)]
  simp [threeSlotWb]

/-- Exact third-coordinate projection `W_c(K) = sum_i chi_c(i) C_i(K)`. -/
theorem threeSlotWc_eq_degreeOneProjection (K : ℕ) :
    threeSlotWc K =
      ∑ i : Fin 27, chiC i * (threeSlotStateCount K i : ℤ) := by
  rw [degreeOneProjection_fiberwise (K := K) (χ := chiC)]
  simp [threeSlotWc]

/-- At a complete four-cell endpoint, the integer Mertens prefix is exactly the
sum of the three degree-one coordinate sums. -/
theorem moebiusPositivePrefix_four_mul_eq_degreeOne (K : ℕ) :
    moebiusPositivePrefix (4 * K) =
      threeSlotWa K + threeSlotWb K + threeSlotWc K := by
  rw [moebiusPositivePrefix_four_mul_eq_fourSlotCellSum]
  unfold threeSlotWa threeSlotWb threeSlotWc
  calc
    (∑ k ∈ Finset.range K, fourSlotCellSum k) =
        ∑ k ∈ Finset.range K,
          (μ (4 * k + 1) + μ (4 * k + 2) + μ (4 * k + 3)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [fourSlotCellSum, moebius_four_mul_add_four]
            ring
    _ =
        (∑ k ∈ Finset.range K, μ (4 * k + 1)) +
          (∑ k ∈ Finset.range K, μ (4 * k + 2)) +
          (∑ k ∈ Finset.range K, μ (4 * k + 3)) := by
            simp only [Finset.sum_add_distrib]

/-- The same identity in the analytic complex-valued Mertens notation used by
the downstream RH bridge: `M(4K) = W_a(K) + W_b(K) + W_c(K)`. -/
theorem mertensSummatory_four_mul_eq_degreeOne (K : ℕ) :
    mertensSummatory (4 * K) =
      (((threeSlotWa K + threeSlotWb K + threeSlotWc K : ℤ)) : ℂ) := by
  rw [← sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory (4 * K),
    sqrtWheelRecoveredPrefix_eq_moebiusPositivePrefix,
    moebiusPositivePrefix_four_mul_eq_degreeOne]

/-! ## Equivalence with the physical `R - 2H` signed field -/

/-- Canonical raw slot prefix `R_j(K)` for the square-root wheel at cutoff `4K`. -/
def threeSlotR (j K : ℕ) : ℤ :=
  primeWheelRawSlotPrefix (primesUpTo (Nat.sqrt (4 * K))) j K

/-- Canonical smooth-core slot prefix `H_j(K)` for the same physical cutoff. -/
def threeSlotH (j K : ℕ) : ℤ :=
  primeWheelSmoothSlotPrefix
    (primesUpTo (Nat.sqrt (4 * K))) (4 * K) j K

/-- Physical signed field `R_j(K) - 2 H_j(K)`. -/
def threeSlotSignedFieldPrefix (j K : ℕ) : ℤ :=
  threeSlotR j K - 2 * threeSlotH j K

/-- On every active slot, the physical `R - 2H` field is exactly the corresponding
Mobius degree-one sum. -/
theorem threeSlotSignedFieldPrefix_eq_moebius
    (j K : ℕ) (hjpos : 1 ≤ j) (hjle : j ≤ 3) :
    threeSlotSignedFieldPrefix j K =
      ∑ k ∈ Finset.range K, μ (4 * k + j) := by
  have h := primeWheelRecoveredSlotPrefix_eq_moebius
    (primesUpTo (Nat.sqrt (4 * K))) (4 * K) j K
    (by
      intro p hp
      exact prime_of_mem_primesUpTo hp)
    (primesUpTo_sqrtCoverage (4 * K))
    le_rfl hjpos hjle
  simpa [threeSlotSignedFieldPrefix, threeSlotR, threeSlotH,
    primeWheelRecoveredSlotPrefix] using h

@[simp] theorem threeSlotSignedFieldPrefix_one_eq_Wa (K : ℕ) :
    threeSlotSignedFieldPrefix 1 K = threeSlotWa K := by
  simpa [threeSlotWa] using
    threeSlotSignedFieldPrefix_eq_moebius 1 K (by omega) (by omega)

@[simp] theorem threeSlotSignedFieldPrefix_two_eq_Wb (K : ℕ) :
    threeSlotSignedFieldPrefix 2 K = threeSlotWb K := by
  simpa [threeSlotWb] using
    threeSlotSignedFieldPrefix_eq_moebius 2 K (by omega) (by omega)

@[simp] theorem threeSlotSignedFieldPrefix_three_eq_Wc (K : ℕ) :
    threeSlotSignedFieldPrefix 3 K = threeSlotWc K := by
  simpa [threeSlotWc] using
    threeSlotSignedFieldPrefix_eq_moebius 3 K (by omega) (by omega)

/-- Coordinatewise degree-one Walsh mass and physical `R - 2H` mass are the
same exact finite object. -/
theorem degreeOne_eq_signedField (K : ℕ) :
    threeSlotWa K + threeSlotWb K + threeSlotWc K =
      threeSlotSignedFieldPrefix 1 K +
        threeSlotSignedFieldPrefix 2 K +
        threeSlotSignedFieldPrefix 3 K := by
  simp

/-- Final exact bridge: the full three-slot `R - 2H` signed field is the Mertens
value at the complete four-cell endpoint. -/
theorem mertensSummatory_four_mul_eq_signedField (K : ℕ) :
    mertensSummatory (4 * K) =
      (((threeSlotSignedFieldPrefix 1 K +
          threeSlotSignedFieldPrefix 2 K +
          threeSlotSignedFieldPrefix 3 K : ℤ)) : ℂ) := by
  rw [threeSlotSignedFieldPrefix_one_eq_Wa,
    threeSlotSignedFieldPrefix_two_eq_Wb,
    threeSlotSignedFieldPrefix_three_eq_Wc]
  exact mertensSummatory_four_mul_eq_degreeOne K

/-! ## Exact physical transition counts on the nonzero sign sector

The empirical `1/8` diagnostic conditions both ends of a cell-to-cell transition
on the eight states whose three coordinates are all nonzero.  In the canonical
mixed-radix `Fin 27` encoding these are exactly the codes
`0, 2, 6, 8, 18, 20, 24, 26`.  The definitions below use those eight codes
literally, so no probability, Markov hypothesis, or auxiliary Boolean state
space enters the formal object.
-/

/-- A three-slot state lies in the sign sector when none of its coordinates is
zero. -/
def IsThreeSlotNonzeroState (i : Fin 27) : Prop :=
  chiA i ≠ 0 ∧ chiB i ≠ 0 ∧ chiC i ≠ 0

/-- Combined degree-one observable seen by Mertens. -/
def threeSlotDegreeOneValue (i : Fin 27) : ℤ :=
  chiA i + chiB i + chiC i

@[simp] theorem threeSlotDegreeOneValue_threeSlotState (k : ℕ) :
    threeSlotDegreeOneValue (threeSlotState k) =
      μ (4 * k + 1) + μ (4 * k + 2) + μ (4 * k + 3) := by
  simp [threeSlotDegreeOneValue]

/-- Exact current-to-next transition count on an arbitrary finite physical cell
family. -/
def threeSlotTransitionCountOn
    (F : Finset ℕ) (s t : Fin 27) : ℕ :=
  ((F.filter fun k =>
      threeSlotState k = s ∧ threeSlotState (k + 1) = t).card)

/-- Prefix transition count for the first `K` adjacent cell edges. -/
def threeSlotTransitionCount (K : ℕ) (s t : Fin 27) : ℕ :=
  threeSlotTransitionCountOn (Finset.range K) s t

/-- Adjacent complete three-slot cells lying wholly inside the physical square
block `[R^2,(R+1)^2)`.  Both the source active sites and the destination active
sites remain inside the block. -/
def threeSlotSquareBlockTransitionCells (R : ℕ) : Finset ℕ :=
  (Finset.range ((R + 1) ^ 2)).filter fun k =>
    R ^ 2 ≤ 4 * k + 1 ∧ 4 * k + 7 < (R + 1) ^ 2

/-- Exact transition count inside one physical square block. -/
def threeSlotSquareBlockTransitionCount
    (R : ℕ) (s t : Fin 27) : ℕ :=
  threeSlotTransitionCountOn (threeSlotSquareBlockTransitionCells R) s t

/-- Integer row mass after restricting destinations to the eight all-nonzero
state codes. -/
def threeSlotTransitionRowTotalOn
    (F : Finset ℕ) (s : Fin 27) : ℤ :=
  (threeSlotTransitionCountOn F s 0 : ℤ) +
    threeSlotTransitionCountOn F s 2 +
    threeSlotTransitionCountOn F s 6 +
    threeSlotTransitionCountOn F s 8 +
    threeSlotTransitionCountOn F s 18 +
    threeSlotTransitionCountOn F s 20 +
    threeSlotTransitionCountOn F s 24 +
    threeSlotTransitionCountOn F s 26

/-- Integer-centered count corresponding to `8 N(s,t) - N(s,Omega)`.
This is the denominator-free form of centering a row around `1/8`. -/
def threeSlotCenteredTransitionCountOn
    (F : Finset ℕ) (s t : Fin 27) : ℤ :=
  8 * (threeSlotTransitionCountOn F s t : ℤ) -
    threeSlotTransitionRowTotalOn F s

/-- Signed mass of a character on the eight all-nonzero state codes. -/
def threeSlotNonzeroCharacterMass (χ : Fin 27 → ℤ) : ℤ :=
  χ 0 + χ 2 + χ 6 + χ 8 + χ 18 + χ 20 + χ 24 + χ 26

@[simp] theorem threeSlotNonzeroCharacterMass_chiA :
    threeSlotNonzeroCharacterMass chiA = 0 := by
  norm_num [threeSlotNonzeroCharacterMass, chiA]

@[simp] theorem threeSlotNonzeroCharacterMass_chiB :
    threeSlotNonzeroCharacterMass chiB = 0 := by
  norm_num [threeSlotNonzeroCharacterMass, chiB]

@[simp] theorem threeSlotNonzeroCharacterMass_chiC :
    threeSlotNonzeroCharacterMass chiC = 0 := by
  norm_num [threeSlotNonzeroCharacterMass, chiC]

@[simp] theorem threeSlotNonzeroCharacterMass_degreeOne :
    threeSlotNonzeroCharacterMass threeSlotDegreeOneValue = 0 := by
  norm_num [threeSlotNonzeroCharacterMass, threeSlotDegreeOneValue,
    chiA, chiB, chiC]

/-- Degree-one transition moment of one source row, tested only against the
eight all-nonzero destination state codes. -/
def threeSlotTransitionMomentOn
    (F : Finset ℕ) (s : Fin 27) (χ : Fin 27 → ℤ) : ℤ :=
  (threeSlotTransitionCountOn F s 0 : ℤ) * χ 0 +
    threeSlotTransitionCountOn F s 2 * χ 2 +
    threeSlotTransitionCountOn F s 6 * χ 6 +
    threeSlotTransitionCountOn F s 8 * χ 8 +
    threeSlotTransitionCountOn F s 18 * χ 18 +
    threeSlotTransitionCountOn F s 20 * χ 20 +
    threeSlotTransitionCountOn F s 24 * χ 24 +
    threeSlotTransitionCountOn F s 26 * χ 26

/-- Row-centered degree-one transition moment.  Algebraically this is the
contraction of `8 N(s,t) - N(s,Omega)` against `χ`. -/
def threeSlotCenteredTransitionMomentOn
    (F : Finset ℕ) (s : Fin 27) (χ : Fin 27 → ℤ) : ℤ :=
  8 * threeSlotTransitionMomentOn F s χ -
    threeSlotTransitionRowTotalOn F s * threeSlotNonzeroCharacterMass χ

/-- Uniform row-centering disappears exactly on any character with zero sign
sector mass.  Thus only the raw signed transition moment remains. -/
theorem threeSlotCenteredTransitionMomentOn_eq_eight_mul
    (F : Finset ℕ) (s : Fin 27) (χ : Fin 27 → ℤ)
    (hχ : threeSlotNonzeroCharacterMass χ = 0) :
    threeSlotCenteredTransitionMomentOn F s χ =
      8 * threeSlotTransitionMomentOn F s χ := by
  simp [threeSlotCenteredTransitionMomentOn, hχ]

@[simp] theorem threeSlotCenteredTransitionMomentOn_chiA
    (F : Finset ℕ) (s : Fin 27) :
    threeSlotCenteredTransitionMomentOn F s chiA =
      8 * threeSlotTransitionMomentOn F s chiA := by
  exact threeSlotCenteredTransitionMomentOn_eq_eight_mul
    F s chiA threeSlotNonzeroCharacterMass_chiA

@[simp] theorem threeSlotCenteredTransitionMomentOn_chiB
    (F : Finset ℕ) (s : Fin 27) :
    threeSlotCenteredTransitionMomentOn F s chiB =
      8 * threeSlotTransitionMomentOn F s chiB := by
  exact threeSlotCenteredTransitionMomentOn_eq_eight_mul
    F s chiB threeSlotNonzeroCharacterMass_chiB

@[simp] theorem threeSlotCenteredTransitionMomentOn_chiC
    (F : Finset ℕ) (s : Fin 27) :
    threeSlotCenteredTransitionMomentOn F s chiC =
      8 * threeSlotTransitionMomentOn F s chiC := by
  exact threeSlotCenteredTransitionMomentOn_eq_eight_mul
    F s chiC threeSlotNonzeroCharacterMass_chiC

@[simp] theorem threeSlotCenteredTransitionMomentOn_degreeOne
    (F : Finset ℕ) (s : Fin 27) :
    threeSlotCenteredTransitionMomentOn F s threeSlotDegreeOneValue =
      8 * threeSlotTransitionMomentOn F s threeSlotDegreeOneValue := by
  exact threeSlotCenteredTransitionMomentOn_eq_eight_mul
    F s threeSlotDegreeOneValue threeSlotNonzeroCharacterMass_degreeOne

/-- Square-block specialization of the row degree-one transition moment. -/
def threeSlotSquareBlockTransitionMoment
    (R : ℕ) (s : Fin 27) (χ : Fin 27 → ℤ) : ℤ :=
  threeSlotTransitionMomentOn (threeSlotSquareBlockTransitionCells R) s χ

/-- Square-block specialization of the centered row degree-one transition
moment. -/
def threeSlotSquareBlockCenteredTransitionMoment
    (R : ℕ) (s : Fin 27) (χ : Fin 27 → ℤ) : ℤ :=
  threeSlotCenteredTransitionMomentOn
    (threeSlotSquareBlockTransitionCells R) s χ

@[simp] theorem threeSlotSquareBlockCenteredTransitionMoment_degreeOne
    (R : ℕ) (s : Fin 27) :
    threeSlotSquareBlockCenteredTransitionMoment R s threeSlotDegreeOneValue =
      8 * threeSlotSquareBlockTransitionMoment R s threeSlotDegreeOneValue := by
  exact threeSlotCenteredTransitionMomentOn_degreeOne
    (threeSlotSquareBlockTransitionCells R) s

/-- Total degree-one mass carried by transitions whose source and destination
both lie in the eight-state sign sector. -/
def threeSlotTransitionDegreeOneMass (K : ℕ) : ℤ :=
  threeSlotTransitionMomentOn (Finset.range K) 0 threeSlotDegreeOneValue +
    threeSlotTransitionMomentOn (Finset.range K) 2 threeSlotDegreeOneValue +
    threeSlotTransitionMomentOn (Finset.range K) 6 threeSlotDegreeOneValue +
    threeSlotTransitionMomentOn (Finset.range K) 8 threeSlotDegreeOneValue +
    threeSlotTransitionMomentOn (Finset.range K) 18 threeSlotDegreeOneValue +
    threeSlotTransitionMomentOn (Finset.range K) 20 threeSlotDegreeOneValue +
    threeSlotTransitionMomentOn (Finset.range K) 24 threeSlotDegreeOneValue +
    threeSlotTransitionMomentOn (Finset.range K) 26 threeSlotDegreeOneValue

/-- The exact residual left after extracting the all-nonzero transition mass
from the destination degree-one sum.  This retains every zero-coordinate and
conditioning contribution rather than discarding it. -/
def threeSlotTransitionDegreeOneDefect (K : ℕ) : ℤ :=
  (∑ k ∈ Finset.range K,
      threeSlotDegreeOneValue (threeSlotState (k + 1))) -
    threeSlotTransitionDegreeOneMass K

/-- The combined degree-one prefix is the sum of the physical cell observables. -/
theorem threeSlotCombinedDegreeOne_eq_stateSum (K : ℕ) :
    threeSlotWa K + threeSlotWb K + threeSlotWc K =
      ∑ k ∈ Finset.range K,
        threeSlotDegreeOneValue (threeSlotState k) := by
  unfold threeSlotWa threeSlotWb threeSlotWc threeSlotDegreeOneValue
  simp only [chiA_threeSlotState, chiB_threeSlotState,
    chiC_threeSlotState, Finset.sum_add_distrib]

/-- Shift the complete cell prefix into the initial cell plus the exact
current-to-next destination sum. -/
theorem threeSlotStateSum_succ (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1),
        threeSlotDegreeOneValue (threeSlotState k)) =
      threeSlotDegreeOneValue (threeSlotState 0) +
        ∑ k ∈ Finset.range K,
          threeSlotDegreeOneValue (threeSlotState (k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      calc
        (∑ k ∈ Finset.range (K + 1 + 1),
            threeSlotDegreeOneValue (threeSlotState k)) =
          (∑ k ∈ Finset.range (K + 1),
              threeSlotDegreeOneValue (threeSlotState k)) +
            threeSlotDegreeOneValue (threeSlotState (K + 1)) := by
              rw [Finset.sum_range_succ]
        _ =
          (threeSlotDegreeOneValue (threeSlotState 0) +
              ∑ k ∈ Finset.range K,
                threeSlotDegreeOneValue (threeSlotState (k + 1))) +
            threeSlotDegreeOneValue (threeSlotState (K + 1)) := by
              rw [ih]
        _ =
          threeSlotDegreeOneValue (threeSlotState 0) +
            ∑ k ∈ Finset.range (K + 1),
              threeSlotDegreeOneValue (threeSlotState (k + 1)) := by
                rw [Finset.sum_range_succ]
                ring

/-- Exact physical pushforward decomposition.  The Mertens-visible degree-one
prefix is the initial cell plus the conditioned eight-state transition mass plus
one explicit defect containing everything discarded by that conditioning. -/
theorem threeSlotCombinedDegreeOne_succ_eq_transitionMass_add_defect
    (K : ℕ) :
    threeSlotWa (K + 1) + threeSlotWb (K + 1) + threeSlotWc (K + 1) =
      threeSlotDegreeOneValue (threeSlotState 0) +
        threeSlotTransitionDegreeOneMass K +
        threeSlotTransitionDegreeOneDefect K := by
  rw [threeSlotCombinedDegreeOne_eq_stateSum, threeSlotStateSum_succ]
  unfold threeSlotTransitionDegreeOneDefect
  ring

/-- Integer form of the same physical pushforward at a complete four-cell
endpoint. -/
theorem moebiusPositivePrefix_four_mul_succ_eq_transitionMass_add_defect
    (K : ℕ) :
    moebiusPositivePrefix (4 * (K + 1)) =
      threeSlotDegreeOneValue (threeSlotState 0) +
        threeSlotTransitionDegreeOneMass K +
        threeSlotTransitionDegreeOneDefect K := by
  rw [moebiusPositivePrefix_four_mul_eq_degreeOne]
  exact threeSlotCombinedDegreeOne_succ_eq_transitionMass_add_defect K

/-- Analytic form of the exact transition pushforward at the complete four-cell
endpoint.  No estimate on the transition mass or defect is asserted. -/
theorem mertensSummatory_four_mul_succ_eq_transitionMass_add_defect
    (K : ℕ) :
    mertensSummatory (4 * (K + 1)) =
      (((threeSlotDegreeOneValue (threeSlotState 0) +
          threeSlotTransitionDegreeOneMass K +
          threeSlotTransitionDegreeOneDefect K : ℤ)) : ℂ) := by
  rw [mertensSummatory_four_mul_eq_degreeOne,
    threeSlotCombinedDegreeOne_succ_eq_transitionMass_add_defect]

/-! ## Exact prime-coordinate to physical-transition seam

Complement-smooth inversion from the finite prime-coordinate operator is
invertible bookkeeping.  Specializing its old-coordinate set to the empty set
recovers the ordinary Möbius prefix from any finite set of prime coordinates.
Composing that identity with the physical transition pushforward above gives an
exact equality between the prime-coordinate recovery sum and the Mertens-visible
eight-state transition mass plus its explicit conditioning defect.  This is a
scalar pushforward seam only; it asserts no per-row transport matching and no
cancellation estimate.
-/

/-- Empty-old-coordinate specialization of complement-smooth inversion. -/
theorem moebiusPositivePrefix_eq_primeCoordinateComplementSmooth
    (T : Finset ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) (x : ℕ) :
    moebiusPositivePrefix x =
      ∑ n ∈ primeSetSmoothIcc T x,
        finiteDifferenceOperator T moebiusPositivePrefix (x / n) := by
  have h := finiteDifferenceOperator_eq_sum_complementSmooth
    (∅ : Finset ℕ) T (by simp) hT (by simp)
    moebiusPositivePrefix
    (by simp [moebiusPositivePrefix, positivePrefix]) x
  simpa using h

/-- **Exact prime-coordinate to physical-transition pushforward seam.**  For
any finite prime set `T`, the complement-smooth recovery of the degree-one
Mertens prefix at `4(K+1)` is exactly the physical conditioned transition mass
plus the explicit defect.  The two eight-state objects are not identified:
`T` remains a prime-coordinate set, while the physical side remains the
canonical three-slot sign state. -/
theorem primeCoordinateComplementSmooth_eq_physicalTransitionPushforward
    (T : Finset ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) (K : ℕ) :
    (∑ n ∈ primeSetSmoothIcc T (4 * (K + 1)),
        finiteDifferenceOperator T moebiusPositivePrefix
          ((4 * (K + 1)) / n)) =
      threeSlotDegreeOneValue (threeSlotState 0) +
        threeSlotTransitionDegreeOneMass K +
        threeSlotTransitionDegreeOneDefect K := by
  rw [← moebiusPositivePrefix_eq_primeCoordinateComplementSmooth
    T hT (4 * (K + 1))]
  exact moebiusPositivePrefix_four_mul_succ_eq_transitionMass_add_defect K

end RHLean.Analysis
