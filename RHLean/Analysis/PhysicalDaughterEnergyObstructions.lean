import RHLean.Analysis.PhysicalSquareCRTPeriodNoGo
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux
import RHLean.Proof.SquareRootLowPrimeGoRecursiveDescent

/-!
# Two obstructions to an uncoupled physical daughter energy

The selected `{11}` least-owner `3` deletion field has positive periodic drift
on its actual six-offset carrier.  Its square cannot belong to a uniformly
linear energy envelope.  This is a statement about the selected deletion term,
not the fully reconstructed Mobius observable.

The root-floor column in the Go telescope is also kept distinct from the
single-square-block endpoint object.  Exact finite certificates disprove their
literal identification, even after subtracting the omitted shallow daughters.
No asymptotic lower bound for that column or for Mertens is asserted.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- Computable atom of the actual `{11}`, least-owner `3` selected deletion
channel, using the compiled six-residue characterization of the owner. -/
def elevenThreeSelectedDeletionAtom (k : ℕ) : ℤ :=
  if k % 9 ∈ physicalNineChannelResidues ∧ tSquareZeroFreeAt 11 k then
    selectedDegreeOneProjectionInt ({11} : Finset ℕ) k
  else 0

/-- Unnormalized prefix mass, with all six offsets assembled before squaring. -/
def elevenThreeSelectedDeletionPrefixMass (K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, elevenThreeSelectedDeletionAtom k

/-- This computable prefix is the literal least-owner channel, not a free
choice of complementary field. -/
theorem elevenThreeSelectedDeletionPrefixMass_eq_channel (K : ℕ) :
    elevenThreeSelectedDeletionPrefixMass K =
      ∑ k ∈ outsidePrimeLeastDeletionChannelCells
        ({11} : Finset ℕ) (Finset.range K) 3,
        selectedDegreeOneProjectionInt ({11} : Finset ℕ) k := by
  rw [outsidePrimeLeastDeletionChannelCells_eleven_three]
  have hsets :
      (physicalSquareHitCells K 3).filter (tSquareZeroFreeAt 11) =
        (Finset.range K).filter (fun k =>
          k % 9 ∈ physicalNineChannelResidues ∧ tSquareZeroFreeAt 11 k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range,
      mem_physicalSquareHitCells_iff (by norm_num : Nat.Prime 3),
      physicalSquarePrimeAtEdge_three_iff, and_assoc]
  rw [hsets, Finset.sum_filter]
  rfl

private theorem elevenZeroFree_add_4356 (k : ℕ) :
    tSquareZeroFreeAt 11 (k + 4356) ↔ tSquareZeroFreeAt 11 k := by
  unfold tSquareZeroFreeAt
  apply forall_congr'
  intro i
  fin_cases i <;>
    norm_num [tTransitionForm, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]

private theorem elevenProjection_add_4356 (k : ℕ) :
    selectedDegreeOneProjectionInt ({11} : Finset ℕ) (k + 4356) =
      selectedDegreeOneProjectionInt ({11} : Finset ℕ) k := by
  norm_num [selectedDegreeOneProjectionInt, selectedPrimeSign, tActiveForm,
    Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]

/-- The retained selected field is periodic, including its least-owner mask. -/
theorem elevenThreeSelectedDeletionAtom_add_period (k : ℕ) :
    elevenThreeSelectedDeletionAtom (k + 4356) =
      elevenThreeSelectedDeletionAtom k := by
  have hmod : (k + 4356) % 9 = k % 9 := by omega
  simp only [elevenThreeSelectedDeletionAtom, hmod,
    elevenZeroFree_add_4356, elevenProjection_add_4356]

private theorem elevenThreeSelectedDeletionAtom_add_blocks (m k : ℕ) :
    elevenThreeSelectedDeletionAtom (4356 * m + k) =
      elevenThreeSelectedDeletionAtom k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 4356 * (m + 1) + k = (4356 * m + k) + 4356 by omega,
        elevenThreeSelectedDeletionAtom_add_period, ih]

/-- Exact one-period signed mass, consistent with the certificate in an earlier layer. -/
theorem elevenThreeSelectedDeletionPrefixMass_one_period :
    elevenThreeSelectedDeletionPrefixMass 4356 = 2280 := by
  native_decide

/-- **Positive drift on the actual selected deletion carrier.**  Preserving
the affine field does not by itself make its unnormalized first moment small. -/
theorem elevenThreeSelectedDeletionPrefixMass_periods (m : ℕ) :
    elevenThreeSelectedDeletionPrefixMass (4356 * m) = 2280 * (m : ℤ) := by
  induction m with
  | zero => simp [elevenThreeSelectedDeletionPrefixMass]
  | succ m ih =>
      have htail :
          (∑ k ∈ Finset.range 4356,
            elevenThreeSelectedDeletionAtom (4356 * m + k)) =
              elevenThreeSelectedDeletionPrefixMass 4356 := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact elevenThreeSelectedDeletionAtom_add_blocks m k
      have hsplit :
          elevenThreeSelectedDeletionPrefixMass (4356 * (m + 1)) =
            elevenThreeSelectedDeletionPrefixMass (4356 * m) +
              elevenThreeSelectedDeletionPrefixMass 4356 := by
        unfold elevenThreeSelectedDeletionPrefixMass
        rw [Nat.mul_succ, Finset.sum_range_add]
        exact congrArg (fun z : ℤ =>
          (∑ k ∈ Finset.range (4356 * m), elevenThreeSelectedDeletionAtom k) + z)
          htail
      rw [hsplit, ih, elevenThreeSelectedDeletionPrefixMass_one_period]
      push_cast
      ring

/-- No uniform linear energy bound can dominate these raw selected deletion
prefixes, even when the scale is the larger source prefix rather than a daughter. -/
theorem elevenThreeSelectedDeletionPrefixMass_not_linear_energy :
    ¬ ∃ C : ℚ, ∀ K : ℕ,
      (elevenThreeSelectedDeletionPrefixMass K : ℚ) ^ 2 ≤ C * (K : ℚ) := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max C 0)
  have hCm : C < (m : ℚ) := (le_max_left C 0).trans_lt hm
  have hm0 : (0 : ℚ) < (m : ℚ) := (le_max_right C 0).trans_lt hm
  have h := hC (4356 * m)
  rw [elevenThreeSelectedDeletionPrefixMass_periods] at h
  push_cast at h
  have hpos := mul_pos hm0 (sub_pos.mpr hCm)
  nlinarith [sq_nonneg (m : ℚ)]

/-- In particular, admitting all those raw selected prefixes into an energy
envelope is incompatible with the compiled prime-11 recurrence. -/
theorem elevenThreeSelectedDeletionPrefixMass_no_ElevenQ2_envelope
    {E : ℕ → ℚ} {C : ℚ} (hC : 0 ≤ C)
    (hdom : ∀ K : ℕ,
      (elevenThreeSelectedDeletionPrefixMass K : ℚ) ^ 2 ≤ E K) :
    ¬ ElevenQ2EnergyStep E C := by
  intro hstep
  have hlinear := elevenQ2EnergyStep_implies_linear hC hstep
  apply elevenThreeSelectedDeletionPrefixMass_not_linear_energy
  exact ⟨4 * C, fun K => (hdom K).trans (hlinear K)⟩

/-! ## The exact Go root-floor correction is not a single-block endpoint -/

/-- Computable arithmetic evaluation of a frozen predecessor cube. -/
def frozenPredecessorMobiusEval (q Y : ℕ) : ℤ :=
  ∑ d ∈ Finset.Icc 1 Y,
    if ∀ p ∈ d.primeFactors, p < q then μ d else 0

private theorem largestPrime_lt_iff_all_primeFactors_lt
    {q d : ℕ} (hq : q.Prime) (hd : 1 ≤ d) :
    canonicalLargestPrimeFactor d < q ↔ ∀ p ∈ d.primeFactors, p < q := by
  by_cases hd1 : 1 < d
  · rw [canonicalLargestPrimeFactor, dif_pos hd1]
    constructor
    · intro h p hp
      exact (Finset.le_max' d.primeFactors p hp).trans_lt h
    · intro h
      exact h _ (Finset.max'_mem _ _)
  · have hdEq : d = 1 := by omega
    subst d
    simp [canonicalLargestPrimeFactor, hq.one_lt]

/-- The efficient evaluator is bridged to the actual cube definition before
any finite certificate is used.  Nonsquarefree terms vanish by Mobius itself. -/
theorem frozenPrimeUniverseMass_eq_frozenPredecessorMobiusEval
    {q Y : ℕ} (hq : q.Prime) :
    frozenPrimeUniverseMass (primesUpTo (q - 1)) Y =
      frozenPredecessorMobiusEval q Y := by
  classical
  rw [frozenPrimeUniverseMass_eq_goSmoothCofactorSum hq]
  unfold squareRootLowPrimeGoSmoothCofactors frozenPredecessorMobiusEval
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hiff := largestPrime_lt_iff_all_primeFactors_lt hq
    (Finset.mem_Icc.mp hd).1
  by_cases hsq : Squarefree d
  · simp [hsq, hiff]
  · have hmu : μ d = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    simp [hsq, hmu]

/-- The shallow root column displayed in the exact Go-or-root split. -/
noncomputable def goRootFloorColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    if R ≤ squareRootEndpoint R / (q * q) then 0
    else frozenPrimeUniverseMass (primesUpTo (q - 1)) R

/-- Boundary left when *all* q-square daughters, including shallow ones, are
retained.  This subtracts each omitted daughter from its root-floor term. -/
noncomputable def goRootFloorCorrection (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    if R ≤ squareRootEndpoint R / (q * q) then 0
    else frozenPrimeUniverseMass (primesUpTo (q - 1)) R -
      squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)

/-- Exact conversion of the max-root column into all daughters plus one signed
correction.  No ownerwise norm is used. -/
theorem goRootFlooredColumn_eq_all_daughters_add_correction (R : ℕ) :
    (∑ q ∈ primesUpTo (R - 1),
      frozenPrimeUniverseMass (primesUpTo (q - 1))
        (max R (squareRootEndpoint R / (q * q)))) =
      (∑ q ∈ primesUpTo (R - 1),
        squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)) +
          goRootFloorCorrection R := by
  rw [lowWheelFrozenSecondContactRootFlooredColumn_eq_goOrRoot]
  unfold goRootFloorCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  split_ifs <;> ring

def goRootFloorColumnEval (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    if R ≤ squareRootEndpoint R / (q * q) then 0
    else frozenPredecessorMobiusEval q R

def goRootFloorCorrectionEval (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    if R ≤ squareRootEndpoint R / (q * q) then 0
    else frozenPredecessorMobiusEval q R -
      frozenPredecessorMobiusEval q (squareRootEndpoint R / (q * q))

theorem goRootFloorColumn_eq_eval (R : ℕ) :
    goRootFloorColumn R = goRootFloorColumnEval R := by
  unfold goRootFloorColumn goRootFloorColumnEval
  apply Finset.sum_congr rfl
  intro q hq
  rw [frozenPrimeUniverseMass_eq_frozenPredecessorMobiusEval
    (mem_primesUpTo.mp hq).1]

theorem goRootFloorCorrection_eq_eval (R : ℕ) :
    goRootFloorCorrection R = goRootFloorCorrectionEval R := by
  unfold goRootFloorCorrection goRootFloorCorrectionEval
  apply Finset.sum_congr rfl
  intro q hq
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff,
    frozenPrimeUniverseMass_eq_frozenPredecessorMobiusEval
      (mem_primesUpTo.mp hq).1,
    frozenPrimeUniverseMass_eq_frozenPredecessorMobiusEval
      (mem_primesUpTo.mp hq).1]

/-- Finite certificate on the literal root column. -/
theorem goRootFloorColumn_1000 : goRootFloorColumn 1000 = 7041 := by
  rw [goRootFloorColumn_eq_eval]
  native_decide

/-- Keeping the shallow daughters still leaves a correction larger than the
claimed single-square-block endpoint bound. -/
theorem goRootFloorCorrection_1000 : goRootFloorCorrection 1000 = 7002 := by
  rw [goRootFloorCorrection_eq_eval]
  native_decide

/-- No choice of selected primes makes this global Go root column equal the
existing aggregate endpoint of the single square block at the same root. -/
theorem goRootFloorColumn_ne_squareBlockEndpoint (P : Finset ℕ) :
    (goRootFloorColumn 1000 : ℝ) ≠ squareBlockOutsidePrimeLeastEndpointT P 1000 := by
  intro h
  have hb := abs_squareBlockOutsidePrimeLeastEndpointT_le_linear P 1000
  rw [← h, goRootFloorColumn_1000] at hb
  norm_num at hb

/-- The same obstruction survives after all shallow Go daughters are restored. -/
theorem goRootFloorCorrection_ne_squareBlockEndpoint (P : Finset ℕ) :
    (goRootFloorCorrection 1000 : ℝ) ≠ squareBlockOutsidePrimeLeastEndpointT P 1000 := by
  intro h
  have hb := abs_squareBlockOutsidePrimeLeastEndpointT_le_linear P 1000
  rw [← h, goRootFloorCorrection_1000] at hb
  norm_num at hb

/-! ## The root-floor term must stay coupled to its root anchor -/

/-- The boundary left after restoring every `q^2` daughter is not the raw
root-floor correction from above.  It is the signed coupling of that correction
with the frozen root anchor already present in the saturated physical source
identity. -/
noncomputable def goCompensatedRootBoundary (R : ℕ) : ℤ :=
  1 - frozenPrimeUniverseMass (primesUpTo (R - 1)) (squareRootEndpoint R) -
    goRootFloorCorrection R

/-- **Exact globally compensated daughter decomposition.**  The complete
saturated physical second-contact source ledger is one compensated root
boundary minus *all* literal Go `q^2` daughters.  Thus neither the raw deletion
field nor the raw root-floor correction is an admissible standalone state; both
must remain inside the full signed reconstruction before any norm is taken. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_compensatedRootBoundary_sub_allDaughters
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      (((goCompensatedRootBoundary R -
        ∑ q ∈ primesUpTo (R - 1),
          squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R) : ℤ) : ℂ)) := by
  have hcolumn :
      (∑ q ∈ primesUpTo (R - 1),
        if R ≤ squareRootEndpoint R / (q * q) then
          squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)
        else frozenPrimeUniverseMass (primesUpTo (q - 1)) R) =
        (∑ q ∈ primesUpTo (R - 1),
          squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)) +
            goRootFloorCorrection R := by
    calc
      (∑ q ∈ primesUpTo (R - 1),
        if R ≤ squareRootEndpoint R / (q * q) then
          squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)
        else frozenPrimeUniverseMass (primesUpTo (q - 1)) R) =
          ∑ q ∈ primesUpTo (R - 1),
            frozenPrimeUniverseMass (primesUpTo (q - 1))
              (max R (squareRootEndpoint R / (q * q))) :=
        (lowWheelFrozenSecondContactRootFlooredColumn_eq_goOrRoot R).symm
      _ = (∑ q ∈ primesUpTo (R - 1),
          squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)) +
            goRootFloorCorrection R :=
        goRootFlooredColumn_eq_all_daughters_add_correction R
  rw [lowWheelFrozenSecondContactSource_sum_eq_rootBoundary_sub_goOrRoot R hR,
    hcolumn]
  unfold goCompensatedRootBoundary
  push_cast
  ring

/-! ## The fully reconstructed signed packet is q-square closed

The raw selected deletion prefix above is not an admissible energy state.  The
correct linear state keeps the complete `raw - 2*smooth` Möbius reconstruction,
the prime-11 finite difference, and every already-selected finite-difference
coordinate together.  On that state the `q^2` daughter map is exactly closed:
it is just evaluation of the same packet at the lower cutoff. -/

/-- The recovered prime-11 finite-difference packet commutes with `q^2` descent
pointwise.  No complete period, owner separation, or norm enters this identity. -/
theorem elevenRecoveredMobiusPacket_q2_closed
    (T : Finset ℕ) (q x : ℕ) :
    finiteDifferenceOperator T
        (freshPrimeDifference 11 (shift (q * q) moebiusPositivePrefix)) x =
      finiteDifferenceOperator T
        (freshPrimeDifference 11 moebiusPositivePrefix) (x / (q * q)) := by
  have h := finiteDifferenceOperator_eleven_squareShift_intertwining
    T q moebiusPositivePrefix
  have hx := congrArg (fun f : ℕ → ℤ => f x) h
  simpa [shift] using hx

/-- **Full signed-reconstruction closure.**  Under square-root prime coverage,
start with the actual recovered field `raw - 2*smooth`, apply the prime-11 Euler
difference and any existing finite Möbius difference fibre, and then descend by
`q^2`.  The result is exactly the *same recovered packet species* evaluated at
`x/q^2`.  Thus the linear admissible state can be chosen self-similarly without
admitting the false raw selected prefixes proved above. -/
theorem recoveredPrimeWheelElevenPacket_q2_selfSimilar
    (P T : Finset ℕ) (upper x q : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator T
        (freshPrimeDifference 11
          (shift (q * q) (fun y =>
            primeWheelRawPositivePrefix P y -
              2 * primeWheelSmoothPositivePrefix P upper y))) x =
      finiteDifferenceOperator T
        (freshPrimeDifference 11 (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y))
        (x / (q * q)) := by
  have hchild : x / (q * q) ≤ upper :=
    (Nat.div_le_self x (q * q)).trans hx
  calc
    finiteDifferenceOperator T
        (freshPrimeDifference 11
          (shift (q * q) (fun y =>
            primeWheelRawPositivePrefix P y -
              2 * primeWheelSmoothPositivePrefix P upper y))) x =
      finiteDifferenceOperator T
        (freshPrimeDifference 11 (shift (q * q) moebiusPositivePrefix)) x :=
      finiteDifferenceOperator_recoveredMobius_eleven_q2_intertwining
        P T upper x q hprime hcover hx
    _ = finiteDifferenceOperator T
        (freshPrimeDifference 11 moebiusPositivePrefix) (x / (q * q)) :=
      elevenRecoveredMobiusPacket_q2_closed T q x
    _ = finiteDifferenceOperator T
        (freshPrimeDifference 11 (fun y =>
          primeWheelRawPositivePrefix P y -
            2 * primeWheelSmoothPositivePrefix P upper y))
        (x / (q * q)) := by
      symm
      exact finiteDifferenceOperator_primeWheelRecovery_freshDifference
        P T upper (x / (q * q)) 11 hprime hcover hchild

end RHLean.Analysis