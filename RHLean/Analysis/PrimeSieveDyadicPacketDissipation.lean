import Mathlib
import RHLean.Analysis.PrimeSieveDyadicPacketEnvelopeStep

/-!
# Scale-by-scale dissipation for the signed dyadic packet energy

the earlier development identifies cumulative deep packet energy as the correct monotone state:

`D_J = L_J + D_{J+1}`,

where `L_J` is the energy deleted when the common cutoff advances from `J` to
`J+1`.  This module exposes the exact signed content of `L_J`, proves the
companion shallow identity

`S_{J+1} = S_J + L_J`,

and formalizes the two useful analytic dissipation targets.

The strongest target is a uniform level fraction

`kappa * D_J <= L_J`.

A weaker but still sufficient target is a reverse-Carleson estimate with only a
subpolynomial loss

`D_J <= C_epsilon * (x+1)^epsilon * L_J`.

Either target, combined with a critical bound for the shallow energy through the
successor cutoff, controls the complete packet tree.  The proof never separates
`pi` and `Li`: every exact level contribution is a squared norm of the existing
signed sibling residual for the clipped `pi - Li` discrepancy.

No level-fraction or reverse-Carleson estimate is assumed unconditionally in
this file.  Those propositions are the prime-specific analytic frontier.  The
existing exact-activity and Selberg developments provide important arithmetic
structure, but no theorem currently supplies the required lower bound on the
energy released at one packet level.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Exact signed energy on one midpoint-tree level -/

/-- Packet energy carried by exactly one recursive midpoint level on an
arbitrary reciprocal-index interval.  Level zero is the root sibling packet;
positive levels sum the corresponding signed packets over the two children.
Intervals that have already terminated contribute zero. -/
def primeSieveDyadicPacketIntervalLevelEnergy
    (y x : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        ((b - a : ℕ) : ℝ) *
          ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2
      else 0
  | level + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        primeSieveDyadicPacketIntervalLevelEnergy y x level a m +
          primeSieveDyadicPacketIntervalLevelEnergy y x level m b
      else 0

/-- Exact-level signed packet energy is nonnegative. -/
theorem primeSieveDyadicPacketIntervalLevelEnergy_nonneg
    (y x level a b : ℕ) :
    0 ≤ primeSieveDyadicPacketIntervalLevelEnergy y x level a b := by
  induction level generalizing a b with
  | zero =>
      by_cases hsplit : a + 1 < b
      · simp only [primeSieveDyadicPacketIntervalLevelEnergy, hsplit, if_true]
        positivity
      · simp [primeSieveDyadicPacketIntervalLevelEnergy, hsplit]
  | succ level ih =>
      by_cases hsplit : a + 1 < b
      · simp only [primeSieveDyadicPacketIntervalLevelEnergy, hsplit, if_true]
        exact add_nonneg (ih a (dyadicPacketMidpoint a b))
          (ih (dyadicPacketMidpoint a b) b)
      · simp [primeSieveDyadicPacketIntervalLevelEnergy, hsplit]

/-- Refining an interval tree by one additional depth adds exactly the signed
packet energy on the newly exposed level. -/
theorem primeSieveDyadicPacketIntervalTreeEnergy_succ_sub_eq_levelEnergy
    (y x level a b : ℕ) :
    primeSieveDyadicPacketIntervalTreeEnergy y x (level + 1) a b -
        primeSieveDyadicPacketIntervalTreeEnergy y x level a b =
      primeSieveDyadicPacketIntervalLevelEnergy y x level a b := by
  induction level generalizing a b with
  | zero =>
      rw [primeSieveDyadicPacketIntervalTreeEnergy_succ,
        primeSieveDyadicPacketIntervalTreeEnergy_zero]
      by_cases hsplit : a + 1 < b
      · simp [primeSieveDyadicPacketIntervalLevelEnergy, hsplit,
          primeSieveDyadicPacketIntervalTreeEnergy_zero]
      · simp [primeSieveDyadicPacketIntervalLevelEnergy, hsplit]
  | succ level ih =>
      rw [primeSieveDyadicPacketIntervalTreeEnergy_succ,
        primeSieveDyadicPacketIntervalTreeEnergy_succ]
      by_cases hsplit : a + 1 < b
      · simp only [hsplit, if_true]
        rw [primeSieveDyadicPacketIntervalLevelEnergy]
        simp only [hsplit, if_true]
        rw [← ih a (dyadicPacketMidpoint a b),
          ← ih (dyadicPacketMidpoint a b) b]
        ring
      · simp [primeSieveDyadicPacketIntervalLevelEnergy, hsplit]

/-- The global deleted-level energy is exactly the sum of signed packet energies
at tree level `J` over those occupied dyadic blocks that still have that level.
This is the explicit arithmetic object whose lower bound is needed for
scale-by-scale dissipation. -/
theorem primeSieveDyadicPacketLevelEnergy_eq_sum_intervalLevelEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketLevelEnergy y x J =
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        if J < j then
          primeSieveDyadicPacketIntervalLevelEnergy y x J
            (primeSieveDyadicBlockLeft j)
            (primeSieveDyadicBlockRight y x j + 1)
        else 0 := by
  unfold primeSieveDyadicPacketLevelEnergy
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hJ : J < j
  · simp only [hJ, if_true]
    have hmin : min J j = J := min_eq_left hJ.le
    have hminSucc : min (J + 1) j = J + 1 := min_eq_left (by omega)
    rw [hmin, hminSucc]
    unfold primeSieveDyadicPacketTreeBlockEnergy
    exact primeSieveDyadicPacketIntervalTreeEnergy_succ_sub_eq_levelEnergy
      y x J (primeSieveDyadicBlockLeft j)
        (primeSieveDyadicBlockRight y x j + 1)
  · simp only [hJ, if_false]
    have hjJ : j ≤ J := Nat.le_of_not_gt hJ
    have hmin : min J j = j := min_eq_right hjJ
    have hminSucc : min (J + 1) j = j := min_eq_right (by omega)
    rw [hmin, hminSucc]
    ring

/-! ## Exact shallow increment and elementary consequences -/

/-- Shallow packet energy is nonnegative. -/
theorem primeSieveDyadicPacketShallowEnergy_nonneg
    (y x J : ℕ) :
    0 ≤ primeSieveDyadicPacketShallowEnergy y x J := by
  unfold primeSieveDyadicPacketShallowEnergy
  apply Finset.sum_nonneg
  intro j _hj
  unfold primeSieveDyadicPacketTreeBlockEnergy
  have hmono := primeSieveDyadicPacketIntervalTreeEnergy_mono
    y x (r := 0) (s := min J j)
      (a := primeSieveDyadicBlockLeft j)
      (b := primeSieveDyadicBlockRight y x j + 1) (Nat.zero_le _)
  simpa using hmono

/-- Advancing the common cutoff by one adds exactly the deleted level energy to
the shallow side.  Together with the earlier development this gives the two exact identities

`S_{J+1} = S_J + L_J` and `D_J = L_J + D_{J+1}`. -/
theorem primeSieveDyadicPacketShallowEnergy_succ_eq
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x (J + 1) =
      primeSieveDyadicPacketShallowEnergy y x J +
        primeSieveDyadicPacketLevelEnergy y x J := by
  unfold primeSieveDyadicPacketShallowEnergy
    primeSieveDyadicPacketLevelEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Shallow energy is monotone in the cutoff. -/
theorem primeSieveDyadicPacketShallowEnergy_le_succ
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J ≤
      primeSieveDyadicPacketShallowEnergy y x (J + 1) := by
  have hlevel := primeSieveDyadicPacketLevelEnergy_nonneg y x J
  have hinc := primeSieveDyadicPacketShallowEnergy_succ_eq y x J
  linarith

/-- The energy released on level `J` is already contained in the shallow energy
through level `J+1`. -/
theorem primeSieveDyadicPacketLevelEnergy_le_shallow_succ
    (y x J : ℕ) :
    primeSieveDyadicPacketLevelEnergy y x J ≤
      primeSieveDyadicPacketShallowEnergy y x (J + 1) := by
  have hshallow := primeSieveDyadicPacketShallowEnergy_nonneg y x J
  have hinc := primeSieveDyadicPacketShallowEnergy_succ_eq y x J
  linarith

/-! ## Analytic dissipation statements -/

/-- Successor of a shared shallow/deep cutoff selector. -/
def dyadicPacketSuccCutoff (cutoff : DyadicPacketCutoff) : DyadicPacketCutoff :=
  fun k x => cutoff k x + 1

/-- **Strong level-fraction dissipation target.**  A fixed positive fraction of
the entire remaining deep signed packet energy is released on the next level,
uniformly over the primorial blocks used by the RH bridge.

This is a prime-specific analytic statement; it is not proved in this module. -/
def DyadicPacketLevelFractionDissipationStatement
    (cutoff : DyadicPacketCutoff) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧
    ∀ (k x : ℕ),
      2 ≤ k →
      primorialBlockLower k ≤ x →
      x ≤ primorialBlockUpper k →
      κ * primeSieveDyadicPacketDeepEnergy
          (primorialPNTPrimeSieveCutoff k) x (cutoff k x) ≤
        primeSieveDyadicPacketLevelEnergy
          (primorialPNTPrimeSieveCutoff k) x (cutoff k x)

/-- **Subpolynomial reverse-Carleson target.**  The entire remaining deep signed
packet energy is controlled by the energy on the next level with only an
`(x+1)^epsilon` loss.  This is weaker than a uniform positive level fraction,
but is still sufficient because the loss can be absorbed into the epsilon
budget of the critical packet-tree estimate.

This is a prime-specific analytic statement; it is not proved in this module. -/
def DyadicPacketReverseCarlesonBlockBoundedStatement
    (cutoff : DyadicPacketCutoff) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicPacketDeepEnergy
            (primorialPNTPrimeSieveCutoff k) x (cutoff k x) ≤
          C * Real.rpow ((x : ℝ) + 1) ε *
            primeSieveDyadicPacketLevelEnergy
              (primorialPNTPrimeSieveCutoff k) x (cutoff k x)

/-! ## Deterministic closure from one dissipative level -/

/-- A critical shallow estimate through the successor cutoff automatically
controls the shallower original cutoff. -/
theorem dyadicPacketShallowEnergyBlockBounded_of_succ
    (cutoff : DyadicPacketCutoff)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff)) :
    DyadicPacketShallowEnergyBlockBoundedStatement cutoff := by
  intro ε hε
  obtain ⟨C, hC, hSb⟩ := hS ε hε
  refine ⟨C, hC, ?_⟩
  intro k x hk hlow hup
  have hmono := primeSieveDyadicPacketShallowEnergy_le_succ
    (primorialPNTPrimeSieveCutoff k) x (cutoff k x)
  have hs := hSb k x hk hlow hup
  simpa [dyadicPacketSuccCutoff] using hmono.trans hs

/-- A uniform positive level fraction converts a critical shallow estimate at
`J+1` into a critical bound for the deep tail at `J`.  No iteration in tree
depth is required. -/
theorem dyadicPacketDeepTailBlockBounded_of_levelFraction
    (cutoff : DyadicPacketCutoff)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hF : DyadicPacketLevelFractionDissipationStatement cutoff) :
    DyadicPacketDeepTailBlockBoundedStatement cutoff := by
  rcases hF with ⟨κ, hκ, hFrac⟩
  intro ε hε
  obtain ⟨CS, hCS, hSb⟩ := hS ε hε
  refine ⟨CS / κ, div_nonneg hCS hκ.le, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let J := cutoff k x
  have hs :
      primeSieveDyadicPacketShallowEnergy y x (J + 1) ≤
        CS * Real.rpow ((x : ℝ) + 1) (1 + ε) := by
    simpa [y, J, dyadicPacketSuccCutoff] using hSb k x hk hlow hup
  have hfrac :
      κ * primeSieveDyadicPacketDeepEnergy y x J ≤
        primeSieveDyadicPacketLevelEnergy y x J := by
    simpa [y, J] using hFrac k x hk hlow hup
  have hlevel := primeSieveDyadicPacketLevelEnergy_le_shallow_succ y x J
  have hκdeep :
      κ * primeSieveDyadicPacketDeepEnergy y x J ≤
        primeSieveDyadicPacketShallowEnergy y x (J + 1) :=
    hfrac.trans hlevel
  have hdeep :
      primeSieveDyadicPacketDeepEnergy y x J ≤
        primeSieveDyadicPacketShallowEnergy y x (J + 1) / κ := by
    apply (le_div_iff₀ hκ).2
    simpa [mul_comm] using hκdeep
  calc
    primeSieveDyadicPacketDeepEnergy y x J ≤
        primeSieveDyadicPacketShallowEnergy y x (J + 1) / κ := hdeep
    _ ≤ (CS * Real.rpow ((x : ℝ) + 1) (1 + ε)) / κ :=
      div_le_div_of_nonneg_right hs hκ.le
    _ = (CS / κ) * Real.rpow ((x : ℝ) + 1) (1 + ε) := by ring

/-- A subpolynomial reverse-Carleson estimate likewise converts a critical
shallow estimate at `J+1` into the critical deep-tail estimate at `J`.  The
proof splits epsilon equally between the reverse-Carleson loss and the shallow
bound. -/
theorem dyadicPacketDeepTailBlockBounded_of_reverseCarleson
    (cutoff : DyadicPacketCutoff)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hR : DyadicPacketReverseCarlesonBlockBoundedStatement cutoff) :
    DyadicPacketDeepTailBlockBoundedStatement cutoff := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨CS, hCS, hSb⟩ := hS (ε / 2) hhalf
  obtain ⟨CR, hCR, hRb⟩ := hR (ε / 2) hhalf
  refine ⟨CR * CS, mul_nonneg hCR hCS, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let J := cutoff k x
  have hs :
      primeSieveDyadicPacketShallowEnergy y x (J + 1) ≤
        CS * Real.rpow ((x : ℝ) + 1) (1 + ε / 2) := by
    simpa [y, J, dyadicPacketSuccCutoff] using hSb k x hk hlow hup
  have hr :
      primeSieveDyadicPacketDeepEnergy y x J ≤
        CR * Real.rpow ((x : ℝ) + 1) (ε / 2) *
          primeSieveDyadicPacketLevelEnergy y x J := by
    simpa [y, J] using hRb k x hk hlow hup
  have hlevel := primeSieveDyadicPacketLevelEnergy_le_shallow_succ y x J
  have hbase : 0 < (x : ℝ) + 1 := by positivity
  have hfac0 :
      0 ≤ CR * Real.rpow ((x : ℝ) + 1) (ε / 2) :=
    mul_nonneg hCR (Real.rpow_nonneg (by positivity) _)
  have hr' :
      primeSieveDyadicPacketDeepEnergy y x J ≤
        (CR * Real.rpow ((x : ℝ) + 1) (ε / 2)) *
          primeSieveDyadicPacketShallowEnergy y x (J + 1) :=
    hr.trans (mul_le_mul_of_nonneg_left hlevel hfac0)
  calc
    primeSieveDyadicPacketDeepEnergy y x J ≤
        (CR * Real.rpow ((x : ℝ) + 1) (ε / 2)) *
          primeSieveDyadicPacketShallowEnergy y x (J + 1) := hr'
    _ ≤ (CR * Real.rpow ((x : ℝ) + 1) (ε / 2)) *
        (CS * Real.rpow ((x : ℝ) + 1) (1 + ε / 2)) :=
      mul_le_mul_of_nonneg_left hs hfac0
    _ = (CR * CS) *
        (Real.rpow ((x : ℝ) + 1) (ε / 2) *
          Real.rpow ((x : ℝ) + 1) (1 + ε / 2)) := by ring
    _ = (CR * CS) *
        Real.rpow ((x : ℝ) + 1) ((ε / 2) + (1 + ε / 2)) := by
      exact congrArg (fun z : ℝ => (CR * CS) * z)
        (Real.rpow_add hbase (ε / 2) (1 + ε / 2)).symm
    _ = (CR * CS) * Real.rpow ((x : ℝ) + 1) (1 + ε) := by
      have hexp : (ε / 2) + (1 + ε / 2) = 1 + ε := by ring
      rw [hexp]

/-- Strong level-fraction dissipation plus a critical successor-shallow bound
controls the complete recursive packet tree. -/
theorem dyadicPacketTreeEnergyBlockBounded_of_levelFraction
    (cutoff : DyadicPacketCutoff)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hF : DyadicPacketLevelFractionDissipationStatement cutoff) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (k x : ℕ),
          2 ≤ k →
          primorialBlockLower k ≤ x →
          x ≤ primorialBlockUpper k →
          primeSieveDyadicPacketTreeEnergy
              (primorialPNTPrimeSieveCutoff k) x ≤
            C * Real.rpow ((x : ℝ) + 1) (1 + ε) :=
  dyadicPacketTreeEnergyBlockBounded_of_shallow_deep cutoff
    (dyadicPacketShallowEnergyBlockBounded_of_succ cutoff hS)
    (dyadicPacketDeepTailBlockBounded_of_levelFraction cutoff hS hF)

/-- The subpolynomial reverse-Carleson estimate is already sufficient for the
complete critical packet-tree bound. -/
theorem dyadicPacketTreeEnergyBlockBounded_of_reverseCarleson
    (cutoff : DyadicPacketCutoff)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hR : DyadicPacketReverseCarlesonBlockBoundedStatement cutoff) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (k x : ℕ),
          2 ≤ k →
          primorialBlockLower k ≤ x →
          x ≤ primorialBlockUpper k →
          primeSieveDyadicPacketTreeEnergy
              (primorialPNTPrimeSieveCutoff k) x ≤
            C * Real.rpow ((x : ℝ) + 1) (1 + ε) :=
  dyadicPacketTreeEnergyBlockBounded_of_shallow_deep cutoff
    (dyadicPacketShallowEnergyBlockBounded_of_succ cutoff hS)
    (dyadicPacketDeepTailBlockBounded_of_reverseCarleson cutoff hS hR)

/-! ## Terminal RH reductions -/

/-- **Uniform-dissipation terminal reduction.**  Apart from the already-existing
coherent-channel and Möbius-dispersion hypotheses, the packet inputs are now a
critical shallow estimate through one successor cutoff and a uniform positive
level-energy fraction at the preceding cutoff. -/
theorem riemannHypothesis_of_dyadicPacketLevelFractionDissipationAnalyticPackage
    (cutoff : DyadicPacketCutoff)
    (hC : DyadicCoherentChannelRHScale)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hF : DyadicPacketLevelFractionDissipationStatement cutoff)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicPacketShallowDeepAnalyticPackage cutoff hC
  · exact dyadicPacketShallowEnergyBlockBounded_of_succ cutoff hS
  · exact dyadicPacketDeepTailBlockBounded_of_levelFraction cutoff hS hF
  · exact hD

/-- **Reverse-Carleson terminal reduction.**  A subpolynomial reverse level-tail
estimate is enough; no fixed positive fraction and no iteration over all tree
levels is required. -/
theorem riemannHypothesis_of_dyadicPacketReverseCarlesonAnalyticPackage
    (cutoff : DyadicPacketCutoff)
    (hC : DyadicCoherentChannelRHScale)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hR : DyadicPacketReverseCarlesonBlockBoundedStatement cutoff)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicPacketShallowDeepAnalyticPackage cutoff hC
  · exact dyadicPacketShallowEnergyBlockBounded_of_succ cutoff hS
  · exact dyadicPacketDeepTailBlockBounded_of_reverseCarleson cutoff hS hR
  · exact hD

end RHLean.Analysis
