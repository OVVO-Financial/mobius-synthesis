import Mathlib
import RHLean.Analysis.FrozenSquareRunKernel
import RHLean.Proof.LowWheelCanonicalRepeatedMovableCancellation
import RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence

open scoped BigOperators

/-!
# Frozen square runs as changes of the canonical Euler frontier

There are two exact ingredients.

First, for a finite old prime universe `S`, admitting one fresh Euler prime `p`
acts on a *signed window* by

`W_{S ∪ {p}}(A,B) = W_S(A,B) - W_S(floor(A/p), floor(B/p))`.

Thus a new prime does not leave another independent copy of one old parent.  Its
whole additive effect is one compressed predecessor-cube window.  This is the
finite algebraic replacement for the false prime-gap lifetime picture.

Second, the frozen square-run kernel gives the exact signed mass of a forward
subdoubling square run,

`K(a,b) = M(a^2-1) - M((b+1)^2-1)`,

while the canonical low-wheel involution gives at every square endpoint

`M(R^2-1) = M(R) - D_R`,

where `D_R = lowWheelCanonicalDowncrossLedger R` is the one signed adjacent
multiplicative root-downcross frontier.  Combining them gives

`K(a,b) = (M(a)-M(b+1)) + (D_{b+1}-D_a)`.

The lower-scale Mertens gap costs at most the root interval length `b+1-a`.
Consequently the frozen-kernel energy and the energy of the *change* in the
canonical downcross frontier differ by only one root-interval square.  The
resulting difference-only statement is proved equivalent to the existing
frozen-square-run, global Mertens-energy, signed square-run, and primorial
residual criteria.

Finally the already-compiled exact late-parent cancellation is applied at both
run endpoints.  Therefore `D_{b+1}-D_a` is literally the difference of the
canonically oriented Euler first-crossing ledgers.  The RH-scale run seam can be
stated on that genuine ordered population with no loss.

No pointwise bound on `D_R`, prime-gap estimate, PNT input, or asymptotic
estimate is introduced.  The remaining arithmetic problem is to control the
signed predecessor windows created by fresh Euler primes before taking norms.
-/

noncomputable section

namespace RHLean.Proof

/-- **Fresh-prime frozen-window recurrence.**  Adding `p` to the finite prime
universe subtracts exactly the old signed window seen through reciprocal
compression. -/
theorem frozenPrimeUniverseWindowMass_insert
    {S : Finset ℕ} {p A B : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass (insert p S) A B =
      frozenPrimeUniverseWindowMass S A B -
        frozenPrimeUniverseWindowMass S (A / p) (B / p) := by
  have hdiv : A / p ≤ B / p := Nat.div_le_div_right hAB
  rw [frozenPrimeUniverseWindowMass_eq_sub hAB,
    frozenPrimeUniverseWindowMass_eq_sub hAB,
    frozenPrimeUniverseWindowMass_eq_sub hdiv,
    frozenPrimeUniverseMass_insert hp hpPrime,
    frozenPrimeUniverseMass_insert hp hpPrime]
  ring

/-- **Additive fresh-prime derivative.**  The change from the old window to the
new window is the negative compressed predecessor window. -/
theorem frozenPrimeUniverseWindowMass_insert_sub_old
    {S : Finset ℕ} {p A B : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass (insert p S) A B -
        frozenPrimeUniverseWindowMass S A B =
      -frozenPrimeUniverseWindowMass S (A / p) (B / p) := by
  rw [frozenPrimeUniverseWindowMass_insert hp hpPrime hAB]
  ring

/-- Reverse-sign form: deleting the fresh coordinate recovers exactly the
compressed predecessor window. -/
theorem frozenPrimeUniverseWindowMass_old_sub_insert
    {S : Finset ℕ} {p A B : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass S A B -
        frozenPrimeUniverseWindowMass (insert p S) A B =
      frozenPrimeUniverseWindowMass S (A / p) (B / p) := by
  rw [frozenPrimeUniverseWindowMass_insert hp hpPrime hAB]
  ring

/-- A zero compressed predecessor window means the fresh prime has no net
signed effect on the physical window.  This is the exact cancellation test to
apply before any magnitude estimate. -/
theorem frozenPrimeUniverseWindowMass_insert_eq_old_of_predecessor_zero
    {S : Finset ℕ} {p A B : ℕ}
    (hp : p ∉ S) (hpPrime : p.Prime) (hAB : A ≤ B)
    (hzero : frozenPrimeUniverseWindowMass S (A / p) (B / p) = 0) :
    frozenPrimeUniverseWindowMass (insert p S) A B =
      frozenPrimeUniverseWindowMass S A B := by
  rw [frozenPrimeUniverseWindowMass_insert hp hpPrime hAB, hzero]
  ring

end RHLean.Proof

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Change of the canonical adjacent root-downcross frontier across the square
run from root `a` to root `b+1`. -/
def canonicalDowncrossRunDifference (a b : ℕ) : ℂ :=
  lowWheelCanonicalDowncrossLedger (b + 1) -
    lowWheelCanonicalDowncrossLedger a

/-- Change of the already-cancelled, canonically oriented Euler first-crossing
ledger across the same square run. -/
def canonicalOrientedRunDifference (a b : ℕ) : ℂ :=
  LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger
      (b + 1) -
    LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger a

/-- **Late-parent cancellation commutes with square time.**  The complete
canonical frontier change is exactly the change of the genuine oriented Euler
first-crossing population.  No norm or estimate is used. -/
theorem canonicalDowncrossRunDifference_eq_orientedRunDifference
    (a b : ℕ) :
    canonicalDowncrossRunDifference a b =
      canonicalOrientedRunDifference a b := by
  unfold canonicalDowncrossRunDifference canonicalOrientedRunDifference
  rw [LateParentCancellation.downcrossLedger_eq_orientedLedger,
    LateParentCancellation.downcrossLedger_eq_orientedLedger]

/-- **Exact square-run / downcross-difference identity.**  The only term between
the frozen square-run kernel and the change in the canonical downcross frontier
is the ordinary lower-scale Mertens gap across the root interval. -/
theorem frozenSquareRunKernel_eq_mertensGap_add_canonicalDowncrossRunDifference
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    frozenSquareRunKernel a b =
      (mertensSummatory a - mertensSummatory (b + 1)) +
        canonicalDowncrossRunDifference a b := by
  have hk := frozenSquareRunKernel_eq_squarePrefix_sub a b (by omega) hab hsub
  have hA := squarePrefixMertens_eq_mertens_sub_canonicalDowncross a ha
  have hBraw :=
    squarePrefixMertens_eq_mertens_sub_canonicalDowncross (b + 1) (by omega)
  have hB :
      squarePrefixMertens b =
        mertensSummatory (b + 1) - lowWheelCanonicalDowncrossLedger (b + 1) := by
    simpa using hBraw
  rw [hk, hA, hB]
  unfold canonicalDowncrossRunDifference
  ring

/-- Oriented form of the same exact run identity.  All late-parent multiplicity
has disappeared before the energy estimate is even stated. -/
theorem frozenSquareRunKernel_eq_mertensGap_add_canonicalOrientedRunDifference
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    frozenSquareRunKernel a b =
      (mertensSummatory a - mertensSummatory (b + 1)) +
        canonicalOrientedRunDifference a b := by
  rw [← canonicalDowncrossRunDifference_eq_orientedRunDifference]
  exact frozenSquareRunKernel_eq_mertensGap_add_canonicalDowncrossRunDifference
    a b ha hab hsub

/-- Reverse form of the same exact identity. -/
theorem canonicalDowncrossRunDifference_eq_kernel_sub_mertensGap
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    canonicalDowncrossRunDifference a b =
      frozenSquareRunKernel a b -
        (mertensSummatory a - mertensSummatory (b + 1)) := by
  have h :=
    frozenSquareRunKernel_eq_mertensGap_add_canonicalDowncrossRunDifference
      a b ha hab hsub
  rw [h]
  ring

/-- The lower-scale Mertens part of the exact run law costs at most the root
interval length. -/
theorem norm_mertensRunGap_le_rootLength
    (a b : ℕ) (hab : a ≤ b) :
    ‖mertensSummatory a - mertensSummatory (b + 1)‖ ≤
      (((b + 1 - a : ℕ) : ℝ)) := by
  have hgap := norm_mertensSummatory_sub_le a (b + 1) (by omega)
  have hneg :
      mertensSummatory a - mertensSummatory (b + 1) =
        -(mertensSummatory (b + 1) - mertensSummatory a) := by
    ring
  rw [hneg, norm_neg]
  exact hgap

private theorem norm_sq_add_le_two_downcrossBridge (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- One-sided energy comparison: the frozen kernel is controlled by the
frontier change plus one root-interval square. -/
theorem norm_frozenSquareRunKernel_sq_le_rootLength_add_downcrossDifference
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    ‖frozenSquareRunKernel a b‖ ^ 2 ≤
      2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 +
        2 * ‖canonicalDowncrossRunDifference a b‖ ^ 2 := by
  have hid :=
    frozenSquareRunKernel_eq_mertensGap_add_canonicalDowncrossRunDifference
      a b ha hab hsub
  have hadd := norm_sq_add_le_two_downcrossBridge
    (mertensSummatory a - mertensSummatory (b + 1))
    (canonicalDowncrossRunDifference a b)
  have hgap := norm_mertensRunGap_le_rootLength a b hab
  have hgap0 :
      0 ≤ ‖mertensSummatory a - mertensSummatory (b + 1)‖ := norm_nonneg _
  have hlen0 : 0 ≤ (((b + 1 - a : ℕ) : ℝ)) := by positivity
  have hgapSq :
      ‖mertensSummatory a - mertensSummatory (b + 1)‖ ^ 2 ≤
        (((b + 1 - a : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  rw [hid]
  calc
    ‖(mertensSummatory a - mertensSummatory (b + 1)) +
        canonicalDowncrossRunDifference a b‖ ^ 2 ≤
      2 * ‖mertensSummatory a - mertensSummatory (b + 1)‖ ^ 2 +
        2 * ‖canonicalDowncrossRunDifference a b‖ ^ 2 := hadd
    _ ≤ 2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 +
        2 * ‖canonicalDowncrossRunDifference a b‖ ^ 2 := by
      nlinarith

/-- Reverse energy comparison: the change in the canonical frontier is
controlled by the frozen kernel plus the same root-interval square. -/
theorem norm_canonicalDowncrossRunDifference_sq_le_kernel_add_rootLength
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    ‖canonicalDowncrossRunDifference a b‖ ^ 2 ≤
      2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
        2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 := by
  have hid :=
    canonicalDowncrossRunDifference_eq_kernel_sub_mertensGap
      a b ha hab hsub
  have hadd := norm_sq_add_le_two_downcrossBridge
    (frozenSquareRunKernel a b)
    (-(mertensSummatory a - mertensSummatory (b + 1)))
  have hgap := norm_mertensRunGap_le_rootLength a b hab
  have hgap0 :
      0 ≤ ‖mertensSummatory a - mertensSummatory (b + 1)‖ := norm_nonneg _
  have hlen0 : 0 ≤ (((b + 1 - a : ℕ) : ℝ)) := by positivity
  have hgapSq :
      ‖mertensSummatory a - mertensSummatory (b + 1)‖ ^ 2 ≤
        (((b + 1 - a : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  rw [hid, sub_eq_add_neg]
  calc
    ‖frozenSquareRunKernel a b +
        -(mertensSummatory a - mertensSummatory (b + 1))‖ ^ 2 ≤
      2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
        2 * ‖-(mertensSummatory a - mertensSummatory (b + 1))‖ ^ 2 := hadd
    _ = 2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
        2 * ‖mertensSummatory a - mertensSummatory (b + 1)‖ ^ 2 := by
      rw [norm_neg]
    _ ≤ 2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
        2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 := by
      nlinarith

/-- The root-interval square is below the physical endpoint to every exponent
`1+ε`, so it is genuinely lower order at the frozen-run energy scale. -/
private theorem rootLength_sq_le_endpoint_rpow
    (a b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤
      Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
  have hlenNat : b + 1 - a ≤ b + 1 := Nat.sub_le _ _
  have hlen :
      (((b + 1 - a : ℕ) : ℝ)) ≤ (((b + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hlenNat
  have hlen0 : 0 ≤ (((b + 1 - a : ℕ) : ℝ)) := by positivity
  have hroot0 : 0 ≤ (((b + 1 : ℕ) : ℝ)) := by positivity
  have hsq :
      (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤ (((b + 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  have hendpoint :
      (((b + 1 : ℕ) : ℝ)) ^ 2 = ((((b + 1) ^ 2 : ℕ) : ℝ)) := by
    norm_cast
  have hbaseNat : 1 ≤ (b + 1) ^ 2 := by
    nlinarith [Nat.zero_le b]
  have hbase :
      (1 : ℝ) ≤ ((((b + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hbaseNat
  have hrpow := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  calc
    (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤ (((b + 1 : ℕ) : ℝ)) ^ 2 := hsq
    _ = ((((b + 1) ^ 2 : ℕ) : ℝ)) := hendpoint
    _ ≤ Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
      simpa using hrpow

/-- **RH-scale downcross-run seam.**  This asks only for the energy of the
change `D_{b+1}-D_a` on forward subdoubling runs.  It does not ask for any
pointwise bound on the absolute frontier `D_R`. -/
def CanonicalDowncrossRunDifferenceEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, 3 ≤ a → a ≤ b →
        (b + 1) ^ 2 < 2 * a ^ 2 →
        ‖canonicalDowncrossRunDifference a b‖ ^ 2 ≤
          C * Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)

/-- The same RH-scale seam after exact late-parent cancellation.  This is the
version to attack arithmetically: only the ordered Euler first-crossing
population remains. -/
def CanonicalOrientedRunDifferenceEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, 3 ≤ a → a ≤ b →
        (b + 1) ^ 2 < 2 * a ^ 2 →
        ‖canonicalOrientedRunDifference a b‖ ^ 2 ≤
          C * Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)

/-- Exact equivalence of the full-frontier and oriented-frontier run seams. -/
theorem canonicalOrientedRunDifferenceEnergyBounded_iff_downcrossRunDifferenceEnergyBounded :
    CanonicalOrientedRunDifferenceEnergyBoundedStatement ↔
      CanonicalDowncrossRunDifferenceEnergyBoundedStatement := by
  constructor
  · intro hO ε hε
    rcases hO ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro a b ha hab hsub
    rw [canonicalDowncrossRunDifference_eq_orientedRunDifference]
    exact hbound a b ha hab hsub
  · intro hD ε hε
    rcases hD ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro a b ha hab hsub
    rw [← canonicalDowncrossRunDifference_eq_orientedRunDifference]
    exact hbound a b ha hab hsub

/-- The downcross-run energy premise supplies the full frozen square-run energy
criterion.  Backward runs have zero frozen kernel; every forward strict
subdoubling run automatically starts at root at least `3`. -/
theorem frozenSquareRunEnergyBounded_of_canonicalDowncrossRunDifferenceEnergyBounded
    (hD : CanonicalDowncrossRunDifferenceEnergyBoundedStatement) :
    FrozenSquareRunEnergyBoundedStatement := by
  intro ε hε
  rcases hD ε hε with ⟨C, hC, hbound⟩
  refine ⟨2 + 2 * C, by positivity, ?_⟩
  intro a b hsub
  by_cases hab : a ≤ b
  · have hmono : (a + 1) ^ 2 ≤ (b + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have ha3 : 3 ≤ a := by
      by_contra hnot
      have ha2 : a ≤ 2 := by omega
      nlinarith
    have hlocal :=
      norm_frozenSquareRunKernel_sq_le_rootLength_add_downcrossDifference
        a b ha3 hab hsub.le
    have hDab := hbound a b ha3 hab hsub
    have hlen := rootLength_sq_le_endpoint_rpow a b hε
    let P : ℝ := Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)
    have hP0 : 0 ≤ P := by
      dsimp [P]
      exact Real.rpow_nonneg (by positivity) _
    have hDab' : ‖canonicalDowncrossRunDifference a b‖ ^ 2 ≤ C * P := by
      simpa [P] using hDab
    have hlen' : (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤ P := by
      simpa [P] using hlen
    calc
      ‖frozenSquareRunKernel a b‖ ^ 2 ≤
          2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 +
            2 * ‖canonicalDowncrossRunDifference a b‖ ^ 2 := hlocal
      _ ≤ 2 * P + 2 * (C * P) := by nlinarith
      _ = (2 + 2 * C) * P := by ring
      _ = (2 + 2 * C) *
          Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by rfl
  · have hba : b + 1 ≤ a := by omega
    rw [frozenSquareRunKernel_eq_zero_of_succ_le hba]
    have hP0 :
        0 ≤ Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) :=
      Real.rpow_nonneg (by positivity) _
    have hcoef : 0 ≤ 2 + 2 * C := by linarith
    have hrhs :
        0 ≤ (2 + 2 * C) *
          Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) :=
      mul_nonneg hcoef hP0
    simpa using hrhs

/-- Conversely, the frozen square-run criterion controls the energy of every
canonical downcross-frontier change on the same forward subdoubling window. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_of_frozenSquareRunEnergyBounded
    (hF : FrozenSquareRunEnergyBoundedStatement) :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement := by
  intro ε hε
  rcases hF ε hε with ⟨C, hC, hbound⟩
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro a b ha hab hsub
  have hlocal :=
    norm_canonicalDowncrossRunDifference_sq_le_kernel_add_rootLength
      a b ha hab hsub.le
  have hK := hbound a b hsub
  have hlen := rootLength_sq_le_endpoint_rpow a b hε
  let P : ℝ := Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact Real.rpow_nonneg (by positivity) _
  have hK' : ‖frozenSquareRunKernel a b‖ ^ 2 ≤ C * P := by
    simpa [P] using hK
  have hlen' : (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤ P := by
    simpa [P] using hlen
  calc
    ‖canonicalDowncrossRunDifference a b‖ ^ 2 ≤
        2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
          2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 := hlocal
    _ ≤ 2 * (C * P) + 2 * P := by nlinarith
    _ = (2 * C + 2) * P := by ring
    _ = (2 * C + 2) *
        Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by rfl

/-- The reconstructed seam is not merely sufficient: it is exactly the existing
frozen square-run energy criterion. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_iff_frozenSquareRunEnergyBounded :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement ↔
      FrozenSquareRunEnergyBoundedStatement := by
  constructor
  · exact frozenSquareRunEnergyBounded_of_canonicalDowncrossRunDifferenceEnergyBounded
  · exact canonicalDowncrossRunDifferenceEnergyBounded_of_frozenSquareRunEnergyBounded

/-- Hence controlling only changes of the signed canonical root-downcross
frontier is exactly the ordinary global Mertens-energy criterion. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_iff_mertensEnergyBounded :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  exact canonicalDowncrossRunDifferenceEnergyBounded_iff_frozenSquareRunEnergyBounded.trans
    frozenSquareRunEnergyBounded_iff_mertensEnergyBounded

/-- The genuinely ordered Euler first-crossing run seam is therefore itself
exactly the global Mertens-energy criterion. -/
theorem canonicalOrientedRunDifferenceEnergyBounded_iff_mertensEnergyBounded :
    CanonicalOrientedRunDifferenceEnergyBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  exact canonicalOrientedRunDifferenceEnergyBounded_iff_downcrossRunDifferenceEnergyBounded.trans
    canonicalDowncrossRunDifferenceEnergyBounded_iff_mertensEnergyBounded

/-- Equivalent form on the repository's maximal signed square-run criterion. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_iff_squareRunEnergyBounded :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement ↔
      SquareRunEnergyBoundedStatement := by
  exact canonicalDowncrossRunDifferenceEnergyBounded_iff_frozenSquareRunEnergyBounded.trans
    frozenSquareRunEnergyBounded_iff_squareRunEnergyBounded

/-- Equivalent form on the synchronized primorial-wheel residual criterion. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_iff_primorialResidualBounded :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement ↔
      PrimeWheelResidualBoundedStatement RHLean.Arithmetic.primorialWheelFamily := by
  exact canonicalDowncrossRunDifferenceEnergyBounded_iff_frozenSquareRunEnergyBounded.trans
    frozenSquareRunEnergyBounded_iff_primorialResidualBounded

end RHLean.Analysis
