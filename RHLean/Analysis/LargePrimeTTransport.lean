import Mathlib
import RHLean.Analysis.FinitePrimeTMixing

/-!
# Large-prime transport on the zero-free T sector

This module supplies the exact arithmetic bridge from the square-root one-large-prime
architecture to the finite `T`-state mixing layer.

The key correction is explicit: `q > R` does not make a product zero-free by itself.
A small cofactor may already contain a prime square.  What the large prime does prove is
stronger and cleaner:

* if `1 <= c < R < q` and `q` is prime, then `q ∤ c`;
* hence `q` is coprime to `c`;
* therefore `mu(q*c) = -mu(c)` with no squarefree hypothesis on `c`;
* consequently `mu(q*c) = 0` iff `mu(c) = 0`.

So the large prime creates no new zero and removes no inherited zero.  On the surviving
zero-free sector it is a pure sign flip.

The second half formalizes the finite eight-state consequence.  A fixed coordinatewise
sign-flip mask is a permutation of the eight sign states, so pulling a transition kernel
through such a transport preserves an exactly uniform kernel and preserves entrywise
uniform-deviation magnitudes.  For the exactly uniform kernel, the three-active-slot
observable has mean zero, second moment three, every positive-lag Markov covariance
vanishes, and the corresponding Green--Kubo second moment is exactly `3*K`.

Important scope boundary: this file does not identify every zero-free Mobius cell with a
canonical large-prime transport cell.  It proves the transfer exactly on the arithmetic
population satisfying the one-large-prime inequalities coordinatewise.
-/

open scoped BigOperators

namespace RHLean.Analysis

/-! ## Exact one-large-prime arithmetic -/

/-- Native square-root transport data for one cofactor/prime pair. -/
structure LargePrimeTransportData (R c q : Nat) : Prop where
  c_pos : 1 <= c
  c_lt_cutoff : c < R
  q_prime : q.Prime
  cutoff_lt_q : R < q

namespace LargePrimeTransportData

/-- A prime above the cutoff cannot divide a positive cofactor below the cutoff. -/
theorem q_not_dvd_c {R c q : Nat} (h : LargePrimeTransportData R c q) :
    ¬ q ∣ c := by
  intro hqc
  have hq_le_c : q <= c := Nat.le_of_dvd h.c_pos hqc
  have hc_lt_q : c < q := lt_trans h.c_lt_cutoff h.cutoff_lt_q
  exact (Nat.not_le_of_gt hc_lt_q) hq_le_c

/-- The large prime is coprime to its small cofactor. -/
theorem coprime {R c q : Nat} (h : LargePrimeTransportData R c q) :
    Nat.Coprime q c := by
  exact h.q_prime.coprime_iff_not_dvd.mpr h.q_not_dvd_c

/-- Exact Mobius transport law.  No squarefree assumption on the cofactor is needed. -/
theorem moebius_mul_eq_neg {R c q : Nat} (h : LargePrimeTransportData R c q) :
    (ArithmeticFunction.moebius (q * c) : Int) =
      -(ArithmeticFunction.moebius c : Int) := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h.coprime]
  rw [ArithmeticFunction.moebius_apply_prime h.q_prime]
  ring

/-- The large prime creates no new Mobius zero and removes no inherited one. -/
theorem moebius_mul_eq_zero_iff {R c q : Nat} (h : LargePrimeTransportData R c q) :
    (ArithmeticFunction.moebius (q * c) : Int) = 0 ↔
      (ArithmeticFunction.moebius c : Int) = 0 := by
  rw [h.moebius_mul_eq_neg]
  simp

/-- A surviving cofactor stays in the zero-free sector after adjoining the large prime. -/
theorem moebius_mul_ne_zero {R c q : Nat} (h : LargePrimeTransportData R c q)
    (hc : (ArithmeticFunction.moebius c : Int) ≠ 0) :
    (ArithmeticFunction.moebius (q * c) : Int) ≠ 0 := by
  intro hz
  exact hc (h.moebius_mul_eq_zero_iff.mp hz)

/-- An inherited zero remains zero after adjoining the large prime. -/
theorem moebius_mul_eq_zero {R c q : Nat} (h : LargePrimeTransportData R c q)
    (hc : (ArithmeticFunction.moebius c : Int) = 0) :
    (ArithmeticFunction.moebius (q * c) : Int) = 0 := by
  exact h.moebius_mul_eq_zero_iff.mpr hc

end LargePrimeTransportData

/-- Six-coordinate source/destination transport data for one `T` transition. -/
structure LargePrimeTTransitionData (R : Nat) where
  cofactor : Fin 6 -> Nat
  largePrime : Fin 6 -> Nat
  admissible : ∀ i, LargePrimeTransportData R (cofactor i) (largePrime i)

/-- Every coordinate of a large-prime transition is the sign reversal of its cofactor. -/
theorem largePrimeTTransition_moebius_flip
    {R : Nat} (D : LargePrimeTTransitionData R) (i : Fin 6) :
    (ArithmeticFunction.moebius (D.largePrime i * D.cofactor i) : Int) =
      -(ArithmeticFunction.moebius (D.cofactor i) : Int) := by
  exact (D.admissible i).moebius_mul_eq_neg

/-- Zero status is inherited coordinatewise from the six small cofactors. -/
theorem largePrimeTTransition_zero_iff
    {R : Nat} (D : LargePrimeTTransitionData R) (i : Fin 6) :
    (ArithmeticFunction.moebius (D.largePrime i * D.cofactor i) : Int) = 0 ↔
      (ArithmeticFunction.moebius (D.cofactor i) : Int) = 0 := by
  exact (D.admissible i).moebius_mul_eq_zero_iff

/-- The six-coordinate transition is zero-free exactly when all six cofactors are zero-free. -/
theorem largePrimeTTransition_all_ne_zero_iff
    {R : Nat} (D : LargePrimeTTransitionData R) :
    (∀ i : Fin 6,
      (ArithmeticFunction.moebius (D.largePrime i * D.cofactor i) : Int) ≠ 0) ↔
      (∀ i : Fin 6, (ArithmeticFunction.moebius (D.cofactor i) : Int) ≠ 0) := by
  constructor
  · intro h i hc
    exact h i ((D.admissible i).moebius_mul_eq_zero_iff.mpr hc)
  · intro h i hp
    exact h i ((D.admissible i).moebius_mul_eq_zero_iff.mp hp)

/-! ## Eight sign states and fixed sign-transport masks -/

/-- The zero-free three-coordinate sign sector. -/
abbrev TSignState := Fin 3 -> Bool

/-- Flip one Boolean sign bit when the mask is active. -/
def tFlipBit (mask bit : Bool) : Bool :=
  if mask then !bit else bit

/-- Coordinatewise sign transport on the eight-state sector. -/
def tFlipState (mask state : TSignState) : TSignState :=
  fun i => tFlipBit (mask i) (state i)

/-- The mask corresponding to adjoining one large prime in every active coordinate. -/
def tAllFlipMask : TSignState := fun _ => true

@[simp] theorem tFlipBit_false (b : Bool) : tFlipBit false b = b := by
  rfl

@[simp] theorem tFlipBit_true (b : Bool) : tFlipBit true b = !b := by
  rfl

@[simp] theorem tFlipBit_involutive (m b : Bool) :
    tFlipBit m (tFlipBit m b) = b := by
  cases m <;> cases b <;> rfl

@[simp] theorem tFlipState_involutive (mask state : TSignState) :
    tFlipState mask (tFlipState mask state) = state := by
  funext i
  simp [tFlipState]

/-- Number of sign states in the `T` sector. -/
theorem tSignState_card : Fintype.card TSignState = 8 := by
  native_decide

/-- A rational transition kernel on the eight-state sign sector. -/
abbrev TKernel := TSignState -> TSignState -> Rat

/-- Exact uniform transition kernel. -/
def uniformTKernel : TKernel := fun _ _ => (1 : Rat) / 8

/-- Pull a kernel through fixed source and destination sign-flip masks. -/
def transportTKernel (K : TKernel) (sourceMask destMask : TSignState) : TKernel :=
  fun u v => K (tFlipState sourceMask u) (tFlipState destMask v)

/-- Fixed large-prime sign transport preserves an exactly uniform transition kernel. -/
theorem transportTKernel_uniform
    (sourceMask destMask : TSignState) :
    transportTKernel uniformTKernel sourceMask destMask = uniformTKernel := by
  rfl

/-- In particular, simultaneous large-prime sign reversal on source and destination
leaves the uniform `T` kernel literally unchanged. -/
theorem allLargePrimeTransport_uniform :
    transportTKernel uniformTKernel tAllFlipMask tAllFlipMask = uniformTKernel := by
  rfl

/-- Entrywise deviation from `1/8` is merely permuted by fixed sign transport. -/
theorem transportTKernel_uniformDeviation
    (K : TKernel) (sourceMask destMask u v : TSignState) :
    |transportTKernel K sourceMask destMask u v - (1 : Rat) / 8| =
      |K (tFlipState sourceMask u) (tFlipState destMask v) - (1 : Rat) / 8| := by
  rfl

/-! ## Exact uniform-kernel second moment -/

/-- Convert one Boolean sign bit to `+1` or `-1`. -/
def tSignedBit (b : Bool) : Rat :=
  if b then 1 else -1

/-- Three-active-slot scalar `a - b + c` on a zero-free cell. -/
def tCellObservable (s : TSignState) : Rat :=
  tSignedBit (s 0) - tSignedBit (s 1) + tSignedBit (s 2)

/-- Uniform expectation over the eight sign states. -/
def uniformTExpectation (f : TSignState -> Rat) : Rat :=
  (1 : Rat) / 8 * ∑ s : TSignState, f s

/-- The active cell observable is exactly centered under the uniform `T` law. -/
theorem uniformTExpectation_tCellObservable_eq_zero :
    uniformTExpectation tCellObservable = 0 := by
  native_decide

/-- Exact diagonal second moment of the active cell observable. -/
theorem uniformTExpectation_tCellObservable_sq_eq_three :
    uniformTExpectation (fun s => tCellObservable s ^ 2) = 3 := by
  native_decide

/-- Apply a transition kernel to an observable. -/
def tKernelApply (K : TKernel) (f : TSignState -> Rat) : TSignState -> Rat :=
  fun u => ∑ v : TSignState, K u v * f v

/-- The uniform kernel annihilates the centered active observable in one step. -/
theorem uniformTKernel_annihilates_tCellObservable :
    tKernelApply uniformTKernel tCellObservable = 0 := by
  funext u
  native_decide +revert

/-- Kernel iteration on observables. -/
def tKernelIterate (K : TKernel) : Nat -> (TSignState -> Rat) -> TSignState -> Rat
  | 0, f => f
  | n + 1, f => tKernelApply K (tKernelIterate K n f)

@[simp] theorem tKernelApply_zero (K : TKernel) :
    tKernelApply K (0 : TSignState -> Rat) = 0 := by
  funext u
  simp [tKernelApply]

/-- Once the uniform kernel kills the centered mode, every positive iterate is zero. -/
theorem uniformTKernel_iterate_tCellObservable_succ (n : Nat) :
    tKernelIterate uniformTKernel (n + 1) tCellObservable = 0 := by
  induction n with
  | zero =>
      simpa [tKernelIterate] using uniformTKernel_annihilates_tCellObservable
  | succ n ih =>
      change tKernelApply uniformTKernel
        (tKernelIterate uniformTKernel (n + 1) tCellObservable) = 0
      rw [ih]
      exact tKernelApply_zero uniformTKernel

/-- Stationary lag covariance of the active observable under the uniform kernel. -/
def uniformTLagCovariance (h : Nat) : Rat :=
  uniformTExpectation fun u =>
    tCellObservable u * tKernelIterate uniformTKernel h tCellObservable u

@[simp] theorem uniformTLagCovariance_zero :
    uniformTLagCovariance 0 = 3 := by
  simpa [uniformTLagCovariance, tKernelIterate, pow_two] using
    uniformTExpectation_tCellObservable_sq_eq_three

@[simp] theorem uniformTLagCovariance_succ (h : Nat) :
    uniformTLagCovariance (h + 1) = 0 := by
  rw [uniformTLagCovariance, uniformTKernel_iterate_tCellObservable_succ h]
  simp [uniformTExpectation]

/-- Green--Kubo second moment for `K` consecutive stationary `T` increments. -/
def uniformTGreenKuboSecondMoment (K : Nat) : Rat :=
  (K : Rat) * uniformTLagCovariance 0 +
    2 * ∑ h ∈ Finset.range K,
      ((K - (h + 1) : Nat) : Rat) * uniformTLagCovariance (h + 1)

/-- Exact random-walk-scale law for the exactly uniform eight-state kernel. -/
theorem uniformTGreenKuboSecondMoment_eq_three_mul (K : Nat) :
    uniformTGreenKuboSecondMoment K = 3 * (K : Rat) := by
  simp [uniformTGreenKuboSecondMoment]
  ring

end RHLean.Analysis
