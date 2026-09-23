import RHLean.Proof.PostRootCovarianceGlobalExponentTransfer
import RHLean.Analysis.DyadicTransportCanonicalForm
import RHLean.Analysis.EulerCRTRoughnessRecursion
import RHLean.Analysis.NativePNTAxer
import RHLean.Analysis.StrongMertensLogNineBalance
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime

/-!
# Unconditional decay pulled back onto the post-root remainder carrier

The fixed-power equivalence in `PostRootCovarianceGlobalExponentTransfer` does
not exhaust the unconditional information already proved elsewhere in the
repository.  Two exact facts survive transport back to the current carrier:

* adjoining `2` cancels the lower odd prefix exactly, so every physical Mertens
  value is an odd dyadic-annulus sum;
* the repository already proves the unconditional strong Mertens estimate
  `M(N) = O(N * exp(-c (log N)^(1/10)))`.

The first fact already improves the elementary quadratic constant by a full
factor of nine over the coarse squarefree-count estimate in the exponent
transfer file.  The second gives an unconditional *subquadratic* upper envelope
for the signed post-root remainder, with the full subexponential rate visible.
On the other side, exact quotient packing of the removed post-root families
gives an elementary lower bound of order `-W^(3/2)`.  These are genuine
quantitative statements on the current carrier, not merely fixed-power
reformulations.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The real prefix used by the covariance tower is exactly the native real
Mertens summatory function at the preceding endpoint. -/
theorem realMertensLength_succ_eq_nativeMertensSummatory (N : ℕ) :
    realMertensLength (N + 1) = nativeMertensSummatory N := by
  unfold realMertensLength nativeMertensSummatory
  have hset :
      Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp
    omega
  rw [hset]
  simp [realMoebiusStep]

/-- **Adjoining two cancels the lower odd prefix.**  In the real covariance
coordinate, the whole Mertens prefix is exactly the odd dyadic annulus
`B/2 < c <= B`. -/
theorem realMertensLength_succ_eq_oddDyadicAnnulus (B : ℕ) :
    realMertensLength (B + 1) =
      ∑ c ∈ dyadicCofactorBoundary B, realMoebiusStep c := by
  have h := mertensSummatory_eq_dyadicCofactorBoundaryMass B
  have hre := congrArg Complex.re h
  simpa [RHLean.Analysis.mertensSummatory, dyadicCofactorBoundaryMass,
    canonicalMoebiusWeight, realMertensLength, realMoebiusStep] using hre

/-! ## Iterating the wheel: `2` then `3`, then every finite prime set

The dyadic annulus is only the first Euler coordinate.  The generic
`roughMertens_wheel_recursion` says that removing a prime from a squarefree
wheel is the multiplicative finite difference at that prime.  The repository's
canonical `finiteDifferenceOperator` says the same thing without choosing an
order for the primes.  First expose the `2 x 3` zero band, then identify the
entire finite-prime wheel with the exact physical Mertens prefix.
-/

/-- **Exact two-prime wheel collapse.**  After adjoining `2` and `3`, the
ordinary Mertens prefix is the difference of two `6`-rough interval masses:

`T_1(B) = T_6(B/2,B] - T_6(B/6,B/3]`.

In particular the entire middle reciprocal band `(B/3,B/2]` has coefficient
zero.  This is the first concrete post-dyadic instance of the full iterative
prime-wheel cancellation; it uses no estimate and no complete-period argument. -/
theorem roughMertens_one_eq_sixWheel_twoBands (B : ℕ) :
    roughMertens 1 B =
      roughInterval 6 (B / 2) B -
        roughInterval 6 (B / 6) (B / 3) := by
  have hsq6 : Squarefree 6 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).2
        ⟨Nat.prime_two.squarefree, (show Nat.Prime 3 by norm_num).squarefree⟩
  have h2 :=
    roughMertens_wheel_recursion
      (W := 2) (p := 2) Nat.prime_two (by norm_num)
        Nat.prime_two.squarefree B
  have h6B :=
    roughMertens_wheel_recursion
      (W := 6) (p := 3) (by norm_num) (by norm_num) hsq6 B
  have h6half :=
    roughMertens_wheel_recursion
      (W := 6) (p := 3) (by norm_num) (by norm_num) hsq6 (B / 2)
  unfold multDiff at h2 h6B h6half
  norm_num at h2 h6B h6half
  have hdiv : B / 2 / 3 = B / 6 := by
    rw [Nat.div_div_eq_div_mul]
  rw [hdiv] at h6half
  unfold roughInterval
  omega

/-- **The wheel really iterates.**  Adjoining the next fresh prime `5` refines
both surviving `6`-rough bands by the same finite difference.  Thus the
physical prefix is already a four-band signed `30`-rough staircase:

`T_1(B) = T_30(B/2,B] - T_30(B/10,B/5]
          - T_30(B/6,B/3] + T_30(B/30,B/15]`.

Nothing is restarted when the prime is added: every previously processed
coordinate is retained and the new prime simply differences the existing
surviving bands. -/
theorem roughMertens_one_eq_thirtyWheel_fourBands (B : ℕ) :
    roughMertens 1 B =
      roughInterval 30 (B / 2) B -
        roughInterval 30 (B / 10) (B / 5) -
        roughInterval 30 (B / 6) (B / 3) +
        roughInterval 30 (B / 30) (B / 15) := by
  have hsq6 : Squarefree 6 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).2
        ⟨Nat.prime_two.squarefree, (show Nat.Prime 3 by norm_num).squarefree⟩
  have hsq30 : Squarefree 30 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 5 6)).2
        ⟨(show Nat.Prime 5 by norm_num).squarefree, hsq6⟩
  have htop :=
    roughInterval_wheel_recursion
      (W := 30) (p := 5) (by norm_num) (by norm_num) hsq30 (B / 2) B
  have hlow :=
    roughInterval_wheel_recursion
      (W := 30) (p := 5) (by norm_num) (by norm_num) hsq30 (B / 6) (B / 3)
  norm_num at htop hlow
  have htop' :
      roughInterval 6 (B / 2) B =
        roughInterval 30 (B / 2) B -
          roughInterval 30 (B / 10) (B / 5) := by
    simpa [Nat.div_div_eq_div_mul] using htop
  have hlow' :
      roughInterval 6 (B / 6) (B / 3) =
        roughInterval 30 (B / 6) (B / 3) -
          roughInterval 30 (B / 30) (B / 15) := by
    simpa [Nat.div_div_eq_div_mul] using hlow
  rw [roughMertens_one_eq_sixWheel_twoBands B, htop', hlow']
  ring

private theorem primorial_squarefree_of_primes
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    Squarefree (RHLean.Arithmetic.primorial S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [RHLean.Arithmetic.primorial]
  | @insert p S hpS ih =>
      have hp : Nat.Prime p := hprime p (by simp)
      have hprimeS : ∀ q ∈ S, Nat.Prime q := by
        intro q hq
        exact hprime q (by simp [hq])
      have hsqS : Squarefree (RHLean.Arithmetic.primorial S) := ih hprimeS
      have hcop : Nat.Coprime p (RHLean.Arithmetic.primorial S) :=
        prime_coprime_primorial S p hp hpS hprimeS
      have hsq : Squarefree (p * RHLean.Arithmetic.primorial S) :=
        (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hsqS⟩
      simpa [RHLean.Arithmetic.primorial_insert S p hpS] using hsq

/-- **Full finite prime-wheel recovery of ordinary Mertens.**  Every selected
prime contributes exactly one multiplicative difference, and after all of them
are taken the rough wheel state is transported back to wheel `1`:

`D_S (T_{prod S}) = T_1`.

This is the unordered finite-set form of the iterative cancellation visible in
the full prime wheel. -/
theorem finiteDifferenceOperator_roughMertens_primorial
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    finiteDifferenceOperator S (roughMertens (RHLean.Arithmetic.primorial S)) = roughMertens 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [RHLean.Arithmetic.primorial]
  | @insert p S hpS ih =>
      have hp : Nat.Prime p := hprime p (by simp)
      have hprimeS : ∀ q ∈ S, Nat.Prime q := by
        intro q hq
        exact hprime q (by simp [hq])
      have hsqS : Squarefree (RHLean.Arithmetic.primorial S) :=
        primorial_squarefree_of_primes S hprimeS
      have hcop : Nat.Coprime p (RHLean.Arithmetic.primorial S) :=
        prime_coprime_primorial S p hp hpS hprimeS
      have hsq : Squarefree (p * RHLean.Arithmetic.primorial S) :=
        (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hsqS⟩
      have hrec :
          freshPrimeDifference p (roughMertens (p * RHLean.Arithmetic.primorial S)) =
            roughMertens (RHLean.Arithmetic.primorial S) := by
        funext x
        have h := roughMertens_wheel_recursion
          (W := p * RHLean.Arithmetic.primorial S) (p := p) hp
          (by exact ⟨RHLean.Arithmetic.primorial S, rfl⟩) hsq x
        have hdiv : (p * RHLean.Arithmetic.primorial S) / p =
            RHLean.Arithmetic.primorial S :=
          Nat.mul_div_cancel_left (RHLean.Arithmetic.primorial S) hp.pos
        rw [hdiv] at h
        simpa [freshPrimeDifference, multDiff] using h
      rw [RHLean.Arithmetic.primorial_insert S p hpS]
      rw [finiteDifferenceOperator_insert_eq_freshPrimeDifference
        S p hp hpS hprimeS]
      rw [hrec]
      exact ih hprimeS

/-- Pointwise divisor-ratio form of the full-wheel identity.  This is the exact
signed staircase on which successive prime additions act:

`T_1(B) = sum_{d | prod S} mu(d) T_{prod S}(floor(B/d))`.

The zero bands seen for `{2,3}` are therefore instances of a general finite
Boolean difference, not a special dyadic phenomenon. -/
theorem roughMertens_one_eq_primeWheel_divisorDifference
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (B : ℕ) :
    roughMertens 1 B =
      ∑ d ∈ (RHLean.Arithmetic.primorial S).divisors,
        (μ d : ℤ) * roughMertens (RHLean.Arithmetic.primorial S) (B / d) := by
  have h := congrFun (finiteDifferenceOperator_roughMertens_primorial S hprime) B
  rw [finiteDifferenceOperator_apply] at h
  simpa using h.symm

/-- **Prime adjoining is an exact refinement, not a new estimate.**  If `p` is
fresh, the recovered physical Mertens prefix is unchanged when the wheel grows
from `S` to `insert p S`; only its signed ratio-band representation is refined.
This is the formal iterative statement behind the full prime wheel. -/
theorem primeWheelMertensTransport_invariant_insert
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    finiteDifferenceOperator (insert p S)
        (roughMertens (RHLean.Arithmetic.primorial (insert p S))) =
      finiteDifferenceOperator S (roughMertens (RHLean.Arithmetic.primorial S)) := by
  have hprimeInsert : ∀ q ∈ insert p S, Nat.Prime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqS
    · exact hp
    · exact hprime q hqS
  rw [finiteDifferenceOperator_roughMertens_primorial (insert p S) hprimeInsert]
  rw [finiteDifferenceOperator_roughMertens_primorial S hprime]

/-! ## The elementary gain hidden by the coarse squarefree sieve -/

/-- The odd dyadic annulus contains at most one quarter of the physical prefix.
The map `c ↦ c / 2` is injective on odd integers and sends the boundary into the
integer interval

`[(B+2)/4, (B-1)/2]`.

Counting that interval gives the sharp uniform upper bound `(B+3)/4`. -/
theorem card_dyadicCofactorBoundary_le_quarter (B : ℕ) :
    (dyadicCofactorBoundary B).card ≤ (B + 3) / 4 := by
  classical
  by_cases hB0 : B = 0
  · subst B
    norm_num [dyadicCofactorBoundary, oddCofactorPrefix]
  · have hmaps : ∀ c ∈ dyadicCofactorBoundary B,
        c / 2 ∈ Finset.Icc ((B + 2) / 4) ((B - 1) / 2) := by
      intro c hc
      rcases mem_dyadicCofactorBoundary.mp hc with
        ⟨_hc1, hcB, hcodd, hdouble⟩
      rcases hcodd with ⟨k, hk⟩
      have hcdiv : c / 2 = k := by omega
      rw [hcdiv]
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hinj : Set.InjOn (fun c : ℕ => c / 2)
        (dyadicCofactorBoundary B : Set ℕ) := by
      intro a ha b hb hab
      rcases mem_dyadicCofactorBoundary.mp (Finset.mem_coe.mp ha) with
        ⟨_ha1, _haB, haodd, _hadouble⟩
      rcases mem_dyadicCofactorBoundary.mp (Finset.mem_coe.mp hb) with
        ⟨_hb1, _hbB, hbodd, _hbdouble⟩
      rcases haodd with ⟨ka, hka⟩
      rcases hbodd with ⟨kb, hkb⟩
      have hada : a / 2 = ka := by omega
      have hbdb : b / 2 = kb := by omega
      change a / 2 = b / 2 at hab
      rw [hada, hbdb] at hab
      omega
    have hcard :=
      Finset.card_le_card_of_injOn (fun c : ℕ => c / 2) hmaps hinj
    rw [Nat.card_Icc] at hcard
    omega

private theorem abs_realMoebiusStep_le_one_dyadic (n : ℕ) :
    |realMoebiusStep n| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h]

/-- The exact signed dyadic identity plus trivial pointwise Möbius support gives
an unconditional quarter-prefix bound.  Unlike the previous `3/4` bound, this
uses the sign flip from adjoining `2`, not only squarefree support. -/
theorem abs_realMertensLength_succ_le_dyadicQuarter (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (((B + 3) / 4 : ℕ) : ℝ) := by
  rw [realMertensLength_succ_eq_oddDyadicAnnulus]
  calc
    |∑ c ∈ dyadicCofactorBoundary B, realMoebiusStep c| ≤
        ∑ c ∈ dyadicCofactorBoundary B, |realMoebiusStep c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ dyadicCofactorBoundary B, (1 : ℝ) := by
      exact Finset.sum_le_sum fun c _hc => abs_realMoebiusStep_le_one_dyadic c
    _ = ((dyadicCofactorBoundary B).card : ℝ) := by simp
    _ ≤ (((B + 3) / 4 : ℕ) : ℝ) := by
      exact_mod_cast card_dyadicCofactorBoundary_le_quarter B

/-- **Bessel transfers arbitrary pointwise Mertens majorants, not only power
laws.**  This is the rate-free form of the return path: any bound `A` for the
physical Mertens prefix immediately gives `E(W) <= A^2/2`. -/
theorem postRootCovarianceRemainder_le_of_mertensMajorant
    {W : ℕ} {A : ℝ}
    (hM : |realMertensLength (W + 1)| ≤ A) :
    postRootCovarianceRemainder W ≤ A ^ 2 / 2 := by
  have hsqMul := mul_self_le_mul_self (abs_nonneg _) hM
  have hsq : realMertensLength (W + 1) ^ 2 ≤ A ^ 2 := by
    calc
      realMertensLength (W + 1) ^ 2 =
          |realMertensLength (W + 1)| ^ 2 := (sq_abs _).symm
      _ ≤ A ^ 2 := by simpa [pow_two] using hsqMul
  exact (postRootCovarianceRemainder_le_half_mertensSquare W).trans
    (div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2))

/-- Squaring the exact quarter-prefix estimate in the Bessel inequality gives

`E(W) <= (floor((W+3)/4))^2 / 2`.

Asymptotically this is `W^2 / 32`, improving the previous squarefree-sieve
coefficient `9/32` by a factor of nine before any analytic decay is used. -/
theorem postRootCovarianceRemainder_le_dyadicQuarterSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((((W + 3) / 4 : ℕ) : ℝ) ^ 2) / 2 := by
  have hM := abs_realMertensLength_succ_le_dyadicQuarter W
  exact postRootCovarianceRemainder_le_of_mertensMajorant hM

/-! ## The opposite side: exact quotient packing gives `W^(3/2)` -/

/-- The complete positive-lag covariance at an endpoint can never lie below
`-W/2`.  This is just the exact Mertens-square/diagonal identity together with
`diagonal + zeroCount = W`; no cancellation estimate is used. -/
theorem neg_half_endpoint_le_realMertensPositiveLagPairSum_succ (W : ℕ) :
    -(W : ℝ) / 2 ≤ realMertensPositiveLagPairSum (W + 1) := by
  rw [realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal]
  have hnorm : 0 ≤ ‖mertensSummatory W‖ ^ 2 := sq_nonneg _
  have hdiag := realMertensDiagonal_add_zeroCount_eq_endpoint W
  have hzero : 0 ≤ (realMertensZeroCount W : ℝ) := by positivity
  nlinarith

/-- At every positive lower endpoint, the complete lower covariance is at most
half the square of that endpoint.  The proof deliberately uses the exact
`p=2` dyadic cancellation rather than a raw prefix-length bound. -/
theorem realMertensPositiveLagPairSum_succ_le_half_endpoint_sq
    {q : ℕ} (hq : 1 ≤ q) :
    realMertensPositiveLagPairSum (q + 1) ≤ (q : ℝ) ^ 2 / 2 := by
  have hcov := realMertensPositiveLagPairSum_le_half_lengthSq (q + 1)
  have hM0 := abs_realMertensLength_succ_le_dyadicQuarter q
  have hfloorNat : (q + 3) / 4 ≤ q := by omega
  have hfloor : (((q + 3) / 4 : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hfloorNat
  have hM : |realMertensLength (q + 1)| ≤ (q : ℝ) := hM0.trans hfloor
  have hsqMul := mul_self_le_mul_self (abs_nonneg _) hM
  have hsq : realMertensLength (q + 1) ^ 2 ≤ (q : ℝ) ^ 2 := by
    calc
      realMertensLength (q + 1) ^ 2 =
          |realMertensLength (q + 1)| ^ 2 := (sq_abs _).symm
      _ ≤ (q : ℝ) ^ 2 := by simpa [pow_two] using hsqMul
  exact hcov.trans
    (div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2))

/-- **All removed post-root family covariance is `O(W^(3/2))` by product
packing alone.**  Each quotient `q = floor(W/p)` lies below `sqrt W`, while the
already-compiled product packing says `sum q <= W`. -/
theorem postRootPrimeFamilyCovarianceTotal_le_half_sqrt_mul_endpoint (W : ℕ) :
    postRootPrimeFamilyCovarianceTotal W ≤
      ((Nat.sqrt W : ℝ) * (W : ℝ)) / 2 := by
  have hpackNat := sum_postRootPrimeFamily_quotients_le_endpoint W
  have hpack :
      (∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) ≤ (W : ℝ) := by
    exact_mod_cast hpackNat
  unfold postRootPrimeFamilyCovarianceTotal
  calc
    (∑ p ∈ postRootPrimeFamilySet W,
        realMertensPositiveLagPairSum (W / p + 1)) ≤
      ∑ p ∈ postRootPrimeFamilySet W,
        ((Nat.sqrt W : ℝ) * ((W / p : ℕ) : ℝ)) / 2 := by
      apply Finset.sum_le_sum
      intro p hp
      rcases mem_postRootPrimeFamilySet.mp hp with ⟨_hpRoot, hpW, hpPrime⟩
      have hqpos : 0 < W / p := Nat.div_pos hpW hpPrime.pos
      have hcov :=
        realMertensPositiveLagPairSum_succ_le_half_endpoint_sq
          (q := W / p) (by omega)
      have hqroot : W / p ≤ Nat.sqrt W := by
        apply (Nat.le_sqrt).2
        simpa [pow_two] using postRootPrimeFamily_quotient_sq_le hp
      have hqrootR : ((W / p : ℕ) : ℝ) ≤ (Nat.sqrt W : ℝ) := by
        exact_mod_cast hqroot
      have hqnonneg : 0 ≤ ((W / p : ℕ) : ℝ) := by positivity
      have hsq : ((W / p : ℕ) : ℝ) ^ 2 ≤
          (Nat.sqrt W : ℝ) * ((W / p : ℕ) : ℝ) := by
        nlinarith
      exact hcov.trans
        (div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2))
    _ = ((Nat.sqrt W : ℝ) / 2) *
        (∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ ((Nat.sqrt W : ℝ) / 2) * (W : ℝ) := by
      exact mul_le_mul_of_nonneg_left hpack (by positivity)
    _ = ((Nat.sqrt W : ℝ) * (W : ℝ)) / 2 := by ring

/-- **Unconditional negative-remainder bound.**  Combining the universal
`-W/2` lower bound for the global covariance with exact product packing of all
removed post-root quotients gives

`E(W) >= -(W + W*floor(sqrt W))/2`.

Thus the negative side of the signed remainder is already only order
`W^(3/2)`, with no PNT error term, independence hypothesis, record condition,
or asymptotic input. -/
theorem neg_half_endpoint_add_sqrt_mul_endpoint_le_postRootCovarianceRemainder
    (W : ℕ) :
    -(W : ℝ) / 2 - ((Nat.sqrt W : ℝ) * (W : ℝ)) / 2 ≤
      postRootCovarianceRemainder W := by
  have hglobal := neg_half_endpoint_le_realMertensPositiveLagPairSum_succ W
  have hfamily :=
    postRootPrimeFamilyCovarianceTotal_le_half_sqrt_mul_endpoint W
  unfold postRootCovarianceRemainder
  linarith

/-- **Unconditional subquadratic remainder envelope.**  The repository's
finished strong Mertens theorem transfers through the Bessel inequality with
its full rate: for fixed positive `c`,

`E(W) <= 1/2 * (C W exp(-c (log W)^(1/10)))^2`.

Thus the current carrier has unconditional decay beyond every fixed quadratic
constant, even though this does not yet constitute a fixed power saving. -/
theorem postRootCovarianceRemainder_le_strongMertensSubexp :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ W : ℕ, 3 ≤ W →
        postRootCovarianceRemainder W ≤
          (C * (W : ℝ) *
            Real.exp (-c * (Real.log (W : ℝ)) ^ ((1 : ℝ) / 10))) ^ 2 / 2 := by
  rcases strongNativeMertensSubexp with ⟨c, C, hc, hC, hM⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro W hW
  let R : ℝ :=
    C * (W : ℝ) *
      Real.exp (-c * (Real.log (W : ℝ)) ^ ((1 : ℝ) / 10))
  have hbound : |nativeMertensSummatory W| ≤ R := by
    simpa [R] using hM W hW
  rw [← realMertensLength_succ_eq_nativeMertensSummatory] at hbound
  exact postRootCovarianceRemainder_le_of_mertensMajorant hbound

/-! ## Normalized consequences -/

/-- The normalized positive part of the signed post-root covariance remainder
vanishes unconditionally.  This uses only the elementary Axer/PNT contraction
`M(W)/W -> 0` already compiled in the repository and the exact Bessel return
inequality `E(W) <= M(W)^2/2`. -/
theorem postRootCovarianceRemainder_posPart_div_sq_tendsto_zero :
    Tendsto
      (fun W : ℕ =>
        max (postRootCovarianceRemainder W) 0 / ((W : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hM :
      Tendsto
        (fun W : ℕ => realMertensLength (W + 1) / (W : ℝ))
        atTop (𝓝 0) := by
    simpa only [realMertensLength_succ_eq_nativeMertensSummatory] using
      RHLean.Analysis.nativeMertens_div_atTop_zero
  have hsq :
      Tendsto
        (fun W : ℕ =>
          (realMertensLength (W + 1) / (W : ℝ)) ^ 2 / 2)
        atTop (𝓝 0) := by
    simpa using (hM.pow 2).div_const 2
  refine squeeze_zero' ?_ ?_ hsq
  · filter_upwards [eventually_ge_atTop 1] with W hW
    have hWpos : (0 : ℝ) < (W : ℝ) := by
      exact_mod_cast (show 0 < W by omega)
    exact div_nonneg (le_max_right _ _) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with W hW
    have hWpos : (0 : ℝ) < (W : ℝ) := by
      exact_mod_cast (show 0 < W by omega)
    have hE := postRootCovarianceRemainder_le_half_mertensSquare W
    have hmax :
        max (postRootCovarianceRemainder W) 0 ≤
          realMertensLength (W + 1) ^ 2 / 2 := by
      exact max_le hE (div_nonneg (sq_nonneg _) (by norm_num))
    rw [div_le_iff₀ (sq_pos_of_pos hWpos)]
    calc
      max (postRootCovarianceRemainder W) 0 ≤
          realMertensLength (W + 1) ^ 2 / 2 := hmax
      _ =
          ((realMertensLength (W + 1) / (W : ℝ)) ^ 2 / 2) *
            ((W : ℝ) ^ 2) := by
        field_simp

/-- Epsilon form: every fixed positive fraction of the quadratic scale is
eventually excluded on the positive side. -/
theorem postRootCovarianceRemainder_eventually_lt_eps_sq
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ W : ℕ in atTop,
      postRootCovarianceRemainder W < eps * ((W : ℝ) ^ 2) := by
  have hlim := postRootCovarianceRemainder_posPart_div_sq_tendsto_zero
  have hsmall :
      ∀ᶠ W : ℕ in atTop,
        max (postRootCovarianceRemainder W) 0 / ((W : ℝ) ^ 2) < eps :=
    (tendsto_order.1 hlim).2 eps heps
  filter_upwards [hsmall, eventually_ge_atTop 1] with W hWsmall hW
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast (show 0 < W by omega)
  have hposle :
      postRootCovarianceRemainder W ≤ max (postRootCovarianceRemainder W) 0 :=
    le_max_left _ _
  have hmul := (div_lt_iff₀ (sq_pos_of_pos hWpos)).1 hWsmall
  exact lt_of_le_of_lt hposle hmul

/-- A completely explicit two-sided envelope on the current signed carrier.
The positive side uses the repository's finished strong Mertens rate; the
negative side uses only exact post-root quotient packing.  No record or envelope
hypothesis occurs in the statement.

This is the useful pointwise synthesis: whichever sign `E(W)` takes, its
absolute value is bounded by the larger of a subexponentially contracted
quadratic term and the elementary `W^(3/2)` packing term. -/
theorem abs_postRootCovarianceRemainder_le_twoSidedUnconditionalEnvelope :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ W : ℕ, 3 ≤ W →
        |postRootCovarianceRemainder W| ≤
          max
            ((C * (W : ℝ) *
              Real.exp (-c * (Real.log (W : ℝ)) ^ ((1 : ℝ) / 10))) ^ 2 / 2)
            (((W : ℝ) + (Nat.sqrt W : ℝ) * (W : ℝ)) / 2) := by
  rcases postRootCovarianceRemainder_le_strongMertensSubexp with
    ⟨c, C, hc, hC, hupper⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro W hW
  let U : ℝ :=
    (C * (W : ℝ) *
      Real.exp (-c * (Real.log (W : ℝ)) ^ ((1 : ℝ) / 10))) ^ 2 / 2
  let B : ℝ := ((W : ℝ) + (Nat.sqrt W : ℝ) * (W : ℝ)) / 2
  have hu : postRootCovarianceRemainder W ≤ U := by
    simpa [U] using hupper W hW
  have hl :=
    neg_half_endpoint_add_sqrt_mul_endpoint_le_postRootCovarianceRemainder W
  have hl' : -B ≤ postRootCovarianceRemainder W := by
    dsimp [B]
    linarith
  have hleft : -max U B ≤ postRootCovarianceRemainder W := by
    have hB : B ≤ max U B := le_max_right _ _
    linarith
  have hright : postRootCovarianceRemainder W ≤ max U B :=
    hu.trans (le_max_left _ _)
  have habs : |postRootCovarianceRemainder W| ≤ max U B :=
    abs_le.mpr ⟨hleft, hright⟩
  simpa [U, B] using habs

end RHLean.Proof
