import Mathlib
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Analysis.SquareRunTopEscapeClassification
import RHLean.Proof.DeathShellSubpolynomial

open scoped BigOperators

/-!
# The unique fresh-prime owner cube straddles both square-run boundaries

Global first-separation ownership assigns every nonzero square-run covariance
atom to one unique fresh prime `p`.  On a subdoubling run this cube is never a
complete cube contained in the physical window.  The endpoint carrying `p`
strips below the lower square anchor, while adjoining `p` to the other endpoint
overshoots the upper square cutoff.

This is the exact chronology statement needed to distinguish unique atom
ownership from the stronger, false idea that the run decomposes into disjoint
complete four-corner cubes.  Four-corner cancellation is therefore genuinely
nonlocal in square time.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- In a subdoubling run, adjoining any prime to any physical site reaches or
passes the upper endpoint. -/
theorem prime_mul_runSite_ge_top_of_subdoubling
    {p a b n : ℕ} (hp : p.Prime)
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    (b + 1) ^ 2 ≤ p * n := by
  have hnLow : a ^ 2 ≤ n := (Finset.mem_Ico.mp hn).1
  have htwo : 2 * a ^ 2 ≤ p * n := Nat.mul_le_mul hp.two_le hnLow
  exact hsub.trans htwo

/-- **Two-sided owner-cube boundary theorem.**

For every nonzero physical pair in a subdoubling run, let `p` be its unique
first differing prime and strip `p` from both endpoints.  In the orientation
where `p` occurred in the first endpoint, that stripped parent lies below the
run while adjoining `p` to the second parent lies above it; and symmetrically in
the other orientation.

Thus the unique owner cube exists, but its complementary corners lie on opposite
sides of the physical square-time window. -/
theorem squareRunFreshPrimeOwner_cube_straddles
    {a b m n : ℕ} (_hab : a ≤ b)
    (hm : m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hmn : m < n)
    (hm0 : realMoebiusStep m ≠ 0)
    (hn0 : realMoebiusStep n ≠ 0)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    let p := squarefreePairFreshPrimeOwner m n
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    (um < a ^ 2 ∧ (b + 1) ^ 2 ≤ p * un) ∨
      (un < a ^ 2 ∧ (b + 1) ^ 2 ≤ p * um) := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  have hmsq := squarefree_of_realMoebiusStep_ne_zero hm0
  have hnsq := squarefree_of_realMoebiusStep_ne_zero hn0
  have hmpos : 0 < m := by
    by_contra hz
    have hmz : m = 0 := by omega
    subst m
    simp [realMoebiusStep] at hm0
  have hnpos : 0 < n := lt_trans hmpos hmn
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hmsq hnsq (by omega)
  rcases squarefreePairFreshPrimeOwner_dvd_xor
      hmsq hnsq (by omega) hmpos hnpos with h | h
  · left
    have hum : um < a ^ 2 := by
      dsimp [um]
      exact squarefreePrimeFamilyParent_lt_runAnchor_of_dvd hp hm h.1 hsub
    have hun : un = n := by
      dsimp [un]
      exact squarefreePrimeFamilyParent_eq_of_not_dvd h.2
    refine ⟨hum, ?_⟩
    change (b + 1) ^ 2 ≤ p * un
    rw [hun]
    exact prime_mul_runSite_ge_top_of_subdoubling hp hn hsub
  · right
    have hun : un < a ^ 2 := by
      dsimp [un]
      exact squarefreePrimeFamilyParent_lt_runAnchor_of_dvd hp hn h.1 hsub
    have hum : um = m := by
      dsimp [um]
      exact squarefreePrimeFamilyParent_eq_of_not_dvd h.2
    refine ⟨hun, ?_⟩
    change (b + 1) ^ 2 ≤ p * um
    rw [hum]
    exact prime_mul_runSite_ge_top_of_subdoubling hp hm hsub

/-- No unique owner cube of a contributing pair can have all four of its
fresh-parent/mixed corners strictly inside a subdoubling square run. -/
theorem squareRunFreshPrimeOwner_not_complete_internal_cube
    {a b m n : ℕ} (hab : a ≤ b)
    (hm : m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hmn : m < n)
    (hm0 : realMoebiusStep m ≠ 0)
    (hn0 : realMoebiusStep n ≠ 0)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    let p := squarefreePairFreshPrimeOwner m n
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    ¬ (um ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2) ∧
       un ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2) ∧
       p * um ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2) ∧
       p * un ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2)) := by
  dsimp only
  intro hall
  have hstraddle := squareRunFreshPrimeOwner_cube_straddles
    hab hm hn hmn hm0 hn0 hsub
  dsimp only at hstraddle
  rcases hstraddle with h | h
  · exact (not_lt_of_ge (Finset.mem_Ico.mp hall.1).1) h.1
  · exact (not_lt_of_ge (Finset.mem_Ico.mp hall.2.1).1) h.1

/-! ## Conditional PNT-spaced prime-flip closure

The exact prime-sieve collapse shows why a bare PNT or prime-gap estimate is not
by itself a Mertens bound: even after the post-root prime counts are controlled,
the signed smooth remainder remains.  The following hypothesis isolates the
stronger chronology proposed here.  It says that PNT-spaced fresh-prime arrivals,
together with complete Euler-generation cancellation, leave at most one
unit-bounded endpoint residual for each reciprocal coordinate below `sqrt x`.

This is intentionally a conditional statement.  The content still to be derived
from the actual owner chronology is precisely this closure representation; once
it is available, the square-root bound is elementary.
-/

/-- **PNT-spaced prime-flip closure hypothesis.**  After every completed Euler
generation has cancelled, `M(x)` is the sum of one unit-bounded residual for
each of the `sqrt x` lower reciprocal coordinates. -/
def PNTSpacedPrimeFlipClosureStatement : Prop :=
  ∀ x : ℕ,
    ∃ residual : Fin (Nat.sqrt x) → ℂ,
      (∀ z, ‖residual z‖ ≤ 1) ∧
      mertensSummatory x = ∑ z, residual z

/-- Under the explicit prime-flip closure hypothesis, the Mertens function obeys
the strong square-root bound pointwise. -/
theorem norm_mertensSummatory_le_sqrt_of_pntSpacedPrimeFlipClosure
    (h : PNTSpacedPrimeFlipClosureStatement) (x : ℕ) :
    ‖mertensSummatory x‖ ≤ (Nat.sqrt x : ℝ) := by
  classical
  rcases h x with ⟨residual, hresidual, hcollapse⟩
  rw [hcollapse]
  calc
    ‖∑ z, residual z‖ ≤
        ∑ z : Fin (Nat.sqrt x), ‖residual z‖ := by
      exact norm_sum_le Finset.univ residual
    _ ≤ ∑ _z : Fin (Nat.sqrt x), (1 : ℝ) := by
      exact Finset.sum_le_sum (fun z _hz => hresidual z)
    _ = (Nat.sqrt x : ℝ) := by simp

/-- The conditional square-root bound is stronger than the repository's
RH-scale squared-energy criterion; the latter holds with constant `C = 1`. -/
theorem mertensEnergyBounded_of_pntSpacedPrimeFlipClosure
    (h : PNTSpacedPrimeFlipClosureStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro x
  have hnorm :=
    norm_mertensSummatory_le_sqrt_of_pntSpacedPrimeFlipClosure h x
  have hnorm0 : 0 ≤ ‖mertensSummatory x‖ := norm_nonneg _
  have hsqrt0 : 0 ≤ (Nat.sqrt x : ℝ) := by positivity
  have hsq :
      ‖mertensSummatory x‖ ^ 2 ≤ (Nat.sqrt x : ℝ) ^ 2 := by
    nlinarith
  have hsqrtNat : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' x
  have hsqrtReal : (Nat.sqrt x : ℝ) ^ 2 ≤ (x : ℝ) := by
    exact_mod_cast hsqrtNat
  have hxsucc : (x : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ x
  have hbase : (1 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le x))
  have hexp : (1 : ℝ) ≤ 1 + ε := by linarith
  have hbasePow :
      ((x + 1 : ℕ) : ℝ) ≤
        Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase hexp
  calc
    ‖mertensSummatory x‖ ^ 2 ≤ (Nat.sqrt x : ℝ) ^ 2 := hsq
    _ ≤ (x : ℝ) := hsqrtReal
    _ ≤ ((x + 1 : ℕ) : ℝ) := hxsucc
    _ ≤ 1 * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
      simpa using hbasePow

/-! ## Worst-case midpoint between consecutive PNT-spaced primes

The ideal closure above corresponds to one unresolved generation per reciprocal
coordinate.  The adversarial phase is to place the physical endpoint exactly at
the midpoint between two consecutive primes.  Then the distance to either
forced Euler flip is one half of the scaled prime gap.  We record that geometry,
then allow a logarithmic number of simultaneous unresolved generations per
reciprocal coordinate.  This gives the pointwise `sqrt x * log x` scale, whose
square is still inside the repository's RH energy criterion because logarithmic
loss is subpolynomial.
-/

/-- A pair of consecutive primes, stated without choosing a global next-prime
function. -/
def ConsecutivePrimePair (pLo pHi : ℕ) : Prop :=
  pLo.Prime ∧ pHi.Prime ∧ pLo < pHi ∧
    ∀ p : ℕ, p.Prime → pLo < p → p < pHi → False

/-- **Explicit PNT-spacing model at a bracketed scale.**  This is an assumption,
not a consequence claimed from ordinary PNT.  Whenever the integer scale `t`
is bracketed by consecutive primes, their gap is at most one binary-logarithmic
unit at `t`.  `log_2` differs from natural-log spacing only by a fixed constant
and has an elementary subpolynomial implementation already present in the repo. -/
def PNTLogPrimeSpacingModel : Prop :=
  ∀ t pLo pHi : ℕ,
    ConsecutivePrimePair pLo pHi →
      pLo ≤ t → t < pHi →
        pHi - pLo ≤ Nat.log 2 (t + 1) + 1

/-- The physical distance from the midpoint of a reciprocal prime gap to either
endpoint flip.  A prime gap `pHi-pLo` is magnified by the lower cofactor `q`. -/
def reciprocalPrimeMidpointDelay (q pLo pHi : ℕ) : ℝ :=
  (q : ℝ) * ((pHi : ℝ) - (pLo : ℝ)) / 2

/-- The endpoint `x` is exactly halfway, in physical `q*p` time, between the two
prime flips `q*pLo` and `q*pHi`. -/
def IsReciprocalPrimeMidpoint (x q pLo pHi : ℕ) : Prop :=
  pLo < pHi ∧
    (x : ℝ) = (q : ℝ) * ((pLo : ℝ) + (pHi : ℝ)) / 2

/-- At the adversarial midpoint, the distance to the upper prime flip is exactly
one half of the scaled prime gap. -/
theorem reciprocalPrimeMidpoint_distance_to_upper
    {x q pLo pHi : ℕ}
    (hmid : IsReciprocalPrimeMidpoint x q pLo pHi) :
    |(q : ℝ) * (pHi : ℝ) - (x : ℝ)| =
      reciprocalPrimeMidpointDelay q pLo pHi := by
  rcases hmid with ⟨hlt, hmid⟩
  have hlohi : (pLo : ℝ) ≤ (pHi : ℝ) := by exact_mod_cast hlt.le
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hdiff0 : (0 : ℝ) ≤ (pHi : ℝ) - (pLo : ℝ) := sub_nonneg.mpr hlohi
  have hnonneg :
      0 ≤ (q : ℝ) * (pHi : ℝ) -
        (q : ℝ) * ((pLo : ℝ) + (pHi : ℝ)) / 2 := by
    have hprod :
        0 ≤ (q : ℝ) * ((pHi : ℝ) - (pLo : ℝ)) / 2 := by positivity
    nlinarith
  rw [hmid, abs_of_nonneg hnonneg]
  unfold reciprocalPrimeMidpointDelay
  ring

/-- Symmetrically, the distance from the midpoint to the lower prime flip is the
same half-gap. -/
theorem reciprocalPrimeMidpoint_distance_to_lower
    {x q pLo pHi : ℕ}
    (hmid : IsReciprocalPrimeMidpoint x q pLo pHi) :
    |(x : ℝ) - (q : ℝ) * (pLo : ℝ)| =
      reciprocalPrimeMidpointDelay q pLo pHi := by
  rcases hmid with ⟨hlt, hmid⟩
  have hlohi : (pLo : ℝ) ≤ (pHi : ℝ) := by exact_mod_cast hlt.le
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hdiff0 : (0 : ℝ) ≤ (pHi : ℝ) - (pLo : ℝ) := sub_nonneg.mpr hlohi
  have hnonneg :
      0 ≤ (q : ℝ) * ((pLo : ℝ) + (pHi : ℝ)) / 2 -
        (q : ℝ) * (pLo : ℝ) := by
    have hprod :
        0 ≤ (q : ℝ) * ((pHi : ℝ) - (pLo : ℝ)) / 2 := by positivity
    nlinarith
  rw [hmid, abs_of_nonneg hnonneg]
  unfold reciprocalPrimeMidpointDelay
  ring

/-- A gap bound `G` at reciprocal depth `q <= sqrt x` gives the coarse physical
worst-case midpoint delay `(sqrt x) * G / 2`. -/
theorem reciprocalPrimeMidpointDelay_le_root_gap
    {x q pLo pHi G : ℕ}
    (hq : q ≤ Nat.sqrt x) (hlohi : pLo ≤ pHi)
    (hgap : pHi - pLo ≤ G) :
    reciprocalPrimeMidpointDelay q pLo pHi ≤
      (Nat.sqrt x : ℝ) * (G : ℝ) / 2 := by
  have hqR : (q : ℝ) ≤ (Nat.sqrt x : ℝ) := by exact_mod_cast hq
  have hgapCast : (((pHi - pLo : ℕ) : ℝ)) ≤ (G : ℝ) := by exact_mod_cast hgap
  have hgapR : (pHi : ℝ) - (pLo : ℝ) ≤ (G : ℝ) := by
    simpa [Nat.cast_sub hlohi] using hgapCast
  have hdiff0 : (0 : ℝ) ≤ (pHi : ℝ) - (pLo : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hlohi)
  have hroot0 : (0 : ℝ) ≤ (Nat.sqrt x : ℝ) := by positivity
  have hmul :
      (q : ℝ) * ((pHi : ℝ) - (pLo : ℝ)) ≤
        (Nat.sqrt x : ℝ) * (G : ℝ) :=
    mul_le_mul hqR hgapR hdiff0 hroot0
  unfold reciprocalPrimeMidpointDelay
  nlinarith

/-- Under the explicit logarithmic spacing model, if the reciprocal integer
scale `floor(x/q)` is bracketed by consecutive primes, the maximally bad
midpoint delay is at most `sqrt(x) * (log_2(x+1)+1) / 2`.  The upper prime may
lie above `x/q`; the model is pinned to the bracketed scale, not to that prime. -/
theorem reciprocalPrimeMidpointDelay_le_root_log_of_pntSpacing
    (hPNT : PNTLogPrimeSpacingModel)
    {x q pLo pHi : ℕ}
    (hq : q ≤ Nat.sqrt x)
    (hpair : ConsecutivePrimePair pLo pHi)
    (hlo : pLo ≤ x / q) (hhi : x / q < pHi) :
    reciprocalPrimeMidpointDelay q pLo pHi ≤
      (Nat.sqrt x : ℝ) *
        (((Nat.log 2 (x + 1) + 1 : ℕ) : ℝ)) / 2 := by
  have hgap0 := hPNT (x / q) pLo pHi hpair hlo hhi
  have hquot : x / q ≤ x := Nat.div_le_self x q
  have hlog :
      Nat.log 2 (x / q + 1) + 1 ≤ Nat.log 2 (x + 1) + 1 := by
    exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
  have hgap : pHi - pLo ≤ Nat.log 2 (x + 1) + 1 := hgap0.trans hlog
  exact reciprocalPrimeMidpointDelay_le_root_gap
    hq hpair.2.2.1.le hgap

/-- Coarse logarithmic square-time overlap budget used for the maximally bad
midpoint phase.  The extra `+1` already built into the logarithm makes the
budget nonzero at tiny endpoints. -/
def pntWorstCaseSquareOverlap (x : ℕ) : ℕ :=
  Nat.log 2 (x + 1) + 1

/-- **Worst-case PNT-spaced prime-flip closure hypothesis.**  Completed Euler
generations cancel, but an adversarial midpoint may leave up to a logarithmic
number of unit residual generations simultaneously alive in each of the
`sqrt x` reciprocal channels. -/
def PNTSpacedWorstCasePrimeFlipClosureStatement : Prop :=
  ∀ x : ℕ,
    ∃ residual : Fin (Nat.sqrt x) × Fin (pntWorstCaseSquareOverlap x) → ℂ,
      (∀ s, ‖residual s‖ ≤ 1) ∧
      mertensSummatory x = ∑ s, residual s

/-- The maximally bad midpoint phase costs only a logarithmic factor:
`|M(x)| <= sqrt(x) * (log_2(x+1)+1)`. -/
theorem norm_mertensSummatory_le_sqrt_mul_log_of_pntWorstCaseClosure
    (h : PNTSpacedWorstCasePrimeFlipClosureStatement) (x : ℕ) :
    ‖mertensSummatory x‖ ≤
      (Nat.sqrt x : ℝ) * (pntWorstCaseSquareOverlap x : ℝ) := by
  classical
  rcases h x with ⟨residual, hresidual, hcollapse⟩
  rw [hcollapse]
  calc
    ‖∑ s, residual s‖ ≤
        ∑ s : Fin (Nat.sqrt x) × Fin (pntWorstCaseSquareOverlap x),
          ‖residual s‖ := by
      exact norm_sum_le Finset.univ residual
    _ ≤ ∑ _s : Fin (Nat.sqrt x) × Fin (pntWorstCaseSquareOverlap x),
          (1 : ℝ) := by
      exact Finset.sum_le_sum (fun s _hs => hresidual s)
    _ = (Nat.sqrt x : ℝ) * (pntWorstCaseSquareOverlap x : ℝ) := by
      simp [Nat.cast_mul]

/-- The squared logarithmic worst-case overlap is subpolynomial.  This is the
same elementary divisor-count mechanism already used elsewhere in the repo. -/
theorem pntWorstCaseSquareOverlap_sq_le_subpolynomial
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℕ,
        ((pntWorstCaseSquareOverlap x : ℝ)) ^ 2 ≤
          C * Real.rpow ((x : ℝ) + 1) ε := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨C, hC, hlin⟩ :=
    RHLean.Proof.card_divisors_le_subpolynomial hhalf
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro x
  let M : ℕ := Nat.log 2 (x + 1)
  have hpowOne : 1 ≤ 2 ^ M := by
    simpa using (Nat.one_le_pow' M 1)
  have hdiv := hlin (2 ^ M) hpowOne
  have hcard : (2 ^ M).divisors.card = M + 1 := by
    have h := congrArg Finset.card (Nat.divisors_prime_pow Nat.prime_two M)
    simpa using h
  rw [hcard] at hdiv
  have hpowNat : 2 ^ M ≤ x + 1 := by
    dsimp [M]
    exact Nat.pow_log_le_self 2 (by omega)
  have hpowCast : (((2 ^ M : ℕ) : ℝ)) ≤ (x : ℝ) + 1 := by
    exact_mod_cast hpowNat
  have hrpow :
      Real.rpow (((2 ^ M : ℕ) : ℝ)) (ε / 2) ≤
        Real.rpow ((x : ℝ) + 1) (ε / 2) :=
    Real.rpow_le_rpow (by positivity) hpowCast hhalf.le
  have hcPow := mul_le_mul_of_nonneg_left hrpow hC
  have hlinear :
      (((M + 1 : ℕ) : ℝ)) ≤
        C * Real.rpow ((x : ℝ) + 1) (ε / 2) :=
    hdiv.trans hcPow
  let L : ℝ := (((M + 1 : ℕ) : ℝ))
  let B : ℝ := (x : ℝ) + 1
  let P : ℝ := Real.rpow B (ε / 2)
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hlinear' : L ≤ C * P := by
    simpa [L, B, P] using hlinear
  have hsquare : L ^ 2 ≤ (C * P) ^ 2 :=
    pow_le_pow_left₀ hL0 hlinear' 2
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hP2 : P ^ 2 = Real.rpow B ε := by
    dsimp [P]
    rw [pow_two, ← Real.rpow_add hBpos]
    congr 1
    ring
  change L ^ 2 ≤ C ^ 2 * Real.rpow B ε
  calc
    L ^ 2 ≤ (C * P) ^ 2 := hsquare
    _ = C ^ 2 * P ^ 2 := by ring
    _ = C ^ 2 * Real.rpow B ε := by rw [hP2]

/-- **Worst-case closure still reaches the RH scale.**  Even when every
reciprocal channel is placed in the maximally bad midpoint phase and we pay a
full logarithmic overlap multiplicity, the resulting `sqrt x * log x` bound has
energy `x * log^2 x`, and the logarithm is absorbed into every positive epsilon. -/
theorem mertensEnergyBounded_of_pntSpacedWorstCasePrimeFlipClosure
    (h : PNTSpacedWorstCasePrimeFlipClosureStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hlog⟩ :=
    pntWorstCaseSquareOverlap_sq_le_subpolynomial hε
  refine ⟨C, hC, ?_⟩
  intro x
  let R : ℝ := (Nat.sqrt x : ℝ)
  let L : ℝ := (pntWorstCaseSquareOverlap x : ℝ)
  let B : ℝ := (x : ℝ) + 1
  have hnorm :=
    norm_mertensSummatory_le_sqrt_mul_log_of_pntWorstCaseClosure h x
  have hnorm' : ‖mertensSummatory x‖ ≤ R * L := by
    simpa [R, L] using hnorm
  have hnorm0 : 0 ≤ ‖mertensSummatory x‖ := norm_nonneg _
  have hRL0 : 0 ≤ R * L := by dsimp [R, L]; positivity
  have hsq : ‖mertensSummatory x‖ ^ 2 ≤ (R * L) ^ 2 := by
    nlinarith
  have hrootNat : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' x
  have hroot : R ^ 2 ≤ B := by
    dsimp [R, B]
    have hcast : (Nat.sqrt x : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hrootNat
    nlinarith
  have hover : L ^ 2 ≤ C * Real.rpow B ε := by
    simpa [L, B] using hlog x
  have hmul :
      R ^ 2 * L ^ 2 ≤ B * (C * Real.rpow B ε) := by
    exact mul_le_mul hroot hover (sq_nonneg L) (by dsimp [B]; positivity)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hone : Real.rpow B (1 : ℝ) = B := by
    exact (Real.rpow_eq_pow B (1 : ℝ)).trans (Real.rpow_one B)
  have hrpow :
      Real.rpow B (1 + ε) = B * Real.rpow B ε := by
    calc
      Real.rpow B (1 + ε) =
          Real.rpow B 1 * Real.rpow B ε :=
        Real.rpow_add hBpos 1 ε
      _ = B * Real.rpow B ε := by
        rw [hone]
  calc
    ‖mertensSummatory x‖ ^ 2 ≤ (R * L) ^ 2 := hsq
    _ = R ^ 2 * L ^ 2 := by ring
    _ ≤ B * (C * Real.rpow B ε) := hmul
    _ = C * (B * Real.rpow B ε) := by ring
    _ = C * Real.rpow B (1 + ε) := by
      exact congrArg (fun t : ℝ => C * t) hrpow.symm
    _ = C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
      congr 2
      dsimp [B]
      norm_num

end RHLean.Analysis