import Mathlib
import RHLean.Proof.CanonicalGapAncestryFlow
import RHLean.Proof.CanonicalSignedParent

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryBridge

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow

/-!
# Concrete canonical ancestry realization and termination

This module realizes the abstract ancestry flow from
`CanonicalGapAncestryFlow.lean` on the repository's native canonical
largest-prime factorization.

An index is a pair `(q,c)` of bounded natural numbers.  It is active precisely
when `q` is prime, `c` is positive and squarefree, `q` is coprime to `c`, and
every prime divisor of `c` is strictly below `q`.  Thus `q` is the distinguished
largest prime of the represented source `q*c`.

Transport-oriented sources (`c ≤ q`) are roots.  Smooth-oriented sources
(`q < c`) have the unique parent obtained by replacing `c` by its canonical
cofactor, i.e. by stripping the largest prime divisor of `c`.  The parent core
is strictly smaller and the Möbius sign reverses exactly.

Because the core decreases along every parent edge, the bounded flow is
nilpotent.  Consequently the renewal equation has a genuinely finite,
tail-free alternating expansion.  The last section pushes this exact identity
through the integer-square-root source clock and records the induced
square-block telescoping identity.

No analytic prefix-energy estimate is asserted.
-/

/-- Finite universe of candidate distinguished-prime/core pairs. -/
abbrev SourceIndex (B : ℕ) := Fin (B + 1) × Fin (B + 1)

/-- Distinguished-prime coordinate. -/
def sourcePrime {B : ℕ} (s : SourceIndex B) : ℕ := s.1.1

/-- Core coordinate. -/
def sourceCore {B : ℕ} (s : SourceIndex B) : ℕ := s.2.1

/-- Integer represented by a source index. -/
def sourceProduct {B : ℕ} (s : SourceIndex B) : ℕ :=
  sourcePrime s * sourceCore s

/-- Native arithmetic admissibility of a canonical source pair. -/
def CanonicalSourceData (q c : ℕ) : Prop :=
  q.Prime ∧ 1 ≤ c ∧ Squarefree c ∧ Nat.Coprime q c ∧
    ∀ p : ℕ, p.Prime → p ∣ c → p < q

/-- Admissibility of a bounded source index. -/
def SourceAdmissible {B : ℕ} (s : SourceIndex B) : Prop :=
  CanonicalSourceData (sourcePrime s) (sourceCore s)

/-- Smooth-oriented sources are precisely admissible sources whose core exceeds
its distinguished prime. -/
def SmoothOriented {B : ℕ} (s : SourceIndex B) : Prop :=
  SourceAdmissible s ∧ sourcePrime s < sourceCore s

/-- Transport-oriented sources are the complementary admissible roots. -/
def TransportOriented {B : ℕ} (s : SourceIndex B) : Prop :=
  SourceAdmissible s ∧ sourceCore s ≤ sourcePrime s

/-- The canonical cofactor is positive for every nontrivial integer. -/
theorem canonicalCofactor_pos {c : ℕ} (hc : 1 < c) :
    1 ≤ canonicalCofactor c := by
  have hprod := canonicalCofactor_mul_largestPrimeFactor hc
  by_contra h
  have hz : canonicalCofactor c = 0 := by omega
  rw [hz, zero_mul] at hprod
  omega

/-- Stripping the largest prime factor strictly decreases a nontrivial integer. -/
theorem canonicalCofactor_lt_self {c : ℕ} (hc : 1 < c) :
    canonicalCofactor c < c := by
  have hpos := canonicalCofactor_pos hc
  have hp2 := (canonicalLargestPrimeFactor_prime hc).two_le
  have hprod := canonicalCofactor_mul_largestPrimeFactor hc
  nlinarith

/-- The canonical cofactor divides the original integer. -/
theorem canonicalCofactor_dvd {c : ℕ} (hc : 1 < c) :
    canonicalCofactor c ∣ c :=
  ⟨canonicalLargestPrimeFactor c,
    (canonicalCofactor_mul_largestPrimeFactor hc).symm⟩

/-- The stripped parent remains an admissible core below the same distinguished
prime. -/
theorem canonicalParentData {q c : ℕ}
    (hdata : CanonicalSourceData q c) (hsmooth : q < c) :
    CanonicalSourceData q (canonicalCofactor c) := by
  rcases hdata with ⟨hq, _hcpos, hsq, hcop, hdom⟩
  have hcgt : 1 < c := lt_trans hq.one_lt hsmooth
  have hdiv := canonicalCofactor_dvd hcgt
  refine ⟨hq, canonicalCofactor_pos hcgt,
    squarefree_canonicalCofactor hsq hcgt,
    hcop.coprime_dvd_right hdiv, ?_⟩
  intro p hp hpc
  exact hdom p hp (hpc.trans hdiv)

/-- Concrete stripped parent in the same bounded universe. -/
noncomputable def parentIndex {B : ℕ} (s : SourceIndex B)
    (h : SmoothOriented s) : SourceIndex B :=
  (s.1,
    ⟨canonicalCofactor (sourceCore s),
      lt_trans
        (canonicalCofactor_lt_self (lt_trans h.1.1.one_lt h.2))
        s.2.2⟩)

@[simp] theorem sourcePrime_parentIndex {B : ℕ} (s : SourceIndex B)
    (h : SmoothOriented s) :
    sourcePrime (parentIndex s h) = sourcePrime s := rfl

@[simp] theorem sourceCore_parentIndex {B : ℕ} (s : SourceIndex B)
    (h : SmoothOriented s) :
    sourceCore (parentIndex s h) = canonicalCofactor (sourceCore s) := rfl

/-- The concrete parent is admissible. -/
theorem parentIndex_admissible {B : ℕ} (s : SourceIndex B)
    (h : SmoothOriented s) : SourceAdmissible (parentIndex s h) := by
  change CanonicalSourceData (sourcePrime s)
    (canonicalCofactor (sourceCore s))
  exact canonicalParentData h.1 h.2

/-- Deterministic parent map.  Nonadmissible candidates and transport-oriented
sources are roots; smooth-oriented sources strip their largest core prime. -/
noncomputable def sourceParent {B : ℕ} (s : SourceIndex B) :
    Option (SourceIndex B) := by
  classical
  exact if h : SmoothOriented s then some (parentIndex s h) else none

/-- A source has a parent exactly when it is smooth-oriented. -/
theorem sourceParent_isSome_iff {B : ℕ} (s : SourceIndex B) :
    (sourceParent s).isSome ↔ SmoothOriented s := by
  classical
  by_cases h : SmoothOriented s <;> simp [sourceParent, h]

/-- Roothood is the negation of smooth orientation. -/
theorem sourceParent_eq_none_iff {B : ℕ} (s : SourceIndex B) :
    sourceParent s = none ↔ ¬ SmoothOriented s := by
  classical
  by_cases h : SmoothOriented s <;> simp [sourceParent, h]

/-- On admissible sources, roothood is exactly transport orientation. -/
theorem sourceParent_eq_none_iff_transport {B : ℕ} (s : SourceIndex B)
    (hadm : SourceAdmissible s) :
    sourceParent s = none ↔ TransportOriented s := by
  rw [sourceParent_eq_none_iff]
  unfold SmoothOriented TransportOriented
  simp only [hadm, true_and]
  omega

/-- Every smooth-oriented source has its concrete parent. -/
theorem smoothSource_has_parent {B : ℕ} (s : SourceIndex B)
    (h : SmoothOriented s) :
    sourceParent s = some (parentIndex s h) := by
  classical
  simp [sourceParent, h]

/-- Every smooth-oriented source has exactly one parent index. -/
theorem smoothSource_parent_unique {B : ℕ} (s : SourceIndex B)
    (h : SmoothOriented s) :
    ∃! t : SourceIndex B, sourceParent s = some t := by
  refine ⟨parentIndex s h, smoothSource_has_parent s h, ?_⟩
  intro t ht
  rw [smoothSource_has_parent s h] at ht
  exact Option.some.inj ht.symm

/-! ## Exact Möbius sign reversal -/

/-- Möbius weight of an admissible source, and zero outside the canonical source
universe. -/
noncomputable def sourceWeight {B : ℕ} (s : SourceIndex B) : ℤ := by
  classical
  exact if SourceAdmissible s then (μ (sourceProduct s) : ℤ) else 0

/-- Evaluation of the weight on an admissible source. -/
theorem sourceWeight_of_admissible {B : ℕ} (s : SourceIndex B)
    (h : SourceAdmissible s) :
    sourceWeight s = (μ (sourceProduct s) : ℤ) := by
  classical
  simp [sourceWeight, h]

/-- Stripping the largest core prime reverses the Möbius sign of the represented
source. -/
theorem sourceMobius_parent {B : ℕ} (s : SourceIndex B)
    (h : SmoothOriented s) :
    (μ (sourceProduct s) : ℤ) =
      -(μ (sourceProduct (parentIndex s h)) : ℤ) := by
  rcases h.1 with ⟨hq, _hcpos, hsq, hcop, _hdom⟩
  have hcgt : 1 < sourceCore s := lt_trans hq.one_lt h.2
  have hparent := parentIndex_admissible s h
  have hparentCop :
      Nat.Coprime (sourcePrime s) (canonicalCofactor (sourceCore s)) := by
    simpa only [sourcePrime_parentIndex, sourceCore_parentIndex] using
      hparent.2.2.2.1
  have hchild := canonicalSignedParent_moebius hsq hcgt
  change (μ (sourcePrime s * sourceCore s) : ℤ) =
    -(μ (sourcePrime s * canonicalCofactor (sourceCore s)) : ℤ)
  calc
    (μ (sourcePrime s * sourceCore s) : ℤ) =
        μ (sourcePrime s) * μ (sourceCore s) :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    _ = μ (sourcePrime s) * (-μ (canonicalCofactor (sourceCore s))) := by
      rw [hchild]
    _ = -(μ (sourcePrime s) * μ (canonicalCofactor (sourceCore s))) := by
      ring
    _ = -(μ (sourcePrime s * canonicalCofactor (sourceCore s)) : ℤ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        hparentCop]

/-- Exact sign reversal of the concrete source weights. -/
theorem sourceWeight_parentIndex {B : ℕ} (s : SourceIndex B)
    (h : SmoothOriented s) :
    sourceWeight s = -sourceWeight (parentIndex s h) := by
  rw [sourceWeight_of_admissible s h.1,
    sourceWeight_of_admissible (parentIndex s h)
      (parentIndex_admissible s h)]
  exact sourceMobius_parent s h

/-- Pointwise sign reversal along every concrete parent edge. -/
theorem sourceWeight_signReversal {B : ℕ} (s t : SourceIndex B)
    (hparent : sourceParent s = some t) :
    sourceWeight s = -sourceWeight t := by
  classical
  by_cases h : SmoothOriented s
  · have ht : parentIndex s h = t := by
      simpa [sourceParent, h] using hparent
    subst t
    exact sourceWeight_parentIndex s h
  · simp [sourceParent, h] at hparent

/-- Concrete finite parent flow on the bounded canonical source universe. -/
noncomputable def boundedSourceFlow (B : ℕ) : ParentFlow (SourceIndex B) where
  parent := sourceParent
  weight := sourceWeight
  signReversal := sourceWeight_signReversal

/-! ## Exhaustive realization of native canonical sources -/

/-- Every prime divisor is at most the native canonical largest prime factor. -/
theorem prime_dvd_le_canonicalLargestPrimeFactor {m p : ℕ}
    (hm : 1 < m) (hp : p.Prime) (hpm : p ∣ m) :
    p ≤ canonicalLargestPrimeFactor m := by
  have hm0 : m ≠ 0 := by omega
  have hmem : p ∈ m.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero hm0).2 ⟨hp, hpm⟩
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hm]
  exact Finset.le_max' m.primeFactors p hmem

/-- Every squarefree `m > 1` produces admissible native source data
`(P⁺(m), m/P⁺(m))`. -/
theorem canonicalSourceData_of_squarefree {m : ℕ}
    (hsq : Squarefree m) (hm : 1 < m) :
    CanonicalSourceData (canonicalLargestPrimeFactor m)
      (canonicalCofactor m) := by
  have hprime := canonicalLargestPrimeFactor_prime hm
  have hcorepos : 1 ≤ canonicalCofactor m := canonicalCofactor_pos hm
  have hcop : Nat.Coprime (canonicalLargestPrimeFactor m)
      (canonicalCofactor m) :=
    hprime.coprime_iff_not_dvd.mpr
      (canonicalLargestPrimeFactor_not_dvd_cofactor hsq hm)
  refine ⟨hprime, hcorepos, squarefree_canonicalCofactor hsq hm, hcop, ?_⟩
  intro p hp hpc
  have hcoreDvd : canonicalCofactor m ∣ m := canonicalCofactor_dvd hm
  have hle := prime_dvd_le_canonicalLargestPrimeFactor hm hp
    (hpc.trans hcoreDvd)
  have hne : p ≠ canonicalLargestPrimeFactor m := by
    intro heq
    subst p
    exact (canonicalLargestPrimeFactor_not_dvd_cofactor hsq hm) hpc
  omega

/-- Every bounded squarefree source has a concrete bounded source index. -/
noncomputable def canonicalSourceIndex (B m : ℕ)
    (_hsq : Squarefree m) (hm : 1 < m) (hB : m ≤ B) : SourceIndex B := by
  have hqle : canonicalLargestPrimeFactor m ≤ m :=
    Nat.le_of_dvd (by omega) (canonicalLargestPrimeFactor_dvd hm)
  have hcle : canonicalCofactor m ≤ m :=
    Nat.le_of_dvd (by omega) (canonicalCofactor_dvd hm)
  exact
    (⟨canonicalLargestPrimeFactor m, by omega⟩,
      ⟨canonicalCofactor m, by omega⟩)

/-- The native index of a squarefree integer is admissible. -/
theorem canonicalSourceIndex_admissible {B m : ℕ}
    (hsq : Squarefree m) (hm : 1 < m) (hB : m ≤ B) :
    SourceAdmissible (canonicalSourceIndex B m hsq hm hB) := by
  change CanonicalSourceData (canonicalLargestPrimeFactor m)
    (canonicalCofactor m)
  exact canonicalSourceData_of_squarefree hsq hm

/-- The native source index reconstructs the original integer exactly. -/
theorem canonicalSourceIndex_product {B m : ℕ}
    (hsq : Squarefree m) (hm : 1 < m) (hB : m ≤ B) :
    sourceProduct (canonicalSourceIndex B m hsq hm hB) = m := by
  change canonicalLargestPrimeFactor m * canonicalCofactor m = m
  simpa [Nat.mul_comm] using canonicalCofactor_mul_largestPrimeFactor hm

/-- The native source index carries the original Möbius weight. -/
theorem canonicalSourceIndex_weight {B m : ℕ}
    (hsq : Squarefree m) (hm : 1 < m) (hB : m ≤ B) :
    sourceWeight (canonicalSourceIndex B m hsq hm hB) = (μ m : ℤ) := by
  rw [sourceWeight_of_admissible _
    (canonicalSourceIndex_admissible hsq hm hB),
    canonicalSourceIndex_product hsq hm hB]

/-- In any admissible pair, the displayed prime is the native canonical largest
prime factor of the represented product. -/
theorem sourcePrime_eq_canonicalLargestPrimeFactor {B : ℕ}
    (s : SourceIndex B) (h : SourceAdmissible s) :
    sourcePrime s = canonicalLargestPrimeFactor (sourceProduct s) := by
  rcases h with ⟨hq, hcpos, _hsq, _hcop, hdom⟩
  have hm : 1 < sourceProduct s := by
    unfold sourceProduct
    nlinarith [hq.two_le]
  have hqDvd : sourcePrime s ∣ sourceProduct s :=
    ⟨sourceCore s, rfl⟩
  have hqle := prime_dvd_le_canonicalLargestPrimeFactor hm hq hqDvd
  have hp := canonicalLargestPrimeFactor_prime hm
  have hpDvd := canonicalLargestPrimeFactor_dvd hm
  change canonicalLargestPrimeFactor (sourceProduct s) ∣
    sourcePrime s * sourceCore s at hpDvd
  have hple : canonicalLargestPrimeFactor (sourceProduct s) ≤ sourcePrime s := by
    rcases hp.dvd_mul.mp hpDvd with hpq | hpc
    · exact Nat.le_of_dvd hq.pos hpq
    · exact (hdom _ hp hpc).le
  exact Nat.le_antisymm hqle hple

/-- In any admissible pair, the displayed core is the native canonical cofactor
of the represented product. -/
theorem sourceCore_eq_canonicalCofactor {B : ℕ}
    (s : SourceIndex B) (h : SourceAdmissible s) :
    sourceCore s = canonicalCofactor (sourceProduct s) := by
  rcases h with ⟨hq, hcpos, hsq, hcop, hdom⟩
  have hm : 1 < sourceProduct s := by
    unfold sourceProduct
    nlinarith [hq.two_le]
  have hqeq := sourcePrime_eq_canonicalLargestPrimeFactor s
    ⟨hq, hcpos, hsq, hcop, hdom⟩
  have hcanon := canonicalCofactor_mul_largestPrimeFactor hm
  rw [← hqeq] at hcanon
  have hmul : canonicalCofactor (sourceProduct s) * sourcePrime s =
      sourceCore s * sourcePrime s := by
    calc
      canonicalCofactor (sourceProduct s) * sourcePrime s =
          sourceProduct s := hcanon
      _ = sourcePrime s * sourceCore s := rfl
      _ = sourceCore s * sourcePrime s := Nat.mul_comm _ _
  exact (Nat.mul_right_cancel hq.pos hmul).symm

/-- Admissible source products are collision-free. -/
theorem sourceProduct_injective_on_admissible {B : ℕ}
    {s t : SourceIndex B} (hs : SourceAdmissible s)
    (ht : SourceAdmissible t) (hprod : sourceProduct s = sourceProduct t) :
    s = t := by
  apply Prod.ext
  · apply Fin.ext
    change sourcePrime s = sourcePrime t
    calc
      sourcePrime s = canonicalLargestPrimeFactor (sourceProduct s) :=
        sourcePrime_eq_canonicalLargestPrimeFactor s hs
      _ = canonicalLargestPrimeFactor (sourceProduct t) := by rw [hprod]
      _ = sourcePrime t :=
        (sourcePrime_eq_canonicalLargestPrimeFactor t ht).symm
  · apply Fin.ext
    change sourceCore s = sourceCore t
    calc
      sourceCore s = canonicalCofactor (sourceProduct s) :=
        sourceCore_eq_canonicalCofactor s hs
      _ = canonicalCofactor (sourceProduct t) := by rw [hprod]
      _ = sourceCore t :=
        (sourceCore_eq_canonicalCofactor t ht).symm

/-- Every bounded squarefree `m > 1` has exactly one admissible source index. -/
theorem canonicalSourceIndex_existsUnique {B m : ℕ}
    (hsq : Squarefree m) (hm : 1 < m) (hB : m ≤ B) :
    ∃! s : SourceIndex B, SourceAdmissible s ∧ sourceProduct s = m := by
  let s₀ := canonicalSourceIndex B m hsq hm hB
  have hs₀ : SourceAdmissible s₀ :=
    canonicalSourceIndex_admissible hsq hm hB
  have hp₀ : sourceProduct s₀ = m :=
    canonicalSourceIndex_product hsq hm hB
  refine ⟨s₀, ⟨hs₀, hp₀⟩, ?_⟩
  intro s hs
  exact sourceProduct_injective_on_admissible hs.1 hs₀
    (hs.2.trans hp₀.symm)

/-! ## Ranked termination and tail-free renewal -/

/-- Finite parent flow with a strictly decreasing natural-number rank. -/
structure RankedParentFlow (ι : Type*) [Fintype ι] where
  flow : ParentFlow ι
  rank : ι → ℕ
  height : ℕ
  rank_lt_height : ∀ i, rank i < height
  parent_rank_lt : ∀ i p, flow.parent i = some p → rank p < rank i

namespace RankedParentFlow

/-- The alternating tail vanishes pointwise once its depth exceeds the rank. -/
theorem alternatingTail_apply_eq_zero_of_rank_lt
    {ι : Type*} [Fintype ι] (F : RankedParentFlow ι)
    (f : ι → ℤ) : ∀ depth i,
      F.rank i < depth →
        alternatingTail F.flow.successorOperator f depth i = 0 := by
  intro depth
  induction depth with
  | zero =>
      intro i hi
      omega
  | succ d ih =>
      intro i hi
      simp only [alternatingTail, Pi.neg_apply]
      cases hparent : F.flow.parent i with
      | none =>
          simp [ParentFlow.successorOperator, hparent]
      | some p =>
          have hrank := F.parent_rank_lt i p hparent
          have hpdepth : F.rank p < d := by omega
          have hzero := ih p hpdepth
          have hstep :
              F.flow.successorOperator
                  (alternatingTail F.flow.successorOperator f d) i =
                alternatingTail F.flow.successorOperator f d p := by
            simp [ParentFlow.successorOperator, hparent]
          rw [hstep, hzero]
          simp

/-- The entire terminal generation vanishes at the declared finite height. -/
theorem alternatingTail_eq_zero
    {ι : Type*} [Fintype ι] (F : RankedParentFlow ι) (f : ι → ℤ) :
    alternatingTail F.flow.successorOperator f F.height = 0 := by
  funext i
  exact alternatingTail_apply_eq_zero_of_rank_lt F f F.height i
    (F.rank_lt_height i)

/-- Exact tail-free finite alternating expansion. -/
theorem finite_alternating_expansion
    {ι : Type*} [Fintype ι] (F : RankedParentFlow ι) :
    F.flow.weight =
      alternatingPrefix F.flow.successorOperator F.flow.rootField F.height := by
  exact finite_renewal_identity F.flow.weight_eq_root_sub_successor
    (alternatingTail_eq_zero F F.flow.weight)

end RankedParentFlow

/-- The concrete flow is ranked by its core coordinate and terminates before
`B+1` generations. -/
noncomputable def boundedSourceRankedFlow (B : ℕ) :
    RankedParentFlow (SourceIndex B) where
  flow := boundedSourceFlow B
  rank := sourceCore
  height := B + 1
  rank_lt_height := fun s => s.2.2
  parent_rank_lt := by
    classical
    intro s t hparent
    by_cases h : SmoothOriented s
    · have ht : parentIndex s h = t := by
        simpa [boundedSourceFlow, sourceParent, h] using hparent
      subst t
      exact canonicalCofactor_lt_self (lt_trans h.1.1.one_lt h.2)
    · simp [boundedSourceFlow, sourceParent, h] at hparent

/-- Exact finite alternating expansion of every bounded canonical source weight
from the transport-oriented root field. -/
theorem boundedSource_weight_eq_finite_alternating (B : ℕ) :
    (boundedSourceFlow B).weight =
      alternatingPrefix (boundedSourceFlow B).successorOperator
        (boundedSourceFlow B).rootField (B + 1) := by
  exact RankedParentFlow.finite_alternating_expansion
    (boundedSourceRankedFlow B)

/-! ## Integer-square-root clock and square-block realization -/

/-- Native integer-square-root entry clock of a source. -/
def sourceClock (B : ℕ) (s : SourceIndex B) : ℕ :=
  Nat.sqrt (sourceProduct s)

/-- Full bounded canonical source prefix under the native entry clock. -/
def sourcePrefix (B x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x (boundedSourceFlow B).weight

/-- Literal finite-sum form of the clock-pushed source prefix. -/
theorem sourcePrefix_eq_sum (B x : ℕ) :
    sourcePrefix B x =
      ∑ s : SourceIndex B,
        if Nat.sqrt (sourceProduct s) ≤ x then sourceWeight s else 0 := by
  rfl

/-- Every represented squarefree integer retains its native integer-square-root
clock. -/
theorem canonicalSourceIndex_clock {B m : ℕ}
    (hsq : Squarefree m) (hm : 1 < m) (hB : m ≤ B) :
    sourceClock B (canonicalSourceIndex B m hsq hm hB) = Nat.sqrt m := by
  unfold sourceClock
  rw [canonicalSourceIndex_product hsq hm hB]

/-- The exact renewal identity survives the actual integer-square-root clock. -/
theorem sourcePrefix_renewal (B x : ℕ) :
    sourcePrefix B x =
      clockPushforward (sourceClock B) x (boundedSourceFlow B).rootField -
      clockPushforward (sourceClock B) x
        ((boundedSourceFlow B).successorOperator
          (boundedSourceFlow B).weight) := by
  unfold sourcePrefix
  exact (boundedSourceFlow B).clockPushforward_renewal (sourceClock B) x

/-- The clock-pushed source field is exactly the finite alternating successor
expansion, with no terminal tail. -/
theorem sourcePrefix_eq_finite_alternating (B x : ℕ) :
    sourcePrefix B x =
      clockPushforward (sourceClock B) x
        (alternatingPrefix (boundedSourceFlow B).successorOperator
          (boundedSourceFlow B).rootField (B + 1)) := by
  unfold sourcePrefix
  rw [boundedSource_weight_eq_finite_alternating B]

/-- Square-block increment induced by the exact clock-pushed source field. -/
def sourceBlockIncrement (B : ℕ) : ℕ → ℤ
  | 0 => sourcePrefix B 0
  | n + 1 => sourcePrefix B (n + 1) - sourcePrefix B n

/-- The induced block increments telescope exactly to the canonical source
prefix. -/
theorem sum_sourceBlockIncrement_eq_prefix (B x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), sourceBlockIncrement B n = sourcePrefix B x := by
  induction x with
  | zero => simp [sourceBlockIncrement]
  | succ x ih =>
      rw [Finset.sum_range_succ, ih]
      simp [sourceBlockIncrement]

/-- Final finite bridge: cumulative square-block source increments are exactly
the integer-square-root pushforward of the tail-free alternating successor
flow. -/
theorem sum_sourceBlockIncrement_eq_finite_alternating (B x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), sourceBlockIncrement B n =
      clockPushforward (sourceClock B) x
        (alternatingPrefix (boundedSourceFlow B).successorOperator
          (boundedSourceFlow B).rootField (B + 1)) := by
  rw [sum_sourceBlockIncrement_eq_prefix B x,
    sourcePrefix_eq_finite_alternating B x]

end CanonicalGapAncestryBridge

end RHLean.Proof