import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootLowPrimeProcessedSeatMatching

/-!
# Displacement diamonds for the low-prime sequential frontier

This module attacks the unstable-pivot population directly.

Fresh-prime extensions commute.  Hence two distinct prime coordinates `q < p`
form a literal four-corner square on every non-head processed seat:

```text
x              --p-->  p*x
| q                      | q
v                        v
q*x            --p-->  p*q*x.
```

Suppose the `q`-step removes one lower/upper pair, while the corresponding
`p`-translate survives that same step.  Then the opposite corner of the square
cannot still belong to the carrier: otherwise the translated `q`-edge would
also have been removed.  Thus an unstable pivot is not a new independent
residual.  It produces an actual missing support corner.

Moreover, for a fixed displaced pivot, distinct later primes produce distinct
missing corners.  This is the injective mechanism needed to charge all pivot
instabilities to the already-isolated born/high cutoff and first-failure
boundaries rather than once per prime.

The final section records the arithmetic orientation of the same extension
operation.  A genuine Euler move adds a prime which dominates every prime
factor already present in the cofactor.  The added prime is then the canonical
largest prime of the child, stripping it recovers the unique parent, and the
Mobius sign reverses.  This is structural only: no quantitative bound on the
terminal frontier is inferred without a separate disjoint owner-slice
partition.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

open CanonicalGapAncestryBridge
open CanonicalGapAncestryFlow

attribute [local instance] Classical.propDecidable

/-- Fresh-prime extensions commute on the processed seat carrier. -/
theorem squareRootLowPrimeProcessedSeatExtend_comm
    (p q : ℕ) (x : Option (ℕ × ℕ)) :
    squareRootLowPrimeProcessedSeatExtend p
        (squareRootLowPrimeProcessedSeatExtend q x) =
      squareRootLowPrimeProcessedSeatExtend q
        (squareRootLowPrimeProcessedSeatExtend p x) := by
  rcases x with _ | z
  · rfl
  · simp only [squareRootLowPrimeProcessedSeatExtend, Option.some.injEq]
    apply Prod.ext
    · dsimp
      ac_rfl
    · rfl

/-- Extending a non-head state keeps it non-head. -/
theorem squareRootLowPrimeProcessedSeatExtend_ne_none
    {p : ℕ} {x : Option (ℕ × ℕ)} (hx : x ≠ none) :
    squareRootLowPrimeProcessedSeatExtend p x ≠ none := by
  rcases x with _ | z
  · exact (hx rfl).elim
  · simp [squareRootLowPrimeProcessedSeatExtend]

/-- Cofactor projection of a non-head extension. -/
theorem squareRootLowPrimeProcessedStateCofactor_extend
    {p : ℕ} {x : Option (ℕ × ℕ)} (hx : x ≠ none) :
    squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p x) =
      p * squareRootLowPrimeProcessedStateCofactor x := by
  rcases x with _ | z
  · exact (hx rfl).elim
  · rfl

/-- Freshness is preserved when extending by a distinct prime. -/
theorem squareRootLowPrimeProcessedSeatExtend_fresh_of_distinct
    {p q : ℕ} {x : Option (ℕ × ℕ)}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hx : x ≠ none)
    (hfresh : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor x) :
    ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
      (squareRootLowPrimeProcessedSeatExtend p x) := by
  rw [squareRootLowPrimeProcessedStateCofactor_extend hx]
  intro hdiv
  rcases hq.dvd_mul.mp hdiv with hqp | hqc
  · have hEq : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    exact hpq hEq.symm
  · exact hfresh hqc

/-- **Lower-endpoint displacement forces a missing top corner.**

If `x` is removed as the lower endpoint of a `q`-edge but its `p`-translate
survives the `q`-step, the `p*q` corner was not in the carrier. -/
theorem squareRootLowPrimeProcessedSeat_lowerDisplacement_forces_top_missing
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S q)
    (hpxFrontier :
      squareRootLowPrimeProcessedSeatExtend p x ∈
        squareRootLowPrimeProcessedSeatFrontierStep S q) :
    squareRootLowPrimeProcessedSeatExtend q
        (squareRootLowPrimeProcessedSeatExtend p x) ∉ S := by
  intro htop
  have hxData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower
  have hpxData := Finset.mem_sdiff.mp hpxFrontier
  have hpxNone : squareRootLowPrimeProcessedSeatExtend p x ≠ none :=
    squareRootLowPrimeProcessedSeatExtend_ne_none hxData.2.1
  have hqFresh :
      ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p x) :=
    squareRootLowPrimeProcessedSeatExtend_fresh_of_distinct
      hp hq hpq hxData.2.1 hxData.2.2.1
  have htranslatedLower :
      squareRootLowPrimeProcessedSeatExtend p x ∈
        squareRootLowPrimeProcessedSeatPairLower S q :=
    mem_squareRootLowPrimeProcessedSeatPairLower.mpr
      ⟨hpxData.1, hpxNone, hqFresh, htop⟩
  exact hpxData.2
    (Finset.mem_union.mpr (Or.inl htranslatedLower))

/-- **Upper-endpoint displacement forces a missing lower corner.**

If `q*x` is the upper endpoint of a removed `q`-edge but `p*q*x` survives the
same step, the opposite lower corner `p*x` was not in the carrier. -/
theorem squareRootLowPrimeProcessedSeat_upperDisplacement_forces_bottom_missing
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S q)
    (hpqxFrontier :
      squareRootLowPrimeProcessedSeatExtend p
          (squareRootLowPrimeProcessedSeatExtend q x) ∈
        squareRootLowPrimeProcessedSeatFrontierStep S q) :
    squareRootLowPrimeProcessedSeatExtend p x ∉ S := by
  intro hbottom
  have hxData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower
  have htopData := Finset.mem_sdiff.mp hpqxFrontier
  have hbottomNone :
      squareRootLowPrimeProcessedSeatExtend p x ≠ none :=
    squareRootLowPrimeProcessedSeatExtend_ne_none hxData.2.1
  have hqFresh :
      ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p x) :=
    squareRootLowPrimeProcessedSeatExtend_fresh_of_distinct
      hp hq hpq hxData.2.1 hxData.2.2.1
  have htranslatedLower :
      squareRootLowPrimeProcessedSeatExtend p x ∈
        squareRootLowPrimeProcessedSeatPairLower S q :=
    mem_squareRootLowPrimeProcessedSeatPairLower.mpr
      ⟨hbottom, hbottomNone, hqFresh, by
        simpa [squareRootLowPrimeProcessedSeatExtend_comm] using htopData.1⟩
  have htranslatedUpper :
      squareRootLowPrimeProcessedSeatExtend p
          (squareRootLowPrimeProcessedSeatExtend q x) ∈
        squareRootLowPrimeProcessedSeatPairUpper S q := by
    unfold squareRootLowPrimeProcessedSeatPairUpper
    apply Finset.mem_image.mpr
    refine ⟨squareRootLowPrimeProcessedSeatExtend p x,
      htranslatedLower, ?_⟩
    exact (squareRootLowPrimeProcessedSeatExtend_comm p q x).symm
  exact htopData.2
    (Finset.mem_union.mpr (Or.inr htranslatedUpper))

/-- For a fixed nonzero seat cofactor, distinct extension primes give distinct
translated states. -/
theorem squareRootLowPrimeProcessedSeatExtend_prime_injective
    {x : Option (ℕ × ℕ)}
    (hx : x ≠ none)
    (hc : 0 < squareRootLowPrimeProcessedStateCofactor x) :
    Function.Injective
      (fun p => squareRootLowPrimeProcessedSeatExtend p x) := by
  intro p r hpr
  rcases x with _ | z
  · exact (hx rfl).elim
  · simp only [squareRootLowPrimeProcessedSeatExtend,
      Option.some.injEq, Prod.mk.injEq] at hpr
    have hmul : p * z.1 = r * z.1 := hpr.1
    exact Nat.mul_right_cancel hc hmul

/-- **No recurrent lower displacement without distinct missing corners.**
For a fixed removed lower pivot and fixed earlier coordinate `q`, the top
missing-corner assignment is injective in the later prime `p`. -/
theorem squareRootLowPrimeProcessedSeat_missingTopCorner_prime_injective
    {q : ℕ} {x : Option (ℕ × ℕ)}
    (hq : 0 < q) (hx : x ≠ none)
    (hc : 0 < squareRootLowPrimeProcessedStateCofactor x) :
    Function.Injective
      (fun p =>
        squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x)) := by
  intro p r hpr
  rcases x with _ | z
  · exact (hx rfl).elim
  · simp only [squareRootLowPrimeProcessedSeatExtend,
      Option.some.injEq, Prod.mk.injEq] at hpr
    have houter : q * (p * z.1) = q * (r * z.1) := hpr.1
    have hinner : p * z.1 = r * z.1 :=
      Nat.mul_left_cancel hq houter
    exact Nat.mul_right_cancel hc hinner

/-- The lower missing-corner assignment from upper displacement is likewise
injective in the later prime. -/
theorem squareRootLowPrimeProcessedSeat_missingBottomCorner_prime_injective
    {x : Option (ℕ × ℕ)}
    (hx : x ≠ none)
    (hc : 0 < squareRootLowPrimeProcessedStateCofactor x) :
    Function.Injective
      (fun p => squareRootLowPrimeProcessedSeatExtend p x) :=
  squareRootLowPrimeProcessedSeatExtend_prime_injective hx hc

/-! ## Canonically oriented Euler ancestry -/

/-- Arithmetic data for one genuine forward Euler move `c -> c*p`. -/
structure SquareRootLowPrimeEulerStepData (c p n : ℕ) : Prop where
  source : CanonicalSourceData p c
  child_eq : n = c * p

/-- Canonical source data is exactly the largest-prime orientation needed by a
forward Euler move. -/
theorem squareRootLowPrimeEulerStep_coreMaxPrime
    {c p n : ℕ} (h : SquareRootLowPrimeEulerStepData c p n) :
    CoreMaxPrime p c := by
  exact ⟨h.source.1, h.source.2.2.2.1,
    fun r hr hrc => h.source.2.2.2.2 r hr hrc⟩

/-- A genuine fresh-prime child is owned by the prime just adjoined. -/
theorem squareRootLowPrimeEulerStep_canonicalLargestPrimeFactor
    {c p n : ℕ} (h : SquareRootLowPrimeEulerStepData c p n) :
    canonicalLargestPrimeFactor n = p := by
  have hp : p.Prime := h.source.1
  have hcpos : 1 ≤ c := h.source.2.1
  have hple : p ≤ c * p := by
    calc
      p = 1 * p := by simp
      _ ≤ c * p := Nat.mul_le_mul_right p hcpos
  have hcle : c ≤ c * p := by
    calc
      c = c * 1 := by simp
      _ ≤ c * p := Nat.mul_le_mul_left c hp.pos
  let s : SourceIndex (c * p) :=
    (⟨p, by omega⟩, ⟨c, by omega⟩)
  have hs : SourceAdmissible s := by
    change CanonicalSourceData p c
    exact h.source
  have howner := sourcePrime_eq_canonicalLargestPrimeFactor s hs
  have howner' : p = canonicalLargestPrimeFactor (p * c) := by
    simpa [s, sourcePrime, sourceProduct, sourceCore] using howner
  simpa [h.child_eq, Nat.mul_comm] using howner'.symm

/-- Stripping the canonical largest prime of a fresh child recovers the unique
parent cofactor. -/
theorem squareRootLowPrimeEulerStep_canonicalCofactor
    {c p n : ℕ} (h : SquareRootLowPrimeEulerStepData c p n) :
    canonicalCofactor n = c := by
  have hp : p.Prime := h.source.1
  have hcpos : 1 ≤ c := h.source.2.1
  have hple : p ≤ c * p := by
    calc
      p = 1 * p := by simp
      _ ≤ c * p := Nat.mul_le_mul_right p hcpos
  have hcle : c ≤ c * p := by
    calc
      c = c * 1 := by simp
      _ ≤ c * p := Nat.mul_le_mul_left c hp.pos
  let s : SourceIndex (c * p) :=
    (⟨p, by omega⟩, ⟨c, by omega⟩)
  have hs : SourceAdmissible s := by
    change CanonicalSourceData p c
    exact h.source
  have hcore := sourceCore_eq_canonicalCofactor s hs
  have hcore' : c = canonicalCofactor (p * c) := by
    simpa [s, sourcePrime, sourceProduct, sourceCore] using hcore
  simpa [h.child_eq, Nat.mul_comm] using hcore'.symm

/-- Exact Mobius sign reversal along one genuine forward Euler edge. -/
theorem squareRootLowPrimeEulerStep_moebius
    {c p n : ℕ} (h : SquareRootLowPrimeEulerStepData c p n) :
    (μ n : ℤ) = -(μ c : ℤ) := by
  rw [h.child_eq]
  have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    h.source.2.2.2.1.symm
  rw [hmul, ArithmeticFunction.moebius_apply_prime h.source.1]
  ring

/-- The child determines its fresh owner prime and its parent uniquely. -/
theorem squareRootLowPrimeEulerStep_unique
    {c c' p p' n : ℕ}
    (h : SquareRootLowPrimeEulerStepData c p n)
    (h' : SquareRootLowPrimeEulerStepData c' p' n) :
    c = c' ∧ p = p' := by
  have hprod : c * p = c' * p' := by
    calc
      c * p = n := h.child_eq.symm
      _ = c' * p' := h'.child_eq
  have hp : p = p' :=
    coreMaxPrime_unique_factor
      (squareRootLowPrimeEulerStep_coreMaxPrime h)
      (squareRootLowPrimeEulerStep_coreMaxPrime h') hprod
  subst p'
  have hc : c = c' :=
    Nat.mul_right_cancel h.source.1.pos hprod
  exact ⟨hc, rfl⟩

/-- Successive genuine Euler moves have strictly increasing owner primes. -/
theorem squareRootLowPrimeEulerStep_owner_strictMono
    {c p n q m : ℕ}
    (h₁ : SquareRootLowPrimeEulerStepData c p n)
    (h₂ : SquareRootLowPrimeEulerStepData n q m) :
    p < q := by
  have hpDiv : p ∣ n := by
    rw [h₁.child_eq]
    exact ⟨c, by simp [Nat.mul_comm]⟩
  exact h₂.source.2.2.2.2 p h₁.source.1 hpDiv

/-- Hence a two-step forward Euler path cannot return to its starting owner
coordinate. -/
theorem squareRootLowPrimeEulerStep_no_owner_backtrack
    {c p n q m : ℕ}
    (h₁ : SquareRootLowPrimeEulerStepData c p n)
    (h₂ : SquareRootLowPrimeEulerStepData n q m) :
    q ≠ p := by
  exact ne_of_gt (squareRootLowPrimeEulerStep_owner_strictMono h₁ h₂)

/-- Two successive genuine Euler moves restore the original Mobius sign. -/
theorem squareRootLowPrimeEulerStep_twoStep_moebius
    {c p n q m : ℕ}
    (h₁ : SquareRootLowPrimeEulerStepData c p n)
    (h₂ : SquareRootLowPrimeEulerStepData n q m) :
    (μ m : ℤ) = μ c := by
  rw [squareRootLowPrimeEulerStep_moebius h₂,
    squareRootLowPrimeEulerStep_moebius h₁]
  ring

/-- A canonically oriented processed-seat extension is literally one Euler
step on the cofactor coordinate.  This is the bridge between the commuting seat
operation and the unique arithmetic parent/owner. -/
theorem squareRootLowPrimeProcessedSeatExtend_eulerStepData
    {p : ℕ} {x : Option (ℕ × ℕ)}
    (hx : x ≠ none)
    (hsource : CanonicalSourceData p
      (squareRootLowPrimeProcessedStateCofactor x)) :
    SquareRootLowPrimeEulerStepData
      (squareRootLowPrimeProcessedStateCofactor x) p
      (squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p x)) := by
  refine ⟨hsource, ?_⟩
  rw [squareRootLowPrimeProcessedStateCofactor_extend hx]
  exact Nat.mul_comm _ _

end RHLean.Proof
