import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootLowPrimeHighResponseMonotone
import RHLean.Proof.SquareRootLowPrimeSquareDefect

/-!
# Reverse-square closure of the channel-tagged high carrier

The combined absolute-seat carrier hides an important monotonicity because the
born block changes the offset of the high seats.  Keep the high channel tagged
instead.  A high state is `(c,s)` with `c < R` and

```text
s < squareRootBornPostTailHighResponse R K j c.
```

If the upper-right corner `(q*p*c,s)` belongs to this carrier, then the lower-
left corner `(q*c,s)` also belongs.  The cofactor is a squarefree divisor of the
upper-right cofactor, its largest prime remains below the processed cutoff, and
the high-response multiplicity increases when the cofactor decreases.

Consequently the reverse four-corner defect is empty on the high carrier.  Any
high-channel desynchronization is forced into the ordinary outward/product
first-failure orientation; it is not an independent unstable population.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed high cofactors visible at a processed-prime cutoff. -/
def squareRootLowPrimeProcessedHighSignedCofactors
    (R P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R - 1)).filter fun c =>
    canonicalLargestPrimeFactor c ≤ P ∧ μ c ≠ 0

/-- Literal locally indexed high seats over one cofactor. -/
def squareRootLowPrimeProcessedHighSeatFiber
    (R K j c : ℕ) : Finset (ℕ × ℕ) :=
  ({c} : Finset ℕ).product
    (Finset.range (squareRootBornPostTailHighResponse R K j c))

/-- Complete channel-tagged high-seat population at cutoff `P`. -/
def squareRootLowPrimeProcessedHighSeatAtoms
    (R K j P : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeProcessedHighSignedCofactors R P).biUnion
    (squareRootLowPrimeProcessedHighSeatFiber R K j)

/-- Option-tagged form used by the generic processed-seat matching lemmas. -/
def squareRootLowPrimeProcessedHighSeatCarrier
    (R K j P : ℕ) : Finset (Option (ℕ × ℕ)) :=
  (squareRootLowPrimeProcessedHighSeatAtoms R K j P).image some

@[simp] theorem mem_squareRootLowPrimeProcessedHighSeatFiber
    {R K j c : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeProcessedHighSeatFiber R K j c ↔
      z.1 = c ∧
        z.2 < squareRootBornPostTailHighResponse R K j c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeProcessedHighSeatFiber, eq_comm, and_comm]

@[simp] theorem mem_squareRootLowPrimeProcessedHighSeatAtoms
    {R K j P : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeProcessedHighSeatAtoms R K j P ↔
      z.1 ∈ squareRootLowPrimeProcessedHighSignedCofactors R P ∧
        z.2 < squareRootBornPostTailHighResponse R K j z.1 := by
  unfold squareRootLowPrimeProcessedHighSeatAtoms
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
    have hdata := mem_squareRootLowPrimeProcessedHighSeatFiber.mp hzc
    rw [hdata.1]
    exact ⟨hc, hdata.2⟩
  · rintro ⟨hc, hs⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨z.1, hc, ?_⟩
    exact mem_squareRootLowPrimeProcessedHighSeatFiber.mpr ⟨rfl, hs⟩

@[simp] theorem some_mem_squareRootLowPrimeProcessedHighSeatCarrier
    {R K j P : ℕ} {z : ℕ × ℕ} :
    some z ∈ squareRootLowPrimeProcessedHighSeatCarrier R K j P ↔
      z ∈ squareRootLowPrimeProcessedHighSeatAtoms R K j P := by
  simp [squareRootLowPrimeProcessedHighSeatCarrier]

@[simp] theorem none_not_mem_squareRootLowPrimeProcessedHighSeatCarrier
    (R K j P : ℕ) :
    none ∉ squareRootLowPrimeProcessedHighSeatCarrier R K j P := by
  simp [squareRootLowPrimeProcessedHighSeatCarrier]

/-- **Arithmetic high-seat downward closure.** -/
theorem squareRootLowPrimeProcessedHighSeatAtoms_downward_square
    {R K j P p q : ℕ} {z : ℕ × ℕ}
    (hp : 0 < p) (hq : q.Prime)
    (hupper :
      (q * (p * z.1), z.2) ∈
        squareRootLowPrimeProcessedHighSeatAtoms R K j P) :
    (q * z.1, z.2) ∈
      squareRootLowPrimeProcessedHighSeatAtoms R K j P := by
  rcases mem_squareRootLowPrimeProcessedHighSeatAtoms.mp hupper with
    ⟨hcUpper, hsUpper⟩
  rcases Finset.mem_filter.mp hcUpper with ⟨hcRange, hlpfMu⟩
  rcases Finset.mem_Icc.mp hcRange with ⟨hcOne, hcTop⟩
  have hcPos : 0 < z.1 := by
    by_contra h
    have hcZero : z.1 = 0 := Nat.eq_zero_of_not_pos h
    rw [hcZero, mul_zero, mul_zero] at hcOne
    omega
  have hsmallPos : 0 < q * z.1 := Nat.mul_pos hq.pos hcPos
  have hsmallLe : q * z.1 ≤ q * (p * z.1) := by
    exact Nat.mul_le_mul_left q (Nat.le_mul_of_pos_left z.1 hp)
  have hsmallRange : q * z.1 ∈ Finset.Icc 1 (R - 1) :=
    Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hsmallPos), hsmallLe.trans hcTop⟩
  have hdiv : q * z.1 ∣ q * (p * z.1) := by
    refine ⟨p, ?_⟩
    ring
  have hsqUpper : Squarefree (q * (p * z.1)) :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hlpfMu.2
  have hsqSmall : Squarefree (q * z.1) :=
    hsqUpper.squarefree_of_dvd hdiv
  have hmuSmall : μ (q * z.1) ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsqSmall
  have hupperGt : 1 < q * (p * z.1) := by
    have hppos : 0 < p * z.1 := Nat.mul_pos hp hcPos
    nlinarith [hq.two_le, hppos]
  have hsmallGt : 1 < q * z.1 := by
    nlinarith [hq.two_le, hcPos]
  have hlpfSmallPrime :
      (canonicalLargestPrimeFactor (q * z.1)).Prime :=
    canonicalLargestPrimeFactor_prime hsmallGt
  have hlpfSmallDvd :
      canonicalLargestPrimeFactor (q * z.1) ∣ q * z.1 :=
    canonicalLargestPrimeFactor_dvd hsmallGt
  have hlpfSmallDvdUpper :
      canonicalLargestPrimeFactor (q * z.1) ∣ q * (p * z.1) :=
    dvd_trans hlpfSmallDvd hdiv
  have hlpfSmallLeUpper :
      canonicalLargestPrimeFactor (q * z.1) ≤
        canonicalLargestPrimeFactor (q * (p * z.1)) :=
    CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
      hupperGt hlpfSmallPrime hlpfSmallDvdUpper
  have hlpfSmallP : canonicalLargestPrimeFactor (q * z.1) ≤ P :=
    hlpfSmallLeUpper.trans hlpfMu.1
  have hsSmall :
      z.2 < squareRootBornPostTailHighResponse R K j (q * z.1) := by
    have hmono := squareRootBornPostTailHighResponse_antitone
      (R := R) (K := K) (j := j) hsmallPos hsmallLe
    exact hsUpper.trans_le hmono
  exact mem_squareRootLowPrimeProcessedHighSeatAtoms.mpr
    ⟨Finset.mem_filter.mpr
      ⟨hsmallRange, hlpfSmallP, hmuSmall⟩,
      hsSmall⟩

/-- Option-level form of high-seat downward square closure. -/
theorem squareRootLowPrimeProcessedHighSeatCarrier_downward_square
    {R K j P p q : ℕ} (hp : 0 < p) (hq : q.Prime)
    (x : Option (ℕ × ℕ))
    (hupper :
      squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x) ∈
        squareRootLowPrimeProcessedHighSeatCarrier R K j P) :
    squareRootLowPrimeProcessedSeatExtend q x ∈
      squareRootLowPrimeProcessedHighSeatCarrier R K j P := by
  rcases x with _ | z
  · simp [squareRootLowPrimeProcessedSeatExtend,
      squareRootLowPrimeProcessedHighSeatCarrier] at hupper
  · simp only [squareRootLowPrimeProcessedSeatExtend,
      some_mem_squareRootLowPrimeProcessedHighSeatCarrier] at hupper ⊢
    exact squareRootLowPrimeProcessedHighSeatAtoms_downward_square hp hq hupper

/-- **The reverse high-channel square defect is empty.** -/
theorem squareRootLowPrimeProcessedHighSeatReverseSquareDefect_eq_empty
    {R K j P p q : ℕ} (hp : 0 < p) (hq : q.Prime) :
    squareRootLowPrimeProcessedSeatReverseSquareDefect
      (squareRootLowPrimeProcessedHighSeatCarrier R K j P) p q = ∅ := by
  apply squareRootLowPrimeProcessedSeatReverseSquareDefect_eq_empty_of_downward
  intro x hupper
  exact squareRootLowPrimeProcessedHighSeatCarrier_downward_square
    hp hq x hupper

end RHLean.Proof
