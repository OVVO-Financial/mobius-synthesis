import Mathlib
import RHLean.Arithmetic.TruncatedBooleanCubeSecondToggle
import RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms
import RHLean.Proof.SquareRootBornPostTailLowPrimeCollapse

/-!
# Canonical root charge for low-prime second-toggle instability

After one prime coordinate has reduced a downward-closed Boolean cube to its
first-failure frontier, a later ordered prime coordinate creates only two
possible corner types.

For a multiplicative cutoff `m <= B` and ordered pivots `a <= b`:

* if the `a` insertion already fails, then the `b` insertion fails
  automatically; this is the original first-failure frontier, not a new
  instability population;
* if both single insertions survive but the double insertion fails, all
  redundant inequalities collapse to the adjacent shell

    `b*m <= B < a*(b*m)`.

The natural charge of the second corner is therefore the still-admissible state
`b*m`, not the failed double child.  If `a` is selected canonically as the least
fresh prime that fails from `b*m`, then `a` is recoverable from the charge and
the cutoff.  The larger pivot `b` and the base `m` are recovered from the
canonical largest-prime factorization of `b*m`.  Hence these instability states
inject into `{1,...,B}` and have cardinality at most `B`.

The final section records a separate but complementary fact about the partially
filled crossing layer: a top-layer prime seat omitted by `j` cannot acquire any
fresh-prime descendant.  Thus the omitted packet remains the signed scalar
`j*M(K)` and should not be copied into the combinatorial instability frontier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Ordered second-toggle corner collapse -/

/-- Once the smaller ordered pivot fails, every larger pivot fails as well. -/
theorem squareRootLowPrimeOrderedSecondToggle_singleFailure_redundant
    {B m a b : ℕ} (hab : a ≤ b) (haFail : B < a * m) :
    B < b * m := by
  exact haFail.trans_le (Nat.mul_le_mul_right m hab)

/-- The genuine double-toggle corner is exactly one adjacent multiplicative
shell.  The base and smaller-single inequalities are forced by the surviving
larger-single state. -/
theorem squareRootLowPrimeOrderedSecondToggle_doubleCorner_iff_adjacentShell
    {B m a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    (m ≤ B ∧ a * m ≤ B ∧ b * m ≤ B ∧ B < a * (b * m)) ↔
      (b * m ≤ B ∧ B < a * (b * m)) := by
  constructor
  · rintro ⟨_hm, _ha, hbB, hdouble⟩
    exact ⟨hbB, hdouble⟩
  · rintro ⟨hbB, hdouble⟩
    have hm_bm : m ≤ b * m := Nat.le_mul_of_pos_left m hb
    have ham_bm : a * m ≤ b * m := Nat.mul_le_mul_right m hab
    exact ⟨hm_bm.trans hbB, ham_bm.trans hbB, hbB, hdouble⟩

/-! ## Canonical recovery of an instability charge -/

/-- Arithmetic data of one ordered double-toggle corner. -/
structure SquareRootLowPrimeDoubleToggleState where
  base : ℕ
  firstPivot : ℕ
  secondPivot : ℕ
  deriving DecidableEq

/-- Fresh primes which fail when applied to one still-admissible root state. -/
def squareRootLowPrimeFailurePrimeCandidates
    (K U B n : ℕ) : Finset ℕ :=
  (Finset.Ioc K U).filter fun p =>
    p.Prime ∧ (¬ p ∣ n) ∧ B < p * n

/-- Canonical instability owner: the least fresh prime whose extension leaves
`{1,...,B}`, with the irrelevant default `1` when no such prime exists. -/
def squareRootLowPrimeCanonicalFailurePrime
    (K U B n : ℕ) : ℕ :=
  if h : (squareRootLowPrimeFailurePrimeCandidates K U B n).Nonempty then
    (squareRootLowPrimeFailurePrimeCandidates K U B n).min' h
  else 1

/-- The surviving larger-pivot state is the root-scale instability charge. -/
def squareRootLowPrimeSecondToggleRootCharge
    (z : SquareRootLowPrimeDoubleToggleState) : ℕ :=
  z.base * z.secondPivot

/-- The canonical data required of a genuine ordered double-toggle corner. -/
def SquareRootLowPrimeCanonicalDoubleToggleData
    (K U B : ℕ) (z : SquareRootLowPrimeDoubleToggleState) : Prop :=
  0 < z.base ∧
    z.firstPivot.Prime ∧
    z.secondPivot.Prime ∧
    canonicalLargestPrimeFactor z.base < z.firstPivot ∧
    z.firstPivot < z.secondPivot ∧
    z.firstPivot = squareRootLowPrimeCanonicalFailurePrime K U B
      (squareRootLowPrimeSecondToggleRootCharge z) ∧
    squareRootLowPrimeSecondToggleRootCharge z ≤ B ∧
    B < z.firstPivot * squareRootLowPrimeSecondToggleRootCharge z

/-- The root charge canonically recovers the larger pivot and the old base. -/
theorem squareRootLowPrimeSecondToggleRootCharge_coordinates
    {K U B : ℕ} {z : SquareRootLowPrimeDoubleToggleState}
    (hz : SquareRootLowPrimeCanonicalDoubleToggleData K U B z) :
    canonicalLargestPrimeFactor
        (squareRootLowPrimeSecondToggleRootCharge z) = z.secondPivot ∧
      canonicalCofactor
        (squareRootLowPrimeSecondToggleRootCharge z) = z.base := by
  rcases hz with
    ⟨hbase, _hfirstPrime, hsecondPrime, hbaseFirst, hfirstSecond,
      _hcanonical, _hrootBound, _hfailure⟩
  have hbaseSecond :
      canonicalLargestPrimeFactor z.base < z.secondPivot :=
    hbaseFirst.trans hfirstSecond
  constructor
  · exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hbase hsecondPrime hbaseSecond
  · exact canonicalCofactor_mul_prime_eq_of_rough
      hbase hsecondPrime hbaseSecond

/-- **Global uniqueness of the second-toggle charge.**  Equality of the
still-admissible root state recovers the larger pivot and base by canonical
factorization, and then recovers the failed smaller pivot from the canonical
first-failure rule. -/
theorem squareRootLowPrimeSecondToggleRootCharge_injective
    {K U B : ℕ} {x y : SquareRootLowPrimeDoubleToggleState}
    (hx : SquareRootLowPrimeCanonicalDoubleToggleData K U B x)
    (hy : SquareRootLowPrimeCanonicalDoubleToggleData K U B y)
    (hcharge : squareRootLowPrimeSecondToggleRootCharge x =
      squareRootLowPrimeSecondToggleRootCharge y) :
    x = y := by
  have hxcoord := squareRootLowPrimeSecondToggleRootCharge_coordinates hx
  have hycoord := squareRootLowPrimeSecondToggleRootCharge_coordinates hy
  rcases hx with
    ⟨_hxbase, _hxfirstPrime, _hxsecondPrime, _hxrough, _hxpivots,
      hxcanonical, _hxbound, _hxfailure⟩
  rcases hy with
    ⟨_hybase, _hyfirstPrime, _hysecondPrime, _hyrough, _hypivots,
      hycanonical, _hybound, _hyfailure⟩
  have hsecond : x.secondPivot = y.secondPivot := by
    calc
      x.secondPivot = canonicalLargestPrimeFactor
          (squareRootLowPrimeSecondToggleRootCharge x) := hxcoord.1.symm
      _ = canonicalLargestPrimeFactor
          (squareRootLowPrimeSecondToggleRootCharge y) := by rw [hcharge]
      _ = y.secondPivot := hycoord.1
  have hbase : x.base = y.base := by
    calc
      x.base = canonicalCofactor
          (squareRootLowPrimeSecondToggleRootCharge x) := hxcoord.2.symm
      _ = canonicalCofactor
          (squareRootLowPrimeSecondToggleRootCharge y) := by rw [hcharge]
      _ = y.base := hycoord.2
  have hfirst : x.firstPivot = y.firstPivot := by
    calc
      x.firstPivot = squareRootLowPrimeCanonicalFailurePrime K U B
          (squareRootLowPrimeSecondToggleRootCharge x) := hxcanonical
      _ = squareRootLowPrimeCanonicalFailurePrime K U B
          (squareRootLowPrimeSecondToggleRootCharge y) := by rw [hcharge]
      _ = y.firstPivot := hycanonical.symm
  rcases x with ⟨xbase, xfirst, xsecond⟩
  rcases y with ⟨ybase, yfirst, ysecond⟩
  simp only at hbase hfirst hsecond
  subst ybase
  subst yfirst
  subst ysecond
  rfl

/-- Every canonical double-toggle charge lies in the root interval. -/
theorem squareRootLowPrimeSecondToggleRootCharge_mem_Icc
    {K U B : ℕ} {z : SquareRootLowPrimeDoubleToggleState}
    (hz : SquareRootLowPrimeCanonicalDoubleToggleData K U B z) :
    squareRootLowPrimeSecondToggleRootCharge z ∈ Finset.Icc 1 B := by
  rcases hz with
    ⟨hbase, _hfirstPrime, hsecondPrime, _hrough, _hpivots,
      _hcanonical, hbound, _hfailure⟩
  have hpos : 0 < squareRootLowPrimeSecondToggleRootCharge z :=
    Nat.mul_pos hbase hsecondPrime.pos
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos), hbound⟩

/-- **Root-scale cardinality theorem for canonical instability states.** -/
theorem squareRootLowPrimeCanonicalDoubleToggleStates_card_le_bound
    {K U B : ℕ} (S : Finset SquareRootLowPrimeDoubleToggleState)
    (hdata : ∀ z ∈ S,
      SquareRootLowPrimeCanonicalDoubleToggleData K U B z) :
    S.card ≤ B := by
  have hinj : Set.InjOn squareRootLowPrimeSecondToggleRootCharge (↑S) := by
    intro x hx y hy hxy
    exact squareRootLowPrimeSecondToggleRootCharge_injective
      (hdata x hx) (hdata y hy) hxy
  have hsubset :
      S.image squareRootLowPrimeSecondToggleRootCharge ⊆ Finset.Icc 1 B := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    exact squareRootLowPrimeSecondToggleRootCharge_mem_Icc (hdata z hz)
  calc
    S.card = (S.image squareRootLowPrimeSecondToggleRootCharge).card := by
      symm
      exact Finset.card_image_iff.mpr hinj
    _ ≤ (Finset.Icc 1 B).card := Finset.card_le_card hsubset
    _ = B := by simp

/-! ## The signed `j*M(K)` packet has no fresh descendants -/

/-- A prime seat in the omitted top portion of reciprocal layer `K` cannot
remain below the square endpoint after any positive cofactor is extended by a
fresh prime `p>K`. -/
theorem squareRootLowPrimeCrossingSeat_no_fresh_descendant
    {R K p a q : ℕ} (ha : 1 ≤ a) (hKp : K < p)
    (hqTop : squareRootEndpoint R / (K + 1) < q) :
    squareRootEndpoint R < (p * a) * q := by
  have hXlt : squareRootEndpoint R < (K + 1) * q := by
    have h := (Nat.div_lt_iff_lt_mul (Nat.succ_pos K)).1 hqTop
    simpa [Nat.mul_comm] using h
  have hKp' : K + 1 ≤ p := Nat.succ_le_iff.mpr hKp
  have hpa : p ≤ p * a := Nat.le_mul_of_pos_right p (by omega)
  have hKpa : K + 1 ≤ p * a := hKp'.trans hpa
  exact hXlt.trans_le (Nat.mul_le_mul_right q hKpa)

/-- Equivalent exclusion form used when constructing literal response atoms. -/
theorem squareRootLowPrimeCrossingSeat_not_fresh_response
    {R K p a q : ℕ} (ha : 1 ≤ a) (hKp : K < p)
    (hqTop : squareRootEndpoint R / (K + 1) < q) :
    ¬ (p * a) * q ≤ squareRootEndpoint R := by
  exact Nat.not_le_of_gt
    (squareRootLowPrimeCrossingSeat_no_fresh_descendant ha hKp hqTop)

end RHLean.Proof
