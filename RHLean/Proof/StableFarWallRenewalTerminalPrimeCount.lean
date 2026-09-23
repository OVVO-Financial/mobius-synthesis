import RHLean.Proof.StableFarWallRenewalTerminal
import RHLean.Proof.StableFarWallOwnedCensus

/-!
# Prime-count form of terminal stable-far renewal multiplicity

For a fixed far prime `p`, put `A = floor(X_R / p)`.  Since `p > R`, one has
`A < R`.  The exact unit-terminal condition

  q*p <= X_R < q^2*p

is therefore equivalent to

  sqrt(A) < q <= A.

So the number of incoming renewal branches at the unit terminal `(1,p)` is
literally the number of primes in the reciprocal interval `(sqrt A, A]`.
This identifies the owner multiplicity left visible by `StableFarWallOwnedCensus`
with the prime-count gap already used elsewhere in the square-root architecture.
No estimate is taken.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- A far prime has reciprocal cofactor cutoff strictly below the root. -/
theorem farPrime_reciprocalCutoff_lt_root
    {R p : ℕ} (hR : 2 ≤ R) (hpFar : R + 8 ≤ p) :
    squareRootEndpoint R / p < R := by
  have hpPos : 0 < p := by omega
  apply (Nat.div_lt_iff_lt_mul hpPos).2
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    simpa [pow_two] using Nat.sub_lt hpos (by norm_num : 0 < 1)
  have hRp : R < p := by omega
  have hRRp : R * R < R * p := Nat.mul_lt_mul_of_pos_left hRp (by omega)
  exact hXlt.trans hRRp

/-- Pointwise form of the terminal-owner interval. -/
theorem mem_lowWheelFarPrimeUnitCrossingOwners_iff_reciprocalPrimeInterval
    {R p q : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpFar : R + 8 ≤ p) :
    q ∈ lowWheelFarPrimeUnitCrossingOwners R p ↔
      q ∈ (Finset.Ioc
        (Nat.sqrt (squareRootEndpoint R / p))
        (squareRootEndpoint R / p)).filter Nat.Prime := by
  have hpPos : 0 < p := hp.pos
  have hAlt : squareRootEndpoint R / p < R :=
    farPrime_reciprocalCutoff_lt_root hR hpFar
  constructor
  · intro hq
    rcases mem_lowWheelFarPrimeUnitCrossingOwners.mp hq with
      ⟨hqPrime, _hqR, hqp, hq2p⟩
    have hqLe : q ≤ squareRootEndpoint R / p :=
      (Nat.le_div_iff_mul_le hpPos).2 hqp
    have hAq2 : squareRootEndpoint R / p < q * q :=
      (Nat.div_lt_iff_lt_mul hpPos).2 (by
        simpa [Nat.mul_assoc] using hq2p)
    have hsqrt : Nat.sqrt (squareRootEndpoint R / p) < q := by
      apply (Nat.sqrt_lt').2
      simpa [pow_two] using hAq2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hsqrt, hqLe⟩, hqPrime⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hsqrt, hqLe⟩
    have hqR : q ≤ R - 1 := by omega
    have hqp : q * p ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hpPos).1 hqLe
    have hAq2 : squareRootEndpoint R / p < q ^ 2 :=
      (Nat.sqrt_lt').1 hsqrt
    have hq2p : squareRootEndpoint R < q * q * p := by
      have := (Nat.div_lt_iff_lt_mul hpPos).1 hAq2
      simpa [pow_two, Nat.mul_assoc] using this
    exact mem_lowWheelFarPrimeUnitCrossingOwners.mpr
      ⟨hqPrime, hqR, hqp, hq2p⟩

/-- **Terminal-owner interval.**  The incoming owners of the unit renewal state
at a fixed far prime are exactly the primes in `(sqrt(X_R/p), X_R/p]`. -/
theorem lowWheelFarPrimeUnitCrossingOwners_eq_reciprocalPrimeInterval
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpFar : R + 8 ≤ p) :
    lowWheelFarPrimeUnitCrossingOwners R p =
      (Finset.Ioc
        (Nat.sqrt (squareRootEndpoint R / p))
        (squareRootEndpoint R / p)).filter Nat.Prime := by
  ext q
  exact mem_lowWheelFarPrimeUnitCrossingOwners_iff_reciprocalPrimeInterval
    hR hp hpFar

/-- The terminal renewal multiplicity is exactly a prime-count gap.  The
additive form avoids any natural-subtraction truncation. -/
theorem unitCrossingOwner_card_add_primeCounting_sqrt_eq
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpFar : R + 8 ≤ p) :
    (lowWheelFarPrimeUnitCrossingOwners R p).card +
        Nat.primeCounting (Nat.sqrt (squareRootEndpoint R / p)) =
      Nat.primeCounting (squareRootEndpoint R / p) := by
  rw [lowWheelFarPrimeUnitCrossingOwners_eq_reciprocalPrimeInterval hR hp hpFar]
  exact primeCard_Ioc_add_primeCounting_eq (Nat.sqrt_le_self _)

/-! ## Sign structure of the fully cancelled far-wall coefficient

The owned-census layer has already removed one genuine strict-crossing
occurrence against every eligible unit far prime.  What remains is the integer
coefficient `lowWheelFarWallCancelledBoundaryCoefficient`.  Its negative part
is completely rigid: it is exactly one copy on either an unmatched top-half
unit prime or an old owned terminal product.  Everywhere else the coefficient
is the nonnegative extra-crossing multiplicity.

This is still before any norm or absolute value.  It rules out hidden negative
multiplicity in the final signed complement and gives the energy step a literal
"positive extra crossings minus multiplicity-one terminal boundary" normal
form.
-/

/-- A top-half unit prime cannot simultaneously be an old owned product. -/
theorem lowWheelFarPrimeTopUnitProduct_not_owned
    {R n : ℕ} (hn : n ∈ lowWheelFarPrimeTopUnitProducts R) :
    n ∉ lowWheelFrozenTopFarOwnedProducts R := by
  have hu : n ∈ lowWheelFarPrimeUnitProducts R :=
    (Finset.mem_filter.mp hn).1
  intro ho
  exact (Finset.disjoint_left.mp
    (lowWheelFarPrimeUnitProducts_disjoint_owned R)) hu ho

/-- On an unmatched top-half unit prime the cancelled coefficient is exactly
`-1`: no crossing can reach it and the single terminal copy remains. -/
theorem lowWheelFarWallCancelledBoundaryCoefficient_eq_neg_one_of_topUnit
    {R n : ℕ} (hn : n ∈ lowWheelFarPrimeTopUnitProducts R) :
    lowWheelFarWallCancelledBoundaryCoefficient R n = -1 := by
  have hcross := lowWheelFarWallCrossingMultiplicity_eq_zero_of_topUnit hn
  have howned := lowWheelFarPrimeTopUnitProduct_not_owned hn
  have hnotPaired : n ∉ lowWheelFarPrimePairedUnitProducts R := by
    intro hp
    have hlow := (Finset.mem_filter.mp hp).2
    have htop := (Finset.mem_filter.mp hn).2
    omega
  unfold lowWheelFarWallCancelledBoundaryCoefficient
    lowWheelFarWallExtraCrossingCoefficient
  simp [hcross, hn, howned, hnotPaired]

/-- On an old owned product the cancelled coefficient is exactly `-1`: owned
products have no strict-crossing occurrence and are disjoint from all unit
prime products. -/
theorem lowWheelFarWallCancelledBoundaryCoefficient_eq_neg_one_of_owned
    {R n : ℕ} (hn : n ∈ lowWheelFrozenTopFarOwnedProducts R) :
    lowWheelFarWallCancelledBoundaryCoefficient R n = -1 := by
  have hcross := lowWheelFarWallCrossingMultiplicity_eq_zero_of_owned hn
  have hnotUnit : n ∉ lowWheelFarPrimeUnitProducts R := by
    intro hu
    exact (Finset.disjoint_left.mp
      (lowWheelFarPrimeUnitProducts_disjoint_owned R)) hu hn
  have hnotPaired : n ∉ lowWheelFarPrimePairedUnitProducts R := by
    intro hp
    exact hnotUnit (Finset.mem_filter.mp hp).1
  have hnotTop : n ∉ lowWheelFarPrimeTopUnitProducts R := by
    intro ht
    exact hnotUnit (Finset.mem_filter.mp ht).1
  unfold lowWheelFarWallCancelledBoundaryCoefficient
    lowWheelFarWallExtraCrossingCoefficient
  simp [hcross, hn, hnotPaired, hnotTop]

/-- Away from the two terminal populations the cancelled coefficient is exactly
the nonnegative extra-crossing coefficient. -/
theorem lowWheelFarWallCancelledBoundaryCoefficient_eq_extra_of_not_terminal
    {R n : ℕ}
    (htop : n ∉ lowWheelFarPrimeTopUnitProducts R)
    (howned : n ∉ lowWheelFrozenTopFarOwnedProducts R) :
    lowWheelFarWallCancelledBoundaryCoefficient R n =
      lowWheelFarWallExtraCrossingCoefficient R n := by
  simp [lowWheelFarWallCancelledBoundaryCoefficient, htop, howned]

/-- Hence the cancelled coefficient is nonnegative everywhere off the exact
terminal support. -/
theorem lowWheelFarWallCancelledBoundaryCoefficient_nonneg_of_not_terminal
    {R n : ℕ}
    (htop : n ∉ lowWheelFarPrimeTopUnitProducts R)
    (howned : n ∉ lowWheelFrozenTopFarOwnedProducts R) :
    0 ≤ lowWheelFarWallCancelledBoundaryCoefficient R n := by
  rw [lowWheelFarWallCancelledBoundaryCoefficient_eq_extra_of_not_terminal
    htop howned]
  exact lowWheelFarWallExtraCrossingCoefficient_nonneg R n

/-- Globally, the fully cancelled coefficient can never be less than `-1`. -/
theorem lowWheelFarWallCancelledBoundaryCoefficient_neg_one_le
    (R n : ℕ) :
    (-1 : ℤ) ≤ lowWheelFarWallCancelledBoundaryCoefficient R n := by
  by_cases htop : n ∈ lowWheelFarPrimeTopUnitProducts R
  · rw [lowWheelFarWallCancelledBoundaryCoefficient_eq_neg_one_of_topUnit htop]
  · by_cases howned : n ∈ lowWheelFrozenTopFarOwnedProducts R
    · rw [lowWheelFarWallCancelledBoundaryCoefficient_eq_neg_one_of_owned howned]
    · have hnonneg :=
        lowWheelFarWallCancelledBoundaryCoefficient_nonneg_of_not_terminal
          htop howned
      omega

/-- Exact negative-support classification: negativity occurs if and only if the
integer is one of the two multiplicity-one terminal populations. -/
theorem lowWheelFarWallCancelledBoundaryCoefficient_lt_zero_iff
    {R n : ℕ} :
    lowWheelFarWallCancelledBoundaryCoefficient R n < 0 ↔
      n ∈ lowWheelFarPrimeTopUnitProducts R ∨
        n ∈ lowWheelFrozenTopFarOwnedProducts R := by
  constructor
  · intro hneg
    by_cases htop : n ∈ lowWheelFarPrimeTopUnitProducts R
    · exact Or.inl htop
    · by_cases howned : n ∈ lowWheelFrozenTopFarOwnedProducts R
      · exact Or.inr howned
      · have hnonneg :=
          lowWheelFarWallCancelledBoundaryCoefficient_nonneg_of_not_terminal
            htop howned
        omega
  · rintro (htop | howned)
    · rw [lowWheelFarWallCancelledBoundaryCoefficient_eq_neg_one_of_topUnit htop]
      norm_num
    · rw [lowWheelFarWallCancelledBoundaryCoefficient_eq_neg_one_of_owned howned]
      norm_num

end RHLean.Proof