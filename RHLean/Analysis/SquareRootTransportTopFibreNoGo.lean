import Mathlib
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm

/-!
# The transport transform carries an exactly same-sign top block

The zero-free `T` sector has an exact uniform-kernel law, and
`LargePrimeTTransport` proves its stationary Green--Kubo identity `V_T(K) = 3*K`.
`DeterministicTGreenKuboComparison` already records that this identity may not be
substituted for the diagonal of an actual deterministic Möbius trajectory: along
an arbitrary zero-free trajectory the active observable only satisfies the
pointwise bound `9`, and the positive-lag correlation is an open arithmetic
input, isolated there as a named `Prop`.

This module records the separate, purely arithmetic obstruction to transporting
any independence law onto the *square-prefix* population `T_R`.  It shows that
the hyperbolic cutoff `c*q <= R^2 - 1` does not cut the population into complete
cancelling orbits plus a bounded boundary.  It selects, at the top of the prime
range, a block on which there is no cancellation whatsoever.

Concretely: for a prime `q` with `X/2 < q <= X`, the reciprocal cutoff is
`floor(X/q) = 1`, so the only surviving cofactor is `c = 1` and the fibre
contributes exactly `mu(1) = 1`.  Every such prime contributes `+1` and none
contributes anything else, so the block over that prime range is *equal to its
own cardinality*:

```text
sum_{X/2 < q <= X, q prime} Rough(q, floor(X/q)) = #{q prime : X/2 < q <= X}.
```

These are exactly the sources `m = q`, a single prime, all of which carry
`mu(m) = -1`.  Parity gives no cancellation here because the number of prime
factors is constant on the block.  By Bertrand the block is nonempty, and it sits
inside the transport term as a summand of the exact splitting proved below.

The consequence for the transfer programme is structural: any statement that the
square-prefix transport population inherits a CRT product law up to a bounded
boundary defect must account for a same-sign block of size `pi(X) - pi(X/2)`,
which is not bounded.  This module proves the block is same-sign and nonempty; it
proves no lower bound on its growth and makes no claim about `T_R` itself beyond
the exact splitting.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- At the top of the prime range the reciprocal cutoff collapses to `1`. -/
theorem squareRootEndpoint_div_eq_one_of_top_fibre
    {X q : ℕ} (hq : 0 < q) (hlow : X < 2 * q) (hhigh : q ≤ X) :
    X / q = 1 := by
  have h1 : 1 ≤ X / q := (Nat.le_div_iff_mul_le hq).2 (by simpa using hhigh)
  have h2 : X / q < 2 := (Nat.div_lt_iff_lt_mul hq).2 (by simpa [Nat.mul_comm] using hlow)
  omega

/-- The rough Möbius prefix at cutoff `1` is the unit source alone. -/
theorem roughCofactorMobiusPrefixMass_one {q : ℕ} (hq : 2 ≤ q) :
    roughCofactorMobiusPrefixMass q 1 = 1 := by
  have hone : canonicalLargestPrimeFactor 1 = 1 := by
    have hnot : ¬ (1 : ℕ) < 1 := by omega
    unfold canonicalLargestPrimeFactor
    rw [dif_neg hnot]
  have hmu : canonicalMoebiusWeight 1 = 1 := by
    unfold canonicalMoebiusWeight
    rw [ArithmeticFunction.moebius_apply_one, Int.cast_one]
  unfold roughCofactorMobiusPrefixMass
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  rw [Finset.sum_singleton, hone, if_pos (by omega), hmu]

/-- The primes at the top of the square-prefix range: those above half the
endpoint.  Every one of these has reciprocal cutoff exactly `1`. -/
def squareRootTopFibrePrimes (R : ℕ) : Finset ℕ :=
  (Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R)).filter Nat.Prime

/-- The block of the reciprocal transform carried by the top prime range. -/
def squareRootTopFibreBlock (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R),
    if q.Prime then
      roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
    else 0

/-- **No-go: the top block admits no cancellation at all.**  Every prime above
half the endpoint contributes exactly `+1`, so the block is its own cardinality.
The hyperbolic cutoff therefore does not decompose the transport population into
complete cancelling orbits plus a bounded boundary. -/
theorem squareRootTopFibreBlock_eq_card (R : ℕ) (hR : 2 ≤ R) :
    squareRootTopFibreBlock R = ((squareRootTopFibrePrimes R).card : ℂ) := by
  classical
  have hpow : R ^ 2 = R * R := by ring
  have hge : 2 * 2 ≤ R * R := Nat.mul_le_mul hR hR
  have hX : 3 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hstep :
      ∀ q ∈ Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R),
        (if q.Prime then
            roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
          else 0) =
          (if q.Prime then (1 : ℂ) else 0) := by
    intro q hqMem
    rcases Finset.mem_Ioc.mp hqMem with ⟨hlow, hhigh⟩
    by_cases hqPrime : q.Prime
    · have hq2 : 2 ≤ q := hqPrime.two_le
      have hdiv : squareRootEndpoint R / q = 1 :=
        squareRootEndpoint_div_eq_one_of_top_fibre (by omega) (by omega) hhigh
      rw [if_pos hqPrime, if_pos hqPrime, hdiv,
        roughCofactorMobiusPrefixMass_one hq2]
    · rw [if_neg hqPrime, if_neg hqPrime]
  calc
    squareRootTopFibreBlock R =
        ∑ q ∈ Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R),
          if q.Prime then (1 : ℂ) else 0 :=
      Finset.sum_congr rfl hstep
    _ = ∑ q ∈ squareRootTopFibrePrimes R, (1 : ℂ) := by
      unfold squareRootTopFibrePrimes
      rw [Finset.sum_filter]
    _ = ((squareRootTopFibrePrimes R).card : ℂ) := by simp

/-- By Bertrand the same-sign block is nonempty, so it is a strictly positive
integer, not a cancelling remainder. -/
theorem one_le_card_squareRootTopFibrePrimes (R : ℕ) (hR : 2 ≤ R) :
    1 ≤ (squareRootTopFibrePrimes R).card := by
  classical
  have hpow : R ^ 2 = R * R := by ring
  have hge : 2 * 2 ≤ R * R := Nat.mul_le_mul hR hR
  have hX : 3 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : squareRootEndpoint R / 2 ≠ 0 := by omega
  obtain ⟨p, hpPrime, hplow, hphigh⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (squareRootEndpoint R / 2) hhalf
  have hpX : p ≤ squareRootEndpoint R := by omega
  have hmem : p ∈ squareRootTopFibrePrimes R := by
    unfold squareRootTopFibrePrimes
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hplow, hpX⟩, hpPrime⟩
  exact Finset.card_pos.mpr ⟨p, hmem⟩

/-- The same-sign block is an exact summand of the transport term: the transport
term splits at `X/2` into a lower block and the top block. -/
theorem squareRootTransportPrimeFirst_eq_lowerBlock_add_topFibreBlock
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTransportPrimeFirst R =
      (∑ q ∈ Finset.Ioc R (squareRootEndpoint R / 2),
          if q.Prime then
            roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
          else 0) +
        squareRootTopFibreBlock R := by
  classical
  have hpow : R ^ 2 = R * R := by ring
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 hmul
  have hhalfX : squareRootEndpoint R / 2 ≤ squareRootEndpoint R :=
    Nat.div_le_self _ _
  have hsplit :
      Finset.Ioc R (squareRootEndpoint R) =
        Finset.Ioc R (squareRootEndpoint R / 2) ∪
          Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj :
      Disjoint (Finset.Ioc R (squareRootEndpoint R / 2))
        (Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rcases Finset.mem_Ioc.mp hq1 with ⟨_, hqhalf⟩
    rcases Finset.mem_Ioc.mp hq2 with ⟨hhalfq, _⟩
    omega
  unfold squareRootTopFibreBlock
  rw [squareRootTransportPrimeFirst_eq_reciprocalRoughTransform R (by omega),
    hsplit, Finset.sum_union hdisj]

end RHLean.Proof
