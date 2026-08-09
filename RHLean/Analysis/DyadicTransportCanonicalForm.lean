import Mathlib
import RHLean.Analysis.DyadicTransportCompression

/-!
# Canonical source form of dyadic transport compression

The packet module proves the exact parent/child cancellation and rewrites each
prime-first cofactor fiber as an odd dyadic boundary.  This companion module
makes the resulting canonical side conditions and sign convention explicit.

For `X = R^2 - 1`, every retained pair satisfies

* `q` is prime and `R < q <= X`;
* `c` is positive, odd, and `c < R < q`;
* `c*q <= X < 2*c*q`;
* `q = P+(c*q)` and `c` is the canonical cofactor.

The paper transport coefficient is `mu(c)`, whereas the source coefficient is
`mu(c*q) = -mu(c)`.  Both exact forms are recorded below.

The module also records the distinct complete-annulus identity

`M(B) = sum_{B < 2*m <= 2*B, m odd} mu(m)`.

The high transport source mass is only the `P+(m) > R` part of that annulus; it
is not the complete annulus and is not by itself the protected RH residual.

This module is classified under `RHLean/Analysis/` because its content is
represented in the bridge paper; the namespace remains `RHLean.Proof` for API
compatibility with existing references.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Exact finite predicate used by the compressed canonical high-source sum. -/
def IsDyadicCanonicalHighSource (R c q : ℕ) : Prop :=
  q ∈ Finset.Ioc R (squareRootEndpoint R) ∧
    q.Prime ∧
      c ∈ dyadicCofactorBoundary (squareRootEndpoint R / q)

instance instDecidableIsDyadicCanonicalHighSource (R c q : ℕ) :
    Decidable (IsDyadicCanonicalHighSource R c q) := by
  unfold IsDyadicCanonicalHighSource
  infer_instance

/-- Every compressed source lies in the upper half of the square-prefix range
and retains all elementary prime/cofactor side conditions explicitly. -/
theorem arithmetic_of_isDyadicCanonicalHighSource
    {R c q : ℕ} (hR : 0 < R)
    (h : IsDyadicCanonicalHighSource R c q) :
    q.Prime ∧
      R < q ∧ q ≤ squareRootEndpoint R ∧
      1 ≤ c ∧ c < R ∧ c < q ∧ Odd c ∧
      c * q ≤ squareRootEndpoint R ∧
      squareRootEndpoint R < 2 * (c * q) := by
  rcases h with ⟨hqmem, hqPrime, hcBoundary⟩
  rcases Finset.mem_Ioc.mp hqmem with ⟨hRq, hqX⟩
  rcases mem_dyadicCofactorBoundary.mp hcBoundary with
    ⟨hc1, hcB, hcOdd, hBdouble⟩
  have hqpos : 0 < q := hqPrime.pos
  have hBlt : squareRootEndpoint R / q < R :=
    squareRootEndpoint_div_lt hR hRq hqpos
  have hcR : c < R := lt_of_le_of_lt hcB hBlt
  have hcq : c < q := lt_trans hcR hRq
  have hupper : c * q ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hqpos).1 hcB
  have hlower : squareRootEndpoint R < 2 * (c * q) := by
    by_contra hnot
    have hle : 2 * (c * q) ≤ squareRootEndpoint R := Nat.le_of_not_gt hnot
    have h2cB : 2 * c ≤ squareRootEndpoint R / q := by
      apply (Nat.le_div_iff_mul_le hqpos).2
      calc
        (2 * c) * q = 2 * (c * q) := by ring
        _ ≤ squareRootEndpoint R := hle
    omega
  exact ⟨hqPrime, hRq, hqX, hc1, hcR, hcq, hcOdd, hupper, hlower⟩

/-- A prime strictly larger than its positive cofactor is the canonical largest
prime factor of their product. -/
theorem canonicalLargestPrimeFactor_mul_prime_eq
    {c q : ℕ} (hc : 0 < c) (hcq : c < q) (hq : q.Prime) :
    canonicalLargestPrimeFactor (c * q) = q := by
  have hm1 : 1 < c * q := by
    calc
      1 < q := hq.one_lt
      _ = 1 * q := by simp
      _ ≤ c * q := Nat.mul_le_mul_right q hc
  have hqmem : q ∈ (c * q).primeFactors := by
    exact Nat.mem_primeFactors.mpr
      ⟨hq, ⟨c, by simp [Nat.mul_comm]⟩,
        Nat.mul_ne_zero (Nat.ne_of_gt hc) hq.ne_zero⟩
  have hall : ∀ p ∈ (c * q).primeFactors, p ≤ q := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := Nat.dvd_of_mem_primeFactors hp
    rcases hpPrime.dvd_mul.mp hpDvd with hpc | hpq
    · exact (Nat.le_of_dvd hc hpc).trans hcq.le
    · exact ((Nat.prime_dvd_prime_iff_eq hpPrime hq).mp hpq).le
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hm1]
  exact ((c * q).primeFactors.max'_eq_iff
    (Nat.nonempty_primeFactors.mpr hm1) q).2 ⟨hqmem, hall⟩

/-- The canonical cofactor of `c*q` is the original lower factor whenever `q`
is prime and strictly larger than `c`. -/
theorem canonicalCofactor_mul_prime_eq
    {c q : ℕ} (hc : 0 < c) (hcq : c < q) (hq : q.Prime) :
    canonicalCofactor (c * q) = c := by
  unfold canonicalCofactor
  rw [canonicalLargestPrimeFactor_mul_prime_eq hc hcq hq]
  simpa [Nat.mul_comm] using Nat.mul_div_right c hq.pos

/-- Full canonical coordinate certificate for every retained dyadic high source. -/
theorem canonicalCoordinates_of_isDyadicCanonicalHighSource
    {R c q : ℕ} (hR : 0 < R)
    (h : IsDyadicCanonicalHighSource R c q) :
    canonicalLargestPrimeFactor (c * q) = q ∧
      canonicalCofactor (c * q) = c := by
  have hdata := arithmetic_of_isDyadicCanonicalHighSource hR h
  exact ⟨canonicalLargestPrimeFactor_mul_prime_eq
      (Nat.zero_lt_of_lt hdata.2.2.2.1) hdata.2.2.2.2.2.1 hdata.1,
    canonicalCofactor_mul_prime_eq
      (Nat.zero_lt_of_lt hdata.2.2.2.1) hdata.2.2.2.2.2.1 hdata.1⟩

/-- A prime larger than the positive cofactor flips the source Möbius weight. -/
theorem canonicalMoebiusWeight_mul_prime_eq_neg
    {c q : ℕ} (hc : 0 < c) (hcq : c < q) (hq : q.Prime) :
    canonicalMoebiusWeight (c * q) = -canonicalMoebiusWeight c := by
  have hcop : Nat.Coprime c q :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hc) hcq hq).symm
  have hmu :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  unfold canonicalMoebiusWeight
  rw [hmu, ArithmeticFunction.moebius_apply_prime hq]
  push_cast
  ring

/-- Raw source-signed mass of the compressed canonical high family. -/
def dyadicCanonicalHighSourceMass (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
    if q.Prime then
      ∑ c ∈ dyadicCofactorBoundary (squareRootEndpoint R / q),
        canonicalMoebiusWeight (c * q)
    else
      0

/-- In one prime fiber, the paper cofactor sign is the negative of the canonical
source sign. -/
theorem dyadicPrimeFiberBoundaryMass_eq_neg_sourceMass
    (R q : ℕ) (hR : 0 < R) (hRq : R < q) (hq : q.Prime) :
    dyadicPrimeFiberBoundaryMass R q =
      -∑ c ∈ dyadicCofactorBoundary (squareRootEndpoint R / q),
        canonicalMoebiusWeight (c * q) := by
  unfold dyadicPrimeFiberBoundaryMass dyadicCofactorBoundaryMass
  calc
    (∑ c ∈ dyadicCofactorBoundary (squareRootEndpoint R / q),
        canonicalMoebiusWeight c) =
      ∑ c ∈ dyadicCofactorBoundary (squareRootEndpoint R / q),
        -canonicalMoebiusWeight (c * q) := by
          apply Finset.sum_congr rfl
          intro c hcBoundary
          rcases mem_dyadicCofactorBoundary.mp hcBoundary with
            ⟨hc1, hcB, hcOdd, hBdouble⟩
          have hBlt : squareRootEndpoint R / q < R :=
            squareRootEndpoint_div_lt hR hRq hq.pos
          have hcq : c < q := lt_trans (lt_of_le_of_lt hcB hBlt) hRq
          have hweight :=
            canonicalMoebiusWeight_mul_prime_eq_neg
              (Nat.zero_lt_of_lt hc1) hcq hq
          rw [hweight]
          ring
    _ = -∑ c ∈ dyadicCofactorBoundary (squareRootEndpoint R / q),
          canonicalMoebiusWeight (c * q) := by
      simp

/-- Exact canonical source-sign form of the complete paper transport term. -/
theorem squareRootTransportCofactorFirst_eq_neg_dyadicCanonicalHighSourceMass
    (R : ℕ) :
    squareRootTransportCofactorFirst R =
      -dyadicCanonicalHighSourceMass R := by
  rw [squareRootTransportCofactorFirst_eq_dyadicBoundaryMass]
  by_cases hR0 : R = 0
  · subst R
    simp [squareRootDyadicTransportBoundaryMass,
      dyadicCanonicalHighSourceMass, squareRootEndpoint]
  · have hR : 0 < R := Nat.pos_of_ne_zero hR0
    unfold squareRootDyadicTransportBoundaryMass dyadicCanonicalHighSourceMass
    calc
      (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime then dyadicPrimeFiberBoundaryMass R q else 0) =
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime then
            -∑ c ∈ dyadicCofactorBoundary (squareRootEndpoint R / q),
              canonicalMoebiusWeight (c * q)
          else 0 := by
            apply Finset.sum_congr rfl
            intro q hqmem
            by_cases hqPrime : q.Prime
            · have hRq : R < q := (Finset.mem_Ioc.mp hqmem).1
              simp only [hqPrime, if_true]
              exact dyadicPrimeFiberBoundaryMass_eq_neg_sourceMass
                R q hR hRq hqPrime
            · simp [hqPrime]
      _ = -∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime then
            ∑ c ∈ dyadicCofactorBoundary (squareRootEndpoint R / q),
              canonicalMoebiusWeight (c * q)
          else 0 := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro q hqmem
            by_cases hqPrime : q.Prime <;> simp [hqPrime]

/-! ## The complete odd dyadic annulus -/

/-- The positive prefix sum used in the compression module is exactly the
repository's Mertens summatory function; the omitted zero term has weight zero. -/
theorem cofactorMobiusPrefixMass_eq_mertensSummatory (B : ℕ) :
    cofactorMobiusPrefixMass B = RHLean.Analysis.mertensSummatory B := by
  unfold cofactorMobiusPrefixMass RHLean.Analysis.mertensSummatory
  have hset :
      Finset.range (B + 1) =
        insert 0 (Finset.Icc 1 B) := by
    ext m
    simp
    omega
  rw [hset]
  simp [canonicalMoebiusWeight]

/-- Exact odd-annulus representation of every Mertens value. -/
theorem mertensSummatory_eq_dyadicCofactorBoundaryMass (B : ℕ) :
    RHLean.Analysis.mertensSummatory B =
      dyadicCofactorBoundaryMass B := by
  rw [← cofactorMobiusPrefixMass_eq_dyadicBoundaryMass]
  exact (cofactorMobiusPrefixMass_eq_mertensSummatory B).symm

/-- Complete odd dyadic-annulus mass at the manuscript square endpoint. -/
def squarePrefixDyadicAnnulusMass (n : ℕ) : ℂ :=
  dyadicCofactorBoundaryMass (RHLean.Analysis.squarePrefixEndpoint n)

/-- The complete odd dyadic annulus is exactly the square-prefix Mertens value.
This theorem concerns the full annulus, not the transport-only high subset. -/
theorem squarePrefixDyadicAnnulusMass_eq_squarePrefixMertens (n : ℕ) :
    squarePrefixDyadicAnnulusMass n =
      RHLean.Analysis.squarePrefixMertens n := by
  unfold squarePrefixDyadicAnnulusMass RHLean.Analysis.squarePrefixMertens
  exact (mertensSummatory_eq_dyadicCofactorBoundaryMass
    (RHLean.Analysis.squarePrefixEndpoint n)).symm

end RHLean.Proof
