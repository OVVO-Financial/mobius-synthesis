import Mathlib
import RHLean.Analysis.SquareWheelSurvivorPrimeFibres
import RHLean.Proof.CanonicalSignedParent

/-!
# Canonical cofactor form of wheel-end prime fibres

The survivor-centered run is now decomposed over one distinguished-prime
coordinate `q`.  Its wheel-end centering term still appears in integer form as

```text
E_k(q) = sum_{L_k < m <= U_k, P+(m)=q} mu(m).
```

This file reindexes that endpoint fibre onto the same canonical `(q,c)` source
universe used by the survivor fixed-prime fibres.

For every nonzero endpoint term, squarefreeness gives the canonical
factorization

```text
m = c*q,
q = P+(m),
c = canonicalCofactor(m),
mu(m) = -mu(c).
```

Conversely, `CanonicalSourceData q c` already says that `q` is a fresh prime
strictly above every prime divisor of the squarefree cofactor `c`; hence `q` is
the canonical largest prime of `c*q` even when the integer `c` itself is larger
than `q`.

Thus

```text
E_k(q)
  = sum_c -mu(c)
      * 1_{CanonicalSourceData q c}
      * 1_{L_k < c*q <= U_k}.
```

No orientation condition `c < q` is imposed.  This is important: the wheel-end
fibre contains both transport-oriented and smooth-oriented canonical sources.
The result puts endpoint centering and survivor activity on literally the same
`(q,c)` atoms, preparing a selector-level first-failure comparison without
introducing a norm.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryBridge
open RHLean.Arithmetic
open RHLean.Analysis

/-- Embed unbounded canonical source data into the repository's bounded source
universe.  This recovers the canonical largest prime and cofactor of `c*q`
without assuming the integer inequality `c < q`. -/
private theorem canonicalCoordinates_mul_of_sourceData
    {q c : ℕ} (hdata : CanonicalSourceData q c) :
    canonicalLargestPrimeFactor (c * q) = q ∧
      canonicalCofactor (c * q) = c := by
  have hqpos : 0 < q := hdata.1.pos
  have hqle : q ≤ c * q := by
    calc
      q = 1 * q := by simp
      _ ≤ c * q := Nat.mul_le_mul_right q hdata.2.1
  have hcle : c ≤ c * q := by
    calc
      c = c * 1 := by simp
      _ ≤ c * q := Nat.mul_le_mul_left c hqpos
  let s : SourceIndex (c * q) :=
    (⟨q, by omega⟩, ⟨c, by omega⟩)
  have hs : SourceAdmissible s := by
    change CanonicalSourceData q c
    exact hdata
  have hp := sourcePrime_eq_canonicalLargestPrimeFactor s hs
  have hc := sourceCore_eq_canonicalCofactor s hs
  have hp' : q = canonicalLargestPrimeFactor (q * c) := by
    simpa [s, sourcePrime, sourceProduct, sourceCore] using hp
  have hc' : c = canonicalCofactor (q * c) := by
    simpa [s, sourcePrime, sourceProduct, sourceCore] using hc
  constructor
  · simpa [Nat.mul_comm] using hp'.symm
  · simpa [Nat.mul_comm] using hc'.symm

/-- Source data gives the integer Möbius sign flip on the represented product.
This is the cofactor sign convention shared by endpoint and survivor fibres. -/
private theorem moebius_mul_eq_neg_of_sourceData
    {q c : ℕ} (hdata : CanonicalSourceData q c) :
    μ (c * q) = -μ c := by
  rcases hdata with ⟨hq, _hc1, _hsq, hcop, _hdom⟩
  have hmu :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm
  rw [hmu, ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- Squarefree endpoint integers in the `q`-th canonical largest-prime fibre. -/
def primorialMinimalWheelEndpointSquarefreePrimeSet (k q : ℕ) : Finset ℕ :=
  (Finset.Ioc (primorialBlockLower k) (primorialBlockUpper k)).filter
    fun m => Squarefree m ∧ canonicalLargestPrimeFactor m = q

/-- Canonical cofactors representing the same endpoint fibre. -/
noncomputable def primorialMinimalWheelEndpointCofactorSet (k q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (primorialBlockUpper k)).filter fun c =>
    CanonicalSourceData q c ∧
      primorialBlockLower k < c * q ∧
      c * q ≤ primorialBlockUpper k

/-- Signed cofactor mass of one wheel-end prime fibre. -/
def primorialMinimalWheelEndpointCofactorFiber (k q : ℕ) : ℂ :=
  ∑ c ∈ primorialMinimalWheelEndpointCofactorSet k q,
    -canonicalMoebiusWeight c

/-- Removing nonsquarefree endpoint terms does not change the endpoint prime
fibre because their Möbius weight is zero. -/
theorem primorialMinimalWheelEndpointPrimeFiber_eq_squarefreeMass
    (k q : ℕ) :
    primorialMinimalWheelEndpointPrimeFiber k q =
      ∑ m ∈ primorialMinimalWheelEndpointSquarefreePrimeSet k q,
        canonicalMoebiusWeight m := by
  classical
  unfold primorialMinimalWheelEndpointPrimeFiber
    primorialMinimalWheelEndpointSquarefreePrimeSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hp : canonicalLargestPrimeFactor m = q
  · by_cases hsq : Squarefree m
    · simp [hp, hsq]
    · have hmu : μ m = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hp, hsq, canonicalMoebiusWeight, hmu]
  · simp [hp]

/-- Exact bijection between squarefree endpoint integers in the `q`-fibre and
canonical cofactors satisfying `CanonicalSourceData q c` and the endpoint
product interval.  Möbius signs reverse along the bijection. -/
theorem endpointSquarefreePrimeMass_eq_endpointCofactorFiber
    (k q : ℕ) :
    (∑ m ∈ primorialMinimalWheelEndpointSquarefreePrimeSet k q,
        canonicalMoebiusWeight m) =
      primorialMinimalWheelEndpointCofactorFiber k q := by
  classical
  unfold primorialMinimalWheelEndpointCofactorFiber
  refine Finset.sum_bij
    (fun m _hm => canonicalCofactor m) ?_ ?_ ?_ ?_
  · intro m hm
    change canonicalCofactor m ∈ primorialMinimalWheelEndpointCofactorSet k q
    rcases Finset.mem_filter.mp hm with ⟨hmIoc, hsq, hpq⟩
    rcases Finset.mem_Ioc.mp hmIoc with ⟨hmLower, hmUpper⟩
    have hLowerPos : 0 < primorialBlockLower k := primorialEndpoint_pos k
    have hmgt : 1 < m := by omega
    have hdata0 := canonicalSourceData_of_squarefree hsq hmgt
    have hdata : CanonicalSourceData q (canonicalCofactor m) := by
      simpa [hpq] using hdata0
    have hclem : canonicalCofactor m ≤ m :=
      Nat.le_of_dvd (by omega) (canonicalCofactor_dvd hmgt)
    have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
    have hprodq : canonicalCofactor m * q = m := by
      simpa [hpq] using hprod
    unfold primorialMinimalWheelEndpointCofactorSet
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr
      ⟨canonicalCofactor_pos hmgt, hclem.trans hmUpper⟩, hdata, ?_, ?_⟩
    · simpa [hprodq] using hmLower
    · simpa [hprodq] using hmUpper
  · intro m₁ hm₁ m₂ hm₂ hcof
    change canonicalCofactor m₁ = canonicalCofactor m₂ at hcof
    rcases Finset.mem_filter.mp hm₁ with ⟨hm₁Ioc, _hsq₁, hpq₁⟩
    rcases Finset.mem_filter.mp hm₂ with ⟨hm₂Ioc, _hsq₂, hpq₂⟩
    rcases Finset.mem_Ioc.mp hm₁Ioc with ⟨hm₁Lower, _hm₁Upper⟩
    rcases Finset.mem_Ioc.mp hm₂Ioc with ⟨hm₂Lower, _hm₂Upper⟩
    have hLowerPos : 0 < primorialBlockLower k := primorialEndpoint_pos k
    have hm₁gt : 1 < m₁ := by omega
    have hm₂gt : 1 < m₂ := by omega
    have hprod₁ := canonicalCofactor_mul_largestPrimeFactor hm₁gt
    have hprod₂ := canonicalCofactor_mul_largestPrimeFactor hm₂gt
    rw [hpq₁] at hprod₁
    rw [hpq₂] at hprod₂
    calc
      m₁ = canonicalCofactor m₁ * q := hprod₁.symm
      _ = canonicalCofactor m₂ * q := by rw [hcof]
      _ = m₂ := hprod₂
  · intro c hc
    unfold primorialMinimalWheelEndpointCofactorSet at hc
    rcases Finset.mem_filter.mp hc with
      ⟨_hcIcc, hdata, hLower, hUpper⟩
    have hcoords := canonicalCoordinates_mul_of_sourceData hdata
    have hmuCne : μ c ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hdata.2.2.1
    have hmuProd : μ (c * q) = -μ c :=
      moebius_mul_eq_neg_of_sourceData hdata
    have hmuProdNe : μ (c * q) ≠ 0 := by
      rw [hmuProd]
      exact neg_ne_zero.mpr hmuCne
    have hsqProd : Squarefree (c * q) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuProdNe
    refine ⟨c * q, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ioc.mpr ⟨hLower, hUpper⟩,
        hsqProd, hcoords.1⟩
    · change canonicalCofactor (c * q) = c
      exact hcoords.2
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmIoc, hsq, _hpq⟩
    rcases Finset.mem_Ioc.mp hmIoc with ⟨hmLower, _hmUpper⟩
    have hLowerPos : 0 < primorialBlockLower k := primorialEndpoint_pos k
    have hmgt : 1 < m := by omega
    have hmu := canonicalSignedParent_moebius hsq hmgt
    unfold canonicalMoebiusWeight
    rw [hmu]
    push_cast
    ring

/-- **Endpoint prime fibre in canonical cofactor coordinates.**  The wheel-end
centering mass and the survivor fixed-prime mass now live on the same
`CanonicalSourceData q c` atoms. -/
theorem primorialMinimalWheelEndpointPrimeFiber_eq_cofactorFiber
    (k q : ℕ) :
    primorialMinimalWheelEndpointPrimeFiber k q =
      primorialMinimalWheelEndpointCofactorFiber k q := by
  rw [primorialMinimalWheelEndpointPrimeFiber_eq_squarefreeMass,
    endpointSquarefreePrimeMass_eq_endpointCofactorFiber]

end RHLean.Proof
