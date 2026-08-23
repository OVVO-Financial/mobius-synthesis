import RHLean.Proof.SquareRootAncestryParentFibres

/-!
# Generic prime-extension windows for square-root ancestry

`BornSmoothChild` was designed for the first balanced extension of an extreme
transport root.  The complete legal successor contains smooth parents at every
ancestry depth, so its inverse-parent fibres require the generic operation:

* start from arbitrary canonical parent data `(q,a)`;
* adjoin a new largest core prime `p` below the distinguished prime `q`;
* require only that the resulting core `a*p` is smooth, `q < a*p`.

This module proves that the deterministic parent map is exactly this operation.
It does not truncate to the first generation.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

/-- A generic legal smooth extension of a canonical parent.  Unlike
`BornSmoothChild`, no extreme-parent or balanced-child hypothesis is imposed. -/
structure CanonicalSmoothPrimeExtension (q a p : ℕ) : Prop where
  parentData : CanonicalSourceData q a
  extension : LegalExtension q a p
  entersSmooth : q < a * p

/-- The generic extension creates canonical source data for the child core. -/
theorem canonicalSmoothPrimeExtension_childData
    {q a p : ℕ} (h : CanonicalSmoothPrimeExtension q a p) :
    CanonicalSourceData q (a * p) := by
  rcases h.parentData with ⟨hq, ha1, hsqA, hqcopA, hdomQ⟩
  rcases h.extension with ⟨hpmax, hpcopParent, hpq⟩
  have hap : Nat.Coprime a p := hpmax.coprime.symm
  have hsqAP : Squarefree (a * p) :=
    (Nat.squarefree_mul hap).2 ⟨hsqA, hpmax.prime.squarefree⟩
  have hqdiv : q ∣ q * a := ⟨a, rfl⟩
  have hqcopP : Nat.Coprime q p := by
    have hpcopQ : Nat.Coprime p q :=
      hpcopParent.coprime_dvd_right hqdiv
    exact hpcopQ.symm
  have hqcopAP : Nat.Coprime q (a * p) :=
    Nat.Coprime.mul_right hqcopA hqcopP
  have hap1 : 1 ≤ a * p := by
    have ha0 : 0 < a := by omega
    exact Nat.mul_pos ha0 hpmax.prime.pos
  refine ⟨hq, hap1, hsqAP, hqcopAP, ?_⟩
  intro r hr hrap
  rcases hr.dvd_mul.mp hrap with hra | hrp
  · exact hdomQ r hr hra
  · have hrEq : r = p :=
      (Nat.prime_dvd_prime_iff_eq hr hpmax.prime).mp hrp
    simpa [hrEq] using hpq

/-- In a generic smooth extension, the adjoined prime is the canonical largest
prime of the new core. -/
theorem canonicalLargestPrimeFactor_mul_eq_extensionPrime
    {q a p : ℕ} (h : CanonicalSmoothPrimeExtension q a p) :
    canonicalLargestPrimeFactor (a * p) = p := by
  have hp := h.extension.coreMax.prime
  have ha1 : 1 ≤ a := h.parentData.2.1
  have hapos : 0 < a := by omega
  have hprodgt : 1 < a * p := by
    nlinarith [hp.two_le]
  have hpdiv : p ∣ a * p := ⟨a, by simp [Nat.mul_comm]⟩
  have hple : p ≤ canonicalLargestPrimeFactor (a * p) :=
    prime_dvd_le_canonicalLargestPrimeFactor hprodgt hp hpdiv
  have htopPrime := canonicalLargestPrimeFactor_prime hprodgt
  have htopDiv := canonicalLargestPrimeFactor_dvd hprodgt
  have htopLe : canonicalLargestPrimeFactor (a * p) ≤ p := by
    rcases htopPrime.dvd_mul.mp htopDiv with htopA | htopP
    · exact (h.extension.coreMax.dominates _ htopPrime htopA).le
    · have heq : canonicalLargestPrimeFactor (a * p) = p :=
        (Nat.prime_dvd_prime_iff_eq htopPrime hp).mp htopP
      exact heq.le
  exact Nat.le_antisymm htopLe hple

/-- The canonical cofactor of the extended core is exactly its original parent
core.  Thus generic extension and deterministic stripping are inverse. -/
theorem canonicalCofactor_mul_eq_extensionParent
    {q a p : ℕ} (h : CanonicalSmoothPrimeExtension q a p) :
    canonicalCofactor (a * p) = a := by
  have hp := h.extension.coreMax.prime
  have hprodgt : 1 < a * p := by
    have ha1 := h.parentData.2.1
    nlinarith [hp.two_le]
  have hfactor := canonicalCofactor_mul_largestPrimeFactor hprodgt
  rw [canonicalLargestPrimeFactor_mul_eq_extensionPrime h] at hfactor
  exact Nat.mul_right_cancel hp.pos hfactor

/-- Every actual smooth source supplies a generic prime extension from its
stripped deterministic parent. -/
theorem smoothSource_has_canonicalSmoothPrimeExtension
    {B : ℕ} (s : SourceIndex B) (hs : SmoothOriented s) :
    CanonicalSmoothPrimeExtension
      (sourcePrime s)
      (canonicalCofactor (sourceCore s))
      (canonicalLargestPrimeFactor (sourceCore s)) := by
  rcases hs.1 with ⟨hq, hc1, hsq, hqcop, hdom⟩
  have hcgt : 1 < sourceCore s := lt_trans hq.one_lt hs.2
  let p := canonicalLargestPrimeFactor (sourceCore s)
  let a := canonicalCofactor (sourceCore s)
  have hp : p.Prime := canonicalLargestPrimeFactor_prime hcgt
  have hpdiv : p ∣ sourceCore s := canonicalLargestPrimeFactor_dvd hcgt
  have haDvd : a ∣ sourceCore s := canonicalCofactor_dvd hcgt
  have hpaNot : ¬ p ∣ a := by
    dsimp [p, a]
    exact canonicalLargestPrimeFactor_not_dvd_cofactor hsq hcgt
  have hpa : Nat.Coprime p a := hp.coprime_iff_not_dvd.mpr hpaNot
  have hpmax : CoreMaxPrime p a := by
    refine ⟨hp, hpa, ?_⟩
    intro r hr hra
    have hrCore : r ∣ sourceCore s := hra.trans haDvd
    have hrle : r ≤ p := by
      dsimp [p]
      exact prime_dvd_le_canonicalLargestPrimeFactor hcgt hr hrCore
    have hrne : r ≠ p := by
      intro heq
      exact hpaNot (heq ▸ hra)
    omega
  have hpq : p < sourcePrime s := by
    exact hdom p hp hpdiv
  have hpcopQ : Nat.Coprime p (sourcePrime s) := by
    have hqcopP : Nat.Coprime (sourcePrime s) p :=
      hqcop.coprime_dvd_right hpdiv
    exact hqcopP.symm
  have hpcopParent : Nat.Coprime p (sourcePrime s * a) :=
    Nat.Coprime.mul_right hpcopQ hpa
  have hparentData : CanonicalSourceData (sourcePrime s) a := by
    dsimp [a]
    exact canonicalParentData
      ⟨hq, hc1, hsq, hqcop, hdom⟩ hs.2
  have hcore : a * p = sourceCore s := by
    dsimp [a, p]
    exact canonicalCofactor_mul_largestPrimeFactor hcgt
  refine ⟨hparentData, ⟨hpmax, hpcopParent, hpq⟩, ?_⟩
  rw [hcore]
  exact hs.2

/-- The actual deterministic parent coordinates are recovered from the generic
extension attached to a smooth source. -/
theorem smoothSource_extension_recovers_parentCore
    {B : ℕ} (s : SourceIndex B) (hs : SmoothOriented s) :
    sourceCore (parentIndex s hs) =
      canonicalCofactor (sourceCore s) := rfl

/-- Arithmetic window predicate for an extension prime at a complete square
endpoint. -/
def SquareRootLegalExtensionPrime
    (R q a p : ℕ) : Prop :=
  CanonicalSmoothPrimeExtension q a p ∧
    q * (a * p) ≤ squareRootEndpoint R

/-- Every legal smooth extension under `R^2-1` is genuinely lower triangular in
its prime coordinates: the extension prime is below the distinguished prime,
and the distinguished prime itself is below the square-root induction scale. -/
theorem squareRootLegalExtensionPrime_lt_distinguished_lt_root
    {R q a p : ℕ} (hR : 2 ≤ R)
    (h : SquareRootLegalExtensionPrime R q a p) :
    p < q ∧ q < R := by
  refine ⟨h.1.extension.belowDistinguished, ?_⟩
  by_contra hnot
  have hRq : R ≤ q := Nat.le_of_not_gt hnot
  have hRcore : R ≤ a * p := hRq.trans h.1.entersSmooth.le
  have hsq : R ^ 2 ≤ q * (a * p) := by
    simpa [pow_two] using Nat.mul_le_mul hRq hRcore
  have hendlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  exact (Nat.not_lt_of_ge hsq) (h.2.trans_lt hendlt)

/-- Every active smooth source at the complete-square clock yields an extension
prime in the explicit square-root window. -/
theorem activeSmoothSource_yields_legalExtensionPrime
    {B R : ℕ} (s : SourceIndex B)
    (hactive : s ∈ activeSmoothSourceSet B (R - 1))
    (hR : 2 ≤ R) :
    SquareRootLegalExtensionPrime R
      (sourcePrime s)
      (canonicalCofactor (sourceCore s))
      (canonicalLargestPrimeFactor (sourceCore s)) := by
  have hs : SmoothOriented s ∧ sourceClock B s ≤ R - 1 := by
    simpa [activeSmoothSourceSet] using hactive
  have hext := smoothSource_has_canonicalSmoothPrimeExtension s hs.1
  refine ⟨hext, ?_⟩
  have hprod : sourceProduct s ≤ squareRootEndpoint R := by
    have h :=
      (sourceClock_le_iff_sourceProduct_le_endpoint
        (x := R - 1) s).1 hs.2
    simpa [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)] using h
  have hcore :=
    canonicalCofactor_mul_largestPrimeFactor
      (lt_trans hs.1.1.1.one_lt hs.1.2)
  change
    sourcePrime s *
        (canonicalCofactor (sourceCore s) *
          canonicalLargestPrimeFactor (sourceCore s)) ≤
      squareRootEndpoint R
  rw [hcore]
  exact hprod

end RHLean.Proof
