import Mathlib
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootLowPrimeSquareDefect

/-!
# Carrier-specific cause of the outward processed-seat square defect

`SquareRootLowPrimeSquareDefect` proves that pivot desynchronization is exactly
the four-corner square defect, and that downward closure kills the reverse
orientation.  Its docstring then names the remaining task: identify the one
surviving orientation on the actual arithmetic carrier.  This file does that.

For `x = some (c,s)` the missing corner is `some (q*(p*c), s)`, and membership
in `squareRootLowPrimeProcessedSeatCarrier R K j U` is a conjunction of four
conditions.  So the defect has at most four causes:

* the hyperbolic endpoint crossing `squareRootEndpoint R < q*(p*c)`;
* the owner cutoff `U < canonicalLargestPrimeFactor (q*(p*c))`;
* a squarefree failure `mu (q*(p*c)) = 0`;
* seat exhaustion `Combined R K j (q*(p*c)) <= s`.

The two middle causes are then removed outright for genuinely scheduled
coordinates.  The owner cutoff cannot fire because the two present side corners
already bound every prime coordinate of the missing one, and the squarefree
failure cannot fire because two distinct fresh primes over a squarefree
cofactor stay squarefree.  What is left is exactly

`squareRootEndpoint R < q*(p*c)`  or  `Combined R K j (q*(p*c)) <= s`,

a hyperbolic endpoint crossing or a seat-count crossing.  There is no interior
residual: every outward defect on this carrier is one of those two boundary
events.

No estimate appears; each step is membership arithmetic.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Membership in the processed carrier -/

/-- Explicit membership test for a non-head processed state. -/
theorem mem_squareRootLowPrimeProcessedSeatCarrier_some
    {R K j U a s : ℕ} :
    some (a, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U ↔
      1 ≤ a ∧ a ≤ squareRootEndpoint R ∧
        canonicalLargestPrimeFactor a ≤ U ∧ μ a ≠ 0 ∧
          s < squareRootLowPrimeCombinedFreshResponse R K j a := by
  constructor
  · intro h
    have hatom : (a, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using h
    have hdata := mem_squareRootLowPrimeProcessedSeatAtoms.mp hatom
    have hfilter := Finset.mem_filter.mp hdata.1
    have hIcc := Finset.mem_Icc.mp hfilter.1
    exact ⟨hIcc.1, hIcc.2, hfilter.2.1, hfilter.2.2, hdata.2⟩
  · rintro ⟨ha1, haW, hlpf, hmu, hs⟩
    have hatom : (a, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
      mem_squareRootLowPrimeProcessedSeatAtoms.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, haW⟩, hlpf, hmu⟩, hs⟩
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hatom

/-! ## The four possible causes -/

/-- **Every outward square defect on the processed carrier is a failure of one
explicit membership condition of the missing corner.** -/
theorem squareRootLowPrimeProcessedSeatOutwardSquareDefect_cause
    {R K j U p q c s : ℕ}
    (hx : some (c, s) ∈ squareRootLowPrimeProcessedSeatOutwardSquareDefect
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p q) :
    squareRootEndpoint R < q * (p * c) ∨
      U < canonicalLargestPrimeFactor (q * (p * c)) ∨
      μ (q * (p * c)) = 0 ∨
      squareRootLowPrimeCombinedFreshResponse R K j (q * (p * c)) ≤ s := by
  rcases mem_squareRootLowPrimeProcessedSeatOutwardSquareDefect.mp hx with
    ⟨_hxS, _hxNone, hpxS, hqxS, hqpxNot⟩
  have hpxS' : some (p * c, s) ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := hpxS
  have hqxS' : some (q * c, s) ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := hqxS
  have hqpxNot' : some (q * (p * c), s) ∉
      squareRootLowPrimeProcessedSeatCarrier R K j U := hqpxNot
  have hpc := mem_squareRootLowPrimeProcessedSeatCarrier_some.mp hpxS'
  have hqc := mem_squareRootLowPrimeProcessedSeatCarrier_some.mp hqxS'
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      have := hqc.1
      simp at this
    · exact h
  have hone : 1 ≤ q * (p * c) := Nat.mul_pos hq hpc.1
  by_contra hcon
  push_neg at hcon
  obtain ⟨hend, hcut, hmu, hseat⟩ := hcon
  exact hqpxNot'
    (mem_squareRootLowPrimeProcessedSeatCarrier_some.mpr
      ⟨hone, hend, hcut, hmu, hseat⟩)

/-! ## Removing the two interior causes -/

/-- The missing corner never crosses the owner cutoff: the two present side
corners already bound every one of its prime coordinates. -/
theorem squareRootLowPrimeOutwardSquareDefect_corner_lpf_le
    {R K j U p q c s : ℕ} (hU : 1 ≤ U)
    (hp : p.Prime) (hq : q.Prime)
    (hpxS : some (p * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hqxS : some (q * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    canonicalLargestPrimeFactor (q * (p * c)) ≤ U := by
  have hpc := mem_squareRootLowPrimeProcessedSeatCarrier_some.mp hpxS
  have hqc := mem_squareRootLowPrimeProcessedSeatCarrier_some.mp hqxS
  have hpcOne : 1 < p * c := by
    have hc : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        have := hpc.1
        simp at this
      · exact h
    have := hp.two_le
    calc 1 < p := hp.one_lt
      _ = p * 1 := (Nat.mul_one p).symm
      _ ≤ p * c := Nat.mul_le_mul_left p hc
  have hqcOne : 1 < q * c := by
    have hc : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        have := hqc.1
        simp at this
      · exact h
    calc 1 < q := hq.one_lt
      _ = q * 1 := (Nat.mul_one q).symm
      _ ≤ q * c := Nat.mul_le_mul_left q hc
  have hqU : q ≤ U :=
    le_trans
      (CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
        hqcOne hq ⟨c, rfl⟩)
      hqc.2.2.1
  have hcornerPos : 0 < q * (p * c) := Nat.mul_pos hq.pos (by omega)
  refine (canonicalLargestPrimeFactor_le_iff_forall_primeFactors_le hU
    hcornerPos).mpr ?_
  intro r hr
  have hrData := Nat.mem_primeFactors.mp hr
  have hrPrime : r.Prime := hrData.1
  rcases (Nat.Prime.dvd_mul hrPrime).mp hrData.2.1 with hrq | hrpc
  · have : r = q := (Nat.prime_dvd_prime_iff_eq hrPrime hq).mp hrq
    omega
  · exact le_trans
      (CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
        hpcOne hrPrime hrpc)
      hpc.2.2.1

/-- The missing corner is squarefree: two distinct fresh primes over a
squarefree cofactor cannot repeat a coordinate. -/
theorem squareRootLowPrimeOutwardSquareDefect_corner_moebius_ne_zero
    {R K j U p q c s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpxS : some (p * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hqxS : some (q * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    μ (q * (p * c)) ≠ 0 := by
  have hpc := mem_squareRootLowPrimeProcessedSeatCarrier_some.mp hpxS
  have hqc := mem_squareRootLowPrimeProcessedSeatCarrier_some.mp hqxS
  have hsqQC : Squarefree (q * c) :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hqc.2.2.2.1
  have hqnd : ¬ q ∣ p * c := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with hqp | hqc'
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).symm
    · have hunit : IsUnit q := hsqQC q (mul_dvd_mul_left q hqc')
      exact absurd (Nat.isUnit_iff.mp hunit) hq.ne_one
  rw [moebius_prime_mul hq hqnd]
  exact neg_ne_zero.mpr hpc.2.2.2.1

/-- **The surviving defect orientation is a boundary crossing.**  For two
distinct scheduled primes the outward square defect on the processed carrier is
caused only by the hyperbolic endpoint or by seat exhaustion. -/
theorem squareRootLowPrimeProcessedSeatOutwardSquareDefect_cause_scheduled
    {R K j U p q c s : ℕ} (hU : 1 ≤ U)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hx : some (c, s) ∈ squareRootLowPrimeProcessedSeatOutwardSquareDefect
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p q) :
    squareRootEndpoint R < q * (p * c) ∨
      squareRootLowPrimeCombinedFreshResponse R K j (q * (p * c)) ≤ s := by
  rcases mem_squareRootLowPrimeProcessedSeatOutwardSquareDefect.mp hx with
    ⟨_hxS, _hxNone, hpxS, hqxS, _hqpxNot⟩
  have hpxS' : some (p * c, s) ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := hpxS
  have hqxS' : some (q * c, s) ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := hqxS
  rcases squareRootLowPrimeProcessedSeatOutwardSquareDefect_cause hx with
    hend | hcut | hmu | hseat
  · exact Or.inl hend
  · exact absurd
      (squareRootLowPrimeOutwardSquareDefect_corner_lpf_le hU hp hq hpxS' hqxS')
      (by omega)
  · exact absurd hmu
      (squareRootLowPrimeOutwardSquareDefect_corner_moebius_ne_zero
        hp hq hpq hpxS' hqxS')
  · exact Or.inr hseat

end RHLean.Proof
