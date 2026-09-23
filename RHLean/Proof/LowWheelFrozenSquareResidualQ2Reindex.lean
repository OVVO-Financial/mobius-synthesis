import RHLean.Proof.LowWheelFrozenSecondContactRoughPrefix

/-!
# Exact q^2 reindex of the frozen square residual

The source/transport cancellation in `LowWheelFrozenSecondContactRoughPrefix`
leaves, at each fixed source scale `A`, a signed square residual

`sum_{c squarefree, rough above p, P+(c)*c <= B} mu(c)`.

This file performs only the next exact arithmetic reindex.  Every residual
cofactor has the unique owner `q = P+(c)`.  Writing `d = c/q` gives

`p < q`, `q*d = c`, `q^2*d <= B`, `P+(d) < q`,

with `d` still squarefree and rough above `p`; moreover the Möbius sign flips.
No norm, estimate, selected-prime tensor, or identification with an ordinary
Mertens prefix is made here.  In particular the fixed-`A` daughter remains an
interval-prime object; completion to ordinary Mertens can only occur after the
outer signed source-scale sum is reassembled.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Owners actually represented in one frozen square-residual fibre. -/
def lowWheelFrozenSourceSquareResidualOwners (p B : ℕ) : Finset ℕ :=
  (lowWheelFrozenSourceSquareResidual p B).image canonicalLargestPrimeFactor

/-- The square-residual fibre having canonical largest-prime owner `q`. -/
def lowWheelFrozenSourceSquareResidualOwnerFiber
    (p B q : ℕ) : Finset ℕ :=
  (lowWheelFrozenSourceSquareResidual p B).filter fun c =>
    canonicalLargestPrimeFactor c = q

@[simp] theorem mem_lowWheelFrozenSourceSquareResidualOwnerFiber
    {p B q c : ℕ} :
    c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q ↔
      c ∈ lowWheelFrozenSourceSquareResidual p B ∧
        canonicalLargestPrimeFactor c = q := by
  simp [lowWheelFrozenSourceSquareResidualOwnerFiber]

/-- The residual is a disjoint fibrewise sum over its canonical largest-prime
owners.  The observable is arbitrary: this is pure reindexing. -/
theorem lowWheelFrozenSourceSquareResidual_sum_eq_sum_ownerFibers
    {M : Type*} [AddCommMonoid M]
    (p B : ℕ) (f : ℕ → M) :
    (∑ c ∈ lowWheelFrozenSourceSquareResidual p B, f c) =
      ∑ q ∈ lowWheelFrozenSourceSquareResidualOwners p B,
        ∑ c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q, f c := by
  let S : Finset ℕ := lowWheelFrozenSourceSquareResidual p B
  let O : Finset ℕ := lowWheelFrozenSourceSquareResidualOwners p B
  let owner : ℕ → ℕ := canonicalLargestPrimeFactor
  have hmaps : ∀ c ∈ S, owner c ∈ O := by
    intro c hc
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := S) (t := O) (g := owner) hmaps f
  have hraw :
      (∑ c ∈ S, f c) =
        ∑ q ∈ O, ∑ c ∈ S with owner c = q, f c := hfiber.symm
  change (∑ c ∈ S, f c) =
    ∑ q ∈ O,
      ∑ c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q, f c
  rw [hraw]
  apply Finset.sum_congr rfl
  intro q hq
  rfl

/-- **Local SR-q^2 kernel.**  A square-residual cofactor with owner `q` strips
canonically as `c=q*d`.  The daughter `d` is still squarefree and rough above
the old source pivot, has all prime factors below `q`, and lies at the genuine
square-dilated cutoff `q^2*d <= B`.  The Möbius sign flips exactly. -/
theorem lowWheelFrozenSourceSquareResidualOwnerFiber_data
    {p B q c : ℕ}
    (hc : c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q) :
    q.Prime ∧ p < q ∧
      Squarefree (canonicalCofactor c) ∧
      RoughAbove p (canonicalCofactor c) ∧
      canonicalLargestPrimeFactor (canonicalCofactor c) < q ∧
      q * canonicalCofactor c = c ∧
      q * q * canonicalCofactor c ≤ B ∧
      canonicalMoebiusWeight c =
        -canonicalMoebiusWeight (canonicalCofactor c) := by
  rcases mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mp hc with
    ⟨hcResidual, howner⟩
  rcases Finset.mem_filter.mp hcResidual with ⟨hcRoughPrefix, hcontact⟩
  rcases Finset.mem_filter.mp hcRoughPrefix with
    ⟨hcIcc, hsq, hrough⟩
  have hcBounds := Finset.mem_Icc.mp hcIcc
  have hcgt : 1 < c := by omega
  have hc0 : c ≠ 0 := by omega
  have hqPrime : q.Prime := by
    simpa [howner] using canonicalLargestPrimeFactor_prime hcgt
  have hqDvd : q ∣ c := by
    simpa [howner] using canonicalLargestPrimeFactor_dvd hcgt
  have hqPF : q ∈ c.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, hc0⟩
  have hpq : p < q := hrough q hqPF
  have hfactor0 :
      canonicalCofactor c * canonicalLargestPrimeFactor c = c :=
    canonicalCofactor_mul_largestPrimeFactor hcgt
  have hfactor : q * canonicalCofactor c = c := by
    simpa [howner, Nat.mul_comm] using hfactor0
  have hdDvd : canonicalCofactor c ∣ c := canonicalCofactor_dvd hcgt
  have hdSq : Squarefree (canonicalCofactor c) :=
    hsq.squarefree_of_dvd hdDvd
  have hdRough : RoughAbove p (canonicalCofactor c) := by
    intro r hr
    have hrPrime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrDvdD : r ∣ canonicalCofactor c := Nat.dvd_of_mem_primeFactors hr
    have hrDvdC : r ∣ c := dvd_trans hrDvdD hdDvd
    have hrC : r ∈ c.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrPrime, hrDvdC, hc0⟩
    exact hrough r hrC
  have hdLt : canonicalLargestPrimeFactor (canonicalCofactor c) < q := by
    have hlt :=
      canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hcgt hsq
    simpa [howner] using hlt
  have hq2 : q * q * canonicalCofactor c ≤ B := by
    have hqmul : q * (q * canonicalCofactor c) = q * c :=
      congrArg (fun n : ℕ => q * n) hfactor
    calc
      q * q * canonicalCofactor c = q * (q * canonicalCofactor c) := by ring
      _ = q * c := hqmul
      _ = canonicalLargestPrimeFactor c * c := by rw [howner]
      _ ≤ B := hcontact
  have hweightD :
      canonicalMoebiusWeight (canonicalCofactor c) =
        -canonicalMoebiusWeight c := by
    simpa [canonicalCofactor, howner] using
      (canonicalMoebiusWeight_div_prime hqPrime hsq hqDvd)
  have hweight :
      canonicalMoebiusWeight c =
        -canonicalMoebiusWeight (canonicalCofactor c) := by
    rw [hweightD]
    ring
  exact ⟨hqPrime, hpq, hdSq, hdRough, hdLt, hfactor, hq2, hweight⟩

/-- Canonical stripped daughters live in the expected interval-prime q^2
window. -/
def lowWheelFrozenSourceSquareResidualDaughterWindow
    (p B q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (B / (q * q))).filter fun d =>
    Squarefree d ∧ RoughAbove p d ∧ canonicalLargestPrimeFactor d < q

/-- Every owner-`q` residual maps into the literal q^2 daughter window. -/
theorem canonicalCofactor_mem_lowWheelFrozenSourceSquareResidualDaughterWindow
    {p B q c : ℕ}
    (hc : c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q) :
    canonicalCofactor c ∈
      lowWheelFrozenSourceSquareResidualDaughterWindow p B q := by
  rcases lowWheelFrozenSourceSquareResidualOwnerFiber_data hc with
    ⟨hqPrime, _hpq, hdSq, hdRough, hdLt, _hfactor, hq2, _hweight⟩
  have hcgt : 1 < c := by
    have hres := (mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mp hc).1
    have hrough := (Finset.mem_filter.mp hres).1
    have hIcc := (Finset.mem_filter.mp hrough).1
    have hbounds := Finset.mem_Icc.mp hIcc
    omega
  have hdPos : 1 ≤ canonicalCofactor c := canonicalCofactor_pos hcgt
  have hqqPos : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
  have hdUpper : canonicalCofactor c ≤ B / (q * q) := by
    apply (Nat.le_div_iff_mul_le hqqPos).2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨hdPos, hdUpper⟩, hdSq, hdRough, hdLt⟩

/-- Conversely, every interval-prime daughter reconstructs a unique square
residual child `q*d` with owner `q`. -/
theorem lowWheelFrozenSourceSquareResidualDaughter_child_mem
    {p B q d : ℕ} (hq : q.Prime) (hpq : p < q)
    (hd : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow p B q) :
    q * d ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q := by
  rcases Finset.mem_filter.mp hd with ⟨hdIcc, hdSq, hdRough, hdLt⟩
  rcases Finset.mem_Icc.mp hdIcc with ⟨hd1, hdUpper⟩
  have hdPos : 0 < d := by omega
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdPos
  have howner : canonicalLargestPrimeFactor (q * d) = q := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough hdPos hq hdLt
    simpa [Nat.mul_comm] using h
  have hqNotDvd : ¬ q ∣ d := by
    intro hdiv
    by_cases hdOne : d = 1
    · subst d
      exact hq.not_dvd_one hdiv
    · have hdgt : 1 < d := by omega
      have hle := prime_dvd_le_canonicalLargestPrimeFactor hdgt hq hdiv
      omega
  have hcop : Nat.Coprime q d := (hq.coprime_iff_not_dvd).2 hqNotDvd
  have hsqChild : Squarefree (q * d) :=
    (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hdSq⟩
  have hroughChild : RoughAbove p (q * d) := by
    intro r hr
    rcases Nat.mem_primeFactors.mp hr with ⟨hrPrime, hrDvd, _hr0⟩
    rcases hrPrime.dvd_mul.mp hrDvd with hrq | hrd
    · have hrEq : r = q :=
        (Nat.prime_dvd_prime_iff_eq hrPrime hq).mp hrq
      simpa [hrEq] using hpq
    · have hrMem : r ∈ d.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hrPrime, hrd, hd0⟩
      exact hdRough r hrMem
  have hqqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hq2 : q * q * d ≤ B := by
    have h := (Nat.le_div_iff_mul_le hqqPos).1 hdUpper
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hchildLower : 2 ≤ q * d := by
    simpa using Nat.mul_le_mul hq.two_le hd1
  have hqLeQ2 : q ≤ q * q := by
    nlinarith [hq.two_le]
  have hchildB : q * d ≤ B := by
    have hmul : q * d ≤ (q * q) * d := Nat.mul_le_mul_right d hqLeQ2
    exact hmul.trans (by simpa [Nat.mul_assoc] using hq2)
  apply mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mpr
  refine ⟨?_, howner⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hchildLower, hchildB⟩,
      hsqChild, hroughChild⟩
  · calc
      canonicalLargestPrimeFactor (q * d) * (q * d) = q * q * d := by
        rw [howner]
        ring
      _ ≤ B := hq2

/-- Reconstructing an interval-prime daughter and stripping its owner returns
the same daughter. -/
theorem lowWheelFrozenSourceSquareResidualDaughter_child_cofactor
    {p B q d : ℕ} (hq : q.Prime) (_hpq : p < q)
    (hd : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow p B q) :
    canonicalCofactor (q * d) = d := by
  rcases Finset.mem_filter.mp hd with ⟨hdIcc, _hdSq, _hdRough, hdLt⟩
  have hdPos : 0 < d := by
    have h := (Finset.mem_Icc.mp hdIcc).1
    omega
  have h := canonicalCofactor_mul_prime_eq_of_rough hdPos hq hdLt
  simpa [Nat.mul_comm] using h

/-- The canonical cofactor map gives the exact fixed-owner carrier bijection. -/
theorem lowWheelFrozenSourceSquareResidualOwnerFiber_image_cofactor
    {p B q : ℕ} (hq : q.Prime) (hpq : p < q) :
    (lowWheelFrozenSourceSquareResidualOwnerFiber p B q).image
        canonicalCofactor =
      lowWheelFrozenSourceSquareResidualDaughterWindow p B q := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨c, hc, rfl⟩
    exact canonicalCofactor_mem_lowWheelFrozenSourceSquareResidualDaughterWindow hc
  · intro hd
    have hc := lowWheelFrozenSourceSquareResidualDaughter_child_mem hq hpq hd
    have hco :=
      lowWheelFrozenSourceSquareResidualDaughter_child_cofactor hq hpq hd
    exact Finset.mem_image.mpr ⟨q * d, hc, hco⟩

/-- Canonical cofactor stripping is injective on one fixed owner fibre. -/
theorem lowWheelFrozenSourceSquareResidualOwnerFiber_cofactor_injective
    {p B q c z : ℕ}
    (hc : c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q)
    (hz : z ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q)
    (hco : canonicalCofactor c = canonicalCofactor z) : c = z := by
  rcases lowWheelFrozenSourceSquareResidualOwnerFiber_data hc with
    ⟨_hcPrime, _hcp, _hcSq, _hcRough, _hcLt, hcfactor, _hcq2, _hcweight⟩
  rcases lowWheelFrozenSourceSquareResidualOwnerFiber_data hz with
    ⟨_hzPrime, _hzp, _hzSq, _hzRough, _hzLt, hzfactor, _hzq2, _hzweight⟩
  calc
    c = q * canonicalCofactor c := hcfactor.symm
    _ = q * canonicalCofactor z := by rw [hco]
    _ = z := hzfactor

/-- **Exact fixed-owner signed q^2 descent.**  Only after the whole owner fibre
is reassembled do we strip `q`; the result is the negative Möbius mass of the
entire interval-prime daughter window. -/
theorem lowWheelFrozenSourceSquareResidualOwnerFiber_mass_eq_neg_daughterMass
    {p B q : ℕ} (hq : q.Prime) (hpq : p < q) :
    (∑ c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q,
        canonicalMoebiusWeight c) =
      -∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow p B q,
        canonicalMoebiusWeight d := by
  let S := lowWheelFrozenSourceSquareResidualOwnerFiber p B q
  let D := lowWheelFrozenSourceSquareResidualDaughterWindow p B q
  have himage : S.image canonicalCofactor = D := by
    simpa [S, D] using
      lowWheelFrozenSourceSquareResidualOwnerFiber_image_cofactor hq hpq
  have hsumImage :
      (∑ d ∈ S.image canonicalCofactor, canonicalMoebiusWeight d) =
        ∑ c ∈ S, canonicalMoebiusWeight (canonicalCofactor c) := by
    apply Finset.sum_image
    intro c hc z hz hco
    exact lowWheelFrozenSourceSquareResidualOwnerFiber_cofactor_injective
      hc hz hco
  calc
    (∑ c ∈ S, canonicalMoebiusWeight c) =
        ∑ c ∈ S, -canonicalMoebiusWeight (canonicalCofactor c) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (lowWheelFrozenSourceSquareResidualOwnerFiber_data hc).2.2.2.2.2.2.2
    _ = -(∑ c ∈ S, canonicalMoebiusWeight (canonicalCofactor c)) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∑ d ∈ S.image canonicalCofactor, canonicalMoebiusWeight d) := by
      rw [← hsumImage]
    _ = -(∑ d ∈ D, canonicalMoebiusWeight d) := by rw [himage]

end RHLean.Proof
