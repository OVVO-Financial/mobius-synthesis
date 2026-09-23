import RHLean.Proof.StableFarWallLowCofactorQ2Descent
import RHLean.Proof.SquareRootLowPrimeGoRecursiveDescent

/-!
# The descended far wall is a literal far slice of the q^2 child transport

After stripping the largest prime `q=P+(c)` from a nonunit far-wall cofactor
`c=q*d`, the descended half satisfies

  q^2 * d * p <= X_R,

with `p >= R+8`.  Therefore `(d,p)` is exactly a far-prime transport pair at
the child cutoff `Y_q = X_R/q^2`: `d` lies in the frozen predecessor cube
below `q`, and `d*p <= Y_q`.

Conversely every such child far-transport pair reconstructs the unique original
far-wall cofactor `c=q*d`.  The inequality `c<R` is forced by `p>R` together
with `q^2*d*p <= R^2-1`; no additional root hypothesis is inserted.

This module proves that ownerwise carrier equality before taking any norm.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Descended far-wall triples with fixed canonical low owner `q`. -/
def lowWheelFarPrimeQ2DescendedOwnerTriples (R q : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeQ2DescendedTriples R).filter fun t => t.1 = q

/-- Far-prime transport pairs in the frozen predecessor cube at the literal
q^2 child cutoff. -/
def lowWheelFarPrimeQ2ChildFarSlice (R q : ℕ) : Finset (ℕ × ℕ) :=
  ((squareRootLowPrimeGoSmoothCofactors q
      (squareRootEndpoint R / (q * q))).product
    (Finset.Icc (R + 8) (squareRootEndpoint R))).filter fun dp =>
      dp.2.Prime ∧
        dp.1 * dp.2 ≤ squareRootEndpoint R / (q * q)

@[simp] theorem mem_lowWheelFarPrimeQ2ChildFarSlice
    {R q d p : ℕ} :
    (d,p) ∈ lowWheelFarPrimeQ2ChildFarSlice R q ↔
      d ∈ squareRootLowPrimeGoSmoothCofactors q
        (squareRootEndpoint R / (q * q)) ∧
      p ∈ Finset.Icc (R + 8) (squareRootEndpoint R) ∧
      p.Prime ∧ d * p ≤ squareRootEndpoint R / (q * q) := by
  simp [lowWheelFarPrimeQ2ChildFarSlice, and_assoc]

private theorem squareRootEndpoint_lt_square
    {R : ℕ} (hR : 0 < R) :
    squareRootEndpoint R < R * R := by
  unfold squareRootEndpoint
  have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hR)
  simpa [pow_two] using Nat.pred_lt hne

private theorem freshPrime_mul_squarefree
    {q d : ℕ} (hq : q.Prime) (hd1 : 1 ≤ d)
    (hdsq : Squarefree d) (hrough : canonicalLargestPrimeFactor d < q) :
    Squarefree (q * d) := by
  have hdpos : 0 < d := by omega
  have hnot : ¬ q ∣ d :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hdpos hq hrough
  have hcop : Nat.Coprime q d := (hq.coprime_iff_not_dvd).2 hnot
  exact (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hdsq⟩

private theorem freshPrime_canonical_coordinates
    {q d : ℕ} (hq : q.Prime) (hd1 : 1 ≤ d)
    (hrough : canonicalLargestPrimeFactor d < q) :
    canonicalLargestPrimeFactor (q * d) = q ∧
      canonicalCofactor (q * d) = d := by
  have hdpos : 0 < d := by omega
  constructor
  · have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough hdpos hq hrough
    simpa [Nat.mul_comm] using h
  · have h := canonicalCofactor_mul_prime_eq_of_rough hdpos hq hrough
    simpa [Nat.mul_comm] using h

/-- **Exact ownerwise carrier identification.**  Forgetting the fixed owner tag
maps the descended far-wall triples bijectively onto the literal far-prime
transport slice of the q^2 child. -/
theorem lowWheelFarPrimeQ2DescendedOwner_image_eq_childFarSlice
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    (lowWheelFarPrimeQ2DescendedOwnerTriples R q).image Prod.snd =
      lowWheelFarPrimeQ2ChildFarSlice R q := by
  ext dp
  rcases dp with ⟨d,p⟩
  constructor
  · intro hdp
    rcases Finset.mem_image.mp hdp with ⟨t, htOwner, htEq⟩
    rcases t with ⟨r,⟨e,s⟩⟩
    have hpair : (e,s) = (d,p) := by
      simpa using htEq
    rcases hpair with ⟨rfl, rfl⟩
    rcases Finset.mem_filter.mp htOwner with ⟨htDesc, hrq⟩
    have hrq' : r = q := hrq
    subst r
    rcases Finset.mem_filter.mp htDesc with ⟨htTriple, hq2⟩
    rcases Finset.mem_image.mp htTriple with ⟨cp, hcp, htag⟩
    rcases cp with ⟨c,u⟩
    change
      (canonicalLargestPrimeFactor c, (canonicalCofactor c, u)) =
        (q, (d, p)) at htag
    have hqEq : canonicalLargestPrimeFactor c = q :=
      congrArg (fun z : ℕ × (ℕ × ℕ) => z.1) htag
    have hdEq : canonicalCofactor c = d :=
      congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1) htag
    have hpEq : u = p :=
      congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.2) htag
    have hdata := lowWheelFarPrimeNonUnitPair_data hcp
    have hprod : canonicalLargestPrimeFactor c * canonicalCofactor c = c :=
      hdata.2.2.2.2.2.2.1
    have hdcPos : 0 < canonicalCofactor c := by
      by_contra hnot
      have hzero : canonicalCofactor c = 0 := by omega
      rw [hzero, mul_zero] at hprod
      have hcgt : 1 < c := (Finset.mem_filter.mp hcp).2
      omega
    have hd1 : 1 ≤ d := by
      rw [← hdEq]
      exact hdcPos
    have hdsq : Squarefree d := by
      simpa [hqEq, hdEq, hpEq] using hdata.2.2.2.2.1
    have hrough : canonicalLargestPrimeFactor d < q := by
      simpa [hqEq, hdEq, hpEq] using hdata.2.2.2.2.2.1
    have hpRange : p ∈ Finset.Icc (R + 8) (squareRootEndpoint R) := by
      have hpair0 := (mem_lowWheelFarPrimeSquarefreePairSet.mp
        (Finset.mem_filter.mp hcp).1).1
      have hu := (mem_lowWheelFarPrimePairSet.mp hpair0).2.1
      simpa [hpEq] using hu
    have hpPrime : p.Prime := by
      simpa [hpEq] using hdata.2.2.2.1
    have hqqpos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
    have hdpCut : d * p ≤ squareRootEndpoint R / (q * q) := by
      apply (Nat.le_div_iff_mul_le hqqpos).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2
    have hdCut : d ≤ squareRootEndpoint R / (q * q) := by
      have hdpGe : d ≤ d * p := by
        have h := Nat.mul_le_mul_left d hpPrime.one_le
        simpa using h
      exact hdpGe.trans hdpCut
    exact mem_lowWheelFarPrimeQ2ChildFarSlice.mpr
      ⟨mem_squareRootLowPrimeGoSmoothCofactors.mpr
          ⟨hd1, hdCut, hdsq, hrough⟩,
        hpRange, hpPrime, hdpCut⟩
  · intro hdp
    rcases mem_lowWheelFarPrimeQ2ChildFarSlice.mp hdp with
      ⟨hdSmooth, hpRange, hpPrime, hdpCut⟩
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hdSmooth with
      ⟨hd1, _hdY, hdsq, hrough⟩
    have hcoords := freshPrime_canonical_coordinates hq hd1 hrough
    have hsqC : Squarefree (q * d) :=
      freshPrime_mul_squarefree hq hd1 hdsq hrough
    have hqqpos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
    have hq2 : q * q * d * p ≤ squareRootEndpoint R := by
      have h := (Nat.le_div_iff_mul_le hqqpos).1 hdpCut
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    have hRpos : 0 < R := by omega
    have hcR : q * d < R := by
      by_contra hnot
      have hRc : R ≤ q * d := Nat.le_of_not_gt hnot
      have hpR : R ≤ p := by
        have := (Finset.mem_Icc.mp hpRange).1
        omega
      have hR2cp : R * R ≤ (q * d) * p := Nat.mul_le_mul hRc hpR
      have hq1 : 1 ≤ q := hq.one_le
      have hcpq : (q * d) * p ≤ q * q * d * p := by
        have h := Nat.mul_le_mul_right ((q * d) * p) hq1
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      have hXlt := squareRootEndpoint_lt_square hRpos
      exact (Nat.not_lt_of_ge (hR2cp.trans (hcpq.trans hq2))) hXlt
    have hcpX : (q * d) * p ≤ squareRootEndpoint R := by
      have hq1 : 1 ≤ q := hq.one_le
      have hle : (q * d) * p ≤ q * q * d * p := by
        have h := Nat.mul_le_mul_right ((q * d) * p) hq1
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      exact hle.trans hq2
    have hcgt : 1 < q * d := by
      have hq2' := hq.two_le
      nlinarith
    have hpair : (q * d, p) ∈ lowWheelFarPrimePairSet R := by
      apply mem_lowWheelFarPrimePairSet.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨by omega, hcR⟩,
        hpRange, hpPrime, hcpX⟩
    have hpairSq : (q * d, p) ∈ lowWheelFarPrimeSquarefreePairSet R :=
      mem_lowWheelFarPrimeSquarefreePairSet.mpr ⟨hpair, hsqC⟩
    have hpairNon : (q * d, p) ∈ lowWheelFarPrimeNonUnitPairSet R :=
      Finset.mem_filter.mpr ⟨hpairSq, hcgt⟩
    have htag :
        lowWheelFarPrimeLowCofactorTag (q * d, p) = (q,(d,p)) := by
      simp [lowWheelFarPrimeLowCofactorTag, hcoords.1, hcoords.2]
    have htriple : (q,(d,p)) ∈ lowWheelFarPrimeLowCofactorTriples R := by
      unfold lowWheelFarPrimeLowCofactorTriples
      exact Finset.mem_image.mpr ⟨(q * d,p), hpairNon, htag⟩
    have hdesc : (q,(d,p)) ∈ lowWheelFarPrimeQ2DescendedTriples R :=
      Finset.mem_filter.mpr ⟨htriple, hq2⟩
    have howner : (q,(d,p)) ∈ lowWheelFarPrimeQ2DescendedOwnerTriples R q :=
      Finset.mem_filter.mpr ⟨hdesc, rfl⟩
    exact Finset.mem_image.mpr ⟨(q,(d,p)), howner, rfl⟩

private theorem lowWheelFarPrimeQ2DescendedOwner_snd_injOn
    (R q : ℕ) :
    Set.InjOn Prod.snd
      (lowWheelFarPrimeQ2DescendedOwnerTriples R q :
        Set (ℕ × (ℕ × ℕ))) := by
  intro a ha b hb hab
  have haQ := (Finset.mem_filter.mp ha).2
  have hbQ := (Finset.mem_filter.mp hb).2
  apply Prod.ext
  · exact haQ.trans hbQ.symm
  · exact hab

/-- Signed mass of a descended owner fibre equals the Möbius mass of the
corresponding child far-transport slice. -/
theorem lowWheelFarPrimeQ2DescendedOwner_mass_eq_childFarSlice
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    (∑ t ∈ lowWheelFarPrimeQ2DescendedOwnerTriples R q,
        canonicalMoebiusWeight t.2.1) =
      ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1 := by
  have himage := lowWheelFarPrimeQ2DescendedOwner_image_eq_childFarSlice hq hqR
  rw [← himage]
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact lowWheelFarPrimeQ2DescendedOwner_snd_injOn R q ha hb hab

end RHLean.Proof
