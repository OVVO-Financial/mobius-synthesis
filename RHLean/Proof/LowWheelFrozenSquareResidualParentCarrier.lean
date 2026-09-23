import RHLean.Proof.LowWheelFrozenSquareResidualParentProduct

/-!
# Flatten the frozen q^2 telescope onto the true parent Mobius carrier

The previous module proves that every source-scale / daughter pair `(A,d)`
represents the genuine arithmetic product `m=A*d`, with exact Mobius parity and
no multiplicity for a fixed square owner.  This file performs the finite Fubini
step left implicit in an earlier layer.

We first retain all three canonical coordinates `(A,q,d)` in a tagged finite
carrier.  Because the tags are literal coordinates, its nested source-scale and
owner fibres are disjoint.  We then map

`(A,q,d) |-> (q, A*d)`.

The map is injective: equality of the first coordinate fixes `q`, and the
fixed-owner injectivity theorem from `LowWheelFrozenSquareResidualParentProduct`
then recovers both `A` and `d`.  Consequently the whole q^2 square residual is
an honest signed Mobius sum over a finite `(q,m)` carrier before any norm is
taken.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Tagged daughters for one represented source scale and one square owner. -/
def lowWheelFrozenSquareResidualTripleFiber
    (R A q : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q).image
    (fun d => (A, (q, d)))

/-- All tagged q^2 daughters attached to one source scale. -/
def lowWheelFrozenSquareResidualTriplesAtScale
    (R A : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFrozenSourceSquareResidualOwners
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A)).biUnion
    (fun q => lowWheelFrozenSquareResidualTripleFiber R A q)

/-- Global tagged q^2 daughter carrier after an earlier layer. -/
def lowWheelFrozenSquareResidualTriples
    (R : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFrozenSecondContactSourceScaleSet R).biUnion
    (fun A => lowWheelFrozenSquareResidualTriplesAtScale R A)

@[simp] theorem mem_lowWheelFrozenSquareResidualTriples
    {R A q d : ℕ} :
    (A, (q, d)) ∈ lowWheelFrozenSquareResidualTriples R ↔
      A ∈ lowWheelFrozenSecondContactSourceScaleSet R ∧
      q ∈ lowWheelFrozenSourceSquareResidualOwners
        (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) ∧
      d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
        (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q := by
  simp [lowWheelFrozenSquareResidualTriples,
    lowWheelFrozenSquareResidualTriplesAtScale,
    lowWheelFrozenSquareResidualTripleFiber]

private theorem lowWheelFrozenSquareResidualTripleFiber_pairwise
    (R A : ℕ) :
    Set.PairwiseDisjoint
      (↑(lowWheelFrozenSourceSquareResidualOwners
        (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A)))
      (fun q => lowWheelFrozenSquareResidualTripleFiber R A q) := by
  intro q _hq r _hr hqr
  change Disjoint
    (lowWheelFrozenSquareResidualTripleFiber R A q)
    (lowWheelFrozenSquareResidualTripleFiber R A r)
  rw [Finset.disjoint_left]
  intro t htq htr
  rcases Finset.mem_image.mp htq with ⟨d, _hd, hdt⟩
  rcases Finset.mem_image.mp htr with ⟨e, _he, het⟩
  have hqe : q = r := by
    have h := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1)
      (hdt.trans het.symm)
    simpa using h
  exact hqr hqe

private theorem lowWheelFrozenSquareResidualTriplesAtScale_fst
    {R A : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFrozenSquareResidualTriplesAtScale R A) :
    t.1 = A := by
  rcases Finset.mem_biUnion.mp ht with ⟨q, _hq, htq⟩
  rcases Finset.mem_image.mp htq with ⟨d, _hd, hdt⟩
  have h := congrArg (fun z : ℕ × (ℕ × ℕ) => z.1) hdt
  simpa using h.symm

private theorem lowWheelFrozenSquareResidualTriplesAtScale_pairwise
    (R : ℕ) :
    Set.PairwiseDisjoint (↑(lowWheelFrozenSecondContactSourceScaleSet R))
      (fun A => lowWheelFrozenSquareResidualTriplesAtScale R A) := by
  intro A _hA B _hB hAB
  change Disjoint
    (lowWheelFrozenSquareResidualTriplesAtScale R A)
    (lowWheelFrozenSquareResidualTriplesAtScale R B)
  rw [Finset.disjoint_left]
  intro t htA htB
  have hfstA := lowWheelFrozenSquareResidualTriplesAtScale_fst htA
  have hfstB := lowWheelFrozenSquareResidualTriplesAtScale_fst htB
  exact hAB (hfstA.symm.trans hfstB)

private theorem lowWheelFrozenSquareResidualTripleFiber_sum
    (R A q : ℕ) (f : ℕ × (ℕ × ℕ) → ℂ) :
    (∑ t ∈ lowWheelFrozenSquareResidualTripleFiber R A q, f t) =
      ∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
          (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q,
        f (A, (q, d)) := by
  unfold lowWheelFrozenSquareResidualTripleFiber
  rw [Finset.sum_image]
  intro d _hd e _he hde
  have h := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.2) hde
  simpa using h

private theorem lowWheelFrozenSquareResidualTriplesAtScale_sum
    (R A : ℕ) (f : ℕ × (ℕ × ℕ) → ℂ) :
    (∑ t ∈ lowWheelFrozenSquareResidualTriplesAtScale R A, f t) =
      ∑ q ∈ lowWheelFrozenSourceSquareResidualOwners
          (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A),
        ∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
            (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q,
          f (A, (q, d)) := by
  unfold lowWheelFrozenSquareResidualTriplesAtScale
  rw [Finset.sum_biUnion
    (lowWheelFrozenSquareResidualTripleFiber_pairwise R A)]
  apply Finset.sum_congr rfl
  intro q _hq
  exact lowWheelFrozenSquareResidualTripleFiber_sum R A q f

/-- The tagged carrier is exactly the nested `A,q,d` sum from an earlier layer. -/
theorem lowWheelFrozenSquareResidualTriples_sum
    (R : ℕ) (f : ℕ × (ℕ × ℕ) → ℂ) :
    (∑ t ∈ lowWheelFrozenSquareResidualTriples R, f t) =
      ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        ∑ q ∈ lowWheelFrozenSourceSquareResidualOwners
            (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A),
          ∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
              (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q,
            f (A, (q, d)) := by
  unfold lowWheelFrozenSquareResidualTriples
  rw [Finset.sum_biUnion
    (lowWheelFrozenSquareResidualTriplesAtScale_pairwise R)]
  apply Finset.sum_congr rfl
  intro A _hA
  exact lowWheelFrozenSquareResidualTriplesAtScale_sum R A f

/-- Forget the source-scale split only after retaining the square owner. -/
def lowWheelFrozenSquareResidualParentKey
    (t : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (t.2.1, t.1 * t.2.2)

/-- The true arithmetic `(square owner, parent product)` carrier. -/
def lowWheelFrozenSquareResidualParentCarrier (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFrozenSquareResidualTriples R).image
    lowWheelFrozenSquareResidualParentKey

/-- The parent key is injective on the actual tagged daughter carrier. -/
theorem lowWheelFrozenSquareResidualParentKey_injOn (R : ℕ) :
    Set.InjOn lowWheelFrozenSquareResidualParentKey
      (lowWheelFrozenSquareResidualTriples R : Set (ℕ × (ℕ × ℕ))) := by
  intro t ht u hu hkey
  rcases t with ⟨A, ⟨q, d⟩⟩
  rcases u with ⟨A', ⟨q', d'⟩⟩
  change (q, A * d) = (q', A' * d') at hkey
  have hq : q = q' := congrArg Prod.fst hkey
  have hprod : A * d = A' * d' := congrArg Prod.snd hkey
  subst q'
  have htData := (mem_lowWheelFrozenSquareResidualTriples).mp ht
  have huData := (mem_lowWheelFrozenSquareResidualTriples).mp hu
  rcases lowWheelFrozenSquareResidualDaughter_product_injective_fixedOwner
      htData.1 htData.2.2 huData.1 huData.2.2 hprod with ⟨hAeq, hdeq⟩
  subst A'
  subst d'
  rfl

/-- Summing a function of the true parent key loses no multiplicity. -/
theorem lowWheelFrozenSquareResidualParentCarrier_sum
    (R : ℕ) (f : ℕ × ℕ → ℂ) :
    (∑ x ∈ lowWheelFrozenSquareResidualParentCarrier R, f x) =
      ∑ t ∈ lowWheelFrozenSquareResidualTriples R,
        f (lowWheelFrozenSquareResidualParentKey t) := by
  unfold lowWheelFrozenSquareResidualParentCarrier
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact lowWheelFrozenSquareResidualParentKey_injOn R ha hb hab

/-- **Parent-product completion of an earlier layer.**  The complete frozen square residual
is the negative true Mobius mass of a finite `(q,m)` arithmetic carrier.  The
outer source-scale parity has disappeared because it is exactly the missing
part of `mu(m)`, not because it was bounded or replaced. -/
theorem lowWheelFrozenSecondContactSquareResidualQ2Mass_eq_parentCarrier
    (R : ℕ) :
    lowWheelFrozenSecondContactSquareResidualQ2Mass R =
      -∑ x ∈ lowWheelFrozenSquareResidualParentCarrier R,
        canonicalMoebiusWeight x.2 := by
  unfold lowWheelFrozenSecondContactSquareResidualQ2Mass
    lowWheelFrozenSecondContactSquareResidualQ2MassAtScale
  calc
    (∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        -(canonicalMoebiusWeight A *
          ∑ q ∈ lowWheelFrozenSourceSquareResidualOwners
              (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A),
            ∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
                (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q,
              canonicalMoebiusWeight d)) =
      -(∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        ∑ q ∈ lowWheelFrozenSourceSquareResidualOwners
            (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A),
          ∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
              (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q,
            canonicalMoebiusWeight A * canonicalMoebiusWeight d) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro A _hA
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.mul_sum]
    _ = -(∑ t ∈ lowWheelFrozenSquareResidualTriples R,
          canonicalMoebiusWeight t.1 * canonicalMoebiusWeight t.2.2) := by
        rw [lowWheelFrozenSquareResidualTriples_sum]
    _ = -(∑ t ∈ lowWheelFrozenSquareResidualTriples R,
          canonicalMoebiusWeight (t.1 * t.2.2)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        rcases t with ⟨A, ⟨q, d⟩⟩
        have hdata := (mem_lowWheelFrozenSquareResidualTriples).mp ht
        exact (lowWheelFrozenSquareResidualDaughter_productWeight
          hdata.1 hdata.2.2).symm
    _ = -∑ x ∈ lowWheelFrozenSquareResidualParentCarrier R,
          canonicalMoebiusWeight x.2 := by
        rw [lowWheelFrozenSquareResidualParentCarrier_sum]
        rfl

/-- Combining with the parent-product completion removes every auxiliary
source-scale sign from the historical low-side residual. -/
theorem lowWheelFrozenSecondContactSquareResidualMass_eq_parentCarrier
    (R : ℕ) :
    lowWheelFrozenSecondContactSquareResidualMass R =
      -∑ x ∈ lowWheelFrozenSquareResidualParentCarrier R,
        canonicalMoebiusWeight x.2 := by
  rw [lowWheelFrozenSecondContactSquareResidualMass_eq_q2Telescope,
    lowWheelFrozenSecondContactSquareResidualQ2Mass_eq_parentCarrier]

end RHLean.Proof
