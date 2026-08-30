import Mathlib
import RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms

/-!
# The unique outward-closure failure in the high channel

A post-root partner has no numerical birth condition and no further roughness
condition: its prime and root-range data are independent of the cofactor.  Once
`r` belongs to the post-root partner set of a smaller cofactor `a`, it belongs
to the partner set of a larger cofactor `b` exactly while the enlarged product
still lies below the square endpoint.

Thus the outward high square defect is precisely

```text
a*r <= R^2-1 < b*r.
```

Together with reverse-square closure, this proves that every high-channel
four-corner defect is one orientation of the existing hyperbolic first-failure
boundary.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A retained post-root partner survives enlargement of the cofactor exactly
when the enlarged product remains below the square endpoint. -/
theorem mem_squareRootPostRootPrimePartnerSet_of_lower_iff_product
    {R a b r : ℕ}
    (hrLower : r ∈ squareRootPostRootPrimePartnerSet R a) :
    r ∈ squareRootPostRootPrimePartnerSet R b ↔
      b * r ≤ squareRootEndpoint R := by
  unfold squareRootPostRootPrimePartnerSet at hrLower ⊢
  rcases Finset.mem_filter.mp hrLower with
    ⟨hrRange, hrPrime, _harX⟩
  constructor
  · intro hrUpper
    exact (Finset.mem_filter.mp hrUpper).2.2
  · intro hbrX
    exact Finset.mem_filter.mpr ⟨hrRange, hrPrime, hbrX⟩

/-- Post-root partners lost when enlarging `a` to `b`. -/
def squareRootPostRootPrimePartnerProductBoundary
    (R a b : ℕ) : Finset ℕ :=
  (squareRootPostRootPrimePartnerSet R a).filter fun r =>
    squareRootEndpoint R < b * r

@[simp] theorem mem_squareRootPostRootPrimePartnerProductBoundary
    {R a b r : ℕ} :
    r ∈ squareRootPostRootPrimePartnerProductBoundary R a b ↔
      r ∈ squareRootPostRootPrimePartnerSet R a ∧
        squareRootEndpoint R < b * r := by
  simp [squareRootPostRootPrimePartnerProductBoundary]

/-- **The outward high defect is exactly the product boundary.** -/
theorem squareRootPostRootPrimePartnerSet_sdiff_larger_eq_productBoundary
    (R a b : ℕ) :
    squareRootPostRootPrimePartnerSet R a \
        squareRootPostRootPrimePartnerSet R b =
      squareRootPostRootPrimePartnerProductBoundary R a b := by
  ext r
  constructor
  · intro hr
    rcases Finset.mem_sdiff.mp hr with ⟨hrLower, hrNotUpper⟩
    apply mem_squareRootPostRootPrimePartnerProductBoundary.mpr
    refine ⟨hrLower, ?_⟩
    have hiff :=
      mem_squareRootPostRootPrimePartnerSet_of_lower_iff_product
        (b := b) hrLower
    exact Nat.lt_of_not_ge (fun hbr => hrNotUpper (hiff.mpr hbr))
  · intro hr
    rcases mem_squareRootPostRootPrimePartnerProductBoundary.mp hr with
      ⟨hrLower, hcross⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hrLower, ?_⟩
    intro hrUpper
    have hbr :=
      (mem_squareRootPostRootPrimePartnerSet_of_lower_iff_product
        (b := b) hrLower).mp hrUpper
    omega

/-- Multiplicative specialization used by a prime extension. -/
theorem squareRootPostRootPrimePartnerSet_sdiff_mul_eq_productBoundary
    (R p a : ℕ) :
    squareRootPostRootPrimePartnerSet R a \
        squareRootPostRootPrimePartnerSet R (p * a) =
      squareRootPostRootPrimePartnerProductBoundary R a (p * a) := by
  exact squareRootPostRootPrimePartnerSet_sdiff_larger_eq_productBoundary
    R a (p * a)

end RHLean.Proof
