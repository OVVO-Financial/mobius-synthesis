import RHLean.Proof.StableFarWallCrossingRenewal

/-!
# Well-founded descent of the stable-far crossing renewal

The crossing renewal is not merely a return to the same physical wall.
It is a strict arithmetic descent.

A crossing product is indexed by `(q, d*p)`, where `q` is the canonical largest
prime stripped from the old low cofactor `c=q*d`, and the returned stable-wall
state has low cofactor `d`. Thus one renewal step replaces `q*d` by `d`.

If a returned state is itself the parent of a second crossing, then the second
stripped owner is the canonical largest prime of `d`, hence is strictly smaller
than the previous owner `q`. The full renewal key retains both the low cofactor
and the genuine far prime. Along compatible successive renewal steps the
second-contact load `q^2*d*p` therefore decreases strictly as well.

No estimate, norm, Mertens hypothesis, or asymptotic input is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- Low cofactor before the crossing owner is stripped. For a crossing product
`(q,d*p)` this is `q*d`. -/
def lowWheelFarPrimeCrossingParentLowCofactor (x : ℕ × ℕ) : ℕ :=
  x.1 * canonicalCofactor x.2

/-- Low cofactor after the crossing owner is stripped. For a crossing product
`(q,d*p)` this is `d`. -/
def lowWheelFarPrimeCrossingRenewalLowCofactor (x : ℕ × ℕ) : ℕ :=
  canonicalCofactor x.2

/-- Parent arithmetic key: old low cofactor together with the unchanged far
prime. -/
def lowWheelFarPrimeCrossingParentKey (x : ℕ × ℕ) : ℕ × ℕ :=
  (lowWheelFarPrimeCrossingParentLowCofactor x,
    canonicalLargestPrimeFactor x.2)

/-- Renewal arithmetic key: stripped low cofactor together with the unchanged
far prime. -/
def lowWheelFarPrimeCrossingRenewalKey (x : ℕ × ℕ) : ℕ × ℕ :=
  (lowWheelFarPrimeCrossingRenewalLowCofactor x,
    canonicalLargestPrimeFactor x.2)

/-- The second-contact quantity whose comparison with `X_R` defines the exact
q^2 descended/crossing split. -/
def lowWheelFarPrimeCrossingSecondContactLoad (x : ℕ × ℕ) : ℕ :=
  x.1 * x.1 * canonicalCofactor x.2 * canonicalLargestPrimeFactor x.2

/-- **One renewal step strictly decreases the low cofactor.** -/
theorem lowWheelFarPrimeCrossingRenewalLowCofactor_lt_parent
    {R : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    lowWheelFarPrimeCrossingRenewalLowCofactor x <
      lowWheelFarPrimeCrossingParentLowCofactor x := by
  rcases Finset.mem_image.mp hx with ⟨t, htCross, rfl⟩
  have ht : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htCross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hq, _hqR, hd1, _hp, _hpR, _hdsq, _hdq, _hcut⟩
  have hcoords := lowWheelFarPrimeProduct_coordinates ht
  have hcof : canonicalCofactor (t.2.1 * t.2.2) = t.2.1 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.2
  simp only [lowWheelFarPrimeCrossingRenewalLowCofactor,
    lowWheelFarPrimeCrossingParentLowCofactor, lowWheelFarPrimeProductKey]
  rw [hcof]
  have hq2 : 2 ≤ t.1 := hq.two_le
  nlinarith

/-- If a returned crossing state is used as the parent of another crossing,
then the next stripped owner is strictly smaller than the previous owner. -/
theorem lowWheelFarPrimeCrossing_nested_owner_lt
    {R : ℕ} {x y : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hy : y ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hchain : lowWheelFarPrimeCrossingParentLowCofactor y =
      lowWheelFarPrimeCrossingRenewalLowCofactor x) :
    y.1 < x.1 := by
  rcases Finset.mem_image.mp hx with ⟨tx, htxCross, htxEq⟩
  rcases Finset.mem_image.mp hy with ⟨ty, htyCross, htyEq⟩
  have htx : tx ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htxCross).1
  have hty : ty ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htyCross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data htx with
    ⟨_hqx, _hqxR, _hdx1, _hpx, _hpxR, _hdxsq, hdxq, _hcutx⟩
  rcases lowWheelFarPrimeLowCofactorTriple_data hty with
    ⟨hqy, _hqyR, hdy1, _hpy, _hpyR, _hdysq, hdyq, _hcuty⟩
  have hcoordsX := lowWheelFarPrimeProduct_coordinates htx
  have hcoordsY := lowWheelFarPrimeProduct_coordinates hty
  have hcofX : canonicalCofactor (tx.2.1 * tx.2.2) = tx.2.1 := by
    simpa [lowWheelFarPrimeProductKey] using hcoordsX.2
  have hcofY : canonicalCofactor (ty.2.1 * ty.2.2) = ty.2.1 := by
    simpa [lowWheelFarPrimeProductKey] using hcoordsY.2
  have hchain' : ty.1 * ty.2.1 = tx.2.1 := by
    rw [← htxEq, ← htyEq] at hchain
    simpa [lowWheelFarPrimeCrossingParentLowCofactor,
      lowWheelFarPrimeCrossingRenewalLowCofactor, lowWheelFarPrimeProductKey,
      hcofX, hcofY] using hchain
  have hdyPos : 0 < ty.2.1 := by omega
  have hlpfY : canonicalLargestPrimeFactor (ty.1 * ty.2.1) = ty.1 := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hdyPos hqy hdyq
    simpa [Nat.mul_comm] using h
  have hownerEq : ty.1 = canonicalLargestPrimeFactor tx.2.1 := by
    have h := congrArg canonicalLargestPrimeFactor hchain'
    rw [hlpfY] at h
    exact h
  have hlt : ty.1 < tx.1 := by
    rw [hownerEq]
    exact hdxq
  rw [← htxEq, ← htyEq]
  simpa [lowWheelFarPrimeProductKey] using hlt

/-- A crossing product has positive renewal cofactor and positive far-prime
coordinate. -/
private theorem crossingProduct_positive_coordinates
    {R : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    0 < lowWheelFarPrimeCrossingRenewalLowCofactor x ∧
      0 < canonicalLargestPrimeFactor x.2 ∧ 2 ≤ x.1 := by
  rcases Finset.mem_image.mp hx with ⟨t, htCross, htx⟩
  have ht : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htCross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hq, _hqR, hd1, hp, _hpR, _hdsq, _hdq, _hcut⟩
  have hcoords := lowWheelFarPrimeProduct_coordinates ht
  have hcof : canonicalCofactor (t.2.1 * t.2.2) = t.2.1 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.2
  have hfar : canonicalLargestPrimeFactor (t.2.1 * t.2.2) = t.2.2 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.1
  rw [← htx]
  simp only [lowWheelFarPrimeCrossingRenewalLowCofactor,
    lowWheelFarPrimeProductKey]
  rw [hcof, hfar]
  exact ⟨by omega, hp.pos, hq.two_le⟩

/-- A full compatible renewal step preserves the far prime and strictly lowers
the second-contact load. -/
theorem lowWheelFarPrimeCrossing_nested_secondContactLoad_lt
    {R : ℕ} {x y : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hy : y ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hchain : lowWheelFarPrimeCrossingParentKey y =
      lowWheelFarPrimeCrossingRenewalKey x) :
    lowWheelFarPrimeCrossingSecondContactLoad y <
      lowWheelFarPrimeCrossingSecondContactLoad x := by
  have hcofactor : lowWheelFarPrimeCrossingParentLowCofactor y =
      lowWheelFarPrimeCrossingRenewalLowCofactor x :=
    congrArg Prod.fst hchain
  have hfar : canonicalLargestPrimeFactor y.2 =
      canonicalLargestPrimeFactor x.2 := congrArg Prod.snd hchain
  have howner := lowWheelFarPrimeCrossing_nested_owner_lt hx hy hcofactor
  rcases crossingProduct_positive_coordinates hx with
    ⟨hcofPos, hfarPos, hxTwo⟩
  have hownerSq : y.1 < x.1 * x.1 := by
    have hxLeSq : x.1 ≤ x.1 * x.1 := by nlinarith
    exact howner.trans_le hxLeSq
  have hfactorPos :
      0 < lowWheelFarPrimeCrossingRenewalLowCofactor x *
        canonicalLargestPrimeFactor x.2 := Nat.mul_pos hcofPos hfarPos
  have hmul := Nat.mul_lt_mul_of_pos_right hownerSq hfactorPos
  unfold lowWheelFarPrimeCrossingSecondContactLoad
  unfold lowWheelFarPrimeCrossingParentLowCofactor at hcofactor
  unfold lowWheelFarPrimeCrossingRenewalLowCofactor at hcofactor hfactorPos hmul
  calc
    y.1 * y.1 * canonicalCofactor y.2 * canonicalLargestPrimeFactor y.2 =
        y.1 * (y.1 * canonicalCofactor y.2) *
          canonicalLargestPrimeFactor y.2 := by ring
    _ = y.1 * canonicalCofactor x.2 *
          canonicalLargestPrimeFactor x.2 := by rw [hcofactor, hfar]
    _ = y.1 * (canonicalCofactor x.2 *
          canonicalLargestPrimeFactor x.2) := by ring
    _ < (x.1 * x.1) * (canonicalCofactor x.2 *
          canonicalLargestPrimeFactor x.2) := hmul
    _ = x.1 * x.1 * canonicalCofactor x.2 *
          canonicalLargestPrimeFactor x.2 := by ring

/-- Once a compatible lower renewal step fits below a cutoff, every still lower
compatible step also fits. -/
theorem lowWheelFarPrimeCrossing_nested_descended_monotone
    {R X : ℕ} {x y : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hy : y ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hchain : lowWheelFarPrimeCrossingParentKey y =
      lowWheelFarPrimeCrossingRenewalKey x)
    (hdesc : lowWheelFarPrimeCrossingSecondContactLoad x ≤ X) :
    lowWheelFarPrimeCrossingSecondContactLoad y ≤ X := by
  exact (lowWheelFarPrimeCrossing_nested_secondContactLoad_lt hx hy hchain).le.trans hdesc

/-- Two strict crossing renewals cannot form a two-cycle. -/
theorem lowWheelFarPrimeCrossing_no_twoCycle
    {R : ℕ} {x y : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (hy : y ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    ¬ (lowWheelFarPrimeCrossingParentLowCofactor y =
          lowWheelFarPrimeCrossingRenewalLowCofactor x ∧
        lowWheelFarPrimeCrossingParentLowCofactor x =
          lowWheelFarPrimeCrossingRenewalLowCofactor y) := by
  rintro ⟨hyx, hxy⟩
  have h1 := lowWheelFarPrimeCrossing_nested_owner_lt hx hy hyx
  have h2 := lowWheelFarPrimeCrossing_nested_owner_lt hy hx hxy
  omega

end RHLean.Proof
