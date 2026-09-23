import Mathlib
import RHLean.Proof.SquareRootLowPrimeCombinedResidualSourceNormalForm
import RHLean.Proof.LowWheelFrozenCofactorTopImageHighPrimeObstruction
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Analysis.PrimeSieveCollapseIdentity

/-!
# The stable far-prime wall, after the witness

This continuation concerns only the literal wall carrier.  It retains the
existing far-prime transport identity, records the sign of the single
insertion `c*q`, and proves that the putative `X_R/q^2` daughter scale is zero.
The top-half prime fibres have cofactor one and physical weight one.  None of
these exact statements bounds the complete signed wall mass.

The final sections expose the wall in three exact classical coordinates:

* as the low-cofactor Mertens fibre attached to every far prime;
* as the sum of an inert positive top-half prime block and the lower prime
  fibres that must cancel it;
* as the complementary term in the all-integer Möbius renewal telescope and,
  equivalently, as smooth Möbius mass minus the full-scale Mertens value.

No estimate is introduced.  In particular the complementary identities retain
`M(X_R)` explicitly and therefore identify, rather than hide, the remaining
classical Mertens-scale seam.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- The wall predicate itself is precisely one far-prime insertion into a
squarefree low cofactor.  The prime and the physical cutoff are unchanged. -/
theorem mem_stableFarWallCarrier_iff_primeInsertion
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState} :
    z ∈ stableFarWallCarrier R ↔
      z.1 = ∅ ∧ z.2.2.Prime ∧
      R + 8 ≤ z.2.2 ∧ z.2.2 ≤ squareRootEndpoint R ∧
      z.2.1 ∈ Finset.Ico 1 R ∧ Squarefree z.2.1 ∧
      z.2.1 * z.2.2 ≤ squareRootEndpoint R := by
  rw [stableFarWallCarrier_eq_stableCarrier]
  rcases z with ⟨t, c, q⟩
  constructor
  · exact lowWheelFarTaggedPhysicalStable_geometry hR
  · rintro ⟨rfl, hq, hfar, hqX, hc, hsq, hprod⟩
    exact lowWheelFarTaggedPhysicalStable_of_prime hR hc hsq hq hfar hqX hprod

/-- The wall's native signed mass is exactly the existing far-prime Mertens
transform.  This is the identity on the entire surviving wall. -/
theorem sum_stableFarWallCarrier_eq_farPrimeTransport
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ z ∈ stableFarWallCarrier R, lowWheelFullTaggedPhysicalWeight z) =
      squareRootFarPrimeTransport R := by
  rw [stableFarWallCarrier_eq_stableCarrier,
    ← lowWheelFarTaggedPhysicalLedger_eq_stable]
  exact lowWheelFarTaggedPhysicalLedger_eq_farPrimeTransport R hR

/-- The native wall weight is `mu(c)`, hence the negative of the Möbius
weight of the represented single-insertion integer `c*q`. -/
theorem stableFarWall_singleInsertion_weight
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ stableFarWallCarrier R) :
    lowWheelFullTaggedPhysicalWeight z =
      -canonicalMoebiusWeight (z.2.1 * z.2.2) := by
  rcases (mem_stableFarWallCarrier_iff_primeInsertion hR).mp hz with
    ⟨hface, hq, hfar, _hqX, hc, _hsq, _hprod⟩
  have hcData := Finset.mem_Ico.mp hc
  have hflip := canonicalMoebiusWeight_mul_prime_eq_neg
    (by omega : 0 < z.2.1) (by omega : z.2.1 < z.2.2) hq
  simp [lowWheelFullTaggedPhysicalWeight, hface, booleanCubeSign, hflip]

/-- Every wall prime has exactly zero daughter scale in the `q^2` schedule
at this endpoint.  This does not make the single-insertion population empty. -/
theorem stableFarWall_primeSquare_daughterScale_eq_zero
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ stableFarWallCarrier R) :
    squareRootEndpoint R / (z.2.2 * z.2.2) = 0 := by
  have hfar := ((mem_stableFarWallCarrier_iff_primeInsertion hR).mp hz).2.2.1
  have hRq : R ≤ z.2.2 := by omega
  have hsq : R ^ 2 ≤ z.2.2 * z.2.2 := by
    simpa only [pow_two] using Nat.mul_le_mul hRq hRq
  have hpos : 0 < R ^ 2 := pow_pos (by omega : 0 < R) 2
  apply Nat.div_eq_of_lt
  exact (Nat.sub_lt hpos (by omega : 0 < 1)).trans_le hsq

/-- Above half the endpoint the literal wall fibre is forced to have cofactor
one and native signed weight one.  Cancellation of the complete wall, if
available, must retain its coupling to the other prime fibres. -/
theorem stableFarWall_topHalf_cofactor_eq_one_and_weight
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ stableFarWallCarrier R)
    (htop : squareRootEndpoint R < 2 * z.2.2) :
    z.2.1 = 1 ∧ lowWheelFullTaggedPhysicalWeight z = 1 := by
  rcases (mem_stableFarWallCarrier_iff_primeInsertion hR).mp hz with
    ⟨hface, _hq, _hfar, _hqX, hc, _hsq, hprod⟩
  have hcOne := (Finset.mem_Ico.mp hc).1
  have hcEq : z.2.1 = 1 := by
    by_contra hne
    have hcTwo : 2 ≤ z.2.1 := by omega
    have hmul := Nat.mul_le_mul_right z.2.2 hcTwo
    omega
  refine ⟨hcEq, ?_⟩
  simp [lowWheelFullTaggedPhysicalWeight, hface, hcEq, booleanCubeSign,
    canonicalMoebiusWeight]

/-! ## The wall is literally a far-prime Mertens ledger -/

/-- Prime-first low-cofactor expansion of the whole wall.  Nonsquarefree
cofactors may be left in the displayed sum because their Möbius weight is zero. -/
theorem stableFarWallLedger_eq_sum_lowCofactorFibres
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ z ∈ stableFarWallCarrier R, lowWheelFullTaggedPhysicalWeight z) =
      ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
        if q.Prime then
          (∑ c ∈ Finset.Ico 1 R,
            if c * q ≤ squareRootEndpoint R then
              canonicalMoebiusWeight c
            else 0)
        else 0 := by
  rw [sum_stableFarWallCarrier_eq_farPrimeTransport hR]
  unfold squareRootFarPrimeTransport
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hprime : q.Prime
  · have hRq : R < q := by
      have hqLow := (Finset.mem_Icc.mp hq).1
      omega
    have hmass := primeDilatedLowCofactorMass_eq_mertensSummatory
      R q (by omega) hRq hprime.pos
    simp only [hprime, if_true]
    rw [← hmass]
    rfl
  · simp [hprime]

/-- The same ledger with the physical squarefree predicate shown explicitly.
This is exactly the carrier formula; removing the predicate recovers the
previous theorem because Möbius vanishes off squarefree support. -/
theorem stableFarWallLedger_eq_sum_squarefree_lowCofactorFibres
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ z ∈ stableFarWallCarrier R, lowWheelFullTaggedPhysicalWeight z) =
      ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
        if q.Prime then
          (∑ c ∈ Finset.Ico 1 R,
            if Squarefree c ∧ c * q ≤ squareRootEndpoint R then
              canonicalMoebiusWeight c
            else 0)
        else 0 := by
  rw [stableFarWallLedger_eq_sum_lowCofactorFibres hR]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hprime : q.Prime
  · simp only [hprime, if_true]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hsq : Squarefree c
    · simp [hsq]
    · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hsq, canonicalMoebiusWeight, hmu]
  · simp [hprime]

/-- The low-cofactor cap has already been compressed: the complete wall is the
ordinary Mertens prefix sampled at `floor(X_R/q)` on every far-prime fibre. -/
theorem stableFarWallLedger_eq_farPrimeMertens
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ z ∈ stableFarWallCarrier R, lowWheelFullTaggedPhysicalWeight z) =
      ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
        if q.Prime then
          mertensSummatory (squareRootEndpoint R / q)
        else 0 := by
  rw [sum_stableFarWallCarrier_eq_farPrimeTransport hR]
  rfl

/-- The repository's generic post-square-root prime tail is definitionally the
same far-prime Mertens ledger after the integer endpoint convention is aligned:
`R+8 ≤ q` is `R+7 < q`. -/
theorem squareRootFarPrimeTransport_eq_primeSieveMertensPrimeTail
    (R : ℕ) :
    squareRootFarPrimeTransport R =
      primeSieveMertensPrimeTail (R + 7) (squareRootEndpoint R) := by
  unfold squareRootFarPrimeTransport primeSieveMertensPrimeTail
  have hset :
      Finset.Icc (R + 8) (squareRootEndpoint R) =
        Finset.Ioc (R + 7) (squareRootEndpoint R) := by
    ext q
    simp
    omega
  rw [hset]

/-! ## Top half versus the lower fibres -/

/-- The part of the far wall below the inert top half.  These are exactly the
prime fibres that would have to offset the positive top block. -/
def stableFarWallLowerMertensFibres (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R / 2),
    if q.Prime then mertensSummatory (squareRootEndpoint R / q) else 0

/-- Exact split of the far wall into the lower far-prime fibres and the inert
same-sign top half. -/
theorem farPrimeTransport_eq_lowerFibres_add_topHalf
    {R : ℕ} (hR : 56 ≤ R) :
    squareRootFarPrimeTransport R =
      stableFarWallLowerMertensFibres R +
        ((squareRootTopFibrePrimes R).card : ℂ) := by
  classical
  have hfirst : 2 * (R + 8) + 1 ≤ 3 * R := by omega
  have hsecond : 3 * R ≤ R * R :=
    Nat.mul_le_mul_right R (by omega : 3 ≤ R)
  have hsq : 2 * (R + 8) + 1 ≤ R ^ 2 := by
    rw [pow_two]
    exact hfirst.trans hsecond
  have htwo : 2 * (R + 8) ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : R + 8 ≤ squareRootEndpoint R / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    simpa [Nat.mul_comm] using htwo
  have hhalfX : squareRootEndpoint R / 2 ≤ squareRootEndpoint R :=
    Nat.div_le_self _ _
  have hset :
      Finset.Icc (R + 8) (squareRootEndpoint R) =
        Finset.Icc (R + 8) (squareRootEndpoint R / 2) ∪
          Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj :
      Disjoint (Finset.Icc (R + 8) (squareRootEndpoint R / 2))
        (Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro q hqLow hqTop
    rcases Finset.mem_Icc.mp hqLow with ⟨_, hqHalf⟩
    rcases Finset.mem_Ioc.mp hqTop with ⟨hHalfq, _⟩
    omega
  unfold squareRootFarPrimeTransport stableFarWallLowerMertensFibres
  rw [hset, Finset.sum_union hdisj, squareRootTopMertensTail_eq_card R]

/-- Prime-count form of the same split.  The top summand is literally
`pi(X_R)-pi(floor(X_R/2))`; no cancellation takes place inside it. -/
theorem farPrimeTransport_eq_topPrimeCount_add_lowerFibres
    {R : ℕ} (hR : 56 ≤ R) :
    squareRootFarPrimeTransport R =
      ((Nat.primeCounting (squareRootEndpoint R) : ℂ) -
        (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ)) +
      stableFarWallLowerMertensFibres R := by
  have hsplit := farPrimeTransport_eq_lowerFibres_add_topHalf hR
  have htop := squareRootTopFibrePrimes_card_add_primeCounting_half R
  have htopC :
      ((squareRootTopFibrePrimes R).card : ℂ) +
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) =
        (Nat.primeCounting (squareRootEndpoint R) : ℂ) := by
    exact_mod_cast htop
  rw [hsplit]
  linear_combination htopC

/-! ## All-integer complement: the classical Mertens seam is explicit -/

/-- The all-integer reciprocal-Mertens contribution from every index which is
*not* one of the far primes. -/
def stableFarWallComplementMertens (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
    if n.Prime ∧ R + 8 ≤ n then
      0
    else
      mertensSummatory (squareRootEndpoint R / n)

/-- The far wall and its all-integer complement sum exactly to one.  This is the
classical identity `sum_{n≤X} M(floor(X/n)) = 1`, partitioned before taking any
absolute value. -/
theorem farPrimeTransport_add_allIntegerComplement_eq_one
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootFarPrimeTransport R + stableFarWallComplementMertens R = 1 := by
  classical
  let X := squareRootEndpoint R
  have hfour : 4 ≤ R ^ 2 := by
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ R * R := Nat.mul_le_mul hR hR
      _ = R ^ 2 := by ring
  have hX : 1 ≤ X := by
    dsimp [X]
    unfold squareRootEndpoint
    omega
  have hfilter :
      (Finset.Icc 1 X).filter (fun n => n.Prime ∧ R + 8 ≤ n) =
        (Finset.Icc (R + 8) X).filter Nat.Prime := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, hnX⟩, hnPrime, hnFar⟩
      exact ⟨⟨hnFar, hnX⟩, hnPrime⟩
    · rintro ⟨⟨hnFar, hnX⟩, hnPrime⟩
      exact ⟨⟨by omega, hnX⟩, hnPrime, hnFar⟩
  have hfar :
      squareRootFarPrimeTransport R =
        ∑ n ∈ Finset.Icc 1 X,
          if n.Prime ∧ R + 8 ≤ n then
            mertensSummatory (X / n)
          else 0 := by
    unfold squareRootFarPrimeTransport
    change (∑ q ∈ Finset.Icc (R + 8) X,
      if q.Prime then mertensSummatory (X / q) else 0) = _
    rw [← Finset.sum_filter, ← hfilter, Finset.sum_filter]
  have hpartition :
      (∑ n ∈ Finset.Icc 1 X,
          if n.Prime ∧ R + 8 ≤ n then
            mertensSummatory (X / n)
          else 0) +
        (∑ n ∈ Finset.Icc 1 X,
          if n.Prime ∧ R + 8 ≤ n then
            0
          else mertensSummatory (X / n)) =
        ∑ n ∈ Finset.Icc 1 X, mertensSummatory (X / n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hfarPrime : n.Prime ∧ R + 8 ≤ n <;> simp [hfarPrime]
  have hunit := RHLean.Analysis.sum_mertensSummatory_div_eq_one hX
  rw [hfar]
  unfold stableFarWallComplementMertens
  change
    (∑ n ∈ Finset.Icc 1 X,
        if n.Prime ∧ R + 8 ≤ n then mertensSummatory (X / n) else 0) +
      (∑ n ∈ Finset.Icc 1 X,
        if n.Prime ∧ R + 8 ≤ n then 0 else mertensSummatory (X / n)) = 1
  rw [hpartition, hunit]

/-- Subtraction form of the all-integer complement identity. -/
theorem farPrimeTransport_eq_one_sub_allIntegerComplement
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootFarPrimeTransport R =
      1 - stableFarWallComplementMertens R := by
  have h := farPrimeTransport_add_allIntegerComplement_eq_one hR
  linear_combination h

/-- The non-unit portion of the all-integer complement.  Separating `n=1`
exposes the full-scale term `M(X_R)` rather than hiding it in the complement. -/
def stableFarWallNonUnitComplementMertens (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 (squareRootEndpoint R),
    if n.Prime ∧ R + 8 ≤ n then
      0
    else
      mertensSummatory (squareRootEndpoint R / n)

/-- The all-integer complement contains one literal full-scale Mertens term,
coming from `n=1`, plus only the non-unit indices. -/
theorem stableFarWallComplementMertens_eq_fullMertens_add_nonUnit
    {R : ℕ} (hR : 2 ≤ R) :
    stableFarWallComplementMertens R =
      mertensSummatory (squareRootEndpoint R) +
        stableFarWallNonUnitComplementMertens R := by
  classical
  let X := squareRootEndpoint R
  have hfour : 4 ≤ R ^ 2 := by
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ R * R := Nat.mul_le_mul hR hR
      _ = R ^ 2 := by ring
  have hX : 1 ≤ X := by
    dsimp [X]
    unfold squareRootEndpoint
    omega
  have hset : Finset.Icc 1 X = ({1} : Finset ℕ) ∪ Finset.Icc 2 X := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 X) := by
    rw [Finset.disjoint_left]
    intro n hnOne hnRest
    simp only [Finset.mem_singleton] at hnOne
    subst n
    simp at hnRest
  unfold stableFarWallComplementMertens stableFarWallNonUnitComplementMertens
  change
    (∑ n ∈ Finset.Icc 1 X,
      if n.Prime ∧ R + 8 ≤ n then 0 else mertensSummatory (X / n)) =
      mertensSummatory X +
        ∑ n ∈ Finset.Icc 2 X,
          if n.Prime ∧ R + 8 ≤ n then 0 else mertensSummatory (X / n)
  rw [hset, Finset.sum_union hdisj]
  simp

/-- The stopping identity in the requested form: the wall is `1`, minus one
full-scale Mertens value, minus the complementary non-far reciprocal fibres.
Thus an estimate for the wall cannot be obtained from this exact telescope
without controlling the original Mertens-scale term. -/
theorem farPrimeTransport_eq_one_sub_fullMertens_sub_nonUnitComplement
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootFarPrimeTransport R =
      1 - mertensSummatory (squareRootEndpoint R) -
        stableFarWallNonUnitComplementMertens R := by
  rw [farPrimeTransport_eq_one_sub_allIntegerComplement hR,
    stableFarWallComplementMertens_eq_fullMertens_add_nonUnit hR]
  ring

/-! ## Equivalent smooth/high partition -/

/-- The exact existing smooth/high identity, specialized to the wall cutoff.
The stable far wall is the `(R+7)`-smooth Möbius mass through `X_R` minus the
ordinary full-scale Mertens value. -/
theorem farPrimeTransport_eq_smoothMobiusMass_sub_fullMertens
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootFarPrimeTransport R =
      primeSieveSmoothMobiusMass (R + 7) (squareRootEndpoint R) -
        mertensSummatory (squareRootEndpoint R) := by
  have hsqrtR : Nat.sqrt (squareRootEndpoint R) < R := by
    apply (Nat.sqrt_lt').2
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := pow_pos (by omega : 0 < R) 2
    omega
  have hroot : Nat.sqrt (squareRootEndpoint R) < R + 7 := by omega
  have hsmooth := primeSieveSmoothMobiusMass_eq_mertens_add_signedSum
    (R + 7) (squareRootEndpoint R) hroot
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail,
    ← squareRootFarPrimeTransport_eq_primeSieveMertensPrimeTail R] at hsmooth
  rw [eq_sub_iff_add_eq]
  simpa [add_comm] using hsmooth.symm

/-- The literal physical wall carries the same stopping identity. -/
theorem stableFarWallLedger_eq_smoothMobiusMass_sub_fullMertens
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ z ∈ stableFarWallCarrier R, lowWheelFullTaggedPhysicalWeight z) =
      primeSieveSmoothMobiusMass (R + 7) (squareRootEndpoint R) -
        mertensSummatory (squareRootEndpoint R) := by
  rw [sum_stableFarWallCarrier_eq_farPrimeTransport hR,
    farPrimeTransport_eq_smoothMobiusMass_sub_fullMertens hR]

end RHLean.Proof