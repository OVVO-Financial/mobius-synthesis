import RHLean.Proof.PrimeWheelFrozenRoughSeatBridge
import RHLean.Arithmetic.LeastPrimeDepthHierarchy
import RHLean.Arithmetic.PrimeWheelFiniteDepthSemiprime
import RHLean.Arithmetic.TruncatedCubeMertensPrefix
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction
import RHLean.Proof.SquareRootLowPrimeGoHyperbolicStripRecursion
import RHLean.Proof.SquareRootLowPrimeGoWallQuantitative

/-!
# Cubic proper-subwheel decomposition

Stop the prime wheel at `Y`, before the physical endpoint `X` has been fully
resolved.  The frozen rough-seat identity says this is still exactly `M(X)`.
This file then changes chronology without taking a norm.

The existing high-prime upper-column telescope gives

`M(X) = F_Y(X) - sum_{Y < p <= X} F_{p^-}(X/p)`.

If `X < (Y+1)^3`, every owner `p > Y` satisfies `X < p^3`.  Opening that
moving predecessor column at its own fresh prime therefore leaves a square
residual at `X/p^2` which is already below `p`, hence is an *ordinary lower
Mertens state*.  Thus

`M(X) = F_Y(X)
        - sum_{Y < p <= X} F_p(X/p)
        - sum_{Y < p <= X} M(X/p^2)`.

This is the exact algebraic form of the prime/semiprime cancellation visible in
the proper-subwheel rough-seat coordinate.  The second sum is the unresolved
moving boundary ledger; the third sum has already lost two owner factors in
scale.  No triangle inequality, density estimate, PNT input, or Mertens bound
is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- At its own full prime cutoff the frozen cube is exactly ordinary integer
Mertens. -/
theorem frozenPrimeUniverseMass_primesUpTo_self_eq_mertensSummatoryInt
    (X : ℕ) :
    frozenPrimeUniverseMass (primesUpTo X) X = mertensSummatoryInt X := by
  unfold frozenPrimeUniverseMass mertensSummatoryInt
  exact truncatedPrimeCube_eq_moebiusPrefix X

/-- **Proper-subwheel high-owner column.**  Advancing the frozen prime universe
from `Y` all the way through `X` recovers ordinary Mertens.  This is the
chronological reading of the same signed object represented by the rough-seat
correlation. -/
theorem mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn
    (X Y : ℕ) (hYX : Y ≤ X) :
    mertensSummatoryInt X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) := by
  have htel := frozenPrimeUniverse_highUpperColumn_telescope X Y X hYX
  rw [frozenPrimeUniverseMass_primesUpTo_self_eq_mertensSummatoryInt] at htel
  omega

/-- The proper-subwheel rough-seat correlation and the chronological high-owner
column are literally the same Mertens value. -/
theorem primeWheelFrozenFullRoughSeatCorrelation_eq_base_sub_highOwnerColumn
    (X Y : ℕ) (hYX : Y ≤ X) :
    primeWheelFrozenFullRoughSeatCorrelation (primesUpTo Y) X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) := by
  rw [← mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn X Y hYX]
  rw [← roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
    (primesUpTo Y) (fun p hp => prime_of_mem_primesUpTo hp) X]
  unfold roughMertens mertensSummatoryInt
  simp [roughMoebius]

/-- Above a cubic proper-subwheel cutoff, every chronological owner is itself
past the cubic completion threshold. -/
theorem properSubwheelHighPrime_owner_cube_gt
    {X Y p : ℕ}
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet Y X)
    (hcubic : X < (Y + 1) ^ 3) :
    X < p ^ 3 := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hYp : Y < p := hpData.2.1
  have hsucc : Y + 1 ≤ p := by omega
  have hpow : (Y + 1) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hsucc 3
  exact hcubic.trans_le hpow

/-- **One high owner opens into a boundary state plus a completed square
residual.**  The latter is already ordinary Mertens because `X/p^2 < p` under
the cubic proper-subwheel hypothesis. -/
theorem properSubwheel_highOwnerMovingTerm_eq_boundary_add_mertensSquare
    {X Y p : ℕ}
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet Y X)
    (hcubic : X < (Y + 1) ^ 3) :
    frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) =
      frozenPrimeUniverseMass (primesUpTo p) (X / p) +
        mertensSummatoryInt (X / (p * p)) := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hpPrime : p.Prime := hpData.1
  have hcube : X < p ^ 3 :=
    properSubwheelHighPrime_owner_cube_gt hp hcubic
  have hcomplete : X / (p * p) < p :=
    squareRootLowPrimeGo_squareCutoff_lt_owner_of_lt_cube hpPrime hcube
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor
      p (X / p) hpPrime
  unfold predecessorPrimeMass at hstep
  rw [Nat.div_div_eq_div_mul] at hstep
  have hmertens :=
    frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner
      hpPrime hcomplete
  rw [hmertens] at hstep
  omega

/-- The entire high-owner moving column splits before any norm into the moving
boundary ledger plus completed lower Mertens square residuals. -/
theorem properSubwheel_highOwnerColumn_eq_boundary_add_mertensSquares
    (X Y : ℕ) (hcubic : X < (Y + 1) ^ 3) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo p) (X / p)) +
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        mertensSummatoryInt (X / (p * p)) := by
  calc
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        (frozenPrimeUniverseMass (primesUpTo p) (X / p) +
          mertensSummatoryInt (X / (p * p))) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact properSubwheel_highOwnerMovingTerm_eq_boundary_add_mertensSquare
        hp hcubic
    _ = _ := by rw [Finset.sum_add_distrib]

/-- **Cubic proper-subwheel normal form.**  The full outer Mobius cancellation
has been consumed exactly.  What remains is one signed chronological boundary
ledger and a twice-dilated lower Mertens column. -/
theorem mertensSummatoryInt_eq_properSubwheelBoundary_sub_mertensSquares
    (X Y : ℕ) (hYX : Y ≤ X) (hcubic : X < (Y + 1) ^ 3) :
    mertensSummatoryInt X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo p) (X / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          mertensSummatoryInt (X / (p * p)) := by
  rw [mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn X Y hYX,
    properSubwheel_highOwnerColumn_eq_boundary_add_mertensSquares X Y hcubic]
  ring

/-- Same normal form on the literal frozen rough-seat correlation. -/
theorem primeWheelFrozenFullRoughSeatCorrelation_eq_boundary_sub_mertensSquares
    (X Y : ℕ) (hYX : Y ≤ X) (hcubic : X < (Y + 1) ^ 3) :
    primeWheelFrozenFullRoughSeatCorrelation (primesUpTo Y) X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo p) (X / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          mertensSummatoryInt (X / (p * p)) := by
  rw [← mertensSummatoryInt_eq_properSubwheelBoundary_sub_mertensSquares
    X Y hYX hcubic]
  rw [← roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
    (primesUpTo Y) (fun p hp => prime_of_mem_primesUpTo hp) X]
  unfold roughMertens mertensSummatoryInt
  simp [roughMoebius]

/-- Square-endpoint specialization.  The wheel may stop strictly below the
physical root; only the cubic inequality and the harmless range condition are
needed. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_boundary_sub_mertensSquares
    (R Y : ℕ)
    (hYX : Y ≤ squareRootEndpoint R)
    (hcubic : squareRootEndpoint R < (Y + 1) ^ 3) :
    squareRootProperSubwheelFrozenCorrelation R Y =
      frozenPrimeUniverseMass (primesUpTo Y) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y (squareRootEndpoint R),
          frozenPrimeUniverseMass (primesUpTo p)
            (squareRootEndpoint R / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y (squareRootEndpoint R),
          mertensSummatoryInt (squareRootEndpoint R / (p * p)) := by
  unfold squareRootProperSubwheelFrozenCorrelation
  exact primeWheelFrozenFullRoughSeatCorrelation_eq_boundary_sub_mertensSquares
    (squareRootEndpoint R) Y hYX hcubic

/-! ## The same cubic scale is the existing semiprime frontier -/

/-- Under the slightly cleaner integer condition `X < Y^3`, the repository's
partial-wheel error theorem says that every nonzero error site has exactly two
unresolved prime coordinates above `Y`, a resolved cofactor below `Y`, and a
reciprocal quotient below `Y`.  Thus the proper-subwheel depth-two geometry and
the existing finite-depth prime-wheel frontier are literally on the same cubic
scale. -/
theorem properSubwheel_partialWheelError_smallCofactor_semiprime
    (Y X : ℕ) (hY : 0 < Y) (hscale : X < Y ^ 3)
    {n : ℕ} (hnpos : 0 < n) (hnX : n ≤ X)
    (herr : μ n - partialPrimeWheelSite Y X n ≠ 0) :
    ∃ a q r : ℕ,
      a < Y ∧ q.Prime ∧ r.Prime ∧ Y < q ∧ Y < r ∧
        n = a * q * r ∧ X / n < Y := by
  have hscale' : X < Y * Y ^ 2 := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hscale
  exact partialPrimeWheel_nonzero_error_smallCofactor_semiprime
    Y Y X hY le_rfl hscale' hnpos hnX herr

/-! ## Split the remaining ledger at the physical square-root wall -/

/-- High-prime owner intervals concatenate exactly. -/
theorem frozenPrimeUniverseHighPrimeSet_split
    (Y R X : ℕ) (hYR : Y ≤ R) (hRX : R ≤ X) :
    frozenPrimeUniverseHighPrimeSet Y X =
      frozenPrimeUniverseHighPrimeSet Y R ∪
        frozenPrimeUniverseHighPrimeSet R X := by
  ext p
  simp only [Finset.mem_union, mem_frozenPrimeUniverseHighPrimeSet]
  constructor
  · rintro ⟨hp, hYp, hpX⟩
    by_cases hpR : p ≤ R
    · exact Or.inl ⟨hp, hYp, hpR⟩
    · exact Or.inr ⟨hp, Nat.lt_of_not_ge hpR, hpX⟩
  · intro h
    rcases h with h | h
    · exact ⟨h.1, h.2.1, h.2.2.trans hRX⟩
    · exact ⟨h.1, lt_of_le_of_lt hYR h.2.1, h.2.2⟩

/-- The middle and top owner intervals are disjoint. -/
theorem frozenPrimeUniverseHighPrimeSet_split_disjoint
    (Y R X : ℕ) :
    Disjoint (frozenPrimeUniverseHighPrimeSet Y R)
      (frozenPrimeUniverseHighPrimeSet R X) := by
  rw [Finset.disjoint_left]
  intro p hpMid hpTop
  have hMid := mem_frozenPrimeUniverseHighPrimeSet.mp hpMid
  have hTop := mem_frozenPrimeUniverseHighPrimeSet.mp hpTop
  omega

/-- Therefore every signed high-owner sum splits without a triangle inequality. -/
theorem sum_frozenPrimeUniverseHighPrimeSet_split
    {A : Type*} [AddCommMonoid A]
    (Y R X : ℕ) (hYR : Y ≤ R) (hRX : R ≤ X) (f : ℕ → A) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X, f p) =
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R, f p) +
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet R X, f p := by
  rw [frozenPrimeUniverseHighPrimeSet_split Y R X hYR hRX]
  exact Finset.sum_union (frozenPrimeUniverseHighPrimeSet_split_disjoint Y R X)

/-- Once a full prime prefix extends beyond the physical cutoff, adding the
owner itself changes nothing: the frozen state is already ordinary Mertens. -/
theorem frozenPrimeUniverseMass_primesUpTo_eq_mertensSummatoryInt_of_lt
    {p Z : ℕ} (hp : p.Prime) (hZ : Z < p) :
    frozenPrimeUniverseMass (primesUpTo p) Z = mertensSummatoryInt Z := by
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor p Z hp
  unfold predecessorPrimeMass at hstep
  have hdiv0 : Z / p = 0 := Nat.div_eq_of_lt hZ
  rw [hdiv0, frozenPrimeUniverseMass_primesUpTo_zero] at hstep
  have hpred := frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner hp hZ
  rw [hpred] at hstep
  omega

/-- A prime strictly above the square root sees a reciprocal cutoff below
itself. -/
theorem squareRootEndpoint_div_lt_owner_of_root_lt
    {R p : ℕ} (hR : 2 ≤ R) (hRp : R < p) :
    squareRootEndpoint R / p < p := by
  have hpPos : 0 < p := by omega
  apply (Nat.div_lt_iff_lt_mul hpPos).2
  have hRPos : 0 < R := by omega
  have hR2Pos : 0 < R ^ 2 := pow_pos hRPos 2
  have hXRsq : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    omega
  have hpow : R ^ 2 < p ^ 2 := Nat.pow_lt_pow_left hRp (by omega)
  have hXp : squareRootEndpoint R < p ^ 2 := hXRsq.trans hpow
  simpa [pow_two] using hXp

/-- The entire top boundary `p > R` is already the existing high-prime Mertens
band.  The only unfinished frozen boundary states are therefore in the middle
owner range `Y < p ≤ R`. -/
theorem squareRootProperSubwheel_topBoundary_eq_mertensBand
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet R (squareRootEndpoint R),
        frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p)) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet R (squareRootEndpoint R),
        mertensSummatoryInt (squareRootEndpoint R / p) := by
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hcut := squareRootEndpoint_div_lt_owner_of_root_lt hR hpData.2.1
  exact frozenPrimeUniverseMass_primesUpTo_eq_mertensSummatoryInt_of_lt
    hpData.1 hcut

/-- The twice-dilated residual vanishes completely for owners above the physical
square root. -/
theorem squareRootProperSubwheel_topSquareResidual_eq_zero
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet R (squareRootEndpoint R),
        mertensSummatoryInt (squareRootEndpoint R / (p * p))) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hcut := squareRootEndpoint_div_lt_owner_of_root_lt hR hpData.2.1
  have hpPos : 0 < p := hpData.1.pos
  have hlt : squareRootEndpoint R < p * p :=
    (Nat.div_lt_iff_lt_mul hpPos).1 hcut
  have hdiv0 : squareRootEndpoint R / (p * p) = 0 := Nat.div_eq_of_lt hlt
  rw [hdiv0]
  simp [mertensSummatoryInt]

/-- **Square-root split of the cubic proper-subwheel normal form.**  Everything
above the physical root is now an ordinary high-prime Mertens band, and its
square residual is identically zero.  The genuinely unfinished signed boundary
ledger has been isolated to `Y < p ≤ R`; the only other term is the completed
lower-scale Mertens column `M(X/p^2)` on that same middle owner range. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_middleBoundary_sub_topBand_sub_middleSquares
    (R Y : ℕ) (hR : 2 ≤ R) (hYR : Y ≤ R)
    (hcubic : squareRootEndpoint R < (Y + 1) ^ 3) :
    squareRootProperSubwheelFrozenCorrelation R Y =
      frozenPrimeUniverseMass (primesUpTo Y) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
          frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p)) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet R (squareRootEndpoint R),
          mertensSummatoryInt (squareRootEndpoint R / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
          mertensSummatoryInt (squareRootEndpoint R / (p * p)) := by
  have hRX : R ≤ squareRootEndpoint R := by
    have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hYX : Y ≤ squareRootEndpoint R := hYR.trans hRX
  have hnormal :=
    squareRootProperSubwheelFrozenCorrelation_eq_boundary_sub_mertensSquares
      R Y hYX hcubic
  have hboundarySplit :=
    sum_frozenPrimeUniverseHighPrimeSet_split
      Y R (squareRootEndpoint R) hYR hRX
      (fun p => frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p))
  have hsquareSplit :=
    sum_frozenPrimeUniverseHighPrimeSet_split
      Y R (squareRootEndpoint R) hYR hRX
      (fun p => mertensSummatoryInt (squareRootEndpoint R / (p * p)))
  have htop := squareRootProperSubwheel_topBoundary_eq_mertensBand R hR
  have htopSq := squareRootProperSubwheel_topSquareResidual_eq_zero R hR
  rw [hboundarySplit, hsquareSplit, htop, htopSq] at hnormal
  calc
    squareRootProperSubwheelFrozenCorrelation R Y =
        frozenPrimeUniverseMass (primesUpTo Y) (squareRootEndpoint R) -
          ((∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
              frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p)) +
            ∑ p ∈ frozenPrimeUniverseHighPrimeSet R (squareRootEndpoint R),
              mertensSummatoryInt (squareRootEndpoint R / p)) -
          ((∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
              mertensSummatoryInt (squareRootEndpoint R / (p * p))) + 0) := hnormal
    _ = _ := by ring

/-! ## Base-plus-boundary telescope: first-power chronology -> square column

The cubic decomposition above can be read one step more structurally.  Advance
the frozen base from a lower cutoff `Y` only through a finite owner prefix `K`,
and move that same prefix of the boundary at the same time.  The first-power
Euler chronology then cancels exactly.  Its only failure of cutoff invariance is
the completed `p^2` Mertens column.

This theorem was previously present only in the research scratch layer.  It is
promoted here because it is the exact production bridge needed to compare the
stable-far Euler chronology with the q-square daughter coordinate before any
energy estimate is taken.
-/

/-- **Exact moving-boundary bridge.**  Under the cubic proper-subwheel
condition, base advance plus the matching moving-boundary prefix leaves only
completed square daughters. -/
theorem properSubwheel_base_sub_boundaryPrefix_eq_advancedBase_add_squares
    (X Y K : ℕ) (hYK : Y ≤ K) (hKX : K ≤ X)
    (hcubic : X < (Y + 1) ^ 3) :
    frozenPrimeUniverseMass (primesUpTo Y) X -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
          frozenPrimeUniverseMass (primesUpTo p) (X / p)) =
      frozenPrimeUniverseMass (primesUpTo K) X +
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
          mertensSummatoryInt (X / (p * p)) := by
  have htel := frozenPrimeUniverse_highUpperColumn_telescope X Y K hYK
  have hsplit :
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
        frozenPrimeUniverseMass (primesUpTo p) (X / p)) +
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
        mertensSummatoryInt (X / (p * p)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    have hpFull : p ∈ frozenPrimeUniverseHighPrimeSet Y X :=
      mem_frozenPrimeUniverseHighPrimeSet.mpr
        ⟨hpData.1, hpData.2.1, hpData.2.2.trans hKX⟩
    exact properSubwheel_highOwnerMovingTerm_eq_boundary_add_mertensSquare
      hpFull hcubic
  omega

end RHLean.Proof
