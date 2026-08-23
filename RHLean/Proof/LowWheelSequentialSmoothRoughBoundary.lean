import Mathlib
import RHLean.Arithmetic.PrimeProductCubeFrontier
import RHLean.Proof.LowWheelSequentialRoughWindowFold

/-!
# Smooth/rough boundary form of the sequential low-wheel state

After a fresh prime `p` is processed, the cumulative rough-window fold leaves one old
signed cofactor cube and counts of `p`-rough integers in reciprocal windows.
Swapping the surviving rough integer `q` with the old cofactor face `u` exposes
the dual geometry.

For `B = floor(X/q)`, window membership is exactly

`B / p < primeFaceProduct u <= B`.

Hence the remaining smooth-face contribution is the difference of two
truncated prime-product cubes, at cutoffs `B` and `B/p`.  Any already-processed
prime coordinate `ell < p` may then be used to collapse each truncated cube to
its exact first-failure frontier.

This is the sequential compounding mechanism: the new prime creates the
rough/smooth reciprocal shell, while an older prime coordinate cancels the
interior of the remaining smooth cube.  No norm or asymptotic estimate appears.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Alternating mass of old smooth prime faces in the reciprocal `1/p` shell
`B/p < P(u) <= B`. -/
def lowWheelSmoothFaceShellMass (p B : ℕ) : ℤ :=
  ∑ u ∈ (primesUpTo (p - 1)).powerset,
    if B / p < primeFaceProduct u ∧ primeFaceProduct u ≤ B then
      booleanCubeSign u
    else
      0

/-- The smooth shell is exactly the difference between the two truncated
prime-product cubes at `B` and `B/p`. -/
theorem lowWheelSmoothFaceShellMass_eq_truncatedCubeDiff
    (p B : ℕ) :
    lowWheelSmoothFaceShellMass p B =
      truncatedCubeAlternatingSum (primesUpTo (p - 1))
        (primeProductAdmissible (primesUpTo (p - 1)) B) -
      truncatedCubeAlternatingSum (primesUpTo (p - 1))
        (primeProductAdmissible (primesUpTo (p - 1)) (B / p)) := by
  classical
  unfold lowWheelSmoothFaceShellMass truncatedCubeAlternatingSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have huSub := Finset.mem_powerset.mp hu
  unfold primeProductAdmissible
  simp only [huSub, true_and]
  have hsmallBig : B / p ≤ B := Nat.div_le_self B p
  by_cases hbig : primeFaceProduct u ≤ B
  · by_cases hsmall : primeFaceProduct u ≤ B / p
    · have hnotShell : ¬ B / p < primeFaceProduct u := Nat.not_lt_of_ge hsmall
      simp [hbig, hsmall, hnotShell]
    · have hshell : B / p < primeFaceProduct u := Nat.lt_of_not_ge hsmall
      simp [hbig, hsmall, hshell]
  · have hsmall : ¬ primeFaceProduct u ≤ B / p := by
      intro h
      exact hbig (h.trans hsmallBig)
    simp [hbig, hsmall]

/-- Reciprocal-window membership expressed on the common unresolved quotient
interval and the smooth cofactor shell at `B = floor(X/q)`. -/
theorem mem_primeDilateCofactorWindow_iff_Ioc_and_smoothShell
    {p R X a q : ℕ} (hp : p.Prime) (ha : 0 < a) :
    q ∈ primeDilateCofactorWindow p R X a ↔
      q ∈ Finset.Ioc R X ∧
        X / q / p < a ∧ a ≤ X / q := by
  constructor
  · intro hq
    have hboundary :=
      (mem_primeDilateCofactorWindow_iff_prefixBoundary hp ha).mp hq
    have hqpos : 0 < q := by
      have := (Finset.mem_Ioc.mp hboundary.1).1
      omega
    have hshell :=
      (primeDilatePrefixBoundary_iff_reciprocalShell p X q a hp hqpos).mp
        hboundary.2
    exact ⟨hboundary.1, hshell.2, hshell.1⟩
  · rintro ⟨hqI, hsmall, hbig⟩
    have hqpos : 0 < q := by
      have := (Finset.mem_Ioc.mp hqI).1
      omega
    apply (mem_primeDilateCofactorWindow_iff_prefixBoundary hp ha).mpr
    refine ⟨hqI, ?_⟩
    apply (primeDilatePrefixBoundary_iff_reciprocalShell p X q a hp hqpos).mpr
    exact ⟨hbig, hsmall⟩

/-- One cumulative survivor window is the common unresolved interval filtered by
the `p`-survivor condition and the reciprocal smooth shell. -/
theorem lowWheelPrimeWindowSurvivorSet_eq_Ioc_filter_smoothShell
    {p R X a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    lowWheelPrimeWindowSurvivorSet p R X a =
      (Finset.Ioc R X).filter fun q =>
        lowWheelHighSurvivor p q ∧
          X / q / p < a ∧ a ≤ X / q := by
  classical
  ext q
  unfold lowWheelPrimeWindowSurvivorSet
  simp only [Finset.mem_filter]
  rw [mem_primeDilateCofactorWindow_iff_Ioc_and_smoothShell hp ha]
  tauto

/-- **Smooth/rough q-first form.**  The state after prime `p` is a sum over
`p`-rough unresolved integers `q`; its coefficient is the alternating mass of
old smooth faces in the reciprocal shell `(B/p,B]`, `B=floor(X/q)`. -/
theorem lowWheelDoubleCubePrimePrefix_step_eq_smoothRoughShellMass
    (R p : ℕ) (hp : p.Prime) :
    lowWheelDoubleCubeSetTransportLedger R (primesUpTo p) =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if lowWheelHighSurvivor p q then
          ((lowWheelSmoothFaceShellMass p
            (squareRootEndpoint R / q) : ℤ) : ℂ)
        else
          0 := by
  rw [lowWheelDoubleCubePrimePrefix_step_eq_survivorWindowCards R p hp]
  calc
    (∑ u ∈ (primesUpTo (p - 1)).powerset,
        (booleanCubeSign u : ℂ) *
          ((lowWheelPrimeWindowSurvivorSet
            p R (squareRootEndpoint R) (primeFaceProduct u)).card : ℂ)) =
      ∑ u ∈ (primesUpTo (p - 1)).powerset,
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if lowWheelHighSurvivor p q ∧
              squareRootEndpoint R / q / p < primeFaceProduct u ∧
              primeFaceProduct u ≤ squareRootEndpoint R / q then
            (booleanCubeSign u : ℂ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have huPos : 0 < primeFaceProduct u :=
        primeFaceProduct_pos_of_mem_powerset hu
      rw [lowWheelPrimeWindowSurvivorSet_eq_Ioc_filter_smoothShell hp huPos]
      calc
        (booleanCubeSign u : ℂ) *
            ((((Finset.Ioc R (squareRootEndpoint R)).filter fun q =>
              lowWheelHighSurvivor p q ∧
                squareRootEndpoint R / q / p < primeFaceProduct u ∧
                primeFaceProduct u ≤ squareRootEndpoint R / q).card : ℕ) : ℂ) =
          ∑ q ∈ ((Finset.Ioc R (squareRootEndpoint R)).filter fun q =>
              lowWheelHighSurvivor p q ∧
                squareRootEndpoint R / q / p < primeFaceProduct u ∧
                primeFaceProduct u ≤ squareRootEndpoint R / q),
            (booleanCubeSign u : ℂ) := by simp [mul_comm]
        _ = ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
            if lowWheelHighSurvivor p q ∧
                squareRootEndpoint R / q / p < primeFaceProduct u ∧
                primeFaceProduct u ≤ squareRootEndpoint R / q then
              (booleanCubeSign u : ℂ)
            else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        ∑ u ∈ (primesUpTo (p - 1)).powerset,
          if lowWheelHighSurvivor p q ∧
              squareRootEndpoint R / q / p < primeFaceProduct u ∧
              primeFaceProduct u ≤ squareRootEndpoint R / q then
            (booleanCubeSign u : ℂ)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if lowWheelHighSurvivor p q then
          ((lowWheelSmoothFaceShellMass p
            (squareRootEndpoint R / q) : ℤ) : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hsurv : lowWheelHighSurvivor p q
      · simp only [hsurv, true_and, if_true]
        unfold lowWheelSmoothFaceShellMass
        push_cast
        rfl
      · simp [hsurv]

/-- Any previously processed prime coordinate collapses the smooth shell to the
difference of two concrete first-failure frontiers. -/
theorem lowWheelSmoothFaceShellMass_eq_twoFirstFailureFrontiers
    {p B ell : ℕ}
    (hell : ell ∈ primesUpTo (p - 1)) :
    lowWheelSmoothFaceShellMass p B =
      (∑ u ∈ primeProductFirstFailureBoundary
          (primesUpTo (p - 1)) B ell,
        booleanCubeSign u) -
      ∑ u ∈ primeProductFirstFailureBoundary
          (primesUpTo (p - 1)) (B / p) ell,
        booleanCubeSign u := by
  rw [lowWheelSmoothFaceShellMass_eq_truncatedCubeDiff]
  have hprime : ∀ r ∈ primesUpTo (p - 1), r.Prime := by
    intro r hr
    exact prime_of_mem_primesUpTo hr
  rw [truncatedPrimeProductCube_eq_frontier hell hprime,
    truncatedPrimeProductCube_eq_frontier hell hprime]

end RHLean.Proof
