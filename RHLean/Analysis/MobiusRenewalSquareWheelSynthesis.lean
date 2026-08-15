import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Analysis.PrimeSievePNTCentering
import RHLean.Analysis.SquareRootTransportRealization
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# Renewal-telescope coordinates for the primorial square-wheel response

Cross-track synthesis witness.  The g-weighted renewal telescope
(`RHLean.Analysis.sum_convolveOne_mul_mertensSummatory_div`), applied to the
far-prime reciprocal Mertens kernel

```text
g_n(d) = 1_{n+9 <= d <= X_n} * 1_{d prime} * M(floor (X_n / d)),
```

produces exactly the reciprocal Mertens transform whose negative global
far-upper rigidity
(`RHLean.Proof.survivorSixteenFarUpperPrimeMass_eq_neg_mertensTransform`)
identifies with the far-upper survivor sector of the square-prefix
decomposition.  Substituting that renewal realization through the matched
square-prefix identity
(`RHLean.Proof.squarePrefixMertens_eq_positiveSmooth_add_matched` and
`squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near`)
into the primorial-wheel zero-mode center
(`RHLean.Analysis.primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter`)
yields one connected equality: at a synchronized wheel sample, the nonzero
wheel response is the square-prefix decomposition with its far-survivor
component realized as a renewal telescope, centered on the primorial block.

This is an exact coordinate identity.  No estimate is asserted anywhere.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Renewal-telescope realization of the far-prime reciprocal Mertens kernel:
the left side of the g-weighted renewal telescope at `X = squarePrefixEndpoint t`
with kernel `g_t(d) = 1_{t+9 <= d <= X_t} * 1_{d prime} * M(floor (X_t / d))`. -/
def survivorFarUpperRenewalTelescope (t : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
    (∑ d ∈ m.divisors,
      if d ∈ Finset.Icc (t + 9) (RHLean.Analysis.squarePrefixEndpoint t) then
        if d.Prime then
          RHLean.Analysis.mertensSummatory
            (RHLean.Analysis.squarePrefixEndpoint t / d)
        else 0
      else 0) *
      RHLean.Analysis.mertensSummatory
        (RHLean.Analysis.squarePrefixEndpoint t / m)

/-- **Renewal-telescope coordinates for the primorial wheel response.**  At a
synchronized wheel sample, the far-survivor component of the square-prefix
decomposition is replaced by its renewal-telescope realization before applying
the existing wheel zero-mode center.  Exact; no estimate is asserted. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_renewalFarSurvivorCenter
    (k n : ℕ) (hn : 55 ≤ n)
    (hlower : primorialBlockLower k < RHLean.Analysis.squarePrefixEndpoint n)
    (hupper : RHLean.Analysis.squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    RHLean.Analysis.squareWheelNonzeroSampleResponse
        (primorialMinimalWheelSystem k) n =
      ((squareRootPositiveSmoothMass (n + 1) +
            squareRootBornSmoothMass (n + 1) -
            survivorFarUpperRenewalTelescope n -
            squareRootNearPrimeTransport (n + 1)) -
          RHLean.Analysis.mertensSummatory (primorialBlockLower k)) -
        RHLean.Analysis.squareWheelSampleRatio
            (primorialMinimalWheelSystem k) n *
          (RHLean.Analysis.mertensSummatory (primorialBlockUpper k) -
            RHLean.Analysis.mertensSummatory (primorialBlockLower k)) := by
  classical
  -- Step 1: the telescope collapses the renewal realization to the
  -- far-prime reciprocal Mertens transform.
  have htel : survivorFarUpperRenewalTelescope n =
      ∑ q ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n),
        if q.Prime then
          RHLean.Analysis.mertensSummatory
            (RHLean.Analysis.squarePrefixEndpoint n / q)
        else 0 := by
    have h0 := RHLean.Analysis.sum_convolveOne_mul_mertensSummatory_div
      (fun d =>
        if d ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) then
          if d.Prime then
            RHLean.Analysis.mertensSummatory
              (RHLean.Analysis.squarePrefixEndpoint n / d)
          else 0
        else 0)
      (RHLean.Analysis.squarePrefixEndpoint n)
    have hsub : Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) ⊆
        Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint n) := by
      intro a ha
      rw [Finset.mem_Icc] at ha ⊢
      omega
    have hvanish : ∀ a ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint n),
        a ∉ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) →
        (if a ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) then
          if a.Prime then
            RHLean.Analysis.mertensSummatory
              (RHLean.Analysis.squarePrefixEndpoint n / a)
          else 0
        else 0) = 0 := by
      intro a _ hnot
      simp [hnot]
    calc survivorFarUpperRenewalTelescope n
        = ∑ a ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint n),
            (if a ∈
                Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) then
              if a.Prime then
                RHLean.Analysis.mertensSummatory
                  (RHLean.Analysis.squarePrefixEndpoint n / a)
              else 0
            else 0) := h0
      _ = ∑ q ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n),
            (if q ∈
                Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) then
              if q.Prime then
                RHLean.Analysis.mertensSummatory
                  (RHLean.Analysis.squarePrefixEndpoint n / q)
              else 0
            else 0) := (Finset.sum_subset hsub hvanish).symm
      _ = ∑ q ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n),
            if q.Prime then
              RHLean.Analysis.mertensSummatory
                (RHLean.Analysis.squarePrefixEndpoint n / q)
            else 0 := by
          refine Finset.sum_congr rfl fun q hq => ?_
          simp [hq]
  -- Step 2: global far-upper rigidity identifies the far survivor with the
  -- negated telescope.
  have hsurv : survivorSixteenFarUpperPrimeMass n =
      -survivorFarUpperRenewalTelescope n := by
    rw [survivorSixteenFarUpperPrimeMass_eq_neg_mertensTransform n hn, htel]
  -- Step 3: the matched square-prefix decomposition with the far survivor in
  -- renewal coordinates.
  have hprefix : RHLean.Analysis.mertensSummatory
      (RHLean.Analysis.squarePrefixEndpoint n) =
      squareRootPositiveSmoothMass (n + 1) +
        squareRootBornSmoothMass (n + 1) -
        survivorFarUpperRenewalTelescope n -
        squareRootNearPrimeTransport (n + 1) := by
    have h1 := squarePrefixMertens_eq_positiveSmooth_add_matched (n + 1)
      (by omega)
    have h2 :=
      squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
        (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h1 h2
    have h1' : RHLean.Analysis.mertensSummatory
        (RHLean.Analysis.squarePrefixEndpoint n) =
        squareRootPositiveSmoothMass (n + 1) +
          squareRootMatchedBornSmoothTransport (n + 1) := h1
    rw [h1', h2, hsurv]
    ring
  -- Step 4: substitute into the primorial-wheel zero-mode center.
  rw [RHLean.Analysis.primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter
    k n hlower hupper]
  simp only [RHLean.Analysis.primorialSquareZeroModeCenter]
  rw [hprefix]

end RHLean.Proof

end
