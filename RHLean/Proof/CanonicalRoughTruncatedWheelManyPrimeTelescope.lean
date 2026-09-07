import Mathlib
import RHLean.Proof.CanonicalRoughTruncatedWheelDefectTelescope

/-!
# Many-prime telescope for truncated Euler-wheel defect shells

The fixed-partner theorem in `CanonicalRoughTruncatedWheelDefectTelescope`
identifies one physical defect shell, with its native `1/p`, as

```text
T_{P insert p}(N) - (1 - 1/p) * T_P(N).
```

The chronological orientation in the canonical rough compression processes the
larger prime first.  Therefore a shell created later at a smaller prime is
transported by every already-applied larger Euler factor.  This file records the
resulting exact telescope for an arbitrary duplicate-free list of prime
coordinates.

For a descending list `L = [p_k, ..., p_1]`, define recursively

```text
Ledger(N, p :: L)
  = (1 - 1/p) * Ledger(N, L)
    + (1/p) * (T_L(N) - T_L(N/p)).
```

Then, with no estimate at all,

```text
Ledger(N,L)
  = T_L(N) - EulerProduct(L) * T_empty(N).
```

For positive `N`, `T_empty(N)=1`, so the complete transported defect ledger is
literally the final truncated-wheel boundary

```text
T_L(N) - EulerProduct(L).
```

This is the quantitative structural replacement for the `(1-P) * Delta`
majorant at fixed partner.  The final section then distinguishes two different
partner aggregates which must not be conflated: the reciprocal-weighted
`(1/q)` upper column telescopes to one final boundary, whereas the literal
physical partner aggregate is unweighted in `q` and is therefore a
prime-weighted discrete boundary drop.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Euler product of a chronological prime list, using the canonical rough Euler factor. -/
def canonicalRoughPrimeListEulerProduct : List ℕ → ℝ
  | [] => 1
  | p :: ps => canonicalRoughEulerFactor p * canonicalRoughPrimeListEulerProduct ps

@[simp] theorem canonicalRoughPrimeListEulerProduct_nil :
    canonicalRoughPrimeListEulerProduct [] = 1 := by
  rfl

@[simp] theorem canonicalRoughPrimeListEulerProduct_cons (p : ℕ) (ps : List ℕ) :
    canonicalRoughPrimeListEulerProduct (p :: ps) =
      canonicalRoughEulerFactor p * canonicalRoughPrimeListEulerProduct ps := by
  rfl

/-- The Finset Euler contraction factor agrees exactly with the chronological
list product whenever the list has no duplicate coordinates. -/
theorem primorialSignedContractionFactor_toFinset_eq_primeListEulerProduct
    (ps : List ℕ) (hnodup : ps.Nodup) :
    primorialSignedContractionFactor ps.toFinset =
      canonicalRoughPrimeListEulerProduct ps := by
  induction ps with
  | nil =>
      simp [primorialSignedContractionFactor,
        canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hpNotList, htailNodup⟩
      have hpNot : p ∉ ps.toFinset := by
        simpa using hpNotList
      simp only [List.toFinset_cons, canonicalRoughPrimeListEulerProduct]
      unfold primorialSignedContractionFactor
      rw [Finset.prod_insert hpNot]
      have ih' := ih htailNodup
      unfold primorialSignedContractionFactor at ih'
      rw [ih']
      unfold canonicalRoughEulerFactor
      rfl

/-- Transported reciprocal shell ledger for one fixed truncation cutoff `N`.
The head of the list is the larger/earlier prime, exactly matching the transport
orientation in `squareRootCanonicalRoughTransportedDefectLedger`. -/
def primorialTruncatedTransportedShellLedger (N : ℕ) : List ℕ → ℝ
  | [] => 0
  | p :: ps =>
      canonicalRoughEulerFactor p *
          primorialTruncatedTransportedShellLedger N ps +
        (1 / (p : ℝ)) *
          (primorialTruncatedSignedReciprocalCube ps.toFinset N -
            primorialTruncatedSignedReciprocalCube ps.toFinset (N / p))

@[simp] theorem primorialTruncatedTransportedShellLedger_nil (N : ℕ) :
    primorialTruncatedTransportedShellLedger N [] = 0 := by
  rfl

/-- **Exact many-prime transported-shell telescope.**

The shell at each prime is converted by the fresh-prime truncated-wheel
recurrence into `new state - EulerFactor * old state`; the recursive transport
then cancels every intermediate state. -/
theorem primorialTruncatedTransportedShellLedger_eq_boundary
    (N : ℕ) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup) :
    primorialTruncatedTransportedShellLedger N ps =
      primorialTruncatedSignedReciprocalCube ps.toFinset N -
        canonicalRoughPrimeListEulerProduct ps *
          primorialTruncatedSignedReciprocalCube ∅ N := by
  induction ps with
  | nil =>
      simp [primorialTruncatedTransportedShellLedger,
        canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have htailPrime : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      rcases List.nodup_cons.mp hnodup with ⟨hpNotList, htailNodup⟩
      have hpNot : p ∉ ps.toFinset := by
        simpa using hpNotList
      have hstep :=
        primorialTruncatedSignedReciprocalCube_shell_div_prime_eq_insert_sub_euler
          (P := ps.toFinset) (p := p) (N := N) hpNot hp
      simp only [primorialTruncatedTransportedShellLedger,
        canonicalRoughPrimeListEulerProduct]
      rw [ih htailPrime htailNodup]
      rw [hstep]
      simp only [List.toFinset_cons]
      unfold canonicalRoughEulerFactor
      ring

/-- At every positive cutoff the empty truncated wheel is the unit state, so the
transported shell ledger is exactly `final truncated cube - full Euler product`. -/
theorem primorialTruncatedTransportedShellLedger_eq_truncated_sub_eulerProduct
    (N : ℕ) (ps : List ℕ) (hN : 1 ≤ N)
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup) :
    primorialTruncatedTransportedShellLedger N ps =
      primorialTruncatedSignedReciprocalCube ps.toFinset N -
        canonicalRoughPrimeListEulerProduct ps := by
  rw [primorialTruncatedTransportedShellLedger_eq_boundary N ps hprime hnodup,
    primorialTruncatedSignedReciprocalCube_empty N hN]
  ring

/-- If the final cutoff already contains the complete wheel, then even the final
boundary vanishes: the transported shell ledger is exactly zero. -/
theorem primorialTruncatedTransportedShellLedger_eq_zero_of_complete
    (N : ℕ) (ps : List ℕ) (hN : 1 ≤ N)
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup)
    (hcomplete : primorialWheelProduct ps.toFinset ≤ N) :
    primorialTruncatedTransportedShellLedger N ps = 0 := by
  rw [primorialTruncatedTransportedShellLedger_eq_truncated_sub_eulerProduct
    N ps hN hprime hnodup]
  have hfactor :=
    primorialTruncatedSignedReciprocalCube_eq_factor ps.toFinset N
      (by
        intro p hp
        exact hprime p (by simpa using hp)) hcomplete
  rw [hfactor,
    primorialSignedContractionFactor_toFinset_eq_primeListEulerProduct ps hnodup]
  ring

/-! ## Reciprocal-weighted upper-column telescope -/

/-- Composite successor cutoffs do not change the prime prefix. -/
theorem primesUpTo_succ_eq_of_not_prime_reciprocal
    (n : ℕ) (hnot : ¬ (n + 1).Prime) :
    primesUpTo (n + 1) = primesUpTo n := by
  ext q
  simp only [mem_primesUpTo]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    refine ⟨hqPrime, ?_⟩
    have hqne : q ≠ n + 1 := by
      intro hEq
      subst q
      exact hnot hqPrime
    omega
  · rintro ⟨hqPrime, hqle⟩
    exact ⟨hqPrime, by omega⟩

/-- **Reciprocal-weighted upper-column telescope.**

The truncated reciprocal Euler recurrence places a native coefficient `1/q`
on the moving `X/q` column.  With exactly that coefficient, summing over a
complete prime prefix cancels both the truncated profile and the matching
uniform Euler contraction, leaving the negative final boundary.  The literal
physical partner aggregate from an earlier layer has no such `1/q`; see the exact
unweighted-column identity below. -/
theorem primorialTruncatedBoundary_upperColumn_telescope
    (X K : ℕ) (hX : 1 ≤ X) :
    (∑ q ∈ primesUpTo K,
      (1 / (q : ℝ)) *
        (primorialTruncatedSignedReciprocalCube
            (primesUpTo (q - 1)) (X / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialSignedContractionFactor (primesUpTo K) -
        primorialTruncatedSignedReciprocalCube (primesUpTo K) X := by
  induction K with
  | zero =>
      have hzero : primesUpTo 0 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        have hdata := mem_primesUpTo.mp hq
        have htwo := hdata.1.two_le
        omega
      rw [hzero]
      simp [primorialSignedContractionFactor,
        primorialTruncatedSignedReciprocalCube_empty X hX]
  | succ K ih =>
      by_cases hq : (K + 1).Prime
      · have hnotMem : K + 1 ∉ primesUpTo K := by
          simp
        have hpred : K + 1 - 1 = K := by omega
        have hset :
            primesUpTo (K + 1) = insert (K + 1) (primesUpTo K) := by
          simpa [hpred] using (insert_freshPrime_primesUpTo_pred_eq hq).symm
        have htrunc :=
          primorialTruncatedSignedReciprocalCube_insert
            (P := primesUpTo K) (p := K + 1) (X := X) hnotMem hq
        have hfactor :
            primorialSignedContractionFactor (primesUpTo (K + 1)) =
              (1 - 1 / ((K + 1 : ℕ) : ℝ)) *
                primorialSignedContractionFactor (primesUpTo K) := by
          rw [hset]
          unfold primorialSignedContractionFactor
          rw [Finset.prod_insert hnotMem]
        calc
          (∑ q ∈ primesUpTo (K + 1),
              (1 / (q : ℝ)) *
                (primorialTruncatedSignedReciprocalCube
                    (primesUpTo (q - 1)) (X / q) -
                  primorialSignedContractionFactor
                    (primesUpTo (q - 1)))) =
            (1 / ((K + 1 : ℕ) : ℝ)) *
                (primorialTruncatedSignedReciprocalCube
                    (primesUpTo K) (X / (K + 1)) -
                  primorialSignedContractionFactor (primesUpTo K)) +
              ∑ q ∈ primesUpTo K,
                (1 / (q : ℝ)) *
                  (primorialTruncatedSignedReciprocalCube
                      (primesUpTo (q - 1)) (X / q) -
                    primorialSignedContractionFactor
                      (primesUpTo (q - 1))) := by
                rw [hset, Finset.sum_insert hnotMem, hpred]
          _ =
            (1 / ((K + 1 : ℕ) : ℝ)) *
                (primorialTruncatedSignedReciprocalCube
                    (primesUpTo K) (X / (K + 1)) -
                  primorialSignedContractionFactor (primesUpTo K)) +
              (primorialSignedContractionFactor (primesUpTo K) -
                primorialTruncatedSignedReciprocalCube
                  (primesUpTo K) X) := by rw [ih]
          _ = primorialSignedContractionFactor (primesUpTo (K + 1)) -
                primorialTruncatedSignedReciprocalCube
                  (primesUpTo (K + 1)) X := by
              rw [hfactor, hset, htrunc]
              ring
      · have hset := primesUpTo_succ_eq_of_not_prime_reciprocal K hq
        rw [hset, ih]

/-- The same reciprocal-weighted identity in final-boundary sign orientation. -/
theorem primorialTruncatedBoundary_upperColumn_telescope_boundary
    (X K : ℕ) (hX : 1 ≤ X) :
    (∑ q ∈ primesUpTo K,
      (1 / (q : ℝ)) *
        (primorialTruncatedSignedReciprocalCube
            (primesUpTo (q - 1)) (X / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      -(primorialTruncatedSignedReciprocalCube (primesUpTo K) X -
          primorialSignedContractionFactor (primesUpTo K)) := by
  rw [primorialTruncatedBoundary_upperColumn_telescope X K hX]
  ring

/-! ## Literal physical partner column -/

/-- **Unweighted partner column = prime-weighted boundary drop.**

The fixed-partner mass in an earlier layer has no reciprocal factor in the partner `q`.
The fresh-prime recurrence therefore does *not* identify that physical column
with a telescoping boundary increment.  Instead it is exactly `q` times the
discrete drop of the boundary when the prime coordinate `q` is adjoined. -/
theorem primorialTruncatedBoundary_unweightedColumn_eq_prime_mul_boundaryDrop
    (X : ℕ) {q : ℕ} (hq : q.Prime) :
    primorialTruncatedSignedReciprocalCube
        (primesUpTo (q - 1)) (X / q) -
      primorialSignedContractionFactor (primesUpTo (q - 1)) =
    (q : ℝ) *
      ((primorialTruncatedSignedReciprocalCube
          (primesUpTo (q - 1)) X -
        primorialSignedContractionFactor (primesUpTo (q - 1))) -
       (primorialTruncatedSignedReciprocalCube
          (primesUpTo q) X -
        primorialSignedContractionFactor (primesUpTo q))) := by
  have hnot : q ∉ primesUpTo (q - 1) :=
    freshPrime_not_mem_primesUpTo_pred hq
  have hset := insert_freshPrime_primesUpTo_pred_eq hq
  have htrunc :=
    primorialTruncatedSignedReciprocalCube_insert
      (P := primesUpTo (q - 1)) (p := q) (X := X) hnot hq
  have hfactor :
      primorialSignedContractionFactor
          (insert q (primesUpTo (q - 1))) =
        (1 - 1 / (q : ℝ)) *
          primorialSignedContractionFactor (primesUpTo (q - 1)) := by
    unfold primorialSignedContractionFactor
    rw [Finset.prod_insert hnot]
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  rw [← hset, htrunc, hfactor]
  field_simp [hq0]
  ring

/-- Summing the literal physical-style partner columns therefore produces a
prime-weighted discrete boundary variation, not one terminal boundary.  This is
the exact seam which a physical post-root/birth bridge must control or cancel
using the existing external/root geometry. -/
theorem primorialTruncatedBoundary_unweightedUpperColumn_eq_primeWeightedDrops
    (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (primorialTruncatedSignedReciprocalCube
          (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      ∑ q ∈ primesUpTo K,
        (q : ℝ) *
          ((primorialTruncatedSignedReciprocalCube
              (primesUpTo (q - 1)) X -
            primorialSignedContractionFactor (primesUpTo (q - 1))) -
           (primorialTruncatedSignedReciprocalCube
              (primesUpTo q) X -
            primorialSignedContractionFactor (primesUpTo q))) := by
  apply Finset.sum_congr rfl
  intro q hq
  exact primorialTruncatedBoundary_unweightedColumn_eq_prime_mul_boundaryDrop
    X (prime_of_mem_primesUpTo hq)

end RHLean.Proof
