import Mathlib
import RHLean.Analysis.FiniteTorusFourierPairing
import RHLean.Proof.SurvivorZeroMode

/-!
# Survivor residue-fibre covariance

This module formalizes the exact signed residue-fibre object suggested by the
survivor diagnostics.  It introduces no cancellation estimate.

For a positive residue modulus `s`, an active survivor source is represented by
its canonical cofactor/prime pair `(c,q)`.  Its signed doubled height is

```text
q^2 - c^2.
```

The active prime fibre over `c` is partitioned by this height modulo `s`.  The
corresponding signed residue mass is

```text
A_{t,s}(u) = sum_c -mu(c) K_{t,s}(c,u),
```

where `K_{t,s}(c,u)` counts active primes in the `c`-fibre with height residue
`u`.

The central quadratic object is not the positive residue energy by itself.  We
separate that energy into the same-cofactor diagonal and the signed
cross-cofactor covariance.  The covariance is then represented on the Fourier
side by the existing exact finite-torus pairing theorem.

No upper bound, probabilistic independence assumption, or off-diagonal sign
claim is made here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

/-- Signed doubled height of a canonical cofactor/prime pair. -/
def survivorHeightDifference (c q : ℕ) : ℤ :=
  (q : ℤ) ^ 2 - (c : ℤ) ^ 2

/-- Residue class of the signed doubled height modulo `s`. -/
def survivorHeightResidue (s c q : ℕ) : ZMod s :=
  ((survivorHeightDifference c q : ℤ) : ZMod s)

/-- Active primes in the fixed cofactor fibre whose signed doubled height has
residue `u` modulo `s`. -/
noncomputable def survivorResiduePrimeFiber
    (Λ : ℝ) (t s c : ℕ) (u : ZMod s) : Finset ℕ := by
  classical
  exact
    (survivorZeroModePrimeFiber Λ t c).filter
      (fun q => survivorHeightResidue s c q = u)

/-- Residue-fibre counting kernel `K_{t,s}(c,u)`. -/
def survivorResidueKernel
    (Λ : ℝ) (t s c : ℕ) (u : ZMod s) : ℕ :=
  (survivorResiduePrimeFiber Λ t s c u).card

/-- Finite cofactor range already used by the exact survivor zero mode. -/
def survivorResidueCofactorRange (t : ℕ) : Finset ℕ :=
  Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t)

/-- Integer signed mass contributed by one cofactor to one residue fibre. -/
def survivorResidueCofactorMass
    (Λ : ℝ) (t s c : ℕ) (u : ZMod s) : ℤ :=
  -(μ c) * (survivorResidueKernel Λ t s c u : ℤ)

/-- Total signed survivor mass in residue fibre `u`. -/
def survivorResidueSignedMass
    (Λ : ℝ) (t s : ℕ) (u : ZMod s) : ℤ :=
  ∑ c ∈ survivorResidueCofactorRange t,
    survivorResidueCofactorMass Λ t s c u

/-- Positive residue-fibre quadratic energy `V_{t,s}`. -/
def survivorResidueEnergy
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℤ :=
  ∑ u : ZMod s,
    survivorResidueSignedMass Λ t s u * survivorResidueSignedMass Λ t s u

/-- Same-cofactor diagonal contribution `D_{t,s}`.  It is deliberately kept in
its exact signed-amplitude form rather than simplified using squarefreeness. -/
def survivorResidueDiagonalEnergy
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℤ :=
  ∑ u : ZMod s,
    ∑ c ∈ survivorResidueCofactorRange t,
      survivorResidueCofactorMass Λ t s c u *
        survivorResidueCofactorMass Λ t s c u

/-- Full residue Gram block between two cofactor fibres. -/
def survivorResidueCofactorGramBlock
    (Λ : ℝ) (t s c c' : ℕ) [NeZero s] : ℤ :=
  ∑ u : ZMod s,
    survivorResidueCofactorMass Λ t s c u *
      survivorResidueCofactorMass Λ t s c' u

/-- Full cofactor Gram expansion, retaining every diagonal and cross term. -/
def survivorResidueFullCofactorGram
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℤ :=
  ∑ c ∈ survivorResidueCofactorRange t,
    ∑ c' ∈ survivorResidueCofactorRange t,
      survivorResidueCofactorGramBlock Λ t s c c'

/-- Signed cross-cofactor covariance `C_{t,s}`.  Defining it as full Gram minus
its same-cofactor diagonal makes the exact logical target explicit without any
entrywise estimate. -/
def survivorResidueCrossCofactorCovariance
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℤ :=
  survivorResidueFullCofactorGram Λ t s -
    survivorResidueDiagonalEnergy Λ t s

/-- The explicit `c ≠ c'` Gram ledger.  For each outer cofactor `c`, the inner
sum is over the same finite cofactor range with `c` erased. -/
def survivorResidueOffDiagonalCofactorGram
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℤ :=
  ∑ c ∈ survivorResidueCofactorRange t,
    ∑ c' ∈ (survivorResidueCofactorRange t).erase c,
      survivorResidueCofactorGramBlock Λ t s c c'

/-- The residue kernels partition the complete active prime fibre. -/
theorem sum_survivorResidueKernel_eq_zeroModeKernel
    (Λ : ℝ) (t s c : ℕ) [NeZero s] :
    (∑ u : ZMod s, survivorResidueKernel Λ t s c u) =
      survivorZeroModeKernel Λ t c := by
  classical
  unfold survivorResidueKernel survivorResiduePrimeFiber
    survivorZeroModeKernel
  calc
    (∑ u : ZMod s,
        ((survivorZeroModePrimeFiber Λ t c).filter
          (fun q => survivorHeightResidue s c q = u)).card) =
      ∑ u : ZMod s,
        ∑ q ∈ survivorZeroModePrimeFiber Λ t c,
          if survivorHeightResidue s c q = u then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro u _hu
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ q ∈ survivorZeroModePrimeFiber Λ t c,
          ∑ u : ZMod s,
            if survivorHeightResidue s c q = u then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ _q ∈ survivorZeroModePrimeFiber Λ t c, 1 := by
          apply Finset.sum_congr rfl
          intro q _hq
          simp
    _ = (survivorZeroModePrimeFiber Λ t c).card := by simp

/-- Summing the residue fibres recovers the integer form of the exact survivor
zero mode. -/
theorem sum_survivorResidueSignedMass_eq_integerZeroMode
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    (∑ u : ZMod s, survivorResidueSignedMass Λ t s u) =
      ∑ c ∈ survivorResidueCofactorRange t,
        -(μ c) * (survivorZeroModeKernel Λ t c : ℤ) := by
  classical
  unfold survivorResidueSignedMass survivorResidueCofactorMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [← Finset.mul_sum]
  have hkernel :
      (∑ u : ZMod s, (survivorResidueKernel Λ t s c u : ℤ)) =
        (survivorZeroModeKernel Λ t c : ℤ) := by
    exact_mod_cast sum_survivorResidueKernel_eq_zeroModeKernel Λ t s c
  rw [hkernel]

/-- Exact full cofactor Gram expansion of the positive residue energy. -/
theorem survivorResidueEnergy_eq_fullCofactorGram
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    survivorResidueEnergy Λ t s =
      survivorResidueFullCofactorGram Λ t s := by
  classical
  unfold survivorResidueEnergy survivorResidueFullCofactorGram
    survivorResidueCofactorGramBlock survivorResidueSignedMass
  calc
    (∑ u : ZMod s,
        (∑ c ∈ survivorResidueCofactorRange t,
            survivorResidueCofactorMass Λ t s c u) *
          (∑ c ∈ survivorResidueCofactorRange t,
            survivorResidueCofactorMass Λ t s c u)) =
      ∑ u : ZMod s,
        ∑ c ∈ survivorResidueCofactorRange t,
          ∑ c' ∈ survivorResidueCofactorRange t,
            survivorResidueCofactorMass Λ t s c u *
              survivorResidueCofactorMass Λ t s c' u := by
            apply Finset.sum_congr rfl
            intro u _hu
            rw [Finset.sum_mul_sum]
    _ = ∑ c ∈ survivorResidueCofactorRange t,
          ∑ c' ∈ survivorResidueCofactorRange t,
            ∑ u : ZMod s,
              survivorResidueCofactorMass Λ t s c u *
                survivorResidueCofactorMass Λ t s c' u := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c _hc
          rw [Finset.sum_comm]

/-- The same-cofactor energy is the diagonal of the cofactor Gram. -/
theorem survivorResidueDiagonalEnergy_eq_sum_diagonalGram
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    survivorResidueDiagonalEnergy Λ t s =
      ∑ c ∈ survivorResidueCofactorRange t,
        survivorResidueCofactorGramBlock Λ t s c c := by
  classical
  unfold survivorResidueDiagonalEnergy survivorResidueCofactorGramBlock
  rw [Finset.sum_comm]

/-- The full cofactor Gram is exactly diagonal plus the explicit `c ≠ c'`
ledger. -/
theorem survivorResidueFullCofactorGram_eq_diagonal_add_offDiagonal
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    survivorResidueFullCofactorGram Λ t s =
      survivorResidueDiagonalEnergy Λ t s +
        survivorResidueOffDiagonalCofactorGram Λ t s := by
  classical
  rw [survivorResidueDiagonalEnergy_eq_sum_diagonalGram]
  unfold survivorResidueFullCofactorGram survivorResidueOffDiagonalCofactorGram
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hsplit :=
    Finset.sum_erase_add
      (s := survivorResidueCofactorRange t)
      (f := fun c' => survivorResidueCofactorGramBlock Λ t s c c') hc
  simpa [add_comm] using hsplit.symm

/-- Therefore the signed cross-cofactor covariance is literally the explicit
sum over unequal cofactors. -/
theorem survivorResidueCrossCofactorCovariance_eq_offDiagonal
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    survivorResidueCrossCofactorCovariance Λ t s =
      survivorResidueOffDiagonalCofactorGram Λ t s := by
  unfold survivorResidueCrossCofactorCovariance
  rw [survivorResidueFullCofactorGram_eq_diagonal_add_offDiagonal]
  ring

/-- Exact decomposition `V = D + C`. -/
theorem survivorResidueEnergy_eq_diagonal_add_crossCovariance
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    survivorResidueEnergy Λ t s =
      survivorResidueDiagonalEnergy Λ t s +
        survivorResidueCrossCofactorCovariance Λ t s := by
  rw [survivorResidueEnergy_eq_fullCofactorGram]
  unfold survivorResidueCrossCofactorCovariance
  ring

/-- Complex cast of the total signed residue mass, used only as the Fourier
input field. -/
def survivorResidueSignedMassComplex
    (Λ : ℝ) (t s : ℕ) (u : ZMod s) : ℂ :=
  ((survivorResidueSignedMass Λ t s u : ℤ) : ℂ)

/-- Complex cast of one cofactor residue field. -/
def survivorResidueCofactorMassComplex
    (Λ : ℝ) (t s c : ℕ) (u : ZMod s) : ℂ :=
  ((survivorResidueCofactorMass Λ t s c u : ℤ) : ℂ)

/-- Fourier-side total residue energy in the repository's exact unnormalized
`ZMod.dft` convention. -/
def survivorResidueSpectralEnergy
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℂ :=
  RHLean.Analysis.finiteTorusSpectralPairing
    (survivorResidueSignedMassComplex Λ t s)
    (survivorResidueSignedMassComplex Λ t s)

/-- Fourier-side same-cofactor diagonal energy. -/
def survivorResidueDiagonalSpectralEnergy
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℂ :=
  ∑ c ∈ survivorResidueCofactorRange t,
    RHLean.Analysis.finiteTorusSpectralPairing
      (survivorResidueCofactorMassComplex Λ t s c)
      (survivorResidueCofactorMassComplex Λ t s c)

/-- Fourier-side signed cross-cofactor covariance. -/
def survivorResidueCrossSpectralCovariance
    (Λ : ℝ) (t s : ℕ) [NeZero s] : ℂ :=
  survivorResidueSpectralEnergy Λ t s -
    survivorResidueDiagonalSpectralEnergy Λ t s

/-- Bilinear Parseval identity for the total signed residue energy.  Since the
physical field is integer-valued, its bilinear self-pairing is exactly the
positive integer energy before casting to `ℂ`. -/
theorem intCast_survivorResidueEnergy_eq_spectral
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    ((survivorResidueEnergy Λ t s : ℤ) : ℂ) =
      survivorResidueSpectralEnergy Λ t s := by
  unfold survivorResidueEnergy survivorResidueSpectralEnergy
    survivorResidueSignedMassComplex
  calc
    (((∑ u : ZMod s,
        survivorResidueSignedMass Λ t s u *
          survivorResidueSignedMass Λ t s u : ℤ)) : ℂ) =
      RHLean.Analysis.finiteTorusPairing
        (fun u : ZMod s => ((survivorResidueSignedMass Λ t s u : ℤ) : ℂ))
        (fun u : ZMod s => ((survivorResidueSignedMass Λ t s u : ℤ) : ℂ)) := by
          unfold RHLean.Analysis.finiteTorusPairing
          push_cast
          rfl
    _ = RHLean.Analysis.finiteTorusSpectralPairing
          (fun u : ZMod s => ((survivorResidueSignedMass Λ t s u : ℤ) : ℂ))
          (fun u : ZMod s => ((survivorResidueSignedMass Λ t s u : ℤ) : ℂ)) :=
      RHLean.Analysis.finiteTorusPairing_eq_spectral _ _

/-- Bilinear Parseval identity for the same-cofactor diagonal. -/
theorem intCast_survivorResidueDiagonalEnergy_eq_spectral
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    ((survivorResidueDiagonalEnergy Λ t s : ℤ) : ℂ) =
      survivorResidueDiagonalSpectralEnergy Λ t s := by
  classical
  unfold survivorResidueDiagonalEnergy survivorResidueDiagonalSpectralEnergy
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _hc
  change
    RHLean.Analysis.finiteTorusPairing
        (survivorResidueCofactorMassComplex Λ t s c)
        (survivorResidueCofactorMassComplex Λ t s c) =
      RHLean.Analysis.finiteTorusSpectralPairing
        (survivorResidueCofactorMassComplex Λ t s c)
        (survivorResidueCofactorMassComplex Λ t s c)
  exact RHLean.Analysis.finiteTorusPairing_eq_spectral _ _

/-- Exact Parseval representation of the signed cross-cofactor covariance. -/
theorem intCast_survivorResidueCrossCovariance_eq_spectral
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    ((survivorResidueCrossCofactorCovariance Λ t s : ℤ) : ℂ) =
      survivorResidueCrossSpectralCovariance Λ t s := by
  unfold survivorResidueCrossCofactorCovariance
    survivorResidueCrossSpectralCovariance
  rw [← survivorResidueEnergy_eq_fullCofactorGram]
  push_cast
  rw [intCast_survivorResidueEnergy_eq_spectral,
    intCast_survivorResidueDiagonalEnergy_eq_spectral]

end RHLean.Proof
