import Mathlib
import RHLean.Analysis.NativePNTMertens
import RHLean.Analysis.NativePNTSquarePrefixContraction
import RHLean.Arithmetic.PrimeFaceMoebius
import RHLean.Arithmetic.PrimorialWheelScale

/-!
# Finite primorial reciprocal Möbius factorization

This module iterates the architecture's only arithmetic improvement lever,
`mu(m*p) = -mu(m)` for a fresh prime, across a finite Boolean prime cube.
Everything is finite and exact.

For a finite prime set `P`, define the signed reciprocal contraction factor

`C_-(P) = prod_{p in P} (1 - 1/p)`

and the unsigned squarefree-support factor

`C_+(P) = prod_{p in P} (1 + 1/p)`.

The complete reciprocal Möbius cube on the squarefree products of `P` has
signed mass `C_-(P)`, while its unsigned reciprocal support mass is `C_+(P)`.
Their product is the finite squarefree Euler factor

`prod_{p in P} (1 - 1/p^2)`.

No infinite product, Mertens product theorem, prime number theorem, or
asymptotic squarefree density is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- Signed fresh-prime contraction factor on a finite prime wheel. -/
def primorialSignedContractionFactor (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - 1 / (p : ℝ))

/-- Unsigned reciprocal mass factor of the same squarefree Boolean cube. -/
def primorialSquarefreeSupportFactor (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 + 1 / (p : ℝ))

/-- Finite squarefree Euler factor attached to the wheel. -/
def primorialSquarefreeEulerFactor (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - 1 / ((p : ℝ) ^ 2))

/-- Signed reciprocal mass of every squarefree product represented by a face of
`P`. -/
def primorialSignedReciprocalCube (P : Finset ℕ) : ℝ :=
  ∑ t ∈ P.powerset,
    ((booleanCubeSign t : ℤ) : ℝ) / (primeFaceProduct t : ℝ)

/-- Unsigned reciprocal support mass of the same complete squarefree cube. -/
def primorialUnsignedReciprocalCube (P : Finset ℕ) : ℝ :=
  ∑ t ∈ P.powerset, 1 / (primeFaceProduct t : ℝ)

/-- Adding one prime coordinate multiplies the complete signed reciprocal cube
by the exact fresh-prime factor `1 - 1/p`. -/
theorem primorialSignedReciprocalCube_insert
    {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (hpPrime : p.Prime) :
    primorialSignedReciprocalCube (insert p P) =
      (1 - 1 / (p : ℝ)) * primorialSignedReciprocalCube P := by
  classical
  unfold primorialSignedReciprocalCube
  rw [Finset.sum_powerset_insert hp]
  have hsecond :
      (∑ t ∈ P.powerset,
        ((booleanCubeSign (insert p t) : ℤ) : ℝ) /
          (primeFaceProduct (insert p t) : ℝ)) =
        (-1 / (p : ℝ)) *
          ∑ t ∈ P.powerset,
            ((booleanCubeSign t : ℤ) : ℝ) / (primeFaceProduct t : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hpt : p ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem ht hp
    have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
    have hsign :
        ((booleanCubeSign (insert p t) : ℤ) : ℝ) =
          -((booleanCubeSign t : ℤ) : ℝ) := by
      unfold booleanCubeSign
      rw [Finset.card_insert_of_notMem hpt, pow_succ]
      push_cast
      ring
    rw [hsign]
    simp only [primeFaceProduct]
    rw [Finset.prod_insert hpt]
    push_cast
    simp only [id_eq]
    field_simp [hpR0]
  rw [hsecond]
  ring

/-- The complete signed reciprocal Boolean cube is exactly the finite product
of fresh-prime contraction factors. -/
theorem primorialSignedReciprocalCube_eq_factor
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    primorialSignedReciprocalCube P = primorialSignedContractionFactor P := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp [primorialSignedReciprocalCube, primorialSignedContractionFactor,
        primeFaceProduct, booleanCubeSign]
  | @insert p P hp ih =>
      rw [primorialSignedReciprocalCube_insert hp
        (hprime p (Finset.mem_insert_self p P))]
      rw [ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))]
      simp [primorialSignedContractionFactor, hp]

/-- Adding one prime coordinate multiplies unsigned squarefree reciprocal mass
by `1 + 1/p`. -/
theorem primorialUnsignedReciprocalCube_insert
    {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (hpPrime : p.Prime) :
    primorialUnsignedReciprocalCube (insert p P) =
      (1 + 1 / (p : ℝ)) * primorialUnsignedReciprocalCube P := by
  classical
  unfold primorialUnsignedReciprocalCube
  rw [Finset.sum_powerset_insert hp]
  have hsecond :
      (∑ t ∈ P.powerset,
        1 / (primeFaceProduct (insert p t) : ℝ)) =
        (1 / (p : ℝ)) *
          ∑ t ∈ P.powerset, 1 / (primeFaceProduct t : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hpt : p ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem ht hp
    have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
    simp only [primeFaceProduct]
    rw [Finset.prod_insert hpt]
    push_cast
    simp only [id_eq]
    field_simp [hpR0]
  rw [hsecond]
  ring

/-- The complete unsigned reciprocal support cube is exactly the finite product
`prod (1 + 1/p)`. -/
theorem primorialUnsignedReciprocalCube_eq_factor
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    primorialUnsignedReciprocalCube P = primorialSquarefreeSupportFactor P := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp [primorialUnsignedReciprocalCube, primorialSquarefreeSupportFactor,
        primeFaceProduct]
  | @insert p P hp ih =>
      rw [primorialUnsignedReciprocalCube_insert hp
        (hprime p (Finset.mem_insert_self p P))]
      rw [ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))]
      simp [primorialSquarefreeSupportFactor, hp]

/-- Exact finite factorization of squarefree survival into signed contraction
and unsigned support population. -/
theorem primorial_signed_mul_support_eq_squarefreeEuler
    (P : Finset ℕ) :
    primorialSignedContractionFactor P * primorialSquarefreeSupportFactor P =
      primorialSquarefreeEulerFactor P := by
  classical
  unfold primorialSignedContractionFactor primorialSquarefreeSupportFactor
    primorialSquarefreeEulerFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  ring

/-- On a complete prime cube, the ratio of signed reciprocal mass to unsigned
support mass is the product of the exact factors `(p-1)/(p+1)`. -/
theorem primorial_signed_to_support_ratio
    (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    primorialSignedContractionFactor P =
      primorialSquarefreeSupportFactor P *
        ∏ p ∈ P, ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
  classical
  unfold primorialSignedContractionFactor primorialSquarefreeSupportFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hprime p hp).pos
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hp1, ne_of_gt hpR]

/-- The first `k` indexed wheel primes are all prime. -/
theorem wheelPrime_range_prime (k : ℕ) :
    ∀ p ∈ (Finset.range k).image wheelPrime, p.Prime := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
  exact wheelPrime_prime i

/-- Concrete signed contraction factor for the first `k` wheel primes. -/
def primorialInitialSignedFactor (k : ℕ) : ℝ :=
  primorialSignedContractionFactor ((Finset.range k).image wheelPrime)

/-- Concrete squarefree-support factor for the first `k` wheel primes. -/
def primorialInitialSupportFactor (k : ℕ) : ℝ :=
  primorialSquarefreeSupportFactor ((Finset.range k).image wheelPrime)

/-- Concrete finite squarefree Euler factor for the first `k` wheel primes. -/
def primorialInitialSquarefreeEulerFactor (k : ℕ) : ℝ :=
  primorialSquarefreeEulerFactor ((Finset.range k).image wheelPrime)

/-- Exact finite primorial factorization, with no passage to an infinite Euler
product. -/
theorem primorialInitial_signed_mul_support_eq_squarefreeEuler (k : ℕ) :
    primorialInitialSignedFactor k * primorialInitialSupportFactor k =
      primorialInitialSquarefreeEulerFactor k := by
  exact primorial_signed_mul_support_eq_squarefreeEuler _

/-- The reciprocal Mertens bound `<= 1` cannot be uniformly improved to any
constant below `1` on all positive prefixes, because the first prefix has
exact value `1`. -/
theorem nativeMertensRecip_no_uniform_bound_lt_one
    {c : ℝ} (hc : c < 1) :
    ¬ (∀ N : ℕ, 1 ≤ N → |RHLean.Analysis.nativeMertensRecip N| ≤ c) := by
  intro h
  have h1 := h 1 (by omega)
  have hvalue : RHLean.Analysis.nativeMertensRecip 1 = 1 := by
    simp [RHLean.Analysis.nativeMertensRecip]
  rw [hvalue, abs_one] at h1
  linarith

end RHLean.Arithmetic
