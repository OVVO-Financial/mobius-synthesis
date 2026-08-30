import Mathlib
import RHLean.Analysis.LargePrimeTTransport
import RHLean.Analysis.SquareRootTransportTopFibreNoGo

/-!
# Exact middle-prime fibre collapse

At the square endpoint `X_R = R^2 - 1`, every prime in the middle range

`R < q <= X_R / 2`

has reciprocal quotient in `[2,R)`.  Hence every cofactor
`1 <= c <= floor(X_R/q)` lies strictly below `R < q`.  The fresh prime `q`
is therefore coprime to `c`, so adjoining it flips the Möbius sign exactly:

`mu(c*q) = -mu(c)`.

This module keeps that pointwise sign law intact and performs only finite exact
regrouping.  It proves:

* each middle prime fibre is `-M(floor(X_R/q))`;
* grouping middle primes by the reciprocal quotient `k` gives the finite shell
  sum `- sum_{2 <= k < R} N_R(k) M(k)`;
* the separate quotient-one top block is deterministic: every top prime
  contributes exactly `-1` to the final Möbius fibre.

No absolute value, Cauchy--Schwarz inequality, prime-count estimate, Mertens
bound, density statement, RH input, or dissipation claim is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- Integer-valued Möbius prefix through `N`.  This is the exact finite object
used in the middle fibres; no estimate is attached to it here. -/
def nativeMertens (N : ℕ) : ℤ :=
  ∑ c ∈ Finset.Icc 1 N, ArithmeticFunction.moebius c

/-- The middle prime range `R < q <= (R^2-1)/2`. -/
def middlePrimeSet (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R / 2)).filter Nat.Prime

@[simp] theorem mem_middlePrimeSet
    {R q : ℕ} :
    q ∈ middlePrimeSet R ↔
      R < q ∧ q ≤ squareRootEndpoint R / 2 ∧ q.Prime := by
  unfold middlePrimeSet
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hRq, hqle⟩
    exact ⟨hRq, hqle, hqPrime⟩
  · rintro ⟨hRq, hqle, hqPrime⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hRq, hqle⟩, hqPrime⟩

/-- The assumptions describing a middle prime force a positive root cutoff. -/
private theorem one_le_root_of_middlePrime
    {R q : ℕ} (hq : q.Prime)
    (hqle : q ≤ squareRootEndpoint R / 2) :
    1 ≤ R := by
  by_contra hR
  have hR0 : R = 0 := by omega
  subst R
  have hqpos : 0 < q := hq.pos
  unfold squareRootEndpoint at hqle
  norm_num at hqle
  omega

/-- Every middle reciprocal quotient lies in the exact finite shell range
`2 <= floor(X_R/q) < R`. -/
theorem middlePrime_quotient_mem_Ico
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) :
    squareRootEndpoint R / q ∈ Finset.Ico 2 R := by
  rcases mem_middlePrimeSet.mp hqmem with ⟨hRq, hqle, hqPrime⟩
  have hR : 1 ≤ R := one_le_root_of_middlePrime hqPrime hqle
  have hqIoc : q ∈ Finset.Ioc R (squareRootEndpoint R / 2) :=
    Finset.mem_Ioc.mpr ⟨hRq, hqle⟩
  exact Finset.mem_Ico.mpr (squareRootMiddleQuotient_range hR hqIoc)

/-- **Fibrewise middle-prime collapse.**

For a prime `q` above `R`, every admitted cofactor is below `R`, hence below
`q`.  The large-prime transport law gives `mu(c*q) = -mu(c)` pointwise, and the
whole fibre is therefore the negative Möbius prefix at the reciprocal quotient.
-/
theorem middlePrimeFibre_sum_moebius_eq_neg_mertens
    (R q : ℕ)
    (hq : q.Prime)
    (hRq : R < q)
    (hqle : q ≤ squareRootEndpoint R / 2) :
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        ArithmeticFunction.moebius (c * q) : ℤ) =
      - (nativeMertens (squareRootEndpoint R / q) : ℤ) := by
  have hR : 1 ≤ R := one_le_root_of_middlePrime hq hqle
  have hqIoc : q ∈ Finset.Ioc R (squareRootEndpoint R / 2) :=
    Finset.mem_Ioc.mpr ⟨hRq, hqle⟩
  have hquotR : squareRootEndpoint R / q < R :=
    squareRootEndpoint_div_lt_root_of_middle hR hqIoc
  unfold nativeMertens
  calc
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        ArithmeticFunction.moebius (c * q) : ℤ) =
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        -(ArithmeticFunction.moebius c : ℤ) := by
          apply Finset.sum_congr rfl
          intro c hc
          rcases Finset.mem_Icc.mp hc with ⟨hc1, hcUpper⟩
          have hcR : c < R := hcUpper.trans_lt hquotR
          let D : LargePrimeTransportData R c q :=
            { c_pos := hc1
              c_lt_cutoff := hcR
              q_prime := hq
              cutoff_lt_q := hRq }
          have hflip := LargePrimeTransportData.moebius_mul_eq_neg D
          simpa [Nat.mul_comm] using hflip
    _ = -(∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
        ArithmeticFunction.moebius c : ℤ) := by
          rw [Finset.sum_neg_distrib]

/-- The signed final Möbius residual carried by one reciprocal prime fibre. -/
def middlePrimeFibreResidual (R q : ℕ) : ℤ :=
  ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
    ArithmeticFunction.moebius (c * q)

/-- Fibrewise collapse in residual notation. -/
theorem middlePrimeFibreResidual_eq_neg_mertens
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) :
    middlePrimeFibreResidual R q =
      -nativeMertens (squareRootEndpoint R / q) := by
  rcases mem_middlePrimeSet.mp hqmem with ⟨hRq, hqle, hqPrime⟩
  unfold middlePrimeFibreResidual
  exact middlePrimeFibre_sum_moebius_eq_neg_mertens
    R q hqPrime hRq hqle

/-- Middle primes with one fixed reciprocal quotient `k`. -/
def middlePrimeReciprocalShell (R k : ℕ) : Finset ℕ :=
  (middlePrimeSet R).filter fun q =>
    squareRootEndpoint R / q = k

/-- The quotient-shell multiplicity `N_R(k)`. -/
def middlePrimeReciprocalCount (R k : ℕ) : ℕ :=
  (middlePrimeReciprocalShell R k).card

@[simp] theorem mem_middlePrimeReciprocalShell
    {R k q : ℕ} :
    q ∈ middlePrimeReciprocalShell R k ↔
      q ∈ middlePrimeSet R ∧ squareRootEndpoint R / q = k := by
  simp [middlePrimeReciprocalShell]

/-- Finite Fubini regrouping of the reciprocal Mertens arguments by their exact
quotient fibres.  No estimate is used between shells. -/
theorem middlePrime_mertens_sum_eq_count_mul_mertens
    (R : ℕ) :
    (∑ q ∈ middlePrimeSet R,
        nativeMertens (squareRootEndpoint R / q) : ℤ) =
      ∑ k ∈ Finset.Ico 2 R,
        (middlePrimeReciprocalCount R k : ℤ) * nativeMertens k := by
  classical
  have hmaps :
      ∀ q ∈ middlePrimeSet R,
        squareRootEndpoint R / q ∈ Finset.Ico 2 R := by
    intro q hq
    exact middlePrime_quotient_mem_Ico hq
  unfold middlePrimeReciprocalCount middlePrimeReciprocalShell
  calc
    (∑ q ∈ middlePrimeSet R,
        nativeMertens (squareRootEndpoint R / q) : ℤ) =
      ∑ k ∈ Finset.Ico 2 R,
        ∑ _q ∈ middlePrimeSet R with
            squareRootEndpoint R / _q = k,
          nativeMertens k := by
            symm
            simpa using
              (Finset.sum_fiberwise_of_maps_to'
                (s := middlePrimeSet R)
                (t := Finset.Ico 2 R)
                (g := fun q => squareRootEndpoint R / q)
                hmaps
                (fun k : ℕ => nativeMertens k))
    _ = ∑ k ∈ Finset.Ico 2 R,
        (((middlePrimeSet R).filter fun q =>
            squareRootEndpoint R / q = k).card : ℤ) * nativeMertens k := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp

/-- **Exact quotient-shell identity for the whole middle block.**

The only operation after the fibrewise sign flip is finite regrouping by
`k = floor(X_R/q)`.  In particular no absolute values are inserted between the
`k`-shells. -/
theorem middlePrimeShell_sum_eq_neg_count_mul_mertens
    (R : ℕ) :
    (∑ q ∈ middlePrimeSet R,
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
          ArithmeticFunction.moebius (c * q) : ℤ) =
      - (∑ k ∈ Finset.Ico 2 R,
          (middlePrimeReciprocalCount R k : ℤ) *
            (nativeMertens k : ℤ)) := by
  classical
  calc
    (∑ q ∈ middlePrimeSet R,
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R / q),
          ArithmeticFunction.moebius (c * q) : ℤ) =
      ∑ q ∈ middlePrimeSet R,
        -nativeMertens (squareRootEndpoint R / q) := by
          apply Finset.sum_congr rfl
          intro q hq
          simpa [middlePrimeFibreResidual] using
            (middlePrimeFibreResidual_eq_neg_mertens hq)
    _ = -(∑ q ∈ middlePrimeSet R,
        nativeMertens (squareRootEndpoint R / q) : ℤ) := by
          rw [Finset.sum_neg_distrib]
    _ = - (∑ k ∈ Finset.Ico 2 R,
          (middlePrimeReciprocalCount R k : ℤ) *
            (nativeMertens k : ℤ)) := by
          rw [middlePrime_mertens_sum_eq_count_mul_mertens]

/-- The exact total middle residual. -/
def middlePrimeTotal (R : ℕ) : ℤ :=
  ∑ q ∈ middlePrimeSet R, middlePrimeFibreResidual R q

/-- The total middle residual is precisely the quotient-shell compression. -/
theorem middlePrimeTotal_eq_neg_count_mul_mertens
    (R : ℕ) :
    middlePrimeTotal R =
      - (∑ k ∈ Finset.Ico 2 R,
          (middlePrimeReciprocalCount R k : ℤ) *
            (nativeMertens k : ℤ)) := by
  unfold middlePrimeTotal middlePrimeFibreResidual
  exact middlePrimeShell_sum_eq_neg_count_mul_mertens R

/-! ## The separate quotient-one top block -/

/-- Every prime in the top half `(X_R/2,X_R]` has reciprocal quotient exactly
`1`. -/
theorem middlePrimeTop_quotient_eq_one
    {R q : ℕ} (hqmem : q ∈ squareRootTopFibrePrimes R) :
    squareRootEndpoint R / q = 1 := by
  rcases Finset.mem_filter.mp hqmem with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hlow, hhigh⟩
  have hXlt : squareRootEndpoint R < 2 * q := by
    have h :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hlow
    simpa [Nat.mul_comm] using h
  exact squareRootEndpoint_div_eq_one_of_top_fibre
    hqPrime.pos hXlt hhigh

/-- A quotient-one top prime has only `c=1` in its final Möbius fibre, so it
contributes exactly `-1`. -/
theorem middlePrimeTopFibreResidual_eq_neg_one
    {R q : ℕ} (hqmem : q ∈ squareRootTopFibrePrimes R) :
    middlePrimeFibreResidual R q = -1 := by
  have hqPrime : q.Prime := (Finset.mem_filter.mp hqmem).2
  have hdiv := middlePrimeTop_quotient_eq_one hqmem
  unfold middlePrimeFibreResidual
  rw [hdiv]
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  simp [ArithmeticFunction.moebius_apply_prime hqPrime]

/-- Deterministic signed baseline of the quotient-one top block. -/
def middlePrimeTopDeterministicBaseline (R : ℕ) : ℤ :=
  -((squareRootTopFibrePrimes R).card : ℤ)

/-- **The `k=1` top block is exactly the deterministic prime baseline.**
Every top prime contributes one final Möbius value `-1`; no cancellation or
prime-count estimate is involved. -/
theorem middlePrimeTopBlock_sum_eq_deterministicBaseline
    (R : ℕ) :
    (∑ q ∈ squareRootTopFibrePrimes R,
        middlePrimeFibreResidual R q : ℤ) =
      middlePrimeTopDeterministicBaseline R := by
  classical
  unfold middlePrimeTopDeterministicBaseline
  calc
    (∑ q ∈ squareRootTopFibrePrimes R,
        middlePrimeFibreResidual R q : ℤ) =
      ∑ _q ∈ squareRootTopFibrePrimes R, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact middlePrimeTopFibreResidual_eq_neg_one hq
    _ = -((squareRootTopFibrePrimes R).card : ℤ) := by
      simp

end RHLean.Proof
