import Mathlib
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Proof.LowWheelTransportTripleCarrier

/-!
# Prime toggle between the low cofactor and residual quotient

On the prime-count-free triple carrier `(c,t,k)`, the Boolean face `t` is kept
fixed and one prime is moved between the cofactor `c` and the residual quotient
`k`.  This is the first same-product move in the transport expansion that flips
exactly one of the two low-wheel signs.

For a fixed prime `p` the map on `(c,k)` is

* if `p | c`, move it out: `(c,k) -> (c/p, p*k)`;
* otherwise, if `p | k`, move it in: `(c,k) -> (c*p, k/p)`;
* otherwise leave the state fixed.

On squarefree cofactors the active move is an involution and reverses the
Möbius sign.  The complete physical product `c * P(t) * k` is invariant.  The
removal direction always preserves the transport carrier.  In the insertion
direction the apparent cofactor and quotient boundary failures are not
independent at the square endpoint: if `c*p >= R` while `P(t)*(k/p) > R`, then
the invariant product is already at least `R^2`, contradicting the endpoint
ceiling `R^2-1`.  Thus every genuine insertion failure is a quotient
root-downcross `P(t)*(k/p) <= R`.

No norm or estimate is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Cofactor/quotient state at one fixed low-prime Boolean face. -/
abbrev LowWheelCofactorQuotientState := ℕ × ℕ

/-- Toggle one prime between the cofactor and quotient coordinates. -/
def lowWheelCofactorQuotientToggleAt
    (p : ℕ) (x : LowWheelCofactorQuotientState) :
    LowWheelCofactorQuotientState :=
  if p ∣ x.1 then
    (x.1 / p, p * x.2)
  else if p ∣ x.2 then
    (x.1 * p, x.2 / p)
  else
    x

/-- The cofactor-times-quotient product is invariant under every fixed-prime
coordinate toggle. -/
theorem lowWheelCofactorQuotientToggleAt_product
    {p : ℕ} (x : LowWheelCofactorQuotientState) :
    (lowWheelCofactorQuotientToggleAt p x).1 *
        (lowWheelCofactorQuotientToggleAt p x).2 = x.1 * x.2 := by
  unfold lowWheelCofactorQuotientToggleAt
  by_cases hpc : p ∣ x.1
  · simp only [hpc, if_true]
    have hcancel : x.1 / p * p = x.1 := Nat.div_mul_cancel hpc
    calc
      (x.1 / p) * (p * x.2) = (x.1 / p * p) * x.2 := by ring
      _ = x.1 * x.2 := by rw [hcancel]
  · simp only [hpc, if_false]
    by_cases hpk : p ∣ x.2
    · simp only [hpk, if_true]
      have hcancel : x.2 / p * p = x.2 := Nat.div_mul_cancel hpk
      calc
        (x.1 * p) * (x.2 / p) = x.1 * (x.2 / p * p) := by ring
        _ = x.1 * x.2 := by rw [hcancel]
    · simp [hpk]

/-- Removing a prime from a squarefree cofactor leaves that prime absent from
the quotient cofactor. -/
theorem prime_not_dvd_div_of_squarefree
    {p c : ℕ} (hp : p.Prime) (hsq : Squarefree c) (hpc : p ∣ c) :
    ¬ p ∣ c / p := by
  intro hpd
  have hcancel : p * (c / p) = c := Nat.mul_div_cancel' hpc
  have hsqdiv : p * p ∣ c := by
    rcases hpd with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [← hcancel, hr]
    ring
  exact hp.not_isUnit (hsq p hsqdiv)

/-- Fresh insertion of a prime reverses the canonical Möbius weight. -/
theorem canonicalMoebiusWeight_mul_freshPrime
    {c p : ℕ} (hp : p.Prime) (hpc : ¬ p ∣ c) :
    canonicalMoebiusWeight (c * p) = -canonicalMoebiusWeight c := by
  have hmu := moebius_prime_mul hp hpc
  unfold canonicalMoebiusWeight
  rw [Nat.mul_comm, hmu]
  push_cast
  ring

/-- Removing a prime from a squarefree cofactor also reverses its Möbius weight. -/
theorem canonicalMoebiusWeight_div_prime
    {c p : ℕ} (hp : p.Prime) (hsq : Squarefree c) (hpc : p ∣ c) :
    canonicalMoebiusWeight (c / p) = -canonicalMoebiusWeight c := by
  have hnot := prime_not_dvd_div_of_squarefree hp hsq hpc
  have hmu := moebius_prime_mul hp hnot
  have hcancel : p * (c / p) = c := Nat.mul_div_cancel' hpc
  have hmu' : μ c = -μ (c / p) := by
    calc
      μ c = μ (p * (c / p)) := congrArg μ hcancel.symm
      _ = -μ (c / p) := hmu
  have hrev : μ (c / p) = -μ c := by linarith
  unfold canonicalMoebiusWeight
  rw [hrev]
  push_cast
  ring

/-- On a squarefree cofactor, every active `p`-toggle reverses the signed weight
at a fixed Boolean face. -/
theorem lowWheelCofactorQuotientToggleAt_weight_neg
    {p c k : ℕ} {t : Finset ℕ}
    (hp : p.Prime) (hsq : Squarefree c)
    (hactive : p ∣ c ∨ p ∣ k) :
    canonicalMoebiusWeight (lowWheelCofactorQuotientToggleAt p (c, k)).1 *
        (booleanCubeSign t : ℂ) =
      -(canonicalMoebiusWeight c * (booleanCubeSign t : ℂ)) := by
  unfold lowWheelCofactorQuotientToggleAt
  by_cases hpc : p ∣ c
  · simp only [hpc, if_true]
    rw [canonicalMoebiusWeight_div_prime hp hsq hpc]
    ring
  · have hpk : p ∣ k := hactive.resolve_left hpc
    simp only [hpc, if_false, hpk, if_true]
    rw [canonicalMoebiusWeight_mul_freshPrime hp hpc]
    ring

/-- On squarefree cofactors the active fixed-prime toggle is genuinely an
involution. -/
theorem lowWheelCofactorQuotientToggleAt_involutive
    {p c k : ℕ} (hp : p.Prime) (hsq : Squarefree c)
    (hactive : p ∣ c ∨ p ∣ k) :
    lowWheelCofactorQuotientToggleAt p
        (lowWheelCofactorQuotientToggleAt p (c, k)) = (c, k) := by
  unfold lowWheelCofactorQuotientToggleAt
  by_cases hpc : p ∣ c
  · have hnot : ¬ p ∣ c / p :=
      prime_not_dvd_div_of_squarefree hp hsq hpc
    have hpMul : p ∣ p * k := dvd_mul_right p k
    simp only [hpc, if_true, hnot, if_false, hpMul]
    have hcCancel : c / p * p = c := Nat.div_mul_cancel hpc
    have hkCancel : (p * k) / p = k := by simp [hp.ne_zero]
    exact Prod.ext hcCancel hkCancel
  · have hpk : p ∣ k := hactive.resolve_left hpc
    have hpMul : p ∣ c * p := dvd_mul_left p c
    simp only [hpc, if_false, hpk, if_true, hpMul]
    have hcCancel : (c * p) / p = c := by simp [hp.ne_zero]
    have hkCancel : p * (k / p) = k := Nat.mul_div_cancel' hpk
    exact Prod.ext hcCancel hkCancel

/-- Physical carrier predicate at one fixed Boolean face. -/
def LowWheelTransportPairCarrier
    (R : ℕ) (t : Finset ℕ) (x : LowWheelCofactorQuotientState) : Prop :=
  1 ≤ x.1 ∧ x.1 < R ∧
    R < primeFaceProduct t * x.2 ∧
      (x.1 * primeFaceProduct t) * x.2 ≤ squareRootEndpoint R

/-- Removing a prime from the cofactor always stays inside the physical
transport carrier.  It lowers `c`, raises the high quotient, and preserves the
complete physical product. -/
theorem lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
    {R c k p : ℕ} {t : Finset ℕ}
    (hp : p.Prime) (hcarrier : LowWheelTransportPairCarrier R t (c, k))
    (hpc : p ∣ c) :
    LowWheelTransportPairCarrier R t
      (lowWheelCofactorQuotientToggleAt p (c, k)) := by
  rcases hcarrier with ⟨hc1, hcR, hhigh, htop⟩
  have hcpos : 0 < c := by omega
  have hcp : p ≤ c := Nat.le_of_dvd hcpos hpc
  have hcdivpos : 1 ≤ c / p :=
    (Nat.one_le_div_iff hp.pos).2 hcp
  have hcdivle : c / p ≤ c := Nat.div_le_self _ _
  have hprod := lowWheelCofactorQuotientToggleAt_product (c, k) (p := p)
  unfold lowWheelCofactorQuotientToggleAt at hprod ⊢
  simp only [hpc, if_true] at hprod ⊢
  refine ⟨hcdivpos, lt_of_le_of_lt hcdivle hcR, ?_, ?_⟩
  · have hkLe : k ≤ p * k := by
      have hp1 : 1 ≤ p := hp.one_le
      exact Nat.le_mul_of_pos_left k hp.pos
    exact hhigh.trans_le (Nat.mul_le_mul_left (primeFaceProduct t) hkLe)
  · calc
      ((c / p) * primeFaceProduct t) * (p * k) =
          ((c / p) * (p * k)) * primeFaceProduct t := by ring
      _ = (c * k) * primeFaceProduct t := by rw [hprod]
      _ = (c * primeFaceProduct t) * k := by ring
      _ ≤ squareRootEndpoint R := htop

/-- In the insertion direction, failure to remain in the carrier is completely
localized to the cofactor cutoff or the high-quotient cutoff. -/
theorem lowWheelCofactorQuotientToggleAt_preserves_or_boundary_of_dvd_quotient
    {R c k p : ℕ} {t : Finset ℕ}
    (hp : p.Prime) (hcarrier : LowWheelTransportPairCarrier R t (c, k))
    (hpc : ¬ p ∣ c) (hpk : p ∣ k) :
    LowWheelTransportPairCarrier R t
        (lowWheelCofactorQuotientToggleAt p (c, k)) ∨
      R ≤ c * p ∨ primeFaceProduct t * (k / p) ≤ R := by
  by_cases hcR : c * p < R
  · by_cases hhigh : R < primeFaceProduct t * (k / p)
    · left
      have hc1 : 1 ≤ c := hcarrier.1
      have hcpos : 0 < c := by omega
      have hcp1 : 1 ≤ c * p := Nat.succ_le_iff.mpr (Nat.mul_pos hcpos hp.pos)
      have hprod := lowWheelCofactorQuotientToggleAt_product (c, k) (p := p)
      unfold lowWheelCofactorQuotientToggleAt at hprod ⊢
      simp only [hpc, if_false, hpk, if_true] at hprod ⊢
      refine ⟨hcp1, hcR, hhigh, ?_⟩
      calc
        ((c * p) * primeFaceProduct t) * (k / p) =
            ((c * p) * (k / p)) * primeFaceProduct t := by ring
        _ = (c * k) * primeFaceProduct t := by rw [hprod]
        _ = (c * primeFaceProduct t) * k := by ring
        _ ≤ squareRootEndpoint R := hcarrier.2.2.2
    · right
      right
      exact Nat.le_of_not_gt hhigh
  · right
    left
    exact Nat.le_of_not_gt hcR

/-- **One-sided square-root insertion frontier.**  At the square endpoint the
cofactor crossing is subsumed by the quotient crossing.  If `c*p >= R` and the
post-toggle quotient were still above `R`, product invariance would force a
physical product at least `R^2`, contradicting the ceiling `R^2-1`. -/
theorem lowWheelCofactorQuotientToggleAt_preserves_or_downcross_of_dvd_quotient
    {R c k p : ℕ} {t : Finset ℕ}
    (hp : p.Prime) (hcarrier : LowWheelTransportPairCarrier R t (c, k))
    (hpc : ¬ p ∣ c) (hpk : p ∣ k) :
    LowWheelTransportPairCarrier R t
        (lowWheelCofactorQuotientToggleAt p (c, k)) ∨
      primeFaceProduct t * (k / p) ≤ R := by
  rcases lowWheelCofactorQuotientToggleAt_preserves_or_boundary_of_dvd_quotient
      hp hcarrier hpc hpk with hmate | hboundary
  · exact Or.inl hmate
  · right
    rcases hboundary with hroot | hdown
    · by_contra hnotDown
      have hhigh : R < primeFaceProduct t * (k / p) := by omega
      have hRpos : 0 < R := by
        have hc1 := hcarrier.1
        have hcR := hcarrier.2.1
        omega
      have hXlt : squareRootEndpoint R < R ^ 2 := by
        unfold squareRootEndpoint
        have hpos : 0 < R ^ 2 := by positivity
        omega
      have hprodEq :
          (c * p) * (primeFaceProduct t * (k / p)) =
            (c * primeFaceProduct t) * k := by
        have hkCancel : p * (k / p) = k := Nat.mul_div_cancel' hpk
        calc
          (c * p) * (primeFaceProduct t * (k / p)) =
              (c * primeFaceProduct t) * (p * (k / p)) := by ring
          _ = (c * primeFaceProduct t) * k := by rw [hkCancel]
      have hsqle :
          R ^ 2 ≤ (c * p) * (primeFaceProduct t * (k / p)) := by
        simpa [pow_two] using Nat.mul_le_mul hroot hhigh.le
      rw [hprodEq] at hsqle
      have hprodlt : (c * primeFaceProduct t) * k < R ^ 2 :=
        hcarrier.2.2.2.trans_lt hXlt
      exact (Nat.not_lt_of_ge hsqle) hprodlt
    · exact hdown

end RHLean.Proof
