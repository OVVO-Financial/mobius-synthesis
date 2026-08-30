import Mathlib
import RHLean.Proof.LowWheelFaceTailToggle

/-!
# Active prime support is invariant under one face-tail transfer

The opposite Othello move transfers one prime `q` between a Boolean face and a
residual tail.  The represented prime support must not depend on which side of
that coordinate system contains `q`.

For every prime `r`, the predicate

`r ∈ face ∨ r ∣ tail`

is therefore invariant under an active `q`-transfer.  This is the key fact that
makes the *least* movable prime canonical on both endpoints of one Othello edge.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Prime support of the face/tail representation is unchanged by an active
fixed-prime transfer. -/
theorem lowWheelFaceTailToggleAt_prime_active_iff
    {q r : ℕ} {x : LowWheelFaceTailState}
    (hq : q.Prime) (hr : r.Prime)
    (hqactive : q ∈ x.1 ∨ q ∣ x.2) :
    (r ∈ (lowWheelFaceTailToggleAt q x).1 ∨
        r ∣ (lowWheelFaceTailToggleAt q x).2) ↔
      (r ∈ x.1 ∨ r ∣ x.2) := by
  rcases x with ⟨t, m⟩
  change
    (r ∈ (lowWheelFaceTailToggleAt q (t, m)).1 ∨
        r ∣ (lowWheelFaceTailToggleAt q (t, m)).2) ↔
      (r ∈ t ∨ r ∣ m)
  unfold lowWheelFaceTailToggleAt
  by_cases hqt : q ∈ t
  · simp only [hqt, if_true]
    constructor
    · intro h
      rcases h with hre | hdiv
      · exact Or.inl (Finset.mem_of_mem_erase hre)
      · rcases hr.dvd_mul.mp hdiv with hrq | hrm
        · have heq : r = q :=
            (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
          subst r
          exact Or.inl hqt
        · exact Or.inr hrm
    · intro h
      rcases h with hrt | hrm
      · by_cases hrq : r = q
        · subst r
          exact Or.inr (dvd_mul_right q m)
        · exact Or.inl (Finset.mem_erase.mpr ⟨hrq, hrt⟩)
      · exact Or.inr (dvd_mul_of_dvd_right hrm q)
  · have hqm : q ∣ m := hqactive.resolve_left hqt
    simp only [hqt, if_false, hqm, if_true]
    constructor
    · intro h
      rcases h with hins | hdiv
      · rcases Finset.mem_insert.mp hins with heq | hrt
        · subst r
          exact Or.inr hqm
        · exact Or.inl hrt
      · have htailDvd : m / q ∣ m := by
          refine ⟨q, ?_⟩
          simpa [Nat.mul_comm] using (Nat.div_mul_cancel hqm).symm
        exact Or.inr (hdiv.trans htailDvd)
    · intro h
      rcases h with hrt | hrm
      · exact Or.inl (Finset.mem_insert_of_mem hrt)
      · by_cases hrq : r = q
        · subst r
          exact Or.inl (Finset.mem_insert_self q t)
        · have hrNotDvdQ : ¬ r ∣ q := by
            intro hrd
            have heq : r = q :=
              (Nat.prime_dvd_prime_iff_eq hr hq).mp hrd
            exact hrq heq
          have hmEq : q * (m / q) = m := Nat.mul_div_cancel' hqm
          have hrProd : r ∣ q * (m / q) := by
            simpa [hmEq] using hrm
          rcases hr.dvd_mul.mp hrProd with hrd | htail
          · exact (hrNotDvdQ hrd).elim
          · exact Or.inr htail

end RHLean.Proof
