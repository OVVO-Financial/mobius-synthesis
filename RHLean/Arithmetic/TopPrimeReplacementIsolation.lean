import Mathlib
import RHLean.Arithmetic.PrimeProductCubeFrontier

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# Top-prime replacement isolation

Let `X = R^2 - 1`.  A prime `q > X / 2` contributes a singleton prime-product
face `{q}` whenever `q <= X`.  Such a face has no admissible upward one-prime
toggle: adjoining any prime `p` forces `q * p > X`.

The singleton is not literally isolated in the undirected face graph, because
removing `q` reaches the empty face.  However that is its only admissible
one-prime-toggle neighbour.  Consequently two distinct top-prime singleton
faces cannot both be paired by an injective one-prime-toggle map, and in
particular cannot both be paired by a one-prime-toggle involution.

This is the finite combinatorial obstruction needed before any recursive
nonlocal prime-replacement construction.  No magnitude estimate is used.
-/

/-- A cutoff lying strictly below twice `q` is the exact arithmetic content of
`X / 2 < q`.  Keeping this generic prevents the square endpoint expression from
obscuring the Presburger division step. -/
private theorem lt_two_mul_of_half_lt
    {X q : ℕ} (h : X / 2 < q) :
    X < 2 * q := by
  omega

/-- Any prime multiplied by a top coordinate crosses the square endpoint.  The
geometric obstruction only needs the top-threshold hypothesis on `q`; primality
of `q` is part of the transport application rather than this inequality. -/
theorem topPrimeAtom_mul_prime_gt_endpoint
    {R q : ℕ}
    (hq_top : (R ^ 2 - 1) / 2 < q) :
    ∀ p : ℕ, Nat.Prime p → q * p > R ^ 2 - 1 := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hXlt2q : R ^ 2 - 1 < 2 * q :=
    lt_two_mul_of_half_lt hq_top
  have hmul : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp2
  calc
    R ^ 2 - 1 < 2 * q := hXlt2q
    _ ≤ p * q := hmul
    _ = q * p := Nat.mul_comm p q

/-- A top-prime singleton that lies below the endpoint is an admissible face of
the ordinary prime-product complex whenever the ambient prime set contains it. -/
theorem topPrimeSingleton_primeProductAdmissible
    {S : Finset ℕ} {R q : ℕ}
    (hqS : q ∈ S)
    (hqX : q ≤ R ^ 2 - 1) :
    primeProductAdmissible S (R ^ 2 - 1) {q} := by
  simp [primeProductAdmissible, primeFaceProduct, hqS, hqX]

/-- No legal insertion of a different prime can extend a top-prime singleton
while remaining in the prime-product complex. -/
theorem topPrimeSingleton_insert_prime_not_admissible
    {S : Finset ℕ} {R q p : ℕ}
    (hq_top : (R ^ 2 - 1) / 2 < q)
    (hp : Nat.Prime p)
    (hpq : p ≠ q) :
    ¬ primeProductAdmissible S (R ^ 2 - 1) (insert p {q}) := by
  intro hadm
  have hgt := topPrimeAtom_mul_prime_gt_endpoint hq_top p hp
  have hprod : primeFaceProduct (insert p {q}) = q * p := by
    simp [primeFaceProduct, hpq, Nat.mul_comm]
  have hle : primeFaceProduct (insert p {q}) ≤ R ^ 2 - 1 := hadm.2
  rw [hprod] at hle
  exact (Nat.not_lt_of_ge hle) hgt

/-- Two prime-product faces differ by one local prime toggle when one is obtained
from the other by inserting a prime that was not already present.  The second
branch records the same relation in the removal direction. -/
def PrimeProductSinglePrimeToggle (u v : Finset ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧
    ((p ∉ u ∧ v = insert p u) ∨
      (p ∉ v ∧ u = insert p v))

/-- The only admissible one-prime-toggle neighbour of a top-prime singleton is
the empty face.  Upward toggles cross the endpoint; a downward toggle from a
singleton necessarily removes its sole coordinate. -/
theorem topPrimeSingleton_admissible_toggle_neighbor_eq_empty
    {S : Finset ℕ} {R q : ℕ} {v : Finset ℕ}
    (hq_top : (R ^ 2 - 1) / 2 < q)
    (hv : primeProductAdmissible S (R ^ 2 - 1) v)
    (htoggle : PrimeProductSinglePrimeToggle {q} v) :
    v = ∅ := by
  rcases htoggle with ⟨p, hp, hup | hdown⟩
  · rcases hup with ⟨hpnot, hv_eq⟩
    subst v
    have hpq : p ≠ q := by
      simpa using hpnot
    exfalso
    exact (topPrimeSingleton_insert_prime_not_admissible
      (S := S) hq_top hp hpq) hv
  · rcases hdown with ⟨hpnot, heq⟩
    have hcard : ({q} : Finset ℕ).card = (insert p v).card :=
      congrArg Finset.card heq
    have hcard' : 1 = v.card + 1 := by
      simpa [hpnot] using hcard
    have hzero : 0 = v.card := by
      apply Nat.succ.inj
      simpa [Nat.succ_eq_add_one] using hcard'
    exact Finset.card_eq_zero.mp hzero.symm

/-- Two distinct top-prime singleton faces cannot both be sent to admissible
one-prime-toggle neighbours by an injective map.  Both images would have to be
the unique common lower neighbour, the empty face. -/
theorem no_injective_singlePrimeToggle_pairing_of_two_topPrimes
    {S : Finset ℕ} {R q₁ q₂ : ℕ}
    (hq₁_top : (R ^ 2 - 1) / 2 < q₁)
    (hq₂_top : (R ^ 2 - 1) / 2 < q₂)
    (hne : q₁ ≠ q₂)
    (f : Finset ℕ → Finset ℕ)
    (hf₁adm : primeProductAdmissible S (R ^ 2 - 1) (f {q₁}))
    (hf₂adm : primeProductAdmissible S (R ^ 2 - 1) (f {q₂}))
    (hf₁toggle : PrimeProductSinglePrimeToggle {q₁} (f {q₁}))
    (hf₂toggle : PrimeProductSinglePrimeToggle {q₂} (f {q₂})) :
    ¬ Function.Injective f := by
  intro hinj
  have hf₁empty : f {q₁} = ∅ :=
    topPrimeSingleton_admissible_toggle_neighbor_eq_empty
      hq₁_top hf₁adm hf₁toggle
  have hf₂empty : f {q₂} = ∅ :=
    topPrimeSingleton_admissible_toggle_neighbor_eq_empty
      hq₂_top hf₂adm hf₂toggle
  have himage : f {q₁} = f {q₂} := by
    rw [hf₁empty, hf₂empty]
  have hsingle : ({q₁} : Finset ℕ) = {q₂} := hinj himage
  have hqeq : q₁ = q₂ := by
    simpa using hsingle
  exact hne hqeq

/-- In particular, no involution can pair two distinct top-prime singleton faces
through admissible one-prime toggles.  This is the precise finite obstruction
forcing any wholesale treatment of the top-prime block to be nonlocal. -/
theorem no_singlePrimeToggle_involution_pairs_two_topPrimes
    {S : Finset ℕ} {R q₁ q₂ : ℕ}
    (hq₁_top : (R ^ 2 - 1) / 2 < q₁)
    (hq₂_top : (R ^ 2 - 1) / 2 < q₂)
    (hne : q₁ ≠ q₂)
    (f : Finset ℕ → Finset ℕ)
    (hinv : ∀ u : Finset ℕ, f (f u) = u)
    (hf₁adm : primeProductAdmissible S (R ^ 2 - 1) (f {q₁}))
    (hf₂adm : primeProductAdmissible S (R ^ 2 - 1) (f {q₂}))
    (hf₁toggle : PrimeProductSinglePrimeToggle {q₁} (f {q₁}))
    (hf₂toggle : PrimeProductSinglePrimeToggle {q₂} (f {q₂})) :
    False := by
  have hinj : Function.Injective f := by
    intro u v huv
    calc
      u = f (f u) := (hinv u).symm
      _ = f (f v) := congrArg f huv
      _ = v := hinv v
  exact
    (no_injective_singlePrimeToggle_pairing_of_two_topPrimes
      hq₁_top hq₂_top hne f hf₁adm hf₂adm hf₁toggle hf₂toggle) hinj

end RHLean.Arithmetic
