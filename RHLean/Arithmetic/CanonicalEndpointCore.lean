import RHLean.Arithmetic.EndpointCoreDecomposition

namespace RHLean.Arithmetic

/-- `p` is the least prime divisor of `n`. -/
def IsLeastPrimeDivisor (n p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ n ∧
    ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ n → p ≤ ℓ

/-- `q` is the greatest prime divisor of `n`. -/
def IsGreatestPrimeDivisor (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧
    ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ n → ℓ ≤ q

/-- Endpoint/core data whose endpoints are extremal among all prime divisors. -/
structure CanonicalEndpointCoreDecomposition (n : ℕ) extends EndpointCoreDecomposition n where
  lower_is_least : IsLeastPrimeDivisor n lower
  upper_is_greatest : IsGreatestPrimeDivisor n upper

namespace CanonicalEndpointCoreDecomposition

variable {n : ℕ}

/-- Any two canonical decompositions have the same lower endpoint. -/
theorem lower_unique
    (d e : CanonicalEndpointCoreDecomposition n) :
    d.lower = e.lower := by
  apply Nat.le_antisymm
  · exact d.lower_is_least.2.2 e.lower e.lower_prime e.toEndpointCoreDecomposition.lower_dvd
  · exact e.lower_is_least.2.2 d.lower d.lower_prime d.toEndpointCoreDecomposition.lower_dvd

/-- Any two canonical decompositions have the same upper endpoint. -/
theorem upper_unique
    (d e : CanonicalEndpointCoreDecomposition n) :
    d.upper = e.upper := by
  apply Nat.le_antisymm
  · exact e.upper_is_greatest.2.2 d.upper d.upper_prime d.toEndpointCoreDecomposition.upper_dvd
  · exact d.upper_is_greatest.2.2 e.upper e.upper_prime e.toEndpointCoreDecomposition.upper_dvd

/-- Once the extremal endpoints agree, the middle core is forced. -/
theorem core_unique
    (d e : CanonicalEndpointCoreDecomposition n) :
    d.core = e.core := by
  have hlower : d.lower = e.lower := lower_unique d e
  have hupper : d.upper = e.upper := upper_unique d e
  have hprod : d.lower * d.core * d.upper = e.lower * e.core * e.upper := by
    calc
      d.lower * d.core * d.upper = n := d.product_eq
      _ = e.lower * e.core * e.upper := e.product_eq.symm
  rw [hlower, hupper] at hprod
  have hmiddle : e.lower * d.core = e.lower * e.core :=
    Nat.mul_right_cancel e.upper_prime.pos hprod
  exact Nat.mul_left_cancel e.lower_prime.pos hmiddle

/-- Canonical endpoint/core components are unique. -/
theorem components_unique
    (d e : CanonicalEndpointCoreDecomposition n) :
    d.lower = e.lower ∧ d.core = e.core ∧ d.upper = e.upper := by
  exact ⟨lower_unique d e, core_unique d e, upper_unique d e⟩

end CanonicalEndpointCoreDecomposition

end RHLean.Arithmetic
