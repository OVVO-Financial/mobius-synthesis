import RHLean.Geometry.LeastPrimeEndpoint

open scoped ArithmeticFunction.Moebius

namespace RHLean.Arithmetic

/-- Every prime divisor of `c` lies strictly inside the endpoint band `(p,q)`. -/
def PrimeBandCore (p q c : ℕ) : Prop :=
  ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ c → p < ℓ ∧ ℓ < q

/-- Exact endpoint/core data for a factorization `n = p*c*q`. -/
structure EndpointCoreDecomposition (n : ℕ) where
  lower : ℕ
  core : ℕ
  upper : ℕ
  lower_prime : Nat.Prime lower
  upper_prime : Nat.Prime upper
  endpoint_order : lower < upper
  core_in_band : PrimeBandCore lower upper core
  lower_core_coprime : Nat.Coprime lower core
  lower_core_upper_coprime : Nat.Coprime (lower * core) upper
  product_eq : lower * core * upper = n

namespace EndpointCoreDecomposition

variable {n : ℕ}

/-- The represented integer is reconstructed exactly from its endpoint/core data. -/
theorem reconstruct (d : EndpointCoreDecomposition n) :
    d.lower * d.core * d.upper = n :=
  d.product_eq

/-- The lower endpoint divides the represented integer. -/
theorem lower_dvd (d : EndpointCoreDecomposition n) : d.lower ∣ n := by
  refine ⟨d.core * d.upper, ?_⟩
  calc
    n = d.lower * d.core * d.upper := d.product_eq.symm
    _ = d.lower * (d.core * d.upper) := by simp [Nat.mul_assoc]

/-- The upper endpoint divides the represented integer. -/
theorem upper_dvd (d : EndpointCoreDecomposition n) : d.upper ∣ n := by
  refine ⟨d.lower * d.core, ?_⟩
  calc
    n = d.lower * d.core * d.upper := d.product_eq.symm
    _ = d.upper * (d.lower * d.core) := by ac_rfl

/-- The middle core divides the represented integer. -/
theorem core_dvd (d : EndpointCoreDecomposition n) : d.core ∣ n := by
  refine ⟨d.lower * d.upper, ?_⟩
  calc
    n = d.lower * d.core * d.upper := d.product_eq.symm
    _ = d.core * (d.lower * d.upper) := by ac_rfl

/-- Every prime divisor of the core lies strictly between the two endpoints. -/
theorem prime_dvd_core_between
    (d : EndpointCoreDecomposition n)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hdiv : ℓ ∣ d.core) :
    d.lower < ℓ ∧ ℓ < d.upper :=
  d.core_in_band ℓ hℓ hdiv

/-- Removing the two prime endpoints preserves the Möbius value of the core. -/
theorem moebius_eq_core (d : EndpointCoreDecomposition n) :
    μ n = μ d.core := by
  calc
    μ n = μ (d.lower * d.core * d.upper) := congrArg μ d.product_eq.symm
    _ = μ d.core := RHLean.Geometry.moebius_endpoint_pair_preserves
      d.lower d.core d.upper d.lower_prime d.upper_prime
        d.lower_core_coprime d.lower_core_upper_coprime

/-- Empty middle core gives the semiprime endpoint case. -/
theorem product_eq_of_core_eq_one
    (d : EndpointCoreDecomposition n) (hcore : d.core = 1) :
    d.lower * d.upper = n := by
  simpa [hcore] using d.product_eq

/-- A nontrivial core cannot contain either endpoint as a prime divisor. -/
theorem endpoints_not_dvd_core (d : EndpointCoreDecomposition n) :
    ¬ d.lower ∣ d.core ∧ ¬ d.upper ∣ d.core := by
  constructor
  · intro hdiv
    have h := d.core_in_band d.lower d.lower_prime hdiv
    exact (Nat.lt_irrefl d.lower) h.1
  · intro hdiv
    have h := d.core_in_band d.upper d.upper_prime hdiv
    exact (Nat.lt_irrefl d.upper) h.2

end EndpointCoreDecomposition

end RHLean.Arithmetic
