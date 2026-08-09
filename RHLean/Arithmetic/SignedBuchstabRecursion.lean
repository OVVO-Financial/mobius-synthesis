import Mathlib

/-!
# The signed Buchstab recursion for the rough Möbius sum

For an integer threshold `b`, call `m` *rough above `b`* when every prime factor
of `m` exceeds `b`.  Define the signed rough Möbius sum
`Z(b, y) = ∑_{1 ≤ m ≤ y, rough above b} μ(m)`.

This module proves the exact one-step Buchstab recursion: for every prime `q`,
```
Z(q-1, y) = Z(q, y) - Z(q, y / q).
```
The threshold `q-1` selects `m` with every prime factor `≥ q`; peeling the single
prime `q` splits that population into the `q`-rough part `Z(q, y)` and the part
divisible by `q`, which reindexes through `m = q·m'` with `μ(q m') = -μ(m')`.

This is the least-prime (rough) recursion linking the frontier's channels.  It is
an exact identity; it is not, by itself, an estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- `m` is rough above `b` when every prime factor of `m` exceeds `b`. -/
def RoughAbove (b m : ℕ) : Prop := ∀ p ∈ m.primeFactors, b < p

instance (b : ℕ) : DecidablePred (RoughAbove b) := fun m =>
  inferInstanceAs (Decidable (∀ p ∈ m.primeFactors, b < p))

/-- Signed rough Möbius sum over `1 ≤ m ≤ y` with every prime factor `> b`. -/
noncomputable def roughMoebiusSum (b y : ℕ) : ℤ :=
  ∑ m ∈ (Finset.Icc 1 y).filter (RoughAbove b), (μ m)

/-- A prime pivot does not divide a number rough above it. -/
theorem RoughAbove.not_dvd {q m : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hr : RoughAbove q m) : ¬ q ∣ m := by
  intro hdvd
  have hmem : q ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hdvd, by omega⟩
  exact (lt_irrefl q) (hr q hmem)

/-- Möbius on a fresh prime multiple. -/
theorem moebius_prime_mul {q m : ℕ} (hq : q.Prime) (hnd : ¬ q ∣ m) :
    μ (q * m) = - μ m := by
  have hcop : Nat.Coprime q m := hq.coprime_iff_not_dvd.mpr hnd
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- Prime factors of a fresh prime multiple. -/
theorem primeFactors_prime_mul {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0) :
    (q * m).primeFactors = insert q m.primeFactors := by
  rw [Nat.primeFactors_mul hq.ne_zero hm, hq.primeFactors, Finset.singleton_union]

/-- **Signed Buchstab recursion.**  For every prime `q`,
`Z(q-1, y) = Z(q, y) - Z(q, y / q)`. -/
theorem roughMoebiusSum_buchstab {q y : ℕ} (hq : q.Prime) :
    roughMoebiusSum (q - 1) y
      = roughMoebiusSum q y - roughMoebiusSum q (y / q) := by
  classical
  have hq2 : 2 ≤ q := hq.two_le
  unfold roughMoebiusSum
  set A := (Finset.Icc 1 y).filter (RoughAbove (q - 1)) with hAdef
  set B := (Finset.Icc 1 y).filter (RoughAbove q) with hBdef
  set C := (Finset.Icc 1 (y / q)).filter (RoughAbove q) with hCdef
  set G := C.image (fun m => q * m) with hGdef
  -- `q`-rough implies `(q-1)`-rough, so `B ⊆ A`.
  have hBA : B ⊆ A := by
    intro m hm
    rw [hBdef, Finset.mem_filter] at hm
    rw [hAdef, Finset.mem_filter]
    exact ⟨hm.1, fun p hp => by have := hm.2 p hp; omega⟩
  -- Sign law on `C`: `μ(q·m) = -μ(m)`.
  have hsign : ∀ m ∈ C, μ (q * m) = - μ m := by
    intro m hm
    rw [hCdef, Finset.mem_filter, Finset.mem_Icc] at hm
    exact moebius_prime_mul hq (RoughAbove.not_dvd hq hm.1.1 hm.2)
  -- Injectivity of `m ↦ q·m` on `C`.
  have hinj : ∀ a ∈ C, ∀ b ∈ C, q * a = q * b → a = b := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  -- `G ⊆ A \ B`.
  have hGsub : G ⊆ A \ B := by
    intro g hg
    rw [hGdef, Finset.mem_image] at hg
    obtain ⟨m, hmC, rfl⟩ := hg
    rw [hCdef, Finset.mem_filter, Finset.mem_Icc] at hmC
    obtain ⟨⟨hm1, hmy⟩, hmrough⟩ := hmC
    have hm0 : m ≠ 0 := by omega
    have hnd : ¬ q ∣ m := RoughAbove.not_dvd hq hm1 hmrough
    have hpf : (q * m).primeFactors = insert q m.primeFactors :=
      primeFactors_prime_mul hq hm0
    have hle : q * m ≤ y :=
      le_trans (Nat.mul_le_mul (le_refl q) hmy)
        (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self y q)
    have hg1 : 1 ≤ q * m := Nat.mul_pos (by omega) (by omega)
    have hgA : q * m ∈ A := by
      rw [hAdef, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hg1, hle⟩, ?_⟩
      intro p hp
      rw [hpf, Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · omega
      · have := hmrough p hp; omega
    have hgB : q * m ∉ B := by
      rw [hBdef, Finset.mem_filter]
      rintro ⟨_, hrough⟩
      have hqmem : q ∈ (q * m).primeFactors := by
        rw [hpf]; exact Finset.mem_insert_self q _
      exact (lt_irrefl q) (hrough q hqmem)
    exact Finset.mem_sdiff.mpr ⟨hgA, hgB⟩
  -- Terms of `A \ B` outside `G` are non-squarefree, hence `μ = 0`.
  have hzero : ∀ m ∈ A \ B, m ∉ G → μ m = 0 := by
    intro m hm hmG
    obtain ⟨hmA, hmnB⟩ := Finset.mem_sdiff.mp hm
    rw [hAdef, Finset.mem_filter] at hmA
    obtain ⟨hmIcc, hArough⟩ := hmA
    obtain ⟨hm1, hmy⟩ := Finset.mem_Icc.mp hmIcc
    -- `¬ q`-rough together with `(q-1)`-rough forces `q ∣ m`.
    have hqmem : q ∈ m.primeFactors := by
      by_contra hqnot
      apply hmnB
      rw [hBdef, Finset.mem_filter]
      refine ⟨hmIcc, ?_⟩
      intro p hp
      have h1 := hArough p hp
      have h2 : p ≠ q := fun h => hqnot (h ▸ hp)
      omega
    have hqdvd : q ∣ m := Nat.dvd_of_mem_primeFactors hqmem
    -- If `q^2 ∤ m` then `m = q·(m/q)` with `m/q ∈ C`, so `m ∈ G` — contradiction.
    have hqsq : q * q ∣ m := by
      by_contra hnsq
      have hmqeq : q * (m / q) = m := Nat.mul_div_cancel' hqdvd
      have hnd' : ¬ q ∣ (m / q) := by
        intro hdvd'
        exact hnsq (by rw [← hmqeq]; exact Nat.mul_dvd_mul_left q hdvd')
      have hmq1 : 1 ≤ m / q :=
        (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hqdvd)
      have hmqy : m / q ≤ y / q := Nat.div_le_div_right hmy
      have hpf : m.primeFactors = insert q (m / q).primeFactors := by
        conv_lhs => rw [← hmqeq]
        exact primeFactors_prime_mul hq (by omega)
      have hmqrough : RoughAbove q (m / q) := by
        intro p hp
        have hpm : p ∈ m.primeFactors := by
          rw [hpf]; exact Finset.mem_insert_of_mem hp
        have h1 := hArough p hpm
        have h2 : p ≠ q := by
          rintro rfl
          exact hnd' (Nat.dvd_of_mem_primeFactors hp)
        omega
      have hmG' : m ∈ G := by
        rw [hGdef, Finset.mem_image]
        refine ⟨m / q, ?_, hmqeq⟩
        rw [hCdef, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hmq1, hmqy⟩, hmqrough⟩
      exact hmG hmG'
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hsf
    exact hq.not_isUnit (hsf q hqsq)
  -- `Σ_{A\B} μ + Σ_C μ = 0`.
  have hAB : (∑ m ∈ A \ B, (μ m)) + (∑ m ∈ C, (μ m)) = 0 := by
    rw [← Finset.sum_subset hGsub hzero, hGdef, Finset.sum_image hinj,
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro m hm
    rw [hsign m hm]
    ring
  -- `Σ_{A\B} μ + Σ_B μ = Σ_A μ`.
  have hsdiff : (∑ m ∈ A \ B, (μ m)) + ∑ m ∈ B, (μ m) = ∑ m ∈ A, (μ m) :=
    Finset.sum_sdiff hBA
  linarith [hsdiff, hAB]

end RHLean.Arithmetic
