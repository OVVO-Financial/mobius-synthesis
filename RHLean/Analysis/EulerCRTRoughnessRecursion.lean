import Mathlib

/-!
# Euler–CRT roughness recursion — first exact slice

This module formalizes the smallest exact slice of the Euler–CRT roughness
recursion recorded for this route.  Everything here is an identity; no analytic
estimate is stated or claimed, and nothing here is imported by the protected RH
theorem chain.

Contents (this slice only):

* `roughMoebius W n` — the Möbius coefficient restricted to `n` coprime to the
  squarefree wheel `W` (the coefficient sequence of `T_W`);
* `roughMertens W x` — the rough summatory function `T_W(x)`;
* `multDiff p F x` — the one-prime multiplicative finite difference
  `(𝒟_p F)(x) = F(x) − F(⌊x/p⌋)`;
* `roughMoebius_wheel_recursion` — the coefficientwise identity;
* `roughMertens_wheel_recursion` — `𝒟_p T_W = T_{W/p}` for `p ∣ W`, `W` squarefree;
* `roughInterval W L U` — the rough interval sum `T_W(U) − T_W(L)`;
* `roughInterval_wheel_recursion` — the interval form of the same recursion,
  `T_{W/p}(L,U] = T_W(L,U] − T_W(⌊L/p⌋,⌊U/p⌋]`;
* `roughMertens_prime_extension` — the prime-*extension* direction,
  `T_{pW}(x) = T_W(x) + T_{pW}(⌊x/p⌋)`, which is the scale-indexed state
  transfer discussed in the research notes.

Later slices (iteration over divisors, telescope to `M`, the `ℤ[√−2]`
isometries, the Boolean/Walsh layer) are added only once this slice is green in
CI.  The open analytic premises remain documented in the research
registry, not encoded here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-! ### The rough Möbius coefficient -/

/-- `μ(n)` restricted to arguments coprime to the wheel `W`; the Dirichlet
coefficient sequence of the rough summatory function `T_W`. -/
def roughMoebius (W n : ℕ) : ℤ := if Nat.Coprime n W then μ n else 0

/-- If `p ∤ n` and `p ∣ W`, coprimality to `W` and to `W/p` agree at `n`. -/
private theorem coprime_wheel_div_of_not_dvd
    {W p n : ℕ} (hp : p.Prime) (hpW : p ∣ W) (hpn : ¬ p ∣ n) :
    Nat.Coprime n (W / p) ↔ Nat.Coprime n W := by
  have hWeq : p * (W / p) = W := Nat.mul_div_cancel' hpW
  have hcop_np : Nat.Coprime n p := ((hp.coprime_iff_not_dvd (n := n)).2 hpn).symm
  constructor
  · intro h
    have hmul : Nat.Coprime n (p * (W / p)) := Nat.Coprime.mul_right hcop_np h
    simpa [hWeq] using hmul
  · intro h
    have h' : Nat.Coprime n (p * (W / p)) := by simpa [hWeq] using h
    exact (Nat.coprime_mul_iff_right.1 h').2

/-- `p ∤ (W/p)` when `p` is prime, `p ∣ W`, and `W` is squarefree. -/
private theorem not_dvd_wheel_div
    {W p : ℕ} (hp : p.Prime) (hpW : p ∣ W) (hW : Squarefree W) :
    ¬ p ∣ (W / p) := by
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hWeq : p * (W / p) = W := Nat.mul_div_cancel' hpW
  have hsq : p * p ∣ W := by
    refine ⟨c, ?_⟩
    calc W = p * (W / p) := hWeq.symm
      _ = p * (p * c) := by rw [hc]
      _ = p * p * c := by ring
  have hunit := hW p hsq
  rw [Nat.isUnit_iff] at hunit
  exact hp.one_lt.ne' hunit

/-- **Pointwise Euler–CRT recursion.** For squarefree `W` and a prime `p ∣ W`,
the coefficient of `𝒟_p T_W = T_W − T_W(·/p)` at `n` equals the coefficient of
`T_{W/p}` at `n`. -/
theorem roughMoebius_wheel_recursion
    {W p : ℕ} (hp : p.Prime) (hpW : p ∣ W) (hW : Squarefree W) (n : ℕ) :
    roughMoebius (W / p) n =
      roughMoebius W n - (if p ∣ n then roughMoebius W (n / p) else 0) := by
  by_cases hpn : p ∣ n
  · -- `p ∣ n`: the `roughMoebius W n` term vanishes.
    have hnotcopW : ¬ Nat.Coprime n W := by
      have hdvdg : p ∣ Nat.gcd n W := Nat.dvd_gcd hpn hpW
      intro hcop
      have hp1 : p ∣ 1 := hcop ▸ hdvdg
      exact hp.one_lt.ne' (Nat.dvd_one.1 hp1)
    have hWn : roughMoebius W n = 0 := by simp [roughMoebius, hnotcopW]
    rw [hWn, if_pos hpn, zero_sub]
    obtain ⟨m, rfl⟩ := hpn
    by_cases hpm : p ∣ m
    · -- `p² ∣ n`: both sides vanish.
      have hnsq : ¬ Squarefree (p * m) := by
        obtain ⟨c, rfl⟩ := hpm
        intro hsf
        have hsq : p * p ∣ p * (p * c) := ⟨c, by ring⟩
        have hunit := hsf p hsq
        rw [Nat.isUnit_iff] at hunit
        exact hp.one_lt.ne' hunit
      have hμ : μ (p * m) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
      have hL : roughMoebius (W / p) (p * m) = 0 := by simp [roughMoebius, hμ]
      have hnotcop_m : ¬ Nat.Coprime m W := by
        have hdvdg : p ∣ Nat.gcd m W := Nat.dvd_gcd hpm hpW
        intro hcop
        have hp1 : p ∣ 1 := hcop ▸ hdvdg
        exact hp.one_lt.ne' (Nat.dvd_one.1 hp1)
      have hR : roughMoebius W ((p * m) / p) = 0 := by
        rw [Nat.mul_div_cancel_left m hp.pos]
        simp [roughMoebius, hnotcop_m]
      rw [hL, hR, neg_zero]
    · -- `p ‖ n`, `n = p·m`, `p ∤ m`.
      have hcop_pm : Nat.Coprime p m := (hp.coprime_iff_not_dvd (n := m)).2 hpm
      have hμ : μ (p * m) = - μ m := by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_pm,
          ArithmeticFunction.moebius_apply_prime hp]
        ring
      have hdivpm : (p * m) / p = m := Nat.mul_div_cancel_left m hp.pos
      have hcop_p_Wp : Nat.Coprime p (W / p) :=
        (hp.coprime_iff_not_dvd (n := W / p)).2 (not_dvd_wheel_div hp hpW hW)
      have hcop_iff : Nat.Coprime (p * m) (W / p) ↔ Nat.Coprime m W := by
        rw [Nat.coprime_mul_iff_left]
        constructor
        · rintro ⟨_, hm⟩
          exact (coprime_wheel_div_of_not_dvd hp hpW hpm).1 hm
        · intro hm
          exact ⟨hcop_p_Wp, (coprime_wheel_div_of_not_dvd hp hpW hpm).2 hm⟩
      rw [hdivpm]
      by_cases hcopm : Nat.Coprime m W
      · have hL : roughMoebius (W / p) (p * m) = μ (p * m) := by
          simp [roughMoebius, hcop_iff.2 hcopm]
        have hR : roughMoebius W m = μ m := by simp [roughMoebius, hcopm]
        rw [hL, hR, hμ]
      · have hnc : ¬ Nat.Coprime (p * m) (W / p) := fun h => hcopm (hcop_iff.1 h)
        have hL : roughMoebius (W / p) (p * m) = 0 := by simp [roughMoebius, hnc]
        have hR : roughMoebius W m = 0 := by simp [roughMoebius, hcopm]
        rw [hL, hR, neg_zero]
  · -- `p ∤ n`: coprimality to `W` and to `W/p` agree.
    rw [if_neg hpn, sub_zero]
    unfold roughMoebius
    by_cases hcop : Nat.Coprime n W
    · rw [if_pos hcop, if_pos ((coprime_wheel_div_of_not_dvd hp hpW hpn).2 hcop)]
    · have hnc : ¬ Nat.Coprime n (W / p) :=
        fun h => hcop ((coprime_wheel_div_of_not_dvd hp hpW hpn).1 h)
      rw [if_neg hcop, if_neg hnc]

/-! ### The rough summatory function and the one-prime removal step -/

/-- The rough summatory function `T_W(x) = ∑_{n ≤ x, (n,W)=1} μ(n)` (including the
harmless `n = 0` term). -/
def roughMertens (W x : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (x + 1), roughMoebius W n

/-- The one-prime multiplicative finite difference `(𝒟_p F)(x) = F(x) − F(⌊x/p⌋)`. -/
def multDiff (p : ℕ) (F : ℕ → ℤ) (x : ℕ) : ℤ := F x - F (x / p)

/-- Reindexing multiples of `p`: summing `f(n/p)` over the multiples of `p` in
`range (x+1)` equals summing `f` over `range (⌊x/p⌋ + 1)`.  Proved by induction on
`x` via `Nat.succ_div`. -/
private theorem sum_dvd_div_range (p : ℕ) (f : ℕ → ℤ) :
    ∀ x : ℕ,
      ∑ n ∈ Finset.range (x + 1), (if p ∣ n then f (n / p) else 0) =
        ∑ m ∈ Finset.range (x / p + 1), f m := by
  intro x
  induction x with
  | zero => simp [Nat.zero_div]
  | succ x ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hdvd : p ∣ (x + 1)
      · have hdiv : (x + 1) / p = x / p + 1 := by rw [Nat.succ_div, if_pos hdvd]
        rw [if_pos hdvd, hdiv, ← Finset.sum_range_succ]
      · have hdiv : (x + 1) / p = x / p := by rw [Nat.succ_div, if_neg hdvd, add_zero]
        rw [if_neg hdvd, add_zero, hdiv]

/-- **One-prime Euler–CRT roughness removal.** For squarefree `W` and a prime
`p ∣ W`, the multiplicative finite difference `𝒟_p T_W` equals `T_{W/p}`. -/
theorem roughMertens_wheel_recursion
    {W p : ℕ} (hp : p.Prime) (hpW : p ∣ W) (hW : Squarefree W) (x : ℕ) :
    multDiff p (roughMertens W) x = roughMertens (W / p) x := by
  unfold multDiff
  have hpoint :
      roughMertens (W / p) x =
        ∑ n ∈ Finset.range (x + 1),
          (roughMoebius W n - (if p ∣ n then roughMoebius W (n / p) else 0)) := by
    unfold roughMertens
    exact Finset.sum_congr rfl (fun n _ => roughMoebius_wheel_recursion hp hpW hW n)
  rw [hpoint, Finset.sum_sub_distrib, sum_dvd_div_range p (roughMoebius W) x]
  rfl

/-! ### Interval form of the one-prime removal step -/

/-- The rough interval sum `T_W(L,U] = T_W(U) − T_W(L)`. -/
def roughInterval (W L U : ℕ) : ℤ := roughMertens W U - roughMertens W L

/-- **Interval form of the one-prime Euler–CRT roughness removal.**  Removing the
prime `p` from the wheel subtracts the sum over the dilated interval:
`T_{W/p}(L,U] = T_W(L,U] − T_W(⌊L/p⌋,⌊U/p⌋]`.

This is the exact two-channel `A − B` split used by the interval-packet
recursion: `A` is the sum over the interval itself and `B` the sum over its
`p`-dilate.  It is a direct consequence of `roughMertens_wheel_recursion`; no
analytic estimate is involved. -/
theorem roughInterval_wheel_recursion
    {W p : ℕ} (hp : p.Prime) (hpW : p ∣ W) (hW : Squarefree W) (L U : ℕ) :
    roughInterval (W / p) L U
      = roughInterval W L U - roughInterval W (L / p) (U / p) := by
  have hU := roughMertens_wheel_recursion hp hpW hW U
  have hL := roughMertens_wheel_recursion hp hpW hW L
  unfold multDiff at hU hL
  unfold roughInterval
  rw [← hU, ← hL]
  ring

/-! ### The prime-extension direction -/

/-- **Prime extension of the roughness wheel.**  Adjoining a prime `p` to a
squarefree wheel `W` satisfies `T_{pW}(x) = T_W(x) + T_{pW}(⌊x/p⌋)`.

This is `roughMertens_wheel_recursion` applied to the wheel `pW` and rearranged;
it is the transfer law for the scale-indexed state `y ↦ T_W(y)`, on which the
parent and child assertions are statements about the same object.  Iterating it
gives the geometric form `T_{pW}(x) = ∑_{j ≥ 0} T_W(⌊x/pʲ⌋)`, which is not
formalized here.  Nothing analytic is claimed: the descent through this law
costs a factor `2` per prime removed, and that loss is exactly the unproved
cancellation the research notes record as open. -/
theorem roughMertens_prime_extension
    {W p : ℕ} (hp : p.Prime) (hpW : Squarefree (p * W)) (x : ℕ) :
    roughMertens (p * W) x = roughMertens W x + roughMertens (p * W) (x / p) := by
  have hdvd : p ∣ p * W := ⟨W, rfl⟩
  have hdiv : (p * W) / p = W := Nat.mul_div_cancel_left W hp.pos
  have h := roughMertens_wheel_recursion hp hdvd hpW x
  rw [hdiv] at h
  unfold multDiff at h
  rw [← h]
  ring

end RHLean.Analysis
