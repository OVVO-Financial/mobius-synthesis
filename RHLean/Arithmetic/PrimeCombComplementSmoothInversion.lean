import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifference
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime

/-!
# Complement-smooth inversion of the finite Möbius difference operator

The fresh-prime recurrence `finiteDifferenceOperator_insert` says that
adjoining a prime `q` multiplies the canonical operator by the Boolean factor
`1 - shift q`.  Adjoining a whole finite prime set `T` therefore multiplies it
by `Π_{q ∈ T} (1 - shift q)`, and on sequences vanishing at `0` that factor
admits a pointwise recovery formula: at each `x` the original value is
recovered by summing `shift n` over the `T`-smooth `n ≤ x`, i.e. over every
`n ≥ 1` all of whose prime factors lie in `T`.  Smoothness constrains the
*support* of the factorization and not its exponents: the index set is not
defined by a squarefreeness restriction, and for a prime `q ∈ T` every power
`q^k ≤ x` is a member.  Restricting the index set to squarefree `n` makes the
identity below false — over `ℤ`, with `f` the indicator of `1`, already at
`S = {3}`, `T = {2}`, `x = 4`.  Each `n` occurs exactly once: this is a
`Finset` sum, not a multiset sum.  The series terminates rather than
converging, since `⌊x / n⌋ = 0` once `n > x` and under `f 0 = 0` the
operator's value at `0` vanishes; the truncation point depends on `x`, so
what is recorded is a recovery formula at each `x` and not a single global
inverse operator.

The module records that recovery:

* `primeSetSmoothIcc T x` — the `T`-smooth numbers in `[1, x]`;
* `eq_sum_freshPrimeDifference_of_apply_zero` — the single-prime case, a
  terminating telescope over the powers of one prime;
* `finiteDifferenceOperator_eq_sum_complementSmooth` — the general statement,
  for disjoint prime sets `S` and `T`:
  `D_S f x = Σ_{n ∈ primeSetSmoothIcc T x} D_{S ∪ T} f ⌊x / n⌋`.

Primality of `S` and `T` together with `Disjoint S T` is what makes `T` a set
of genuinely fresh coordinates: each insertion step consumes a prime not
dividing the primorial built so far, so the Boolean factors multiply.  Each
of the three hypotheses fails concretely over `ℤ` with `f` the indicator of
`1`: at `S = {2,3}`, `T = {3}`, `x = 3` the right-hand side re-expands a
coordinate that `S` already carries; at `S = {6}`, `T = {2}`, `x = 2` the two
`Finset`s are disjoint but `2` already divides the primorial of `S`; at
`S = {3}`, `T = {4}`, `x = 2` a composite member of `T` is not a coordinate
at all.  `f 0 = 0` is likewise essential: with `f ≡ 1`, `S = ∅`, `T = {2}`
the identity already fails at `x = 1`.

Bookkeeping only; no estimate is asserted anywhere in this module.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-! ## The `T`-smooth window -/

/-- The `T`-smooth numbers in `[1, x]`: every `n` with `1 ≤ n ≤ x` all of
whose prime factors lie in `T`.  The condition constrains the support of the
factorization only and imposes no squarefreeness: if `q ∈ T` is prime and
`q^k ≤ x` then `q^k` is a member.  Only the prime elements of `T` have any
effect, since `Nat.primeFactors` returns primes; `T` is not required to be a
prime set here, and the prime-set hypotheses enter in the theorems below.
The lower endpoint excludes `0`, which has no prime factors and would
otherwise pass the filter vacuously. -/
def primeSetSmoothIcc (T : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun n => ∀ q ∈ n.primeFactors, q ∈ T)

@[simp] theorem mem_primeSetSmoothIcc {T : Finset ℕ} {x n : ℕ} :
    n ∈ primeSetSmoothIcc T x ↔
      1 ≤ n ∧ n ≤ x ∧ ∀ q ∈ n.primeFactors, q ∈ T := by
  classical
  simp only [primeSetSmoothIcc, Finset.mem_filter, Finset.mem_Icc]
  tauto

@[simp] theorem primeSetSmoothIcc_zero (T : Finset ℕ) :
    primeSetSmoothIcc T 0 = ∅ := by
  classical
  ext n
  simp [mem_primeSetSmoothIcc]
  omega

/-- With no fresh coordinates the smooth window is the single point `n = 1`. -/
theorem primeSetSmoothIcc_empty_of_pos {x : ℕ} (hx : 1 ≤ x) :
    primeSetSmoothIcc ∅ x = {1} := by
  classical
  ext n
  simp only [mem_primeSetSmoothIcc, Finset.mem_singleton, Finset.notMem_empty]
  constructor
  · rintro ⟨hn1, _, hfac⟩
    have hempty : n.primeFactors = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      exact fun q hq => (hfac q hq).elim
    rcases Nat.primeFactors_eq_empty.mp hempty with h | h
    · omega
    · exact h
  · rintro rfl
    exact ⟨le_rfl, hx, by simp⟩

/-- A member of the singleton smooth window at `q` is a power of `q`.  No
primality hypothesis is needed: when `q` is not prime the only member is
`1 = q ^ 0`. -/
theorem exists_pow_of_mem_primeSetSmoothIcc_singleton
    {q x e : ℕ} (he : e ∈ primeSetSmoothIcc {q} x) :
    ∃ k : ℕ, e = q ^ k := by
  rw [mem_primeSetSmoothIcc] at he
  obtain ⟨he1, _, hfac⟩ := he
  refine ⟨e.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd
    (by omega) ?_⟩
  intro d hd hdvd
  have : d ∈ e.primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdvd, by omega⟩
  simpa using hfac d this

/-! ## Single-prime inversion -/

/-- **Terminating Neumann series for one prime.**  For a sequence vanishing at
`0`, the Boolean difference `f - shift q f` is inverted by summing over the
powers of `q` in `[1, x]`; the telescope closes because `⌊x / q^k⌋ = 0` once
`q^k > x`. -/
theorem eq_sum_freshPrimeDifference_of_apply_zero
    {R : Type*} [CommRing R]
    (q : ℕ) (hq : Nat.Prime q) (g : ℕ → R) (hg : g 0 = 0) (x : ℕ) :
    g x = ∑ e ∈ primeSetSmoothIcc {q} x, freshPrimeDifference q g (x / e) := by
  classical
  induction x using Nat.strong_induction_on with
  | h x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [hg]
    -- split the window into `e = 1` and the `q`-multiples of the window at `⌊x/q⌋`
    have hsplit : primeSetSmoothIcc {q} x =
        insert 1 ((primeSetSmoothIcc {q} (x / q)).image (fun e => q * e)) := by
      ext e
      simp only [Finset.mem_insert, Finset.mem_image, mem_primeSetSmoothIcc]
      constructor
      · rintro ⟨he1, hex, hfac⟩
        rcases eq_or_lt_of_le he1 with rfl | he2
        · exact Or.inl rfl
        · have hne : e ≠ 0 := by omega
          have hqe : q ∣ e := by
            obtain ⟨r, hr⟩ := Nat.exists_prime_and_dvd (by omega : e ≠ 1)
            have : r ∈ e.primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hr.1, hr.2, hne⟩
            have hrq : r = q := by simpa using hfac r this
            exact hrq ▸ hr.2
          obtain ⟨e', rfl⟩ := hqe
          refine Or.inr ⟨e', ⟨?_, ?_, ?_⟩, rfl⟩
          · rcases Nat.eq_zero_or_pos e' with rfl | h
            · simp at hne
            · exact h
          · exact (Nat.le_div_iff_mul_le hq.pos).mpr
              (by rw [Nat.mul_comm] at hex; exact hex)
          · intro r hr
            exact hfac r (Nat.primeFactors_mono (dvd_mul_left e' q) hne hr)
      · rintro (rfl | ⟨e', he', rfl⟩)
        · exact ⟨le_rfl, hx, by simp⟩
        · obtain ⟨he'1, he'x, he'fac⟩ := he'
          refine ⟨Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero hq.ne_zero (by omega)), ?_, ?_⟩
          · rw [Nat.mul_comm]
            exact (Nat.le_div_iff_mul_le hq.pos).mp he'x
          · intro r hr
            rw [Nat.primeFactors_mul hq.ne_zero (by omega)] at hr
            rcases Finset.mem_union.mp hr with hr | hr
            · simpa using (by simpa [hq.primeFactors] using hr : r = q)
            · exact he'fac r hr
    have hnotmem : (1 : ℕ) ∉
        (primeSetSmoothIcc {q} (x / q)).image (fun e => q * e) := by
      intro hmem
      obtain ⟨e', he', he1⟩ := Finset.mem_image.mp hmem
      have : 1 ≤ e' := (mem_primeSetSmoothIcc.mp he').1
      have := hq.two_le
      nlinarith [he1]
    have hinj : ∀ a ∈ primeSetSmoothIcc {q} (x / q),
        ∀ b ∈ primeSetSmoothIcc {q} (x / q), q * a = q * b → a = b :=
      fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hq.pos hab
    rw [hsplit, Finset.sum_insert hnotmem, Finset.sum_image hinj]
    have hdiv : ∀ e ∈ primeSetSmoothIcc {q} (x / q),
        freshPrimeDifference q g (x / (q * e)) =
          freshPrimeDifference q g (x / q / e) := by
      intro e _
      rw [Nat.div_div_eq_div_mul]
    rw [Finset.sum_congr rfl hdiv, ← ih (x / q) (Nat.div_lt_self hx hq.one_lt)]
    simp [freshPrimeDifference, shift]

/-! ## Complement-smooth inversion -/

/-- **Complement-smooth inversion.**  For disjoint prime sets `S` and `T` and
any sequence vanishing at `0`, the operator at `S` — the relative complement
of `T` inside `S ∪ T`, whence the name — is recovered from the operator at
`S ∪ T` by a `T`-smooth sum:
`D_S f x = Σ_{n ≤ x, n T-smooth} D_{S ∪ T} f ⌊x / n⌋`, the sum running once
over every `T`-smooth `n ≤ x`, non-squarefree values allowed.  Bookkeeping
only: this is an exact re-expression, not an estimate. -/
theorem finiteDifferenceOperator_eq_sum_complementSmooth
    {R : Type*} [CommRing R]
    (S T : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ q ∈ T, Nat.Prime q)
    (hdisj : Disjoint S T)
    (f : ℕ → R) (hf : f 0 = 0) (x : ℕ) :
    finiteDifferenceOperator S f x =
      ∑ n ∈ primeSetSmoothIcc T x,
        finiteDifferenceOperator (S ∪ T) f (x / n) := by
  classical
  -- the operator inherits the vanishing at `0`
  have hzero : ∀ (U : Finset ℕ), finiteDifferenceOperator U f 0 = 0 := by
    intro U
    simp [finiteDifferenceOperator_apply, hf]
  revert hT hdisj
  induction T using Finset.induction_on with
  | empty =>
      intro _ _
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · simp [hzero]
      · rw [primeSetSmoothIcc_empty_of_pos hx]
        simp
  | @insert q T hqT ih =>
      intro hT hdisj
      have hq : Nat.Prime q := hT q (Finset.mem_insert_self q T)
      have hT' : ∀ r ∈ T, Nat.Prime r := fun r hr =>
        hT r (Finset.mem_insert_of_mem hr)
      have hqS : q ∉ S := (Finset.disjoint_insert_right.mp hdisj).1
      have hdisj' : Disjoint S T := (Finset.disjoint_insert_right.mp hdisj).2
      have hU : ∀ r ∈ S ∪ T, Nat.Prime r := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · exact hS r hr
        · exact hT' r hr
      have hqU : q ∉ S ∪ T := by
        simp only [Finset.mem_union, not_or]
        exact ⟨hqS, hqT⟩
      -- the fresh prime `q` acts on the operator at `S ∪ T` as a Boolean factor
      have hfresh :
          freshPrimeDifference q (finiteDifferenceOperator (S ∪ T) f) =
            finiteDifferenceOperator (insert q (S ∪ T)) f := by
        rw [finiteDifferenceOperator_insert (S ∪ T) q hq hqU hU f]
        funext y
        simp only [freshPrimeDifference, Pi.sub_apply, shift,
          finiteDifferenceOperator_apply]
        refine congrArg _ (Finset.sum_congr rfl fun d _ => ?_)
        rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
      have hunion : S ∪ insert q T = insert q (S ∪ T) := Finset.union_insert q S T
      -- step 1: invert the primes of `T`
      rw [ih hT' hdisj']
      -- step 2: invert the fresh prime `q` inside each `T`-smooth fiber
      have hstep : ∀ n ∈ primeSetSmoothIcc T x,
          finiteDifferenceOperator (S ∪ T) f (x / n) =
            ∑ e ∈ primeSetSmoothIcc {q} (x / n),
              finiteDifferenceOperator (S ∪ insert q T) f (x / n / e) := by
        intro n _
        rw [hunion]
        rw [← hfresh]
        exact eq_sum_freshPrimeDifference_of_apply_zero q hq
          (finiteDifferenceOperator (S ∪ T) f) (hzero (S ∪ T)) (x / n)
      rw [Finset.sum_congr rfl hstep]
      -- step 3: the factorization `m = n * q^k` reindexes the double sum
      rw [Finset.sum_sigma']
      refine Finset.sum_nbij' (fun ne => ne.1 * ne.2)
        (fun m => ⟨ordCompl[q] m, ordProj[q] m⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨n, e⟩ hne
        rw [Finset.mem_sigma] at hne
        obtain ⟨hn, he⟩ := hne
        have hn' : n ∈ primeSetSmoothIcc T x := hn
        have he' : e ∈ primeSetSmoothIcc {q} (x / n) := he
        obtain ⟨hn1, hnx, hnfac⟩ := mem_primeSetSmoothIcc.mp hn'
        obtain ⟨he1, hex, hefac⟩ := mem_primeSetSmoothIcc.mp he'
        show n * e ∈ primeSetSmoothIcc (insert q T) x
        refine mem_primeSetSmoothIcc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
            ?_, ?_⟩
        · rw [Nat.mul_comm]
          exact (Nat.le_div_iff_mul_le (by omega : 0 < n)).mp hex
        · intro r hr
          rw [Nat.primeFactors_mul (by omega) (by omega)] at hr
          rcases Finset.mem_union.mp hr with hr | hr
          · exact Finset.mem_insert_of_mem (hnfac r hr)
          · have : r = q := by simpa using hefac r hr
            exact this ▸ Finset.mem_insert_self q T
      · intro m hm
        obtain ⟨hm1, hmx, hmfac⟩ := mem_primeSetSmoothIcc.mp hm
        have hm0 : m ≠ 0 := by omega
        have hcompl : ordCompl[q] m * ordProj[q] m = m := by
          rw [Nat.mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self m q
        have hpos : 0 < ordCompl[q] m := Nat.ordCompl_pos q hm0
        rw [Finset.mem_sigma]
        constructor
        · refine mem_primeSetSmoothIcc.mpr ⟨hpos, le_trans (Nat.ordCompl_le m q) hmx, ?_⟩
          intro r hr
          have hrm : r ∈ m.primeFactors :=
            Nat.primeFactors_mono (Nat.ordCompl_dvd m q) hm0 hr
          rcases Finset.mem_insert.mp (hmfac r hrm) with rfl | hrT
          · exact absurd (Nat.mem_primeFactors.mp hr).2.1
              (Nat.not_dvd_ordCompl hq hm0)
          · exact hrT
        · refine mem_primeSetSmoothIcc.mpr ⟨Nat.ordProj_pos m q, ?_, ?_⟩
          · rw [Nat.le_div_iff_mul_le hpos, Nat.ordProj_mul_ordCompl_eq_self]
            exact hmx
          · intro r hr
            have hrp : r.Prime := (Nat.mem_primeFactors.mp hr).1
            have hrd : r ∣ q ^ m.factorization q := (Nat.mem_primeFactors.mp hr).2.1
            have : r = q := (Nat.prime_dvd_prime_iff_eq hrp hq).mp
              (hrp.dvd_of_dvd_pow hrd)
            simp [this]
      · rintro ⟨n, e⟩ hne
        rw [Finset.mem_sigma] at hne
        obtain ⟨hn, he⟩ := hne
        have hn' : n ∈ primeSetSmoothIcc T x := hn
        have he' : e ∈ primeSetSmoothIcc {q} (x / n) := he
        obtain ⟨hn1, hnx, hnfac⟩ := mem_primeSetSmoothIcc.mp hn'
        obtain ⟨k, rfl⟩ := exists_pow_of_mem_primeSetSmoothIcc_singleton he'
        have hn0 : n ≠ 0 := by omega
        have hqk : 0 < q ^ k := pow_pos hq.pos k
        have hqn : ¬ q ∣ n := fun hdvd =>
          hqT (hnfac q (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hn0⟩))
        have hfacq : (n * q ^ k).factorization q = k := by
          rw [Nat.factorization_mul hn0 hqk.ne']
          simp [Nat.factorization_eq_zero_of_not_dvd hqn, hq.factorization_pow]
        have hproj : ordProj[q] (n * q ^ k) = q ^ k := by rw [hfacq]
        have hcompl : n * q ^ k / q ^ k = n := by
          rw [Nat.mul_div_assoc n dvd_rfl, Nat.div_self hqk, Nat.mul_one]
        simp [hproj, hcompl]
      · intro m hm
        obtain ⟨hm1, hmx, hmfac⟩ := mem_primeSetSmoothIcc.mp hm
        have hm0 : m ≠ 0 := by omega
        show ordCompl[q] m * ordProj[q] m = m
        rw [Nat.mul_comm]
        exact Nat.ordProj_mul_ordCompl_eq_self m q
      · rintro ⟨n, e⟩ hne
        rw [Finset.mem_sigma] at hne
        show finiteDifferenceOperator (S ∪ insert q T) f (x / n / e) =
          finiteDifferenceOperator (S ∪ insert q T) f (x / (n * e))
        rw [Nat.div_div_eq_div_mul]

end RHLean.Arithmetic
