import Mathlib
import RHLean.Analysis.SquareRootCombinedSignedResidual
import RHLean.Analysis.SquareRootPositiveSmoothCollapse

/-!
# Born-smooth mass in the lower-scale Möbius/reciprocal form

The transport term already has an exact lower-scale form: for `X = R^2 - 1`,

`T_R = sum_{R < q <= X, q prime} M(floor(X/q))`,

a Möbius prefix mass read at the reciprocal cutoff of each upper prime.  This
module puts the born-smooth mass `A_R^born` into the *same* form, so that the
matched difference `A_R^born - T_R` becomes one signed sum over a single prime
range, with no norm taken anywhere.

Every born-smooth source below `R^2` factors canonically as `m = c*q` with
`q = P+(m)` prime and `q <= c`; along that factorization `mu(c*q) = -mu(c)`, and
the cofactor is exactly `q`-rough below `q`.  Two facts make the form clean:

* the smoothness cutoff is automatic.  `q <= c` and `c*q <= R^2 - 1` already
  force `q < R`, so the born orientation never sees the cutoff `P+(m) <= R`;
* the fibre of `q` is the rough Möbius prefix over the window `[q, floor(X/q)]`,
  which is a difference of two lower-scale prefixes at `floor(X/q)` and `q-1`.

Writing `Rough(q,B) = sum_{c <= B, P+(c) < q} mu(c)` and `M` for the Mertens
summatory function, the results are

```text
A_R^born = 1 - sum_{q <= R, q prime} (Rough(q, floor(X/q)) - M(q-1)),
T_R      =     sum_{R < q <= X, q prime} Rough(q, floor(X/q)),
```

the second because `floor(X/q) < q` above `R`, where the roughness restriction is
vacuous and `Rough` collapses to `M`.  Subtracting gives the unified form

```text
A_R^born - T_R
  = 1 - sum_{q <= X, q prime} Rough(q, floor(X/q))
      + sum_{q <= R, q prime} M(q-1),
```

one signed sum of lower-scale Möbius data at reciprocal cutoffs over the whole
prime range, plus the prime-indexed Mertens prefix transform that the
positive-orientation collapse already isolates.

Combined with the centering of the companion module, the main-term match asked
of `A_R^born - T_R^sm` is the same unified object plus the combined signed
residual `D_R`, so its cancellation can be studied without norms.

No analytic estimate is proved or assumed.  The RH-scale statement on the
unified form is a named proposition, proved *equivalent* to the existing
square-prefix criterion and nothing more.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-! ## Rough lower-scale Möbius prefixes -/

/-- Möbius prefix mass restricted to cofactors that are rough below `q`:
`Rough(q,B) = sum_{1 <= c <= B, P+(c) < q} mu(c)`. -/
def roughCofactorMobiusPrefixMass (q B : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 B,
    if canonicalLargestPrimeFactor c < q then canonicalMoebiusWeight c else 0

/-- The same restricted Möbius mass over a window `[A,B]`. -/
def roughCofactorMobiusWindowMass (q A B : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc A B,
    if canonicalLargestPrimeFactor c < q then canonicalMoebiusWeight c else 0

private theorem primeFactor_le_canonicalLargestPrimeFactor'
    {n p : ℕ} (hn : 1 < n) (hp : p ∈ n.primeFactors) :
    p ≤ canonicalLargestPrimeFactor n := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hn]
  exact Finset.le_max' n.primeFactors p hp

private theorem canonicalLargestPrimeFactor_le_self
    {c : ℕ} (hc : 1 ≤ c) : canonicalLargestPrimeFactor c ≤ c := by
  rcases Nat.lt_or_ge 1 c with hc1 | hc1
  · exact Nat.le_of_dvd (by omega) (canonicalLargestPrimeFactor_dvd hc1)
  · have hc0 : c = 1 := by omega
    subst hc0
    have hnot : ¬ (1 : ℕ) < 1 := by omega
    unfold canonicalLargestPrimeFactor
    rw [dif_neg hnot]

/-- Below `q` the roughness restriction is vacuous, so the rough prefix is the
plain lower-scale Möbius prefix. -/
theorem roughCofactorMobiusPrefixMass_eq_cofactorMobiusPrefixMass
    {q B : ℕ} (hB : B < q) :
    roughCofactorMobiusPrefixMass q B = cofactorMobiusPrefixMass B := by
  unfold roughCofactorMobiusPrefixMass cofactorMobiusPrefixMass
  refine Finset.sum_congr rfl ?_
  intro c hc
  rcases Finset.mem_Icc.mp hc with ⟨hc1, hcB⟩
  have hrough : canonicalLargestPrimeFactor c < q :=
    lt_of_le_of_lt ((canonicalLargestPrimeFactor_le_self hc1).trans hcB) hB
  rw [if_pos hrough]

/-- The rough window above the turning point `q` is the difference of the rough
prefix at `B` and the plain Möbius prefix at `q-1`. -/
theorem roughCofactorMobiusWindowMass_eq_prefix_sub_prefix
    {q B : ℕ} (hq : 1 ≤ q) (hqB : q ≤ B + 1) :
    roughCofactorMobiusWindowMass q q B =
      roughCofactorMobiusPrefixMass q B - cofactorMobiusPrefixMass (q - 1) := by
  have hsplit :
      Finset.Icc 1 B = Finset.Icc 1 (q - 1) ∪ Finset.Icc q B := by
    ext c
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (q - 1)) (Finset.Icc q B) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rcases Finset.mem_Icc.mp hc1 with ⟨_, hcq⟩
    rcases Finset.mem_Icc.mp hc2 with ⟨hqc, _⟩
    omega
  have hlow :
      (∑ c ∈ Finset.Icc 1 (q - 1),
        if canonicalLargestPrimeFactor c < q then
          canonicalMoebiusWeight c else 0) =
        cofactorMobiusPrefixMass (q - 1) := by
    have hstep :=
      roughCofactorMobiusPrefixMass_eq_cofactorMobiusPrefixMass
        (q := q) (B := q - 1) (by omega)
    unfold roughCofactorMobiusPrefixMass at hstep
    exact hstep
  unfold roughCofactorMobiusWindowMass roughCofactorMobiusPrefixMass
  rw [hsplit, Finset.sum_union hdisj, hlow]
  ring

/-! ## Canonical coordinates of a rough product -/

/-- A prime above every prime factor of a positive cofactor is the canonical
largest prime factor of the product.  This generalizes the transport-side lemma,
where the cofactor was smaller than the prime outright. -/
theorem canonicalLargestPrimeFactor_mul_prime_eq_of_rough
    {c q : ℕ} (hc : 0 < c) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < q) :
    canonicalLargestPrimeFactor (c * q) = q := by
  have hm1 : 1 < c * q := by
    calc
      1 < q := hq.one_lt
      _ = 1 * q := (one_mul q).symm
      _ ≤ c * q := Nat.mul_le_mul_right q hc
  have hqmem : q ∈ (c * q).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hq, ⟨c, by ring⟩, Nat.mul_ne_zero (Nat.ne_of_gt hc) hq.ne_zero⟩
  have hall : ∀ p ∈ (c * q).primeFactors, p ≤ q := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := Nat.dvd_of_mem_primeFactors hp
    rcases hpPrime.dvd_mul.mp hpDvd with hpc | hpq
    · have hple : p ≤ c := Nat.le_of_dvd hc hpc
      have hc1 : 1 < c := lt_of_lt_of_le hpPrime.one_lt hple
      have hpmem : p ∈ c.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpPrime, hpc, by omega⟩
      have hple' := primeFactor_le_canonicalLargestPrimeFactor' hc1 hpmem
      omega
    · exact ((Nat.prime_dvd_prime_iff_eq hpPrime hq).mp hpq).le
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hm1]
  exact ((c * q).primeFactors.max'_eq_iff
    (Nat.nonempty_primeFactors.mpr hm1) q).2 ⟨hqmem, hall⟩

/-- The canonical cofactor of a rough product is the original lower factor. -/
theorem canonicalCofactor_mul_prime_eq_of_rough
    {c q : ℕ} (hc : 0 < c) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < q) :
    canonicalCofactor (c * q) = c := by
  unfold canonicalCofactor
  rw [canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hq hrough]
  simpa [Nat.mul_comm] using Nat.mul_div_right c hq.pos

/-- A prime above every prime factor of a positive cofactor flips the source
Möbius weight. -/
theorem canonicalMoebiusWeight_mul_prime_eq_neg_of_rough
    {c q : ℕ} (hc : 0 < c) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < q) :
    canonicalMoebiusWeight (c * q) = -canonicalMoebiusWeight c := by
  have hnotdvd : ¬ q ∣ c := by
    intro hdvd
    have hc1 : 1 < c := lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd hc hdvd)
    have hmem : q ∈ c.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hdvd, by omega⟩
    have hle := primeFactor_le_canonicalLargestPrimeFactor' hc1 hmem
    omega
  have hcop : Nat.Coprime c q := ((hq.coprime_iff_not_dvd).mpr hnotdvd).symm
  have hmu :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  unfold canonicalMoebiusWeight
  rw [hmu, ArithmeticFunction.moebius_apply_prime hq]
  push_cast
  ring

/-! ## The born orientation carries its own smoothness cutoff -/

/-- **The smoothness cutoff is automatic on the born side.**  `q <= c` together
with `c*q <= R^2 - 1` already forces `q < R`, so the born orientation never needs
the separate cutoff `P+(m) <= R`. -/
theorem canonicalLargestPrimeFactor_lt_of_bornOrientation
    {R m : ℕ} (hm : 1 < m) (hX : m ≤ squareRootEndpoint R)
    (hborn : canonicalLargestPrimeFactor m ≤ canonicalCofactor m) :
    canonicalLargestPrimeFactor m < R := by
  have hprod : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm
  have hsq :
      canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m ≤ m := by
    calc
      canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m
          ≤ canonicalCofactor m * canonicalLargestPrimeFactor m :=
        Nat.mul_le_mul_right _ hborn
      _ = m := hprod
  by_contra hnot
  have hRq : R ≤ canonicalLargestPrimeFactor m := by omega
  have hRR :
      R * R ≤ canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m :=
    Nat.mul_le_mul hRq hRq
  have hpow : R ^ 2 = R * R := by ring
  unfold squareRootEndpoint at hX
  omega

/-- On the born orientation, a cofactor that is not rough below the canonical
prime forces a repeated prime factor, so the source carries no Möbius mass. -/
private theorem canonicalMoebiusWeight_eq_zero_of_cofactor_not_rough
    {m : ℕ} (hm : 1 < m)
    (hnot : ¬ canonicalLargestPrimeFactor (canonicalCofactor m) <
              canonicalLargestPrimeFactor m)
    (hborn : canonicalLargestPrimeFactor m ≤ canonicalCofactor m) :
    canonicalMoebiusWeight m = 0 := by
  have hqPrime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hm
  have hprod : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm
  have hc1 : 1 < canonicalCofactor m := lt_of_lt_of_le hqPrime.one_lt hborn
  have hcdvd :
      canonicalLargestPrimeFactor (canonicalCofactor m) ∣ canonicalCofactor m :=
    canonicalLargestPrimeFactor_dvd hc1
  have hcprime :
      (canonicalLargestPrimeFactor (canonicalCofactor m)).Prime :=
    canonicalLargestPrimeFactor_prime hc1
  have hcofdvd : canonicalCofactor m ∣ m :=
    ⟨canonicalLargestPrimeFactor m, hprod.symm⟩
  have hmem :
      canonicalLargestPrimeFactor (canonicalCofactor m) ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hcprime, hcdvd.trans hcofdvd, by omega⟩
  have hle := primeFactor_le_canonicalLargestPrimeFactor' hm hmem
  have heq :
      canonicalLargestPrimeFactor (canonicalCofactor m) =
        canonicalLargestPrimeFactor m := by omega
  have hqdvdc : canonicalLargestPrimeFactor m ∣ canonicalCofactor m := heq ▸ hcdvd
  have hsqdvd :
      canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m ∣ m := by
    obtain ⟨k, hk⟩ := hqdvdc
    refine ⟨k, ?_⟩
    calc
      m = canonicalCofactor m * canonicalLargestPrimeFactor m := hprod.symm
      _ = canonicalLargestPrimeFactor m * k *
            canonicalLargestPrimeFactor m := by rw [hk]
      _ = canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m * k := by
        ring
  have hnotsq : ¬ Squarefree m := by
    intro hsf
    have hunit := hsf _ hsqdvd
    rw [Nat.isUnit_iff] at hunit
    exact hqPrime.ne_one hunit
  unfold canonicalMoebiusWeight
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnotsq]
  simp

/-! ## Prime-first coordinates of the born-smooth population -/

/-- Born-orientation canonical source integers in the complete square prefix,
cut out purely by canonical coordinates. -/
def squareRootBornSmoothSourceSet (R : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (squareRootEndpoint R)).filter fun m =>
    canonicalLargestPrimeFactor (canonicalCofactor m) <
        canonicalLargestPrimeFactor m ∧
      canonicalLargestPrimeFactor m ≤ canonicalCofactor m

/-- Prime-first canonical coordinates for the same born-orientation family. -/
def squareRootBornSmoothPairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 R).product
      (Finset.Icc 1 (squareRootEndpoint R))).filter fun qc =>
    qc.1.Prime ∧ canonicalLargestPrimeFactor qc.2 < qc.1 ∧
      qc.1 ≤ qc.2 ∧ qc.2 * qc.1 ≤ squareRootEndpoint R

/-- Native source mass on the born-orientation population. -/
def squareRootBornSmoothSourceMass (R : ℕ) : ℂ :=
  ∑ m ∈ squareRootBornSmoothSourceSet R, canonicalMoebiusWeight m

/-- The same source mass reindexed by prime/cofactor coordinates. -/
def squareRootBornSmoothPairSourceMass (R : ℕ) : ℂ :=
  ∑ qc ∈ squareRootBornSmoothPairSet R, canonicalMoebiusWeight (qc.2 * qc.1)

private theorem bornSmoothIndicator_sum_eq_sourceMass (R : ℕ) :
    (∑ m ∈ Finset.Icc 2 (squareRootEndpoint R),
      if canonicalLargestPrimeFactor m ≤ R ∧
          canonicalLargestPrimeFactor m ≤ canonicalCofactor m then
        canonicalMoebiusWeight m
      else 0) =
      squareRootBornSmoothSourceMass R := by
  classical
  unfold squareRootBornSmoothSourceMass squareRootBornSmoothSourceSet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rcases Finset.mem_Icc.mp hm with ⟨hm2, hmX⟩
  have hm1 : 1 < m := by omega
  by_cases hborn : canonicalLargestPrimeFactor m ≤ canonicalCofactor m
  · have hsmooth : canonicalLargestPrimeFactor m ≤ R :=
      (canonicalLargestPrimeFactor_lt_of_bornOrientation hm1 hmX hborn).le
    by_cases hrough : canonicalLargestPrimeFactor (canonicalCofactor m) <
        canonicalLargestPrimeFactor m
    · rw [if_pos ⟨hsmooth, hborn⟩, if_pos ⟨hrough, hborn⟩]
    · rw [if_pos ⟨hsmooth, hborn⟩,
        if_neg (fun hcon => hrough hcon.1)]
      exact canonicalMoebiusWeight_eq_zero_of_cofactor_not_rough hm1 hrough hborn
  · rw [if_neg (fun hcon => hborn hcon.2), if_neg (fun hcon => hborn hcon.2)]

/-- Peeling the two degenerate sources.  The zero source carries no Möbius mass
and fails the born orientation; the unit source carries mass `1` and passes it.
Everything else is the canonical born-orientation population. -/
theorem squareRootBornSmoothMass_eq_one_add_sourceMass
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootBornSmoothMass R = 1 + squareRootBornSmoothSourceMass R := by
  classical
  have hpred : R - 1 + 1 = R := by omega
  have hpow : R ^ 2 = R * R := by ring
  have hge : 2 * 2 ≤ R * R := Nat.mul_le_mul hR hR
  have hzeroP : canonicalLargestPrimeFactor 0 = 1 := by
    have hnot : ¬ (1 : ℕ) < 0 := by omega
    unfold canonicalLargestPrimeFactor
    rw [dif_neg hnot]
  have honeP : canonicalLargestPrimeFactor 1 = 1 := by
    have hnot : ¬ (1 : ℕ) < 1 := by omega
    unfold canonicalLargestPrimeFactor
    rw [dif_neg hnot]
  have hzeroC : canonicalCofactor 0 = 0 := by
    unfold canonicalCofactor
    rw [hzeroP]
  have honeC : canonicalCofactor 1 = 1 := by
    unfold canonicalCofactor
    rw [honeP]
  have hcond0 :
      ¬ (canonicalLargestPrimeFactor 0 ≤ R ∧
        canonicalLargestPrimeFactor 0 ≤ canonicalCofactor 0) := by
    rw [hzeroP, hzeroC]
    omega
  have hcond1 :
      canonicalLargestPrimeFactor 1 ≤ R ∧
        canonicalLargestPrimeFactor 1 ≤ canonicalCofactor 1 := by
    rw [honeP, honeC]
    omega
  have hmu1 : canonicalMoebiusWeight 1 = 1 := by
    unfold canonicalMoebiusWeight
    simp
  have hins :
      cumulativeSquarePrefixSet (R - 1) =
        insert 0 (insert 1 (Finset.Icc 2 (squareRootEndpoint R))) := by
    ext m
    simp only [cumulativeSquarePrefixSet, squareRootEndpoint, hpred,
      Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold squareRootBornSmoothMass
  rw [hins, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    if_neg hcond0, if_pos hcond1, hmu1,
    bornSmoothIndicator_sum_eq_sourceMass R]
  ring

private theorem bornSource_to_pair_mem {R m : ℕ}
    (hm : m ∈ squareRootBornSmoothSourceSet R) :
    (canonicalLargestPrimeFactor m, canonicalCofactor m) ∈
      squareRootBornSmoothPairSet R := by
  classical
  rcases Finset.mem_filter.mp hm with ⟨hmRange, hrough, hborn⟩
  rcases Finset.mem_Icc.mp hmRange with ⟨hm2, hmX⟩
  have hm1 : 1 < m := by omega
  have hqPrime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hm1
  have hprod : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm1
  have hqR : canonicalLargestPrimeFactor m < R :=
    canonicalLargestPrimeFactor_lt_of_bornOrientation hm1 hmX hborn
  have hcpos : 0 < canonicalCofactor m := lt_of_lt_of_le hqPrime.pos hborn
  have hcdvd : canonicalCofactor m ∣ m :=
    ⟨canonicalLargestPrimeFactor m, hprod.symm⟩
  have hcX : canonicalCofactor m ≤ squareRootEndpoint R :=
    (Nat.le_of_dvd (by omega) hcdvd).trans hmX
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hqPrime, hrough, hborn, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨hqPrime.two_le, by omega⟩
  · exact Finset.mem_Icc.mpr ⟨hcpos, hcX⟩
  · rw [hprod]
    exact hmX

private theorem bornSource_pair_injective {R m n : ℕ}
    (hm : m ∈ squareRootBornSmoothSourceSet R)
    (hn : n ∈ squareRootBornSmoothSourceSet R)
    (hpair :
      (canonicalLargestPrimeFactor m, canonicalCofactor m) =
        (canonicalLargestPrimeFactor n, canonicalCofactor n)) :
    m = n := by
  classical
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1 with ⟨hm2, _⟩
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1 with ⟨hn2, _⟩
  have hmprod := canonicalCofactor_mul_largestPrimeFactor (by omega : 1 < m)
  have hnprod := canonicalCofactor_mul_largestPrimeFactor (by omega : 1 < n)
  have hq : canonicalLargestPrimeFactor m = canonicalLargestPrimeFactor n :=
    congrArg Prod.fst hpair
  have hc : canonicalCofactor m = canonicalCofactor n :=
    congrArg Prod.snd hpair
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hmprod.symm
    _ = canonicalCofactor n * canonicalLargestPrimeFactor n := by rw [hc, hq]
    _ = n := hnprod

private theorem bornPair_surjective {R : ℕ} (qc : ℕ × ℕ)
    (hqc : qc ∈ squareRootBornSmoothPairSet R) :
    ∃ m ∈ squareRootBornSmoothSourceSet R,
      (canonicalLargestPrimeFactor m, canonicalCofactor m) = qc := by
  classical
  rcases Finset.mem_filter.mp hqc with ⟨hbase, hqPrime, hrough, hborn, hmul⟩
  rcases Finset.mem_product.mp hbase with ⟨hqMem, hcMem⟩
  rcases Finset.mem_Icc.mp hqMem with ⟨hq2, _hqR⟩
  rcases Finset.mem_Icc.mp hcMem with ⟨hc1, _hcX⟩
  have hcPos : 0 < qc.2 := hc1
  have hlargest : canonicalLargestPrimeFactor (qc.2 * qc.1) = qc.1 :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hqPrime hrough
  have hcofactor : canonicalCofactor (qc.2 * qc.1) = qc.2 :=
    canonicalCofactor_mul_prime_eq_of_rough hcPos hqPrime hrough
  have hm2 : 2 ≤ qc.2 * qc.1 := by
    calc
      2 = 1 * 2 := by norm_num
      _ ≤ qc.2 * qc.1 := Nat.mul_le_mul hc1 hq2
  refine ⟨qc.2 * qc.1, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm2, hmul⟩, ?_, ?_⟩
    · rw [hlargest, hcofactor]
      exact hrough
    · rw [hlargest, hcofactor]
      exact hborn
  · apply Prod.ext
    · exact hlargest
    · exact hcofactor

/-- Reindex the born-orientation source population by its unique prime-first
canonical coordinates. -/
theorem squareRootBornSmoothSourceMass_eq_pairSourceMass (R : ℕ) :
    squareRootBornSmoothSourceMass R = squareRootBornSmoothPairSourceMass R := by
  classical
  unfold squareRootBornSmoothSourceMass squareRootBornSmoothPairSourceMass
  refine Finset.sum_bij
    (fun m _hm => (canonicalLargestPrimeFactor m, canonicalCofactor m))
    (fun m hm => bornSource_to_pair_mem hm)
    (fun m hm n hn hmn => bornSource_pair_injective hm hn hmn)
    (fun qc hqc => by simpa using bornPair_surjective qc hqc)
    ?_
  intro m hm
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1 with ⟨hm2, _⟩
  rw [canonicalCofactor_mul_largestPrimeFactor (by omega : 1 < m)]

/-! ## The born-smooth reciprocal transform -/

/-- The born-smooth fibre of a prime `q`: the lower-scale rough Möbius prefix at
the reciprocal cutoff `floor(X/q)`, measured from the orientation turning point
`q`. -/
def squareRootBornSmoothPrimeFibre (R q : ℕ) : ℂ :=
  roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q) -
    cofactorMobiusPrefixMass (q - 1)

/-- Prime-indexed lower-scale reciprocal transform carried by the born
orientation. -/
def squareRootBornSmoothReciprocalTransform (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 2 R,
    if q.Prime then squareRootBornSmoothPrimeFibre R q else 0

theorem squareRootBornSmoothPairSourceMass_eq_neg_reciprocalTransform
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootBornSmoothPairSourceMass R =
      -squareRootBornSmoothReciprocalTransform R := by
  classical
  unfold squareRootBornSmoothPairSourceMass squareRootBornSmoothPairSet
    squareRootBornSmoothReciprocalTransform
  rw [Finset.sum_filter]
  calc
    (∑ qc ∈ (Finset.Icc 2 R).product (Finset.Icc 1 (squareRootEndpoint R)),
        if qc.1.Prime ∧ canonicalLargestPrimeFactor qc.2 < qc.1 ∧
            qc.1 ≤ qc.2 ∧ qc.2 * qc.1 ≤ squareRootEndpoint R then
          canonicalMoebiusWeight (qc.2 * qc.1)
        else 0) =
      ∑ q ∈ Finset.Icc 2 R,
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          if q.Prime ∧ canonicalLargestPrimeFactor c < q ∧
              q ≤ c ∧ c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight (c * q)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Icc 2 R)
          (t := Finset.Icc 1 (squareRootEndpoint R))
          (f := fun qc : ℕ × ℕ =>
            if qc.1.Prime ∧ canonicalLargestPrimeFactor qc.2 < qc.1 ∧
                qc.1 ≤ qc.2 ∧ qc.2 * qc.1 ≤ squareRootEndpoint R then
              canonicalMoebiusWeight (qc.2 * qc.1)
            else 0))
    _ = ∑ q ∈ Finset.Icc 2 R,
          if q.Prime then -squareRootBornSmoothPrimeFibre R q else 0 := by
      refine Finset.sum_congr rfl ?_
      intro q hqMem
      by_cases hqPrime : q.Prime
      · simp only [hqPrime, true_and, if_true]
        have hqpos : 0 < q := hqPrime.pos
        have hq2 : 2 ≤ q := hqPrime.two_le
        have hset :
            (Finset.Icc 1 (squareRootEndpoint R)).filter
                (fun c => canonicalLargestPrimeFactor c < q ∧
                  q ≤ c ∧ c * q ≤ squareRootEndpoint R) =
              (Finset.Icc q (squareRootEndpoint R / q)).filter
                (fun c => canonicalLargestPrimeFactor c < q) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨_hc1, _hcX⟩, hrough, hqc, hcmul⟩
            exact ⟨⟨hqc, (Nat.le_div_iff_mul_le hqpos).2 hcmul⟩, hrough⟩
          · rintro ⟨⟨hqc, hcdiv⟩, hrough⟩
            have hcmul : c * q ≤ squareRootEndpoint R :=
              (Nat.le_div_iff_mul_le hqpos).1 hcdiv
            have hcX : c ≤ squareRootEndpoint R :=
              hcdiv.trans (Nat.div_le_self _ _)
            exact ⟨⟨by omega, hcX⟩, hrough, hqc, hcmul⟩
        have hqB : q ≤ squareRootEndpoint R / q + 1 := by
          have hqR : q ≤ R := (Finset.mem_Icc.mp hqMem).2
          have hmono : (q - 1) * q ≤ (R - 1) * R :=
            Nat.mul_le_mul (by omega) hqR
          have hexp : (R - 1) * R = R * R - R := by
            rw [Nat.sub_mul, one_mul]
          have hend : R * R - R ≤ squareRootEndpoint R := by
            have hpow : R ^ 2 = R * R := by ring
            unfold squareRootEndpoint
            omega
          have hkey : (q - 1) * q ≤ squareRootEndpoint R := by
            calc
              (q - 1) * q ≤ (R - 1) * R := hmono
              _ = R * R - R := hexp
              _ ≤ squareRootEndpoint R := hend
          have hdiv : q - 1 ≤ squareRootEndpoint R / q :=
            (Nat.le_div_iff_mul_le hqpos).2 hkey
          omega
        rw [← Finset.sum_filter, hset, Finset.sum_filter]
        have hstep :
            (∑ c ∈ Finset.Icc q (squareRootEndpoint R / q),
              if canonicalLargestPrimeFactor c < q then
                canonicalMoebiusWeight (c * q)
              else 0) =
              -roughCofactorMobiusWindowMass q q (squareRootEndpoint R / q) := by
          unfold roughCofactorMobiusWindowMass
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro c hc
          rcases Finset.mem_Icc.mp hc with ⟨hqc, _⟩
          by_cases hrough : canonicalLargestPrimeFactor c < q
          · rw [if_pos hrough, if_pos hrough]
            exact canonicalMoebiusWeight_mul_prime_eq_neg_of_rough
              (by omega) hqPrime hrough
          · rw [if_neg hrough, if_neg hrough, neg_zero]
        unfold squareRootBornSmoothPrimeFibre
        rw [hstep, roughCofactorMobiusWindowMass_eq_prefix_sub_prefix
          (by omega) hqB]
      · simp [hqPrime]
    _ = -∑ q ∈ Finset.Icc 2 R,
          if q.Prime then squareRootBornSmoothPrimeFibre R q else 0 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro q _hqMem
      by_cases hqPrime : q.Prime <;> simp [hqPrime]

/-- **Born-smooth reciprocal form.**  The entire born orientation is the unit
source minus the prime-indexed lower-scale reciprocal transform. -/
theorem squareRootBornSmoothMass_eq_one_sub_reciprocalTransform
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootBornSmoothMass R =
      1 - squareRootBornSmoothReciprocalTransform R := by
  rw [squareRootBornSmoothMass_eq_one_add_sourceMass R hR,
    squareRootBornSmoothSourceMass_eq_pairSourceMass,
    squareRootBornSmoothPairSourceMass_eq_neg_reciprocalTransform R hR]
  ring

/-! ## The unified reciprocal transform -/

/-- The unified lower-scale Möbius/reciprocal transform: the rough Möbius prefix
at the reciprocal cutoff of *every* prime up to the square endpoint. -/
def squareRootUnifiedReciprocalTransform (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 2 (squareRootEndpoint R),
    if q.Prime then
      roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
    else 0

/-- Above `R` the reciprocal cutoff falls below the prime itself, so the
roughness restriction is vacuous and the transport term is already in the unified
form. -/
theorem squareRootTransportPrimeFirst_eq_reciprocalRoughTransform
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportPrimeFirst R =
      ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        if q.Prime then
          roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
        else 0 := by
  rw [squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)]
  refine Finset.sum_congr rfl ?_
  intro q hqMem
  by_cases hqPrime : q.Prime
  · rcases Finset.mem_Ioc.mp hqMem with ⟨hRq, _hqX⟩
    have hdivR : squareRootEndpoint R / q < R :=
      squareRootEndpoint_div_lt (by omega) hRq hqPrime.pos
    have hdivlt : squareRootEndpoint R / q < q := lt_trans hdivR hRq
    rw [if_pos hqPrime, if_pos hqPrime,
      roughCofactorMobiusPrefixMass_eq_cofactorMobiusPrefixMass hdivlt,
      cofactorMobiusPrefixMass_eq_mertensSummatory]
  · simp [hqPrime]

/-- The unified transform splits at `R` into the born range and the transport
range. -/
theorem squareRootUnifiedReciprocalTransform_eq_low_add_high
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootUnifiedReciprocalTransform R =
      (∑ q ∈ Finset.Icc 2 R,
          if q.Prime then
            roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
          else 0) +
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          if q.Prime then
            roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
          else 0 := by
  classical
  have hpow : R ^ 2 = R * R := by ring
  have hge : 2 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hsplit :
      Finset.Icc 2 (squareRootEndpoint R) =
        Finset.Icc 2 R ∪ Finset.Ioc R (squareRootEndpoint R) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj :
      Disjoint (Finset.Icc 2 R) (Finset.Ioc R (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rcases Finset.mem_Icc.mp hq1 with ⟨_, hqR⟩
    rcases Finset.mem_Ioc.mp hq2 with ⟨hRq, _⟩
    omega
  unfold squareRootUnifiedReciprocalTransform
  rw [hsplit, Finset.sum_union hdisj]

/-- The born-smooth reciprocal transform is the low part of the unified transform
minus the prime-indexed Mertens prefix transform already isolated by the
positive-orientation collapse. -/
theorem squareRootBornSmoothReciprocalTransform_eq_low_sub_primeMertens
    (R : ℕ) :
    squareRootBornSmoothReciprocalTransform R =
      (∑ q ∈ Finset.Icc 2 R,
          if q.Prime then
            roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
          else 0) -
        squareRootPositiveSmoothPrimeMertensTransform R := by
  unfold squareRootBornSmoothReciprocalTransform
    squareRootPositiveSmoothPrimeMertensTransform
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro q _hqMem
  by_cases hqPrime : q.Prime
  · rw [if_pos hqPrime, if_pos hqPrime, if_pos hqPrime]
    unfold squareRootBornSmoothPrimeFibre
    rw [cofactorMobiusPrefixMass_eq_mertensSummatory]
    ring
  · simp [hqPrime]

/-! ## The matched object in unified reciprocal form -/

/-- **Unified lower-scale Möbius/reciprocal form of the matched object.**
`A_R^born - T_R` is one signed sum of lower-scale Möbius prefixes at reciprocal
cutoffs over the whole prime range, plus the prime-indexed Mertens prefix
transform.  No norm and no triangle inequality is used. -/
theorem squareRootMatchedBornSmoothTransport_eq_unifiedReciprocalForm
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootMatchedBornSmoothTransport R =
      1 - squareRootUnifiedReciprocalTransform R +
        squareRootPositiveSmoothPrimeMertensTransform R := by
  unfold squareRootMatchedBornSmoothTransport
  rw [squareRootBornSmoothMass_eq_one_sub_reciprocalTransform R hR,
    squareRootBornSmoothReciprocalTransform_eq_low_sub_primeMertens R,
    squareRootTransportPrimeFirst_eq_reciprocalRoughTransform R hR,
    squareRootUnifiedReciprocalTransform_eq_low_add_high R hR]
  ring

/-- **Exact main-term match.**  The centered main-term difference
`A_R^born - T_R^sm` is the same unified lower-scale Möbius/reciprocal object plus
the combined signed residual `D_R`.  The residual is carried whole, so the
cancellation between the reciprocal transform, the prime-Mertens transform and
the residual can be studied as one signed identity, without norms. -/
theorem squareRootMatchedBornSmoothPNTMain_eq_unifiedReciprocalForm_add_combinedResidual
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootMatchedBornSmoothPNTMain R =
      (1 - squareRootUnifiedReciprocalTransform R +
          squareRootPositiveSmoothPrimeMertensTransform R) +
        squareRootTransportCombinedResidual R := by
  have h := squareRootMatchedBornSmoothTransport_eq_pntMain_sub_combinedResidual R
  rw [squareRootMatchedBornSmoothTransport_eq_unifiedReciprocalForm R hR] at h
  rw [h]
  ring

/-- The RH-scale target stated directly on the unified reciprocal form.  Named
proposition only; nothing here asserts or assumes it. -/
def SquareRootUnifiedReciprocalBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖1 - squareRootUnifiedReciprocalTransform R +
            squareRootPositiveSmoothPrimeMertensTransform R‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- **The square-prefix RH criterion in unified reciprocal form.**  The target
`‖A_R^born - T_R‖^2 ≪_eps R^(2+eps)` is equivalent to the same bound on the
unified lower-scale Möbius/reciprocal object.  This is an equivalence of
statements; neither side is proved here. -/
theorem squareRootUnifiedReciprocalBounded_iff_matchedTransportBounded :
    SquareRootUnifiedReciprocalBoundedStatement ↔
      SquareRootMatchedTransportBoundedStatement := by
  unfold SquareRootUnifiedReciprocalBoundedStatement
    SquareRootMatchedTransportBoundedStatement
  constructor
  · intro h ε hε
    obtain ⟨C, hC0, hC⟩ := h ε hε
    refine ⟨C, hC0, fun R hR => ?_⟩
    rw [squareRootMatchedBornSmoothTransport_eq_unifiedReciprocalForm R hR]
    exact hC R hR
  · intro h ε hε
    obtain ⟨C, hC0, hC⟩ := h ε hε
    refine ⟨C, hC0, fun R hR => ?_⟩
    rw [← squareRootMatchedBornSmoothTransport_eq_unifiedReciprocalForm R hR]
    exact hC R hR

/-- The same criterion read through the combined signed residual: the unified
reciprocal form and the combined residual together carry exactly the RH-scale
target, with `Q_R` and `E_R` never separated. -/
theorem squareRootUnifiedReciprocalBounded_iff_matchedCombinedBounded :
    SquareRootUnifiedReciprocalBoundedStatement ↔
      SquareRootMatchedCombinedBoundedStatement := by
  rw [squareRootUnifiedReciprocalBounded_iff_matchedTransportBounded,
    squareRootMatchedCombinedBounded_iff_matchedTransportBounded]

end RHLean.Proof
