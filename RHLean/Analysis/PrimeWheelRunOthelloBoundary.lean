import Mathlib
import RHLean.Proof.PrefixCarrierOthelloWalls
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity
import RHLean.Analysis.SquareWheelNesting
import RHLean.Analysis.SquareRunEscapeCovariance
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# The Othello boundary of a wheel prefix and of a whole square run

The three cumulative coordinates of this project

```text
M(x),        R_k(x) = M(x) - M(L_k),        sum of Delta_j over a square run
```

are the same object read in three charts.  The global Othello theorem applies to
the carrier underneath all three, so each of them equals the signed mass of one
explicit boundary rather than a sum of local Möbius estimates.

This file installs the transport.

* `primorialWheelResidual_eq_wallMass` rewrites the pinned primorial-wheel
  residual — which the arithmetic certificate already identifies with the
  Mertens increment `M(x) - M(L_k)` — as the anchor wall plus the cutoff wall
  of the prefix carrier `(L_k, x]`.
* `sum_canonicalTotalIncrement_Ico_eq_runWallMass` does the same for an entire
  consecutive run of complete square blocks.  Two separate mechanisms are
  composed there and should not be confused.  The square times collapse by the
  **already-known telescope** `sum Delta_j = M(X_b) - M(X_{a-1})`, which is what
  removes the block count; what is left is then a cumulative arithmetic
  interval `(X_{a-1}, X_b]`, and the fixed-prime pairing reduces that interval
  to its two walls.  Nothing here is a survivor trajectory: the interval is not
  a space-time carrier, and no birth-to-capture cancellation is claimed.  That
  statement — an atom born and captured strictly inside a run costs zero
  whatever its lifetime — is proved separately, on the actual birth/death
  process, in `RHLean.Proof.LifetimeRunCancellation`.
* `mertensEnergyBounded_of_iteratedPrefixBoundaryBounded` states what is left to
  prove.  If some finite peel of distinguished primes leaves an iterated
  boundary of RH-scale population, the Mertens energy criterion follows — and
  hence, through the equivalences already in the repository, the pinned
  primorial-wheel residual criterion and the maximal signed square-run
  criterion.  The remaining problem is a multiplicity bound on a run boundary,
  not a statement about individual Möbius seats.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The complete-square endpoint is monotone. -/
theorem squarePrefixEndpoint_mono {a b : ℕ} (hab : a ≤ b) :
    squarePrefixEndpoint a ≤ squarePrefixEndpoint b := by
  have hsquare : (a + 1) ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have ha := squarePrefixEndpoint_add_one a
  have hb := squarePrefixEndpoint_add_one b
  omega

/-! ## The wheel prefix -/

/-- **The pinned wheel residual is exactly the mass of its two walls.**

The residual is the raw seeded prefix minus twice its smooth core; the
arithmetic certificate makes it the Möbius mass of `(L_k, x]`; the global
Othello theorem then collapses that whole prefix onto its boundary. -/
theorem primorialWheelResidual_eq_wallMass
    {p : ℕ} (hp : p.Prime) (k : ℕ) {x : ℕ}
    (hx : x ≤ primorialBlockUpper k) :
    (primorialWheelSystem k).residual x =
      (∑ n ∈ primeCarrierAnchorWall p (primorialBlockLower k) x, μ n) +
        ∑ n ∈ primeCarrierCutoffWall p (primorialBlockLower k) x, μ n := by
  rw [primorialWheel_residual_eq_moebiusInterval k hx]
  exact sum_moebius_Ioc_eq_wallMass hp (primorialBlockLower k) x

/-- Population bound for the pinned wheel residual in terms of its boundary
alone. -/
theorem abs_primorialWheelResidual_le_wallCard
    {p : ℕ} (hp : p.Prime) (k : ℕ) {x : ℕ}
    (hx : x ≤ primorialBlockUpper k) :
    |(primorialWheelSystem k).residual x| ≤
      ((primorialBlockLower k : ℕ) : ℤ) + ((x - x / p : ℕ) : ℤ) := by
  rw [primorialWheel_residual_eq_moebiusInterval k hx]
  exact abs_sum_moebius_Ioc_le_wallCard hp (primorialBlockLower k) x

/-! ## A whole square run as one carrier -/

/-- A consecutive run of complete square blocks is the Möbius mass of the single
cumulative arithmetic interval `(X_{a-1}, X_b]`.  This is the pre-existing
square-prefix telescope, restated in interval form; it is where the block count
disappears. -/
theorem sum_canonicalTotalIncrement_Ico_eq_moebius_Ioc_cast
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) =
      (((∑ n ∈ Finset.Ioc (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), μ n : ℤ) : ℂ)) := by
  have hmono : squarePrefixEndpoint (a - 1) ≤ squarePrefixEndpoint b :=
    squarePrefixEndpoint_mono (by omega)
  calc (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j)
      = squarePrefixMertens b - squarePrefixMertens (a - 1) :=
        sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub a b ha hab
    _ = mertensSummatory (squarePrefixEndpoint b) -
          mertensSummatory (squarePrefixEndpoint (a - 1)) := rfl
    _ = ∑ n ∈ Finset.Ioc (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), (((μ n : ℤ) : ℂ)) :=
        (moebius_Ioc_cast_eq_mertens_sub hmono).symm
    _ = (((∑ n ∈ Finset.Ioc (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), μ n : ℤ) : ℂ)) := by
        push_cast
        ring

/-- **Run-level wall identity.**

The whole signed square run equals the anchor wall at `X_{a-1}` plus the cutoff
wall at `X_b`.  The block count drops out at the first step, by the existing
square-prefix telescope; the pairing then acts on the resulting cumulative
interval.  The two steps are independent, and only the first one is about square
time. -/
theorem sum_canonicalTotalIncrement_Ico_eq_runWallMass
    {p : ℕ} (hp : p.Prime) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) =
      (((∑ n ∈ primeCarrierAnchorWall p (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), μ n : ℤ) : ℂ)) +
      (((∑ n ∈ primeCarrierCutoffWall p (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), μ n : ℤ) : ℂ)) := by
  rw [sum_canonicalTotalIncrement_Ico_eq_moebius_Ioc_cast a b ha hab,
    sum_moebius_Ioc_eq_wallMass hp (squarePrefixEndpoint (a - 1))
      (squarePrefixEndpoint b)]
  push_cast
  ring

/-- The run is bounded by its boundary population alone. -/
theorem norm_sum_canonicalTotalIncrement_Ico_le_runWallCard
    {p : ℕ} (hp : p.Prime) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    ‖∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j‖ ≤
      ((squarePrefixEndpoint (a - 1) : ℕ) : ℝ) +
        ((squarePrefixEndpoint b - squarePrefixEndpoint b / p : ℕ) : ℝ) := by
  rw [sum_canonicalTotalIncrement_Ico_eq_moebius_Ioc_cast a b ha hab,
    Complex.norm_intCast]
  have hbound := abs_sum_moebius_Ioc_le_wallCard hp
    (squarePrefixEndpoint (a - 1)) (squarePrefixEndpoint b)
  exact_mod_cast hbound

/-! ## What is left to prove -/

/-- **The iterated-boundary multiplicity target.**

For every cumulative prefix carrier `(0, x]` some finite peel of distinguished
primes leaves an Othello boundary whose population is of RH scale.  This is a
statement about one run boundary, not about individual Möbius values. -/
def IteratedPrefixBoundaryBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℕ, ∃ ps : List ℕ, (∀ p ∈ ps, Nat.Prime p) ∧
        ((iteratedPrimeEscapePart ps (Finset.Ioc 0 x)).card : ℝ) ^ 2 ≤
          C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)

/-- The Mertens summatory function is the Möbius mass of its prefix carrier. -/
theorem mertensSummatory_eq_moebius_Ioc_cast (x : ℕ) :
    mertensSummatory x =
      (((∑ n ∈ Finset.Ioc 0 x, μ n : ℤ) : ℂ)) := by
  have hcast := moebius_Ioc_cast_eq_mertens_sub (Nat.zero_le x)
  rw [mertensSummatory_zero, sub_zero] at hcast
  rw [← hcast]
  push_cast
  ring

/-- **The reduction.**  An RH-scale multiplicity bound on the iterated Othello
boundary of the prefix carrier gives the Mertens energy criterion, and hence,
through the equivalences already recorded in this repository, the pinned
primorial-wheel residual criterion and the maximal signed square-run
criterion. -/
theorem mertensEnergyBounded_of_iteratedPrefixBoundaryBounded
    (h : IteratedPrefixBoundaryBoundedStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro x
  obtain ⟨ps, hps, hcard⟩ := hbound x
  have habs := abs_sum_moebius_le_card_iteratedPrimeEscapePart ps hps
    (Finset.Ioc 0 x)
  have hnorm : ‖mertensSummatory x‖ ≤
      ((iteratedPrimeEscapePart ps (Finset.Ioc 0 x)).card : ℝ) := by
    rw [mertensSummatory_eq_moebius_Ioc_cast x, Complex.norm_intCast]
    exact_mod_cast habs
  calc ‖mertensSummatory x‖ ^ 2
      ≤ ((iteratedPrimeEscapePart ps (Finset.Ioc 0 x)).card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := hcard

/-! ## Global square-run covariance ownership by fresh primes -/

/-- Literal unordered-pair covariance in a physical interval `[A,B)`. -/
def squareRunPhysicalPairCovariance (w : ℕ → ℝ) (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico A B,
    ∑ m ∈ Finset.Ico A n, w m * w n

@[simp] theorem squareRunPhysicalPairCovariance_self
    (w : ℕ → ℝ) (A : ℕ) :
    squareRunPhysicalPairCovariance w A A = 0 := by
  simp [squareRunPhysicalPairCovariance]

private theorem squareRunPhysicalPairCovariance_succ_top
    (w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    squareRunPhysicalPairCovariance w A (B + 1) =
      squareRunPhysicalPairCovariance w A B +
        w B * (signedBlockPrefix w B - signedBlockPrefix w A) := by
  unfold squareRunPhysicalPairCovariance
  rw [Finset.sum_Ico_succ_top hAB]
  have hsum := Finset.sum_Ico_eq_sub w hAB
  unfold signedBlockPrefix at hsum ⊢
  rw [← Finset.sum_mul, hsum]
  ring

private theorem squareRunInnerCovariance_succ_top
    (w : ℕ → ℝ) (A B : ℕ) :
    signedBlockInnerCovariance w A (B + 1) =
      signedBlockInnerCovariance w A B +
        w B * (signedBlockPrefix w B - signedBlockPrefix w A) := by
  unfold signedBlockInnerCovariance
  rw [signedBlockCrossCovariance_succ, signedBlockPrefix_succ]
  ring

/-- The prefix-difference Green--Kubo coordinate is exactly the physical pair
sum in the window. -/
theorem signedBlockInnerCovariance_eq_squareRunPhysicalPairCovariance
    (w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    signedBlockInnerCovariance w A B =
      squareRunPhysicalPairCovariance w A B := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [signedBlockInnerCovariance]
  | succ B hAB ih =>
      rw [squareRunInnerCovariance_succ_top w A B,
        squareRunPhysicalPairCovariance_succ_top w hAB, ih]

/-- Hence `squareRunCovariance` is literally the sum of its physical unordered
Möbius pairs. -/
theorem squareRunCovariance_eq_physicalPairCovariance
    {a b : ℕ} (hab : a ≤ b) :
    squareRunCovariance a b =
      squareRunPhysicalPairCovariance realMoebiusStep
        (a ^ 2) ((b + 1) ^ 2) := by
  unfold squareRunCovariance
  apply signedBlockInnerCovariance_eq_squareRunPhysicalPairCovariance
  exact Nat.pow_le_pow_left (by omega) 2

/-- Prime coordinates on which two canonical squarefree faces disagree. -/
def squarefreePairFreshPrimeSet (m n : ℕ) : Finset ℕ :=
  (squarefreePrimeFace m \ squarefreePrimeFace n) ∪
    (squarefreePrimeFace n \ squarefreePrimeFace m)

/-- Distinct squarefree integers have a nonempty symmetric-difference face. -/
theorem squarefreePairFreshPrimeSet_nonempty
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    (squarefreePairFreshPrimeSet m n).Nonempty := by
  by_contra hnone
  have hempty : squarefreePairFreshPrimeSet m n = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnone
  have hfaces : squarefreePrimeFace m = squarefreePrimeFace n := by
    ext p
    by_cases hpm : p ∈ squarefreePrimeFace m
    · have hpn : p ∈ squarefreePrimeFace n := by
        by_contra hpnot
        have hmem : p ∈ squarefreePairFreshPrimeSet m n := by
          simp [squarefreePairFreshPrimeSet, hpm, hpnot]
        rw [hempty] at hmem
        simp at hmem
      simp [hpm, hpn]
    · have hpn : p ∉ squarefreePrimeFace n := by
        intro hpn
        have hmem : p ∈ squarefreePairFreshPrimeSet m n := by
          simp [squarefreePairFreshPrimeSet, hpm, hpn]
        rw [hempty] at hmem
        simp at hmem
      simp [hpm, hpn]
  apply hmn
  have hprod := congrArg primeFaceProduct hfaces
  simpa [primeFaceProduct_squarefreePrimeFace hm,
    primeFaceProduct_squarefreePrimeFace hn] using hprod

/-- Canonical chronological owner: the least prime at which the two faces
separate.  The default `1` is unreachable on a contributing distinct squarefree
pair. -/
def squarefreePairFreshPrimeOwner (m n : ℕ) : ℕ :=
  if h : (squarefreePairFreshPrimeSet m n).Nonempty then
    (squarefreePairFreshPrimeSet m n).min' h
  else 1

/-- The canonical owner belongs to the differing-prime set. -/
theorem squarefreePairFreshPrimeOwner_mem
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    squarefreePairFreshPrimeOwner m n ∈ squarefreePairFreshPrimeSet m n := by
  have hne := squarefreePairFreshPrimeSet_nonempty hm hn hmn
  unfold squarefreePairFreshPrimeOwner
  rw [dif_pos hne]
  exact Finset.min'_mem _ hne

/-- The owner occurs in exactly one of the two endpoint faces. -/
theorem squarefreePairFreshPrimeOwner_xor
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    (squarefreePairFreshPrimeOwner m n ∈ squarefreePrimeFace m ∧
      squarefreePairFreshPrimeOwner m n ∉ squarefreePrimeFace n) ∨
    (squarefreePairFreshPrimeOwner m n ∈ squarefreePrimeFace n ∧
      squarefreePairFreshPrimeOwner m n ∉ squarefreePrimeFace m) := by
  have hmem := squarefreePairFreshPrimeOwner_mem hm hn hmn
  simpa [squarefreePairFreshPrimeSet] using hmem

/-- The owner is a genuine prime. -/
theorem squarefreePairFreshPrimeOwner_prime
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    (squarefreePairFreshPrimeOwner m n).Prime := by
  rcases squarefreePairFreshPrimeOwner_xor hm hn hmn with h | h
  · exact (Nat.mem_primeFactors.mp (by
      simpa [squarefreePrimeFace] using h.1)).1
  · exact (Nat.mem_primeFactors.mp (by
      simpa [squarefreePrimeFace] using h.1)).1

/-- Every earlier prime coordinate agrees in the two faces. -/
theorem squarefreePairFreshPrimeOwner_chronology
    {m n q : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (hq : q < squarefreePairFreshPrimeOwner m n) :
    (q ∈ squarefreePrimeFace m ↔ q ∈ squarefreePrimeFace n) := by
  have hne := squarefreePairFreshPrimeSet_nonempty hm hn hmn
  unfold squarefreePairFreshPrimeOwner at hq
  rw [dif_pos hne] at hq
  by_contra hiff
  have hdiff : q ∈ squarefreePairFreshPrimeSet m n := by
    by_cases hqm : q ∈ squarefreePrimeFace m
    · have hqn : q ∉ squarefreePrimeFace n := by
        intro hqn
        exact hiff (by simp [hqm, hqn])
      simp [squarefreePairFreshPrimeSet, hqm, hqn]
    · have hqn : q ∈ squarefreePrimeFace n := by
        by_contra hqn
        exact hiff (by simp [hqm, hqn])
      simp [squarefreePairFreshPrimeSet, hqm, hqn]
  have hle : (squarefreePairFreshPrimeSet m n).min' hne ≤ q :=
    Finset.min'_le _ _ hdiff
  omega

/-- Intrinsic first-separation predicate. -/
def IsSquarefreePairFreshPrimeOwner (p m n : ℕ) : Prop :=
  p ∈ squarefreePairFreshPrimeSet m n ∧
    ∀ q ∈ squarefreePairFreshPrimeSet m n, p ≤ q

/-- The canonical least differing prime satisfies the intrinsic predicate. -/
theorem squarefreePairFreshPrimeOwner_isOwner
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    IsSquarefreePairFreshPrimeOwner (squarefreePairFreshPrimeOwner m n) m n := by
  have hne := squarefreePairFreshPrimeSet_nonempty hm hn hmn
  constructor
  · exact squarefreePairFreshPrimeOwner_mem hm hn hmn
  · intro q hq
    unfold squarefreePairFreshPrimeOwner
    rw [dif_pos hne]
    exact Finset.min'_le _ _ hq

/-- **Unique chronological ownership.**  Every distinct squarefree pair has one
and only one first separating Euler prime. -/
theorem existsUnique_squarefreePairFreshPrimeOwner
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    ∃! p : ℕ, IsSquarefreePairFreshPrimeOwner p m n := by
  refine ⟨squarefreePairFreshPrimeOwner m n,
    squarefreePairFreshPrimeOwner_isOwner hm hn hmn, ?_⟩
  intro p hp
  have hcanon := squarefreePairFreshPrimeOwner_isOwner hm hn hmn
  have hp_le := hp.2 (squarefreePairFreshPrimeOwner m n) hcanon.1
  have hc_le := hcanon.2 p hp.1
  omega

/-- Nonzero real Möbius weight forces squarefree support. -/
theorem squarefree_of_realMoebiusStep_ne_zero
    {n : ℕ} (hn : realMoebiusStep n ≠ 0) : Squarefree n := by
  apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
  intro hmu
  apply hn
  simp [realMoebiusStep, hmu]

private theorem prime_not_dvd_div_of_squarefree
    {p n : ℕ} (hp : p.Prime) (hn : Squarefree n) (hpn : p ∣ n) :
    ¬ p ∣ n / p := by
  intro hpd
  have hcancel : p * (n / p) = n := Nat.mul_div_cancel' hpn
  have hsqdiv : p * p ∣ n := by
    rcases hpd with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [← hcancel, hr]
    ring
  exact hp.not_isUnit (hn p hsqdiv)

/-- Remove `p` from a squarefree endpoint when present. -/
def squarefreePrimeFamilyParent (p n : ℕ) : ℕ :=
  if p ∣ n then n / p else n

/-- The stripped squarefree parent is fresh to `p`. -/
theorem squarefreePrimeFamilyParent_not_dvd
    {p n : ℕ} (hp : p.Prime) (hn : Squarefree n) :
    ¬ p ∣ squarefreePrimeFamilyParent p n := by
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · simp [hpn, prime_not_dvd_div_of_squarefree hp hn hpn]
  · simp [hpn]

/-- If `p` is present, adjoining it to the stripped parent reconstructs the
endpoint exactly. -/
theorem prime_mul_squarefreePrimeFamilyParent_eq
    {p n : ℕ} (hpn : p ∣ n) :
    p * squarefreePrimeFamilyParent p n = n := by
  simp [squarefreePrimeFamilyParent, hpn, Nat.mul_div_cancel' hpn]

/-- If `p` is absent, stripping does nothing. -/
theorem squarefreePrimeFamilyParent_eq_of_not_dvd
    {p n : ℕ} (hpn : ¬ p ∣ n) :
    squarefreePrimeFamilyParent p n = n := by
  simp [squarefreePrimeFamilyParent, hpn]

private theorem primeFace_mem_iff_dvd
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    p ∈ squarefreePrimeFace n ↔ p ∣ n := by
  constructor
  · intro h
    exact (Nat.mem_primeFactors.mp (by
      simpa [squarefreePrimeFace] using h)).2.1
  · intro h
    have hmem : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, h, hn.ne'⟩
    simpa [squarefreePrimeFace] using hmem

/-- The owner divides exactly one endpoint. -/
theorem squarefreePairFreshPrimeOwner_dvd_xor
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (hmpos : 0 < m) (hnpos : 0 < n) :
    (squarefreePairFreshPrimeOwner m n ∣ m ∧
      ¬ squarefreePairFreshPrimeOwner m n ∣ n) ∨
    (squarefreePairFreshPrimeOwner m n ∣ n ∧
      ¬ squarefreePairFreshPrimeOwner m n ∣ m) := by
  have hp := squarefreePairFreshPrimeOwner_prime hm hn hmn
  rcases squarefreePairFreshPrimeOwner_xor hm hn hmn with h | h
  · left
    exact ⟨(primeFace_mem_iff_dvd hp hmpos).mp h.1,
      fun hd => h.2 ((primeFace_mem_iff_dvd hp hnpos).mpr hd)⟩
  · right
    exact ⟨(primeFace_mem_iff_dvd hp hnpos).mp h.1,
      fun hd => h.2 ((primeFace_mem_iff_dvd hp hmpos).mpr hd)⟩

/-- **Fresh-parent cube realization.**  The unique owner strips both endpoints
to `p`-free parents, and the physical pair is exactly one of the two mixed
corners obtained by adjoining `p` to one parent. -/
theorem squarefreePairFreshPrimeOwner_parentCube
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (hmpos : 0 < m) (hnpos : 0 < n) :
    let p := squarefreePairFreshPrimeOwner m n
    (¬ p ∣ squarefreePrimeFamilyParent p m) ∧
    (¬ p ∣ squarefreePrimeFamilyParent p n) ∧
      ((m = p * squarefreePrimeFamilyParent p m ∧
          n = squarefreePrimeFamilyParent p n) ∨
       (m = squarefreePrimeFamilyParent p m ∧
          n = p * squarefreePrimeFamilyParent p n)) := by
  let p := squarefreePairFreshPrimeOwner m n
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hm hn hmn
  have hfreshM : ¬ p ∣ squarefreePrimeFamilyParent p m :=
    squarefreePrimeFamilyParent_not_dvd hp hm
  have hfreshN : ¬ p ∣ squarefreePrimeFamilyParent p n :=
    squarefreePrimeFamilyParent_not_dvd hp hn
  refine ⟨hfreshM, hfreshN, ?_⟩
  rcases squarefreePairFreshPrimeOwner_dvd_xor hm hn hmn hmpos hnpos with h | h
  · left
    refine ⟨?_, (squarefreePrimeFamilyParent_eq_of_not_dvd h.2).symm⟩
    exact (prime_mul_squarefreePrimeFamilyParent_eq h.1).symm
  · right
    refine ⟨(squarefreePrimeFamilyParent_eq_of_not_dvd h.2).symm, ?_⟩
    exact (prime_mul_squarefreePrimeFamilyParent_eq h.1).symm

/-- Owner-projector expansion of one physical Möbius pair over all primes up to
`X`. -/
def squarefreePairFreshPrimeOwnerExpansion (X m n : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo X,
    if IsSquarefreePairFreshPrimeOwner p m n then
      realMoebiusStep m * realMoebiusStep n
    else 0

/-- **One atom, one prime.**  Every physical positive-lag Möbius pair is
reconstructed exactly once by its chronological owner projector. -/
theorem squarefreePairFreshPrimeOwnerExpansion_eq_pairWeight
    {X m n : ℕ} (hmn : m < n) (hnX : n ≤ X) :
    squarefreePairFreshPrimeOwnerExpansion X m n =
      realMoebiusStep m * realMoebiusStep n := by
  by_cases hm0 : realMoebiusStep m = 0
  · simp [squarefreePairFreshPrimeOwnerExpansion, hm0]
  by_cases hn0 : realMoebiusStep n = 0
  · simp [squarefreePairFreshPrimeOwnerExpansion, hn0]
  have hmsq := squarefree_of_realMoebiusStep_ne_zero hm0
  have hnsq := squarefree_of_realMoebiusStep_ne_zero hn0
  have hmpos : 0 < m := by
    by_contra h
    have hmz : m = 0 := by omega
    subst m
    simp [realMoebiusStep] at hm0
  have hnpos : 0 < n := lt_trans hmpos hmn
  let p := squarefreePairFreshPrimeOwner m n
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hmsq hnsq (by omega)
  have hpown : IsSquarefreePairFreshPrimeOwner p m n :=
    squarefreePairFreshPrimeOwner_isOwner hmsq hnsq (by omega)
  have hpX : p ≤ X := by
    rcases squarefreePairFreshPrimeOwner_dvd_xor
        hmsq hnsq (by omega) hmpos hnpos with h | h
    · exact (Nat.le_of_dvd hmpos h.1).trans (hmn.le.trans hnX)
    · exact (Nat.le_of_dvd hnpos h.1).trans hnX
  have hpP : p ∈ primesUpTo X := mem_primesUpTo.mpr ⟨hp, hpX⟩
  unfold squarefreePairFreshPrimeOwnerExpansion
  rw [Finset.sum_eq_single p]
  · rw [if_pos hpown]
  · intro q _hqP hqp
    have hnot : ¬ IsSquarefreePairFreshPrimeOwner q m n := by
      intro hqown
      have hq_le : q ≤ p := hqown.2 p hpown.1
      have hp_le : p ≤ q := hpown.2 q hqown.1
      exact hqp (by omega)
    rw [if_neg hnot]
  · exact fun hnot => (hnot hpP).elim

/-- Sum every physical run pair after projecting it to its unique owner prime. -/
def squareRunFreshPrimeOwnedCovariance (a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
    ∑ m ∈ Finset.Ico (a ^ 2) n,
      squarefreePairFreshPrimeOwnerExpansion ((b + 1) ^ 2) m n

/-- **Global no-overlap ownership theorem.**  The entire square-run covariance
carrier is exactly the sum of the unique fresh-prime owner projectors.  No
physical covariance atom is omitted or counted twice. -/
theorem squareRunFreshPrimeOwnedCovariance_eq_covariance
    {a b : ℕ} (hab : a ≤ b) :
    squareRunFreshPrimeOwnedCovariance a b = squareRunCovariance a b := by
  rw [squareRunCovariance_eq_physicalPairCovariance hab]
  unfold squareRunFreshPrimeOwnedCovariance squareRunPhysicalPairCovariance
  apply Finset.sum_congr rfl
  intro n hn
  have hnTop : n ≤ (b + 1) ^ 2 := (Finset.mem_Ico.mp hn).2.le
  apply Finset.sum_congr rfl
  intro m hm
  exact squarefreePairFreshPrimeOwnerExpansion_eq_pairWeight
    (Finset.mem_Ico.mp hm).2 hnTop

end RHLean.Analysis
