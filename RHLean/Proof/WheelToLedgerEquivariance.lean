import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime
import RHLean.Geometry.ComplexSquareRecovery
import RHLean.Proof.SquareRootAncestryParentFibres

/-!
# Wheel-to-ledger equivariance

This module isolates the exact finite seam between the prime-wheel fresh-prime
mechanics and the canonical square-root ancestry flow.  No analytic estimate,
zero-free region, or Strong Mertens input appears here.

The carrier is the factor pair `(q,c)`.  Fermat coordinates send that pair to a
complex point whose squared real coordinate is `c*q`, while the ancestry source
represents exactly `q*c`.  The only nontrivial issue is the move: the ancestry
parent strips the *largest* prime factor of the core, whereas the abstract wheel
fresh-prime insertion can adjoin a fresh core prime in any order.

Consequently unrestricted fresh-prime equivariance is false.  It becomes exact
precisely on the ordered submove in which the newly adjoined prime is larger
than every prime already present in the parent core.  This is the chronological
Eulerian prime-extension rule needed by the transport bridge.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Geometry
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

/-- A wheel factor configuration carried by the same canonical factor data as
one ancestry source, but before packaging it as a bounded `SourceIndex`. -/
structure WheelFactorConfiguration (B : ℕ) where
  q : ℕ
  c : ℕ
  data : CanonicalSourceData q c
  q_lt : q < B + 1
  c_lt : c < B + 1

/-- Physical product represented by one wheel factor configuration. -/
def wheelProduct {B : ℕ} (x : WheelFactorConfiguration B) : ℕ :=
  x.q * x.c

/-- Whole-source signed wheel weight. -/
def wheelSignedWeight {B : ℕ} (x : WheelFactorConfiguration B) : ℤ :=
  μ (wheelProduct x)

/-- Package the factor pair into the bounded ancestry carrier. -/
def wheelToSource {B : ℕ} (x : WheelFactorConfiguration B) : SourceIndex B :=
  (⟨x.q, x.q_lt⟩, ⟨x.c, x.c_lt⟩)

@[simp] theorem sourcePrime_wheelToSource {B : ℕ}
    (x : WheelFactorConfiguration B) :
    sourcePrime (wheelToSource x) = x.q := rfl

@[simp] theorem sourceCore_wheelToSource {B : ℕ}
    (x : WheelFactorConfiguration B) :
    sourceCore (wheelToSource x) = x.c := rfl

/-- The factor carrier is an admissible ancestry source. -/
theorem wheelToSource_admissible {B : ℕ}
    (x : WheelFactorConfiguration B) :
    SourceAdmissible (wheelToSource x) := by
  exact x.data

/-- Product preservation on the real ancestry carrier. -/
@[simp] theorem sourceProduct_wheelToSource {B : ℕ}
    (x : WheelFactorConfiguration B) :
    sourceProduct (wheelToSource x) = wheelProduct x := rfl

/-- The explicit `C -> R` realization: the real coordinate after squaring the
Fermat point is exactly the product carried by the ancestry source. -/
theorem fermatSqReal_eq_sourceProduct {B : ℕ}
    (x : WheelFactorConfiguration B) :
    ((fermatPoint (x.c : ℝ) (x.q : ℝ)) ^ 2).re =
      (sourceProduct (wheelToSource x) : ℝ) := by
  rw [fermatPoint_sq_re, sourceProduct_wheelToSource]
  simp [wheelProduct, Nat.cast_mul, mul_comm]

/-- Whole-source weight preservation. -/
theorem sourceWeight_wheelToSource {B : ℕ}
    (x : WheelFactorConfiguration B) :
    sourceWeight (wheelToSource x) = wheelSignedWeight x := by
  rw [sourceWeight_of_admissible _ (wheelToSource_admissible x)]
  rfl

/-- Relative to the raw cofactor weight `mu(c)`, the fixed distinguished prime
contributes the expected single sign. -/
theorem sourceWeight_wheelToSource_eq_neg_cofactor {B : ℕ}
    (x : WheelFactorConfiguration B) :
    sourceWeight (wheelToSource x) = -(μ x.c : ℤ) := by
  rw [sourceWeight_of_admissible _ (wheelToSource_admissible x)]
  change (μ (x.q * x.c) : ℤ) = -(μ x.c : ℤ)
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    x.data.2.2.2.1]
  rw [ArithmeticFunction.moebius_apply_prime x.data.1]
  ring

/-- Exact finite-boundary compatibility.  The physical product cutoff and the
ancestry square-root clock are the same condition. -/
theorem wheelToSource_clock_iff_product_cutoff
    {B R : ℕ} (hR : 1 ≤ R) (x : WheelFactorConfiguration B) :
    sourceClock B (wheelToSource x) ≤ R - 1 ↔
      wheelProduct x ≤ squareRootEndpoint R := by
  rw [sourceClock_le_iff_sourceProduct_le_endpoint,
    squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR]
  rfl

/-- One abstract fresh-prime move on a fixed distinguished-prime fibre.  This
is the multiplicative core branch `c -> c*p` underlying the wheel insertion
identity. -/
structure WheelFreshPrimeMove (B : ℕ) where
  parent : WheelFactorConfiguration B
  child : WheelFactorConfiguration B
  freshPrime : ℕ
  freshPrime_prime : freshPrime.Prime
  same_distinguished : child.q = parent.q
  child_core : child.c = parent.c * freshPrime
  fresh : ¬ freshPrime ∣ parent.c
  child_smooth : child.q < child.c

namespace WheelFreshPrimeMove

/-- The chronological Eulerian submove: the newly adjoined core prime is larger
than every prime already present in the parent core. -/
def Ordered {B : ℕ} (m : WheelFreshPrimeMove B) : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ m.parent.c → r < m.freshPrime

/-- The child is a legal smooth-oriented ancestry state. -/
theorem child_smoothOriented {B : ℕ} (m : WheelFreshPrimeMove B) :
    SmoothOriented (wheelToSource m.child) := by
  exact ⟨wheelToSource_admissible m.child, by simpa using m.child_smooth⟩

/-- Parent equivariance is equivalent to the ancestry cofactor being the wheel
parent core. -/
theorem sourceParent_eq_parent_iff_cofactor {B : ℕ}
    (m : WheelFreshPrimeMove B) :
    sourceParent (wheelToSource m.child) = some (wheelToSource m.parent) ↔
      canonicalCofactor m.child.c = m.parent.c := by
  let hs : SmoothOriented (wheelToSource m.child) := child_smoothOriented m
  rw [smoothSource_has_parent (wheelToSource m.child) hs]
  constructor
  · intro h
    have hidx :
        parentIndex (wheelToSource m.child) hs = wheelToSource m.parent :=
      Option.some.inj h
    have hc := congrArg (fun s => sourceCore s) hidx
    simpa using hc
  · intro hc
    apply congrArg some
    apply Prod.ext
    · apply Fin.ext
      change m.child.q = m.parent.q
      exact m.same_distinguished
    · apply Fin.ext
      change canonicalCofactor m.child.c = m.parent.c
      exact hc

/-- For a fresh multiplicative core step, recovering the wheel parent core is
exactly the assertion that the inserted prime is the canonical largest prime of
the child core. -/
theorem cofactor_eq_parent_iff_inserted_is_top {B : ℕ}
    (m : WheelFreshPrimeMove B) :
    canonicalCofactor m.child.c = m.parent.c ↔
      canonicalLargestPrimeFactor m.child.c = m.freshPrime := by
  have hchildgt : 1 < m.child.c :=
    lt_trans m.child.data.1.one_lt m.child_smooth
  have hfactor := canonicalCofactor_mul_largestPrimeFactor hchildgt
  constructor
  · intro hc
    exact Nat.mul_left_cancel m.parent.data.2.1 <| by
      calc
        m.parent.c * canonicalLargestPrimeFactor m.child.c =
            canonicalCofactor m.child.c *
              canonicalLargestPrimeFactor m.child.c := by rw [hc]
        _ = m.child.c := hfactor
        _ = m.parent.c * m.freshPrime := m.child_core
  · intro hp
    exact Nat.mul_right_cancel m.freshPrime_prime.pos <| by
      calc
        canonicalCofactor m.child.c * m.freshPrime =
            canonicalCofactor m.child.c *
              canonicalLargestPrimeFactor m.child.c := by rw [hp]
        _ = m.child.c := hfactor
        _ = m.parent.c * m.freshPrime := m.child_core

/-- The inserted prime is the canonical top core prime exactly when the fresh
prime was adjoined in increasing prime order. -/
theorem inserted_is_top_iff_ordered {B : ℕ}
    (m : WheelFreshPrimeMove B) :
    canonicalLargestPrimeFactor m.child.c = m.freshPrime ↔ Ordered m := by
  have hchildgt : 1 < m.child.c :=
    lt_trans m.child.data.1.one_lt m.child_smooth
  constructor
  · intro htop r hr hrc
    have hrchild : r ∣ m.child.c := by
      rw [m.child_core]
      exact dvd_mul_of_dvd_left hrc m.freshPrime
    have hrle :=
      prime_dvd_le_canonicalLargestPrimeFactor hchildgt hr hrchild
    rw [htop] at hrle
    have hrne : r ≠ m.freshPrime := by
      intro heq
      subst r
      exact m.fresh hrc
    omega
  · intro hord
    have hpdiv : m.freshPrime ∣ m.child.c := by
      refine ⟨m.parent.c, ?_⟩
      rw [m.child_core]
      exact Nat.mul_comm _ _
    have hple :=
      prime_dvd_le_canonicalLargestPrimeFactor hchildgt
        m.freshPrime_prime hpdiv
    have hlpfPrime := canonicalLargestPrimeFactor_prime hchildgt
    have hlpfDvd := canonicalLargestPrimeFactor_dvd hchildgt
    have hlpfDvdProd :
        canonicalLargestPrimeFactor m.child.c ∣
          m.parent.c * m.freshPrime := by
      rw [← m.child_core]
      exact hlpfDvd
    rcases hlpfPrime.dvd_mul.mp hlpfDvdProd with hc | hp
    · have hlt := hord _ hlpfPrime hc
      omega
    · rcases m.freshPrime_prime.eq_one_or_self_of_dvd
        (canonicalLargestPrimeFactor m.child.c) hp with hone | heq
      · exact (hlpfPrime.ne_one hone).elim
      · exact heq

/-- **Exact equivariance criterion.**  The generic fresh-prime wheel move maps
to the canonical ancestry parent edge if and only if it is the chronological
ordered fresh-prime submove. -/
theorem sourceParent_eq_parent_iff_ordered {B : ℕ}
    (m : WheelFreshPrimeMove B) :
    sourceParent (wheelToSource m.child) = some (wheelToSource m.parent) ↔
      Ordered m := by
  rw [sourceParent_eq_parent_iff_cofactor,
    cofactor_eq_parent_iff_inserted_is_top,
    inserted_is_top_iff_ordered]

/-- The commuting square on the legal chronological wheel move. -/
theorem wheelToLedger_parent_equivariant {B : ℕ}
    (m : WheelFreshPrimeMove B) (hord : Ordered m) :
    sourceParent (wheelToSource m.child) = some (wheelToSource m.parent) :=
  (sourceParent_eq_parent_iff_ordered m).2 hord

/-- Weight reversal is transported for free once the parent square commutes. -/
theorem wheelSignedWeight_reversal_of_ordered {B : ℕ}
    (m : WheelFreshPrimeMove B) (hord : Ordered m) :
    wheelSignedWeight m.child = -wheelSignedWeight m.parent := by
  rw [← sourceWeight_wheelToSource, ← sourceWeight_wheelToSource]
  exact sourceWeight_signReversal _ _
    (wheelToLedger_parent_equivariant m hord)

/-- Explicit obstruction to unrestricted equivariance: if the parent core
already contains a prime larger than the newly inserted fresh prime, the wheel
move cannot be the ancestry parent edge. -/
theorem not_parent_equivariant_of_larger_parent_prime
    {B : ℕ} (m : WheelFreshPrimeMove B) {r : ℕ}
    (hr : r.Prime) (hrc : r ∣ m.parent.c) (hpr : m.freshPrime < r) :
    sourceParent (wheelToSource m.child) ≠ some (wheelToSource m.parent) := by
  intro heq
  have hord := (sourceParent_eq_parent_iff_ordered m).1 heq
  have hlt := hord r hr hrc
  omega

end WheelFreshPrimeMove

/-- Concrete admissible parent for the smallest nonordered counterexample. -/
def wheelFreshPrimeCounterexampleParent : WheelFactorConfiguration 70 where
  q := 7
  c := 5
  data := by
    refine ⟨by norm_num, by norm_num, ?_, by norm_num, ?_⟩
    · exact (show Nat.Prime 5 by norm_num).squarefree
    · intro p _hp hpd
      have hple : p ≤ 5 := Nat.le_of_dvd (by norm_num) hpd
      omega
  q_lt := by norm_num
  c_lt := by norm_num

/-- Concrete admissible smooth child for the same counterexample. -/
def wheelFreshPrimeCounterexampleChild : WheelFactorConfiguration 70 where
  q := 7
  c := 10
  data := by
    refine ⟨by norm_num, by norm_num, ?_, by norm_num, ?_⟩
    · have h2 : Squarefree 2 := (show Nat.Prime 2 by norm_num).squarefree
      have h5 : Squarefree 5 := (show Nat.Prime 5 by norm_num).squarefree
      have hcop : Nat.Coprime 2 5 := by norm_num
      simpa using (Nat.squarefree_mul hcop).2 ⟨h2, h5⟩
    · intro p hp hpd
      have hpd' : p ∣ 2 * 5 := by simpa using hpd
      rcases hp.dvd_mul.mp hpd' with h2 | h5
      · rcases (Nat.dvd_prime (show Nat.Prime 2 by norm_num)).mp h2 with hp1 | hp2
        · exact (hp.ne_one hp1).elim
        · subst p
          norm_num
      · rcases (Nat.dvd_prime (show Nat.Prime 5 by norm_num)).mp h5 with hp1 | hp5
        · exact (hp.ne_one hp1).elim
        · subst p
          norm_num
  q_lt := by norm_num
  c_lt := by norm_num

/-- The unrestricted wheel insertion `5 -> 5*2` is fresh but not chronological. -/
def wheelFreshPrimeCounterexample : WheelFreshPrimeMove 70 where
  parent := wheelFreshPrimeCounterexampleParent
  child := wheelFreshPrimeCounterexampleChild
  freshPrime := 2
  freshPrime_prime := by norm_num
  same_distinguished := rfl
  child_core := by
    change 10 = 5 * 2
    norm_num
  fresh := by
    change ¬ 2 ∣ 5
    norm_num
  child_smooth := by
    change 7 < 10
    norm_num

/-- **Refutation of unrestricted equivariance.**  For `(q,c,p) = (7,5,2)`, the
wheel move appends a genuinely fresh prime, but ancestry strips `5`, the largest
prime of the child core `10`, rather than the newly appended `2`. -/
theorem unrestricted_wheelFreshPrime_parent_equivariance_fails :
    sourceParent (wheelToSource wheelFreshPrimeCounterexample.child) ≠
      some (wheelToSource wheelFreshPrimeCounterexample.parent) := by
  exact WheelFreshPrimeMove.not_parent_equivariant_of_larger_parent_prime
    wheelFreshPrimeCounterexample (r := 5)
    (by norm_num)
    (by change 5 ∣ 5; simp)
    (by change 2 < 5; norm_num)

end RHLean.Proof
