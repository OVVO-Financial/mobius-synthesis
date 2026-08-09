import Mathlib
import RHLean.Proof.CanonicalGapPrefixGram

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryFlow

open BalancedCanonicalGap

/-!
# Canonical prime-extension ancestry flow

This module records the exact arithmetic mechanism suggested by the balanced/
extreme cancellation scan. A smooth-oriented source is represented as a legal
prime extension of a transport-oriented parent. The extension reverses the
Möbius sign, while the parent and child enter the square-prefix process at their
own integer-square-root clocks.

The final sections derive a concrete finite-parent renewal equation and isolate
the abstract finite renewal algebra

```text
V = U - S V,
```

without asserting the still-open analytic estimate for its square-block
pushforward.
-/

/-- `p` is the unique largest prime in the factorization `a * p`: it is prime,
coprime to the remaining core, and strictly dominates every prime divisor of the
remaining core. -/
structure CoreMaxPrime (p a : ℕ) : Prop where
  prime : p.Prime
  coprime : Nat.Coprime p a
  dominates : ∀ r : ℕ, r.Prime → r ∣ a → r < p

/-- An extreme transport-oriented source `q * a`. The distinguished prime `q`
dominates the core and the geometric condition `2a ≤ q` places the unordered
factor pair in the extreme region. -/
structure ExtremeTransportParent (q a : ℕ) : Prop where
  coprime : Nat.Coprime q a
  dominant : DominantPrime q a
  extreme : 2 * a ≤ q

/-- A legal prime extension of the core `a` below the distinguished prime `q`. -/
structure LegalExtension (q a p : ℕ) : Prop where
  coreMax : CoreMaxPrime p a
  coprimeParent : Nat.Coprime p (q * a)
  belowDistinguished : p < q

/-- A balanced born-smooth child `q * (a*p)` obtained from the extreme transport
parent `q*a`. The inequalities `q < ap < 2q` are exactly the balanced
born-smooth geometry after the extension. -/
structure BornSmoothChild (q a p : ℕ) : Prop where
  parent : ExtremeTransportParent q a
  extension : LegalExtension q a p
  entersSmooth : q < a * p
  remainsBalanced : a * p < 2 * q

/-- Expanded characterization of a legal born-smooth child. -/
theorem bornSmoothChild_iff (q a p : ℕ) :
    BornSmoothChild q a p ↔
      ExtremeTransportParent q a ∧ LegalExtension q a p ∧
        q < a * p ∧ a * p < 2 * q := by
  constructor
  · intro h
    exact ⟨h.parent, h.extension, h.entersSmooth, h.remainsBalanced⟩
  · rintro ⟨hparent, hextension, hlo, hhi⟩
    exact ⟨hparent, hextension, hlo, hhi⟩

/-- Stripping the extension prime from a legal born-smooth child recovers its
extreme transport parent. -/
theorem bornSmoothChild_parent {q a p : ℕ} (h : BornSmoothChild q a p) :
    ExtremeTransportParent q a := h.parent

/-- The stripped parent lies on the extreme side of the gap boundary. -/
theorem parent_extreme_gap {q a p : ℕ} (h : BornSmoothChild q a p) :
    a ≤ q - a := by
  have hext : 2 * a ≤ q := h.parent.extreme
  omega

/-- The stripped parent is a canonical unordered factor pair. -/
theorem parent_canonicalPair {q a p : ℕ} (h : BornSmoothChild q a p) :
    CanonicalPair a (q - a) := by
  have hext : 2 * a ≤ q := h.parent.extreme
  have haq : a ≤ q := by omega
  have hadd : a + (q - a) = q := Nat.add_sub_of_le haq
  unfold CanonicalPair
  simpa [hadd] using
    (And.intro h.parent.coprime.symm (Or.inl h.parent.dominant))

/-- The extended child lies in the balanced gap region. -/
theorem child_balancedGap {q a p : ℕ} (h : BornSmoothChild q a p) :
    BalancedGap q (a * p - q) := by
  have hlo : q < a * p := h.entersSmooth
  have hhi : a * p < 2 * q := h.remainsBalanced
  constructor <;> omega

/-- The extended child is a canonical unordered factor pair. -/
theorem child_canonicalPair {q a p : ℕ} (h : BornSmoothChild q a p) :
    CanonicalPair q (a * p - q) := by
  have hqpos : 1 ≤ q := h.parent.dominant.1.one_le
  apply (canonicalPair_iff_endpoint_prime hqpos (child_balancedGap h)).2
  exact Or.inl h.parent.dominant.1

/-- **Exact ancestry sign reversal.** Adjoining the legal extension prime changes
the Möbius sign and nothing else. -/
theorem child_weight_eq_neg_parent {q a p : ℕ} (h : BornSmoothChild q a p) :
    (μ (q * (a * p)) : ℤ) = -(μ (q * a) : ℤ) := by
  calc
    (μ (q * (a * p)) : ℤ) = μ ((q * a) * p) := by
      congr 1
      ring
    _ = (μ (q * a) : ℤ) * μ p :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        h.extension.coprimeParent.symm
    _ = -(μ (q * a) : ℤ) := by
      rw [ArithmeticFunction.moebius_apply_prime h.extension.coreMax.prime]
      ring

/-- The largest extension prime in a factorization is unique. -/
theorem coreMaxPrime_unique_factor {a a' p p' : ℕ}
    (hp : CoreMaxPrime p a) (hp' : CoreMaxPrime p' a')
    (hprod : a * p = a' * p') : p = p' := by
  have hpdiv : p ∣ a' * p' := by
    rw [← hprod]
    exact ⟨a, by simp [Nat.mul_comm]⟩
  have hp_le : p ≤ p' := by
    rcases hp.prime.dvd_mul.mp hpdiv with hpa' | hpp'
    · exact (hp'.dominates p hp.prime hpa').le
    · exact Nat.le_of_dvd hp'.prime.pos hpp'
  have hp'div : p' ∣ a * p := by
    rw [hprod]
    exact ⟨a', by simp [Nat.mul_comm]⟩
  have hp'_le : p' ≤ p := by
    rcases hp'.prime.dvd_mul.mp hp'div with hp'a | hp'p
    · exact (hp.dominates p' hp'.prime hp'a).le
    · exact Nat.le_of_dvd hp.prime.pos hp'p
  exact Nat.le_antisymm hp_le hp'_le

/-- `a,p` is a legal smooth-parent witness for the child core `c`. -/
def IsSmoothParent (q c a p : ℕ) : Prop :=
  c = a * p ∧ BornSmoothChild q a p

/-- The legal smooth parent and its stripped extension prime are unique. -/
theorem smoothParent_unique {q c a a' p p' : ℕ}
    (h : IsSmoothParent q c a p) (h' : IsSmoothParent q c a' p') :
    a = a' ∧ p = p' := by
  have hprod : a * p = a' * p' := by
    calc
      a * p = c := h.1.symm
      _ = a' * p' := h'.1
  have hp : p = p' :=
    coreMaxPrime_unique_factor h.2.extension.coreMax
      h'.2.extension.coreMax hprod
  have ha_mul : a * p = a' * p := by simpa [hp] using hprod
  have ha : a = a' :=
    Nat.mul_right_cancel h.2.extension.coreMax.prime.pos ha_mul
  exact ⟨ha, hp⟩

/-! ## Distinct parent and child clocks -/

/-- Integer-square-root entry clock of the transport parent. -/
def parentClock (q a : ℕ) : ℕ := Nat.sqrt (q * a)

/-- Integer-square-root entry clock of the extended smooth child. -/
def childClock (q a p : ℕ) : ℕ := Nat.sqrt (q * (a * p))

/-- A legal extension never enters before its parent. -/
theorem parentClock_le_childClock {q a p : ℕ} (h : BornSmoothChild q a p) :
    parentClock q a ≤ childClock q a p := by
  apply Nat.sqrt_le_sqrt
  have ha : a ≤ a * p :=
    Nat.le_mul_of_pos_right a h.extension.coreMax.prime.pos
  exact Nat.mul_le_mul_left q ha

/-- Integer-valued indicator. -/
def indicator (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

/-- Combined parent/child contribution at square-prefix clock `x`. -/
def ancestryPairValue (q a p x : ℕ) : ℤ :=
  (μ (q * a) : ℤ) * indicator (parentClock q a ≤ x) +
    (μ (q * (a * p)) : ℤ) * indicator (childClock q a p ≤ x)

/-- The parent and its opposite-signed child form one exact activity interval. -/
theorem ancestryPairValue_eq_interval {q a p x : ℕ}
    (h : BornSmoothChild q a p) :
    ancestryPairValue q a p x =
      (μ (q * a) : ℤ) *
        indicator (parentClock q a ≤ x ∧ x < childClock q a p) := by
  unfold ancestryPairValue
  rw [child_weight_eq_neg_parent h]
  have hclock := parentClock_le_childClock h
  by_cases hp : parentClock q a ≤ x
  · by_cases hc : childClock q a p ≤ x
    · simp [indicator, hp, hc]
    · have hxlt : x < childClock q a p := Nat.lt_of_not_ge hc
      simp [indicator, hp, hc, hxlt]
  · have hc : ¬childClock q a p ≤ x := by omega
    simp [indicator, hp, hc]

/-- The ancestry pair contributes nothing before the parent enters. -/
theorem ancestryPairValue_eq_zero_before_parent {q a p x : ℕ}
    (h : BornSmoothChild q a p) (hx : x < parentClock q a) :
    ancestryPairValue q a p x = 0 := by
  rw [ancestryPairValue_eq_interval h]
  simp [indicator]
  omega

/-- The ancestry pair contributes nothing after the child has entered. -/
theorem ancestryPairValue_eq_zero_after_child {q a p x : ℕ}
    (h : BornSmoothChild q a p) (hx : childClock q a p ≤ x) :
    ancestryPairValue q a p x = 0 := by
  rw [ancestryPairValue_eq_interval h]
  simp [indicator, hx]

/-- Inside the parent-child activity interval the pair contributes exactly the
parent Möbius weight. -/
theorem ancestryPairValue_eq_parent_weight {q a p x : ℕ}
    (h : BornSmoothChild q a p)
    (hleft : parentClock q a ≤ x) (hright : x < childClock q a p) :
    ancestryPairValue q a p x = (μ (q * a) : ℤ) := by
  rw [ancestryPairValue_eq_interval h]
  simp [indicator, hleft, hright]

/-- The same interval identity on a shifted square-block window. -/
theorem ancestryPairValue_window {q a p N r : ℕ}
    (h : BornSmoothChild q a p) :
    ancestryPairValue q a p (N + r) =
      (μ (q * a) : ℤ) *
        indicator (parentClock q a ≤ N + r ∧ N + r < childClock q a p) :=
  ancestryPairValue_eq_interval h

/-- Exact decomposition of an activity interval relative to a window origin.
The three terms are: activity already open at `N`, an opening after `N`, and a
closing after `N`. -/
theorem activityIndicator_window_decomposition {s t N r : ℕ} (hst : s ≤ t) :
    indicator (s ≤ N + r ∧ N + r < t) =
      indicator (s ≤ N ∧ N < t) +
      indicator (N < s ∧ s ≤ N + r) -
      indicator (N < t ∧ t ≤ N + r) := by
  by_cases hsn : s ≤ N <;>
  by_cases hnt : N < t <;>
  by_cases hsr : s ≤ N + r <;>
  by_cases hrt : N + r < t <;>
  by_cases hns : N < s <;>
  by_cases htr : t ≤ N + r <;>
  simp [indicator, hsn, hnt, hsr, hrt, hns, htr] <;> omega

/-- Exact window-boundary decomposition of one legal ancestry edge. -/
theorem ancestryPairValue_window_decomposition {q a p N r : ℕ}
    (h : BornSmoothChild q a p) :
    ancestryPairValue q a p (N + r) =
      (μ (q * a) : ℤ) *
          indicator (parentClock q a ≤ N ∧ N < childClock q a p) +
      (μ (q * a) : ℤ) *
          indicator (N < parentClock q a ∧ parentClock q a ≤ N + r) -
      (μ (q * a) : ℤ) *
          indicator (N < childClock q a p ∧ childClock q a p ≤ N + r) := by
  rw [ancestryPairValue_window h]
  rw [activityIndicator_window_decomposition (parentClock_le_childClock h)]
  ring

/-! ## Concrete finite-parent renewal equation -/

section FiniteParentFlow

variable {ι : Type*} [Fintype ι]

/-- A finite signed field with at most one parent per node and exact sign reversal
along every parent edge. -/
structure ParentFlow (ι : Type*) [Fintype ι] where
  parent : ι → Option ι
  weight : ι → ℤ
  signReversal : ∀ i p, parent i = some p → weight i = -weight p

namespace ParentFlow

/-- Restriction of the field to root nodes. -/
def rootField (F : ParentFlow ι) : ι → ℤ := fun i =>
  match F.parent i with
  | none => F.weight i
  | some _ => 0

/-- Pull a field from the unique parent of each nonroot node. -/
def successorOperator (F : ParentFlow ι) : (ι → ℤ) →+ (ι → ℤ) where
  toFun f i :=
    match F.parent i with
    | none => 0
    | some p => f p
  map_zero' := by
    funext i
    cases F.parent i <;> rfl
  map_add' f g := by
    funext i
    simp only [Pi.add_apply]
    cases F.parent i <;> rfl

/-- The exact finite successor reindexing: roots minus the parent pullback. -/
theorem weight_eq_root_sub_successor (F : ParentFlow ι) :
    F.weight = rootField F - successorOperator F F.weight := by
  funext i
  cases hparent : F.parent i with
  | none => simp [rootField, successorOperator, hparent]
  | some p =>
      have hsign := F.signReversal i p hparent
      simp [rootField, successorOperator, hparent, hsign]

/-- Push a finite signed field through arbitrary integer clocks. -/
def clockPushforward (clock : ι → ℕ) (x : ℕ) : (ι → ℤ) →+ ℤ where
  toFun f := ∑ i, if clock i ≤ x then f i else 0
  map_zero' := by simp
  map_add' f g := by
    classical
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hix : clock i ≤ x <;> simp [hix]

/-- The renewal equation survives every square-block or other clock pushforward
without changing the clocks. -/
theorem clockPushforward_renewal (F : ParentFlow ι)
    (clock : ι → ℕ) (x : ℕ) :
    clockPushforward clock x F.weight =
      clockPushforward clock x (rootField F) -
        clockPushforward clock x (successorOperator F F.weight) := by
  have hfield := weight_eq_root_sub_successor F
  calc
    clockPushforward clock x F.weight =
        clockPushforward clock x
          (rootField F - successorOperator F F.weight) :=
      congrArg (fun v => clockPushforward clock x v) hfield
    _ = clockPushforward clock x (rootField F) -
          clockPushforward clock x (successorOperator F F.weight) :=
      map_sub (clockPushforward clock x) (rootField F)
        (successorOperator F F.weight)

end ParentFlow

end FiniteParentFlow

/-! ## Abstract successor renewal algebra -/

section Renewal

variable {M : Type*} [AddCommGroup M]

/-- The smooth-oriented field generated by the successor operator. -/
def successorSmoothField (S : M →+ M) (V : M) : M := -S V

/-- Recursive alternating partial sum `U - S U + S² U - ...`. -/
def alternatingPrefix (S : M →+ M) (U : M) : ℕ → M
  | 0 => 0
  | n + 1 => U - S (alternatingPrefix S U n)

/-- The signed unresolved tail after the same number of generations. -/
def alternatingTail (S : M →+ M) (V : M) : ℕ → M
  | 0 => V
  | n + 1 => -S (alternatingTail S V n)

/-- `V = U - S V` is equivalently root field plus the smooth successor field. -/
theorem renewal_eq_root_add_smooth {S : M →+ M} {U V : M}
    (hrenew : V = U - S V) :
    V = U + successorSmoothField S V := by
  simpa [successorSmoothField, sub_eq_add_neg] using hrenew

/-- Exact finite renewal identity with its unresolved terminal generation. -/
theorem alternatingPrefix_add_tail {S : M →+ M} {U V : M}
    (hrenew : V = U - S V) (depth : ℕ) :
    alternatingPrefix S U depth + alternatingTail S V depth = V := by
  induction depth with
  | zero => simp [alternatingPrefix, alternatingTail]
  | succ n ih =>
      simp only [alternatingPrefix, alternatingTail]
      calc
        (U - S (alternatingPrefix S U n)) +
              -S (alternatingTail S V n) =
            U - S (alternatingPrefix S U n + alternatingTail S V n) := by
              rw [map_add]
              abel
        _ = U - S V := by rw [ih]
        _ = V := hrenew.symm

/-- On a finite cutoff, once the terminal generation vanishes, the alternating
successor expansion is exact. -/
theorem finite_renewal_identity {S : M →+ M} {U V : M}
    (hrenew : V = U - S V) {depth : ℕ}
    (htail : alternatingTail S V depth = 0) :
    V = alternatingPrefix S U depth := by
  have h := alternatingPrefix_add_tail hrenew depth
  rw [htail, add_zero] at h
  exact h.symm

end Renewal

end CanonicalGapAncestryFlow

end RHLean.Proof
