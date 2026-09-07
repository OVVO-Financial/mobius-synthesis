import Mathlib
import RHLean.Proof.LifetimeEndpointDecomposition

open scoped BigOperators

/-!
# Lifetime cancellation across a square-time run

This is the Go statement, and unlike a prime-toggle pairing it really is about
trajectories.

An atom of the square-time process has a birth stage and a capture stage, and
its activity indicator is the indicator of the half-open lifetime

```text
A_t = 1  when  birth <= t < death,     A_t = 0  otherwise.
```

Summing the activity increments over a run `a, ..., b` telescopes to
`A_b - A_a`, so an atom that is born after the run starts and captured before it
ends contributes

```text
0 - 0 = 0
```

whatever its lifetime was.  A stone that lived one stage and a stone that lived
ten thousand stages cost the run exactly the same: nothing.  The length of the
lifetime does not appear anywhere in the statement or the proof, which is the
property a cumulative run needs and which a fixed-prime pairing does not
provide.

The file then connects this to the repository's actual birth/death process.

* `isLifetimeActive_of_le_of_birth_le` proves that `IsLifetimeActive` really is
  a lifetime *interval*: for a nonnegative cutoff slope the moving-high
  threshold `2 * Lambda * t` is nondecreasing, so an atom alive at `t` and
  already born at `s <= t` is alive at `s`.  Death is permanent; there is no
  resurrection between birth and capture, which is what makes the indicator
  above the right model.
* `sum_lifetimeActiveAtomMass_increment_Ico_eq_birthDeath_endpoints` states the
  aggregate run identity in the existing `Active = Birth - Death` endpoint
  coordinates.

**Scope.**  What is proved here is *interval structure plus endpoint telescope*,
not a fully instantiated birth/death-time representation.  No explicit pair of
functions `beta, delta : CanonicalSourceAtom -> N` is constructed, and the
pointwise identification

```text
indicator of IsLifetimeActive (alpha, t)  =  indicator of  beta alpha <= t < delta alpha
```

is not proved.  The abstract lifetime telescope is proved for the indicator
model, the actual active predicate is separately proved to have the
no-resurrection property that makes the model faithful, and the aggregate run
identity for the actual mass follows from the telescope directly.  That is
sufficient for the endpoint argument; constructing the explicit birth and
capture times would be an additional step.

No estimate, asymptotic input or RH hypothesis appears here.
-/

noncomputable section

namespace RHLean.Proof

/-! ## Telescoping a run -/

/-- A run of increments telescopes to its two endpoints. -/
theorem sum_increment_Ico {G : Type*} [AddCommGroup G] (f : ℕ → G)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, (f (k + 1) - f k)) = f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub f b,
    Finset.sum_range_sub f a]
  abel

/-! ## One lifetime -/

/-- Activity indicator of an atom with birth stage `β` and capture stage `δ`. -/
def lifetimeActivity (β δ t : ℕ) : ℤ :=
  if β ≤ t ∧ t < δ then 1 else 0

theorem lifetimeActivity_eq_zero_of_lt_birth {β δ t : ℕ} (h : t < β) :
    lifetimeActivity β δ t = 0 := by
  have hnot : ¬ (β ≤ t ∧ t < δ) := by omega
  unfold lifetimeActivity
  exact if_neg hnot

theorem lifetimeActivity_eq_zero_of_death_le {β δ t : ℕ} (h : δ ≤ t) :
    lifetimeActivity β δ t = 0 := by
  have hnot : ¬ (β ≤ t ∧ t < δ) := by omega
  unfold lifetimeActivity
  exact if_neg hnot

/-- The activity of one atom telescopes across a run. -/
theorem sum_lifetimeActivity_increment_Ico (β δ : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b,
        (lifetimeActivity β δ (k + 1) - lifetimeActivity β δ k)) =
      lifetimeActivity β δ b - lifetimeActivity β δ a :=
  sum_increment_Ico (lifetimeActivity β δ) hab

/-- **Interior lifetimes cost nothing.**

An atom born strictly after the start of the run and captured by its end
contributes exactly zero to the run.  The hypotheses constrain only where the
two endpoints of the lifetime sit relative to the two endpoints of the run; the
length `δ - β` of the lifetime never appears. -/
theorem sum_lifetimeActivity_increment_Ico_eq_zero_of_interior
    {β δ a b : ℕ} (hab : a ≤ b) (hborn : a < β) (hcaptured : δ ≤ b) :
    (∑ k ∈ Finset.Ico a b,
        (lifetimeActivity β δ (k + 1) - lifetimeActivity β δ k)) = 0 := by
  rw [sum_lifetimeActivity_increment_Ico β δ hab,
    lifetimeActivity_eq_zero_of_death_le hcaptured,
    lifetimeActivity_eq_zero_of_lt_birth hborn]
  ring

/-! ## A whole population across a run -/

/-- The weighted activity of a whole finite population telescopes to its two
endpoint populations. -/
theorem sum_population_lifetimeIncrement_Ico
    {α : Type*} (P : Finset α) (w : α → ℤ) (β δ : α → ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, ∑ s ∈ P,
        w s * (lifetimeActivity (β s) (δ s) (k + 1) -
          lifetimeActivity (β s) (δ s) k)) =
      ∑ s ∈ P, w s * (lifetimeActivity (β s) (δ s) b -
        lifetimeActivity (β s) (δ s) a) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [← Finset.mul_sum, sum_lifetimeActivity_increment_Ico (β s) (δ s) hab]

/-- **Only the two endpoint populations survive a run.**

Every atom whose lifetime opens and closes strictly inside the run drops out,
so the run is carried entirely by the atoms alive at one of its two ends.  This
is the birth/death form of "pair the interior, keep the boundary", and here the
interior really is a set of trajectories. -/
theorem sum_population_lifetimeIncrement_Ico_eq_endpointPopulation
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℤ) (β δ : α → ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, ∑ s ∈ P,
        w s * (lifetimeActivity (β s) (δ s) (k + 1) -
          lifetimeActivity (β s) (δ s) k)) =
      ∑ s ∈ P.filter (fun s =>
          lifetimeActivity (β s) (δ s) b ≠ 0 ∨
            lifetimeActivity (β s) (δ s) a ≠ 0),
        w s * (lifetimeActivity (β s) (δ s) b -
          lifetimeActivity (β s) (δ s) a) := by
  classical
  rw [sum_population_lifetimeIncrement_Ico P w β δ hab]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro s hsP hsNot
  have hzero : ¬ (lifetimeActivity (β s) (δ s) b ≠ 0 ∨
      lifetimeActivity (β s) (δ s) a ≠ 0) := by
    intro hor
    exact hsNot (Finset.mem_filter.mpr ⟨hsP, hor⟩)
  push_neg at hzero
  rw [hzero.1, hzero.2]
  ring

/-! ## The repository's own birth/death process -/

/-- **Death is permanent.**  For a nonnegative cutoff slope the moving-high
threshold `2 * Lambda * t` is nondecreasing, so an atom alive at `t` and already
born at `s ≤ t` is alive at `s`.  Lifetime activity is therefore genuinely an
interval, which is what makes the indicator model above faithful. -/
theorem isLifetimeActive_of_le_of_birth_le
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {p : CanonicalSourceAtom} {s t : ℕ}
    (hst : s ≤ t) (hborn : p.1 ≤ s) (ht : IsLifetimeActive Λ p t) :
    IsLifetimeActive Λ p s := by
  refine ⟨hborn, ?_⟩
  have hhigh : 2 * Λ * (t : ℝ) < |canonicalHeightTwice p.2| := ht.2
  have hcast : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have hnn : (0 : ℝ) ≤ 2 * Λ * ((t : ℝ) - (s : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  show 2 * Λ * (s : ℝ) < |canonicalHeightTwice p.2|
  linarith

/-- The survivor mass telescopes across a square-time run. -/
theorem sum_lifetimeActiveAtomMass_increment_Ico
    (Λ : ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b,
        (lifetimeActiveAtomMass Λ (k + 1) - lifetimeActiveAtomMass Λ k)) =
      lifetimeActiveAtomMass Λ b - lifetimeActiveAtomMass Λ a :=
  sum_increment_Ico (lifetimeActiveAtomMass Λ) hab

/-- The same run identity in the existing `Active = Birth - Death` endpoint
coordinates: a whole run of survivor increments is fixed by the birth and death
processes at its two ends alone. -/
theorem sum_lifetimeActiveAtomMass_increment_Ico_eq_birthDeath_endpoints
    (Λ : ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b,
        (lifetimeActiveAtomMass Λ (k + 1) - lifetimeActiveAtomMass Λ k)) =
      (lifetimeBirthMass Λ b - lifetimeDeathMass Λ b) -
        (lifetimeBirthMass Λ a - lifetimeDeathMass Λ a) := by
  rw [sum_lifetimeActiveAtomMass_increment_Ico Λ hab,
    lifetimeActiveAtomMass_eq_birth_sub_death,
    lifetimeActiveAtomMass_eq_birth_sub_death]

end RHLean.Proof
