import Mathlib
import RHLean.Arithmetic.BooleanCubeCancellation

/-!
# Least-coordinate toggle duality

This is the finite sign-reversing involution behind the largest/smallest-prime
duality used in the Othello endgame.

Fix one distinguished coordinate `a` in a finite set `S`.  Give every nonempty
face the Boolean sign `(-1)^|t|`.  Suppose a payload `g` is unchanged when `a`
is inserted into any nonempty face which omits `a`.  Splitting the powerset at
`a` pairs every nonempty old face with its `a`-child with opposite signs.  The
empty old face has no payload, while its child `{a}` survives.  Therefore the
whole nonempty alternating cube is exactly `-g {a}`.

For a finite linearly ordered coordinate set, if `a` is its least element then
inserting `a` into a nonempty face does not change that face's maximum.  Hence
any payload depending only on the maximum coordinate satisfies the preceding
invariance automatically.  On prime-factor faces this is the finite core of
Alladi's largest/smallest-prime duality: an arbitrarily large divisor-history
fibre has one signed last move.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Alternating payload on the nonempty faces of a finite coordinate set. -/
def finiteNonemptyFaceAlternatingSum
    {α A : Type*} [DecidableEq α] [AddCommGroup A]
    (S : Finset α) (g : Finset α → A) : A :=
  ∑ t ∈ S.powerset, if t.Nonempty then booleanCubeSign t • g t else 0

/-- **Least-toggle singleton survival.**  If inserting the distinguished
coordinate preserves the payload on every nonempty face omitting it, then all
non-singleton histories cancel and only the singleton `{a}` remains. -/
theorem finiteNonemptyFaceAlternatingSum_eq_neg_singleton
    {α A : Type*} [DecidableEq α] [AddCommGroup A]
    (S : Finset α) (a : α) (g : Finset α → A)
    (ha : a ∈ S)
    (hinvariant : ∀ u ∈ (S.erase a).powerset, u.Nonempty →
      g (insert a u) = g u) :
    finiteNonemptyFaceAlternatingSum S g = -g {a} := by
  have hdecomp : S = insert a (S.erase a) := (Finset.insert_erase ha).symm
  have haErase : a ∉ S.erase a := Finset.notMem_erase a S
  unfold finiteNonemptyFaceAlternatingSum
  rw [hdecomp, Finset.sum_powerset_insert haErase]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ u ∈ (S.erase a).powerset,
        if u = ∅ then -g {a} else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have hau : a ∉ u :=
        Finset.notMem_of_mem_powerset_of_notMem hu haErase
      have hinsNonempty : (insert a u).Nonempty :=
        ⟨a, Finset.mem_insert_self _ _⟩
      by_cases huEmpty : u = ∅
      · subst u
        simp [booleanCubeSign]
      · have huNonempty : u.Nonempty := Finset.nonempty_iff_ne_empty.mpr huEmpty
        have hginv := hinvariant u hu huNonempty
        have hsign : booleanCubeSign (insert a u) = -booleanCubeSign u := by
          unfold booleanCubeSign
          rw [Finset.card_insert_of_notMem hau, pow_succ]
          ring
        simp only [huNonempty, hinsNonempty, if_true]
        rw [hginv, hsign]
        simp [huEmpty]
    _ = -g {a} := by simp

/-- Total maximum-coordinate payload, zero on the empty face. -/
def finiteFaceMaxPayload
    {α A : Type*} [LinearOrder α] [AddCommGroup A]
    (f : α → A) (t : Finset α) : A :=
  if h : t.Nonempty then f (t.max' h) else 0

/-- Inserting the least ambient coordinate into a nonempty face does not change
that face's maximum payload. -/
theorem finiteFaceMaxPayload_insert_least
    {α A : Type*} [LinearOrder α] [AddCommGroup A]
    (S : Finset α) (a : α) (f : α → A)
    (hmin : ∀ x ∈ S, a ≤ x)
    {u : Finset α} (hu : u ∈ (S.erase a).powerset)
    (huNonempty : u.Nonempty) :
    finiteFaceMaxPayload f (insert a u) = finiteFaceMaxPayload f u := by
  have huSub : u ⊆ S.erase a := Finset.mem_powerset.mp hu
  have hmaxMem : u.max' huNonempty ∈ u := Finset.max'_mem u huNonempty
  have hmaxS : u.max' huNonempty ∈ S :=
    (Finset.mem_erase.mp (huSub hmaxMem)).2
  have haMax : a ≤ u.max' huNonempty := hmin _ hmaxS
  have hinsNonempty : (insert a u).Nonempty :=
    ⟨a, Finset.mem_insert_self _ _⟩
  have hmaxEq :
      (insert a u).max' hinsNonempty = max a (u.max' huNonempty) := by
    simpa using (Finset.max'_insert a u huNonempty)
  unfold finiteFaceMaxPayload
  rw [dif_pos hinsNonempty, dif_pos huNonempty, hmaxEq,
    max_eq_right haMax]

/-- **Largest-coordinate / least-coordinate duality.**  On a finite ordered
set with least coordinate `a`, the complete nonempty alternating face sum of a
maximum-coordinate payload is exactly the negative payload at `a`. -/
theorem finiteNonemptyFaceAlternatingMax_eq_neg_least
    {α A : Type*} [LinearOrder α] [AddCommGroup A]
    (S : Finset α) (a : α) (f : α → A)
    (ha : a ∈ S)
    (hmin : ∀ x ∈ S, a ≤ x) :
    finiteNonemptyFaceAlternatingSum S (finiteFaceMaxPayload f) = -f a := by
  rw [finiteNonemptyFaceAlternatingSum_eq_neg_singleton
    S a (finiteFaceMaxPayload f) ha]
  · simp [finiteFaceMaxPayload]
  · intro u hu huNonempty
    exact finiteFaceMaxPayload_insert_least S a f hmin hu huNonempty

end RHLean.Proof
