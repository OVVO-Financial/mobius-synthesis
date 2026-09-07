import Mathlib
import RHLean.Proof.GlobalPrefixCarrierOthello

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# The two walls of a cumulative prefix carrier

The global Othello theorem reduces the signed Möbius mass of any finite region
to the sites whose distinguished-prime mate has left the region.  For the region
actually carrying a Mertens increment — the ordered prefix carrier `(L, x]` —
that boundary is completely explicit and consists of exactly two walls.

* **Anchor wall.**  A site `n` carrying exactly one factor `p` has mate `n / p`,
  which can only leave the carrier downwards.  It does so precisely when
  `n ≤ p * L`.
* **Cutoff wall.**  A site `n` free of `p` has mate `n * p`, which can only
  leave the carrier upwards.  It does so precisely when `x < n * p`.

Square hits are frozen by the toggle, stay inside the carrier and carry no
Möbius mass, so they never reach the boundary at all.  Hence

```text
sum over (L, x] of mu = anchor wall mass + cutoff wall mass,
```

an exact identity in which the whole interior of the prefix has cancelled in
mated pairs.  The pairing is by two cycles of one fixed prime, so this is the
cumulative form of a *pairing*, not of an alternating-component argument: no
path longer than one edge occurs anywhere in the proof.

The file closes with the honest population bounds for the two walls at a single
prime: the anchor wall injects into `(0, L]` by dividing out `p`, and the cutoff
wall injects into `(x / p, x]`.  Neither is yet a saving at one prime; they are
the quantities an iterated multiplicity theorem has to control.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The anchor wall of the prefix carrier `(L, x]`: sites carrying exactly one
factor `p` whose quotient falls back past the fixed lower anchor. -/
def primeCarrierAnchorWall (p L x : ℕ) : Finset ℕ :=
  (Finset.Ioc L x).filter fun n => p ∣ n ∧ ¬ p ^ 2 ∣ n ∧ n ≤ p * L

/-- The cutoff wall of the prefix carrier `(L, x]`: sites free of `p` whose
`p`-multiple overshoots the moving right endpoint. -/
def primeCarrierCutoffWall (p L x : ℕ) : Finset ℕ :=
  (Finset.Ioc L x).filter fun n => ¬ p ∣ n ∧ x < n * p

@[simp] theorem mem_primeCarrierAnchorWall {p L x n : ℕ} :
    n ∈ primeCarrierAnchorWall p L x ↔
      n ∈ Finset.Ioc L x ∧ p ∣ n ∧ ¬ p ^ 2 ∣ n ∧ n ≤ p * L :=
  Finset.mem_filter

@[simp] theorem mem_primeCarrierCutoffWall {p L x n : ℕ} :
    n ∈ primeCarrierCutoffWall p L x ↔
      n ∈ Finset.Ioc L x ∧ ¬ p ∣ n ∧ x < n * p :=
  Finset.mem_filter

theorem primeCarrierWalls_disjoint (p L x : ℕ) :
    Disjoint (primeCarrierAnchorWall p L x) (primeCarrierCutoffWall p L x) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  exact (mem_primeCarrierCutoffWall.mp hn').2.1
    (mem_primeCarrierAnchorWall.mp hn).2.1

/-- **The Othello boundary of a prefix carrier is exactly its two walls.** -/
theorem primeEscapePart_Ioc_eq_walls {p : ℕ} (hp : p.Prime) (L x : ℕ) :
    primeEscapePart p (Finset.Ioc L x) =
      primeCarrierAnchorWall p L x ∪ primeCarrierCutoffWall p L x := by
  ext n
  constructor
  · intro hn
    obtain ⟨hmem, hout⟩ := mem_primeEscapePart.mp hn
    have hIoc := Finset.mem_Ioc.mp hmem
    by_cases hsq : p ^ 2 ∣ n
    · exfalso
      refine hout ?_
      rw [primeCarrierToggle_of_sq_dvd hsq]
      exact hmem
    · by_cases hdvd : p ∣ n
      · refine Finset.mem_union.mpr
          (Or.inl (mem_primeCarrierAnchorWall.mpr ⟨hmem, hdvd, hsq, ?_⟩))
        rw [primeCarrierToggle_of_dvd hdvd hsq] at hout
        have hdivle : n / p ≤ x := le_trans (Nat.div_le_self n p) hIoc.2
        have hnotlt : ¬ (L < n / p) := by
          intro hlt
          exact hout (Finset.mem_Ioc.mpr ⟨hlt, hdivle⟩)
        have hle : n / p ≤ L := not_lt.mp hnotlt
        have hmul : p * (n / p) = n := Nat.mul_div_cancel' hdvd
        calc n = p * (n / p) := hmul.symm
          _ ≤ p * L := Nat.mul_le_mul (le_refl p) hle
      · refine Finset.mem_union.mpr
          (Or.inr (mem_primeCarrierCutoffWall.mpr ⟨hmem, hdvd, ?_⟩))
        rw [primeCarrierToggle_of_not_dvd hdvd] at hout
        have hgrow : n ≤ n * p := by
          have h : n * 1 ≤ n * p := Nat.mul_le_mul (le_refl n) hp.one_lt.le
          rwa [mul_one] at h
        have hlow : L < n * p := lt_of_lt_of_le hIoc.1 hgrow
        have hnotle : ¬ (n * p ≤ x) := by
          intro hle
          exact hout (Finset.mem_Ioc.mpr ⟨hlow, hle⟩)
        exact not_le.mp hnotle
  · intro hn
    rcases Finset.mem_union.mp hn with h | h
    · obtain ⟨hmem, hdvd, hsq, hle⟩ := mem_primeCarrierAnchorWall.mp h
      refine mem_primeEscapePart.mpr ⟨hmem, ?_⟩
      rw [primeCarrierToggle_of_dvd hdvd hsq]
      intro hcontra
      have hlt := (Finset.mem_Ioc.mp hcontra).1
      have hdiv : n / p ≤ L := by
        have hmul : p * (n / p) = n := Nat.mul_div_cancel' hdvd
        have h1 : p * (n / p) ≤ p * L := by rw [hmul]; exact hle
        exact Nat.le_of_mul_le_mul_left h1 hp.pos
      exact absurd hlt (not_lt.mpr hdiv)
    · obtain ⟨hmem, hdvd, hgt⟩ := mem_primeCarrierCutoffWall.mp h
      refine mem_primeEscapePart.mpr ⟨hmem, ?_⟩
      rw [primeCarrierToggle_of_not_dvd hdvd]
      intro hcontra
      have hle := (Finset.mem_Ioc.mp hcontra).2
      exact absurd hle (not_le.mpr hgt)

/-- **Cumulative prefix pairing identity.**  A whole ordered prefix of Möbius
values equals the signed mass of its two boundary walls: every interior site is
mated with its `p`-partner and cancels against it. -/
theorem sum_moebius_Ioc_eq_wallMass {p : ℕ} (hp : p.Prime) (L x : ℕ) :
    (∑ n ∈ Finset.Ioc L x, μ n) =
      (∑ n ∈ primeCarrierAnchorWall p L x, μ n) +
        ∑ n ∈ primeCarrierCutoffWall p L x, μ n := by
  rw [sum_moebius_eq_sum_primeEscapePart hp (Finset.Ioc L x),
    primeEscapePart_Ioc_eq_walls hp L x]
  exact Finset.sum_union (primeCarrierWalls_disjoint p L x)

/-! ## Wall populations -/

/-- The anchor wall injects into `(0, L]` by dividing out its single `p`. -/
theorem card_primeCarrierAnchorWall_le {p : ℕ} (hp : p.Prime) (L x : ℕ) :
    (primeCarrierAnchorWall p L x).card ≤ L := by
  have hmaps : ∀ n ∈ primeCarrierAnchorWall p L x,
      n / p ∈ Finset.Ioc 0 L := by
    intro n hn
    obtain ⟨hmem, hdvd, _hsq, hle⟩ := mem_primeCarrierAnchorWall.mp hn
    have hIoc := Finset.mem_Ioc.mp hmem
    have hpos : 0 < n := lt_of_le_of_lt (Nat.zero_le L) hIoc.1
    refine Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hpos hdvd) hp.pos, ?_⟩
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hdvd
    have h1 : p * (n / p) ≤ p * L := by rw [hmul]; exact hle
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hinj : Set.InjOn (fun n => n / p) (primeCarrierAnchorWall p L x) := by
    intro a ha b hb hab
    have hab' : a / p = b / p := hab
    have hadvd := (mem_primeCarrierAnchorWall.mp (Finset.mem_coe.mp ha)).2.1
    have hbdvd := (mem_primeCarrierAnchorWall.mp (Finset.mem_coe.mp hb)).2.1
    have hA : p * (a / p) = a := Nat.mul_div_cancel' hadvd
    have hB : p * (b / p) = b := Nat.mul_div_cancel' hbdvd
    calc a = p * (a / p) := hA.symm
      _ = p * (b / p) := by rw [hab']
      _ = b := hB
  calc (primeCarrierAnchorWall p L x).card ≤ (Finset.Ioc 0 L).card :=
        Finset.card_le_card_of_injOn (fun n => n / p) hmaps hinj
    _ = L := by simp

/-- The cutoff wall lives in the top `p`-adic window `(x / p, x]`. -/
theorem card_primeCarrierCutoffWall_le {p : ℕ} (hp : p.Prime) (L x : ℕ) :
    (primeCarrierCutoffWall p L x).card ≤ x - x / p := by
  have hsub : primeCarrierCutoffWall p L x ⊆ Finset.Ioc (x / p) x := by
    intro n hn
    obtain ⟨hmem, _hdvd, hgt⟩ := mem_primeCarrierCutoffWall.mp hn
    have hIoc := Finset.mem_Ioc.mp hmem
    exact Finset.mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hp.pos).mpr hgt, hIoc.2⟩
  calc (primeCarrierCutoffWall p L x).card ≤ (Finset.Ioc (x / p) x).card :=
        Finset.card_le_card hsub
    _ = x - x / p := by simp

/-- **Prefix mass never exceeds the two wall populations.** -/
theorem abs_sum_moebius_Ioc_le_wallCard {p : ℕ} (hp : p.Prime) (L x : ℕ) :
    |∑ n ∈ Finset.Ioc L x, μ n| ≤ (L : ℤ) + ((x - x / p : ℕ) : ℤ) := by
  rw [sum_moebius_Ioc_eq_wallMass hp L x]
  have hanchor : |∑ n ∈ primeCarrierAnchorWall p L x, μ n| ≤ (L : ℤ) := by
    refine le_trans (abs_sum_moebius_le_card _) ?_
    exact_mod_cast card_primeCarrierAnchorWall_le hp L x
  have hcutoff :
      |∑ n ∈ primeCarrierCutoffWall p L x, μ n| ≤ ((x - x / p : ℕ) : ℤ) := by
    refine le_trans (abs_sum_moebius_le_card _) ?_
    exact_mod_cast card_primeCarrierCutoffWall_le hp L x
  exact le_trans (abs_add_le _ _) (add_le_add hanchor hcutoff)

end RHLean.Proof
