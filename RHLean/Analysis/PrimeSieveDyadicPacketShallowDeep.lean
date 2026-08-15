import Mathlib
import RHLean.Analysis.PrimeSieveDyadicSignedPackets
import RHLean.Proof.DeathShellSubpolynomial

/-!
# Recursive midpoint packets and the shallow/deep analytic split

PR #323 exposed the signed sibling packet for the clipped prime discrepancy
`D = pi - Li`.  This module builds the deterministic recursive midpoint tree on
that coordinate, proves the discrete Faber--Schauder frame inequality, and
isolates the remaining analytic frontier as one shallow signed-mode estimate and
one deep recursive-tail estimate taken at a shared cutoff.

For an interval `[a,b]`, recursively split at

`m = a + floor ((b-a)/2)`.

At each node the contribution is

`width * ||B / width||^2`,

i.e. `|B|^2 / width`.  The generic frame theorem proves that chord energy on an
interval of width at most `2^depth` is bounded by `2 * depth` times its complete
midpoint-packet-tree energy.  The depth loss is then absorbed into an arbitrary
positive power using the repository's existing subpolynomial divisor theorem,
applied to `2^j`, whose divisor count is exactly `j+1`.

A cutoff selector `J(k,x)` gives the exact partition

`treeEnergy = shallowEnergy + deepEnergy`.

The only new analytic predicates left open are

* `DyadicPacketShallowEnergyBlockBoundedStatement J`;
* `DyadicPacketDeepTailBlockBoundedStatement J`.

No prime-distribution estimate, recursive contraction estimate, or RH-strength
bound is proved here.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Generic midpoint frame -/

/-- Integer midpoint used by the recursive packet tree. -/
def dyadicPacketMidpoint (a b : ℕ) : ℕ :=
  a + (b - a) / 2

private def genericSignedSiblingPacket
    (f : ℕ → ℂ) (a m b : ℕ) : ℂ :=
  (((b - m : ℕ) : ℂ) * (f m - f a)) -
    (((m - a : ℕ) : ℂ) * (f b - f m))

private def genericSignedSiblingResidual
    (f : ℕ → ℂ) (a m b : ℕ) : ℂ :=
  (((b - a : ℕ) : ℂ)⁻¹) * genericSignedSiblingPacket f a m b

private def genericChordEnergy (f : ℕ → ℂ) (a b : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico a b, ‖genericSignedSiblingResidual f a d b‖ ^ 2

private def genericMidpointPacketTreeEnergy
    (f : ℕ → ℂ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        ((b - a : ℕ) : ℝ) *
            ‖genericSignedSiblingResidual f a m b‖ ^ 2 +
          genericMidpointPacketTreeEnergy f depth a m +
          genericMidpointPacketTreeEnergy f depth m b
      else 0

private theorem dyadicPacketMidpoint_facts
    {a b : ℕ} (h : a + 1 < b) :
    a < dyadicPacketMidpoint a b ∧ dyadicPacketMidpoint a b < b := by
  unfold dyadicPacketMidpoint
  omega

private theorem dyadicPacketMidpoint_child_widths
    {a b depth : ℕ}
    (hsplit : a + 1 < b)
    (hwidth : b - a ≤ 2 ^ (depth + 1)) :
    dyadicPacketMidpoint a b - a ≤ 2 ^ depth ∧
      b - dyadicPacketMidpoint a b ≤ 2 ^ depth := by
  have hp : 2 ^ (depth + 1) = 2 * 2 ^ depth := by
    rw [pow_succ]
    ring
  rw [hp] at hwidth
  unfold dyadicPacketMidpoint
  omega

private theorem genericSignedSiblingResidual_eq_zero_left
    (f : ℕ → ℂ) (a b : ℕ) :
    genericSignedSiblingResidual f a a b = 0 := by
  simp [genericSignedSiblingResidual, genericSignedSiblingPacket]

private theorem genericSignedSiblingResidual_eq_zero_of_width_le_one
    {f : ℕ → ℂ} {a b d : ℕ}
    (hwidth : b - a ≤ 1) (hd : d ∈ Finset.Ico a b) :
    genericSignedSiblingResidual f a d b = 0 := by
  have hdI := Finset.mem_Ico.mp hd
  have hda : d = a := by omega
  subst d
  exact genericSignedSiblingResidual_eq_zero_left f a b

private theorem genericChordEnergy_eq_zero_of_width_le_one
    (f : ℕ → ℂ) {a b : ℕ} (hwidth : b - a ≤ 1) :
    genericChordEnergy f a b = 0 := by
  unfold genericChordEnergy
  apply Finset.sum_eq_zero
  intro d hd
  rw [genericSignedSiblingResidual_eq_zero_of_width_le_one hwidth hd]
  simp

private theorem sum_Ico_split
    (g : ℕ → ℝ) {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b) :
    (∑ d ∈ Finset.Ico a b, g d) =
      (∑ d ∈ Finset.Ico a m, g d) +
        ∑ d ∈ Finset.Ico m b, g d := by
  have hdis : Disjoint (Finset.Ico a m) (Finset.Ico m b) := by
    rw [Finset.disjoint_left]
    intro d hdl hdr
    simp only [Finset.mem_Ico] at hdl hdr
    omega
  have hunion : Finset.Ico a m ∪ Finset.Ico m b = Finset.Ico a b := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  rw [← hunion, Finset.sum_union hdis]

private theorem genericResidual_eq_affine_left
    {f : ℕ → ℂ} {a d b : ℕ}
    (had : a ≤ d) (hdb : d ≤ b) (hab : a < b) :
    genericSignedSiblingResidual f a d b =
      f d - f a -
        ((((d - a : ℕ) : ℂ) * (((b - a : ℕ) : ℂ)⁻¹)) *
          (f b - f a)) := by
  have hab0 : ((((b - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - a))
  have hwidthNat : b - a = (b - d) + (d - a) := by omega
  have hwidth :
      (((b - a : ℕ) : ℂ)) =
        ((b - d : ℕ) : ℂ) + ((d - a : ℕ) : ℂ) := by
    exact_mod_cast hwidthNat
  unfold genericSignedSiblingResidual genericSignedSiblingPacket
  field_simp [hab0]
  rw [hwidth]
  ring

private theorem genericResidual_eq_affine_right
    {f : ℕ → ℂ} {a d b : ℕ}
    (had : a ≤ d) (hdb : d ≤ b) (hab : a < b) :
    genericSignedSiblingResidual f a d b =
      f d - f b -
        ((((b - d : ℕ) : ℂ) * (((b - a : ℕ) : ℂ)⁻¹)) *
          (f a - f b)) := by
  have hab0 : ((((b - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - a))
  have hwidthNat : b - a = (b - d) + (d - a) := by omega
  have hwidth :
      (((b - a : ℕ) : ℂ)) =
        ((b - d : ℕ) : ℂ) + ((d - a : ℕ) : ℂ) := by
    exact_mod_cast hwidthNat
  unfold genericSignedSiblingResidual genericSignedSiblingPacket
  field_simp [hab0]
  rw [hwidth]
  ring

private theorem genericResidual_left_decomposition
    {f : ℕ → ℂ} {a d m b : ℕ}
    (had : a ≤ d) (hdm : d ≤ m) (hmb : m < b) (ham : a < m) :
    genericSignedSiblingResidual f a d b =
      genericSignedSiblingResidual f a d m +
        ((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) *
          genericSignedSiblingResidual f a m b) := by
  have hdb : d ≤ b := hdm.trans hmb.le
  have hab : a < b := ham.trans hmb
  have ham0 : ((((m - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m - a))
  have hab0 : ((((b - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - a))
  rw [genericResidual_eq_affine_left had hdb hab,
    genericResidual_eq_affine_left had hdm ham,
    genericResidual_eq_affine_left ham.le hmb.le hab]
  field_simp [ham0, hab0]
  ring

private theorem genericResidual_right_decomposition
    {f : ℕ → ℂ} {a m d b : ℕ}
    (ham : a < m) (hmd : m ≤ d) (hdb : d ≤ b) (hmb : m < b) :
    genericSignedSiblingResidual f a d b =
      genericSignedSiblingResidual f m d b +
        ((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) *
          genericSignedSiblingResidual f a m b) := by
  have had : a ≤ d := ham.le.trans hmd
  have hab : a < b := ham.trans hmb
  have hmb0 : ((((b - m : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - m))
  have hab0 : ((((b - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - a))
  rw [genericResidual_eq_affine_right had hdb hab,
    genericResidual_eq_affine_right hmd hdb hmb,
    genericResidual_eq_affine_right ham.le hmb.le hab]
  field_simp [hmb0, hab0]
  ring

private theorem natCast_ratio_norm_le_one
    {p q : ℕ} (hpq : p ≤ q) (hq : 0 < q) :
    ‖((p : ℂ) * ((q : ℂ)⁻¹))‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  simpa [div_eq_mul_inv] using (div_le_one hqR).2 hpqR

private theorem left_tent_energy_le
    (c : ℂ) {a m : ℕ} (ham : a < m) :
    (∑ d ∈ Finset.Ico a m,
      ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) ≤
      ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
  calc
    (∑ d ∈ Finset.Ico a m,
        ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) ≤
      ∑ _d ∈ Finset.Ico a m, ‖c‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hdI := Finset.mem_Ico.mp hd
        let r : ℝ :=
          ‖(((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹))‖
        have hr0 : 0 ≤ r := norm_nonneg _
        have hr1 : r ≤ 1 := by
          dsimp [r]
          exact natCast_ratio_norm_le_one (by omega) (by omega)
        have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
        rw [norm_mul]
        change (r * ‖c‖) ^ 2 ≤ ‖c‖ ^ 2
        have hmul : r * ‖c‖ ≤ ‖c‖ := by
          simpa using mul_le_mul_of_nonneg_right hr1 hc0
        exact (sq_le_sq₀ (mul_nonneg hr0 hc0) hc0).2 hmul
    _ = ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
      simp [Nat.card_Ico, nsmul_eq_mul]

private theorem right_tent_energy_le
    (c : ℂ) {m b : ℕ} (hmb : m < b) :
    (∑ d ∈ Finset.Ico m b,
      ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) ≤
      ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
  calc
    (∑ d ∈ Finset.Ico m b,
        ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) ≤
      ∑ _d ∈ Finset.Ico m b, ‖c‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hdI := Finset.mem_Ico.mp hd
        let r : ℝ :=
          ‖(((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹))‖
        have hr0 : 0 ≤ r := norm_nonneg _
        have hr1 : r ≤ 1 := by
          dsimp [r]
          exact natCast_ratio_norm_le_one (by omega) (by omega)
        have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
        rw [norm_mul]
        change (r * ‖c‖) ^ 2 ≤ ‖c‖ ^ 2
        have hmul : r * ‖c‖ ≤ ‖c‖ := by
          simpa using mul_le_mul_of_nonneg_right hr1 hc0
        exact (sq_le_sq₀ (mul_nonneg hr0 hc0) hc0).2 hmul
    _ = ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
      simp [Nat.card_Ico, nsmul_eq_mul]

private theorem weighted_norm_add_sq
    (q : ℕ) (hq : 1 ≤ q) (u v : ℂ) :
    (q : ℝ) * ‖u + v‖ ^ 2 ≤
      ((q + 1 : ℕ) : ℝ) * ‖u‖ ^ 2 +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
  have htri := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  have hsum0 : 0 ≤ ‖u‖ + ‖v‖ := add_nonneg hu hv
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsq hq0
  have hyoung :
      (q : ℝ) * (‖u‖ + ‖v‖) ^ 2 ≤
        ((q + 1 : ℕ) : ℝ) * ‖u‖ ^ 2 +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
    push_cast
    nlinarith [sq_nonneg (‖u‖ - (q : ℝ) * ‖v‖)]
  exact hscaled.trans hyoung

private theorem genericChordEnergy_split_weighted
    (f : ℕ → ℂ) (q : ℕ) (hq : 1 ≤ q)
    {a m b : ℕ} (ham : a < m) (hmb : m < b) :
    (q : ℝ) * genericChordEnergy f a b ≤
      ((q + 1 : ℕ) : ℝ) *
          (genericChordEnergy f a m + genericChordEnergy f m b) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) * ((b - a : ℕ) : ℝ) *
          ‖genericSignedSiblingResidual f a m b‖ ^ 2 := by
  let c := genericSignedSiblingResidual f a m b
  have hsplit := sum_Ico_split
    (g := fun d => ‖genericSignedSiblingResidual f a d b‖ ^ 2)
    ham.le hmb.le
  unfold genericChordEnergy
  rw [hsplit, mul_add]
  have hleft :
      (q : ℝ) * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
          ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
    calc
      (q : ℝ) * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) =
        ∑ d ∈ Finset.Ico a m,
          (q : ℝ) * ‖genericSignedSiblingResidual f a d b‖ ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ ∑ d ∈ Finset.Ico a m,
          (((q + 1 : ℕ) : ℝ) *
              ‖genericSignedSiblingResidual f a d m‖ ^ 2 +
            (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
              ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro d hd
            have hdI := Finset.mem_Ico.mp hd
            rw [genericResidual_left_decomposition hdI.1 hdI.2.le hmb ham]
            exact weighted_norm_add_sq q hq _ _
      _ = ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico a m,
            ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
            (∑ d ∈ Finset.Ico a m,
              ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico a m,
            ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
            ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
            have ht := left_tent_energy_le c ham
            have hcoef : 0 ≤ (q : ℝ) * ((q + 1 : ℕ) : ℝ) := by positivity
            have hs := mul_le_mul_of_nonneg_left ht hcoef
            convert add_le_add_left hs
              (((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico a m,
                ‖genericSignedSiblingResidual f a d m‖ ^ 2)) using 1
            all_goals ring
  have hright :
      (q : ℝ) * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
          ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
    calc
      (q : ℝ) * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) =
        ∑ d ∈ Finset.Ico m b,
          (q : ℝ) * ‖genericSignedSiblingResidual f a d b‖ ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ ∑ d ∈ Finset.Ico m b,
          (((q + 1 : ℕ) : ℝ) *
              ‖genericSignedSiblingResidual f m d b‖ ^ 2 +
            (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
              ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro d hd
            have hdI := Finset.mem_Ico.mp hd
            rw [genericResidual_right_decomposition ham hdI.1 hdI.2.le hmb]
            exact weighted_norm_add_sq q hq _ _
      _ = ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico m b,
            ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
            (∑ d ∈ Finset.Ico m b,
              ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico m b,
            ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
            ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
            have ht := right_tent_energy_le c hmb
            have hcoef : 0 ≤ (q : ℝ) * ((q + 1 : ℕ) : ℝ) := by positivity
            have hs := mul_le_mul_of_nonneg_left ht hcoef
            convert add_le_add_left hs
              (((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico m b,
                ‖genericSignedSiblingResidual f m d b‖ ^ 2)) using 1
            all_goals ring
  have hwidth :
      ((m - a : ℕ) : ℝ) + ((b - m : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) := by
    have hn : b - a = (m - a) + (b - m) := by omega
    exact_mod_cast hn.symm
  have hsum := add_le_add hleft hright
  dsimp [c] at hsum ⊢
  calc
    (q : ℝ) * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) +
        (q : ℝ) * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
      (((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
          ((m - a : ℕ) : ℝ) * ‖genericSignedSiblingResidual f a m b‖ ^ 2) +
      (((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
          ((b - m : ℕ) : ℝ) * ‖genericSignedSiblingResidual f a m b‖ ^ 2) := hsum
    _ = ((q + 1 : ℕ) : ℝ) *
          ((∑ d ∈ Finset.Ico a m,
              ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
            ∑ d ∈ Finset.Ico m b,
              ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) * ((b - a : ℕ) : ℝ) *
          ‖genericSignedSiblingResidual f a m b‖ ^ 2 := by
            rw [← hwidth]
            ring

private theorem genericMidpointPacketTreeEnergy_nonneg
    (f : ℕ → ℂ) (depth a b : ℕ) :
    0 ≤ genericMidpointPacketTreeEnergy f depth a b := by
  induction depth generalizing a b with
  | zero => simp [genericMidpointPacketTreeEnergy]
  | succ depth ih =>
      simp only [genericMidpointPacketTreeEnergy]
      by_cases h : a + 1 < b
      · simp [h]
        have hroot :
            0 ≤ ((b - a : ℕ) : ℝ) *
              ‖genericSignedSiblingResidual f a (dyadicPacketMidpoint a b) b‖ ^ 2 := by
          positivity
        exact add_nonneg (add_nonneg hroot (ih _ _)) (ih _ _)
      · simp [h]

private theorem genericMidpointPacketTreeEnergy_mono_succ
    (f : ℕ → ℂ) (depth a b : ℕ) :
    genericMidpointPacketTreeEnergy f depth a b ≤
      genericMidpointPacketTreeEnergy f (depth + 1) a b := by
  induction depth generalizing a b with
  | zero =>
      simpa [genericMidpointPacketTreeEnergy] using
        genericMidpointPacketTreeEnergy_nonneg f 1 a b
  | succ depth ih =>
      simp only [genericMidpointPacketTreeEnergy]
      by_cases hsplit : a + 1 < b
      · simp [hsplit]
        exact add_le_add (add_le_add_left (ih _ _) _) (ih _ _)
      · simp [hsplit]

private theorem genericMidpointPacketTreeEnergy_mono
    (f : ℕ → ℂ) {r s a b : ℕ} (hrs : r ≤ s) :
    genericMidpointPacketTreeEnergy f r a b ≤
      genericMidpointPacketTreeEnergy f s a b := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih =>
      exact ih.trans (genericMidpointPacketTreeEnergy_mono_succ f s a b)

/-- Deterministic discrete Faber--Schauder frame. -/
private theorem genericChordEnergy_le_midpointPacketTreeEnergy
    (f : ℕ → ℂ) :
    ∀ (depth a b : ℕ), a ≤ b → b - a ≤ 2 ^ depth →
      genericChordEnergy f a b ≤
        (2 * depth : ℕ) * genericMidpointPacketTreeEnergy f depth a b := by
  intro depth
  induction depth with
  | zero =>
      intro a b hab hwidth
      have hw : b - a ≤ 1 := by simpa using hwidth
      rw [genericChordEnergy_eq_zero_of_width_le_one f hw]
      simp
  | succ depth ih =>
      intro a b hab hwidth
      by_cases hsplit : a + 1 < b
      · let m := dyadicPacketMidpoint a b
        have hm := dyadicPacketMidpoint_facts hsplit
        have hchildren := dyadicPacketMidpoint_child_widths hsplit hwidth
        have hleftIH := ih a m hm.1.le hchildren.1
        have hrightIH := ih m b hm.2.le hchildren.2
        have htree :
            genericMidpointPacketTreeEnergy f (depth + 1) a b =
              ((b - a : ℕ) : ℝ) *
                  ‖genericSignedSiblingResidual f a m b‖ ^ 2 +
                genericMidpointPacketTreeEnergy f depth a m +
                genericMidpointPacketTreeEnergy f depth m b := by
          simp [genericMidpointPacketTreeEnergy, hsplit, m]
        by_cases hdepth : depth = 0
        · subst depth
          have hleft0 : genericChordEnergy f a m = 0 :=
            genericChordEnergy_eq_zero_of_width_le_one f hchildren.1
          have hright0 : genericChordEnergy f m b = 0 :=
            genericChordEnergy_eq_zero_of_width_le_one f hchildren.2
          have hw := genericChordEnergy_split_weighted
            f 1 (by norm_num) (a := a) (m := m) (b := b) hm.1 hm.2
          have htree1 :
              genericMidpointPacketTreeEnergy f 1 a b =
                ((b - a : ℕ) : ℝ) *
                  ‖genericSignedSiblingResidual f a m b‖ ^ 2 := by
            simpa [genericMidpointPacketTreeEnergy] using htree
          calc
            genericChordEnergy f a b ≤
                2 * ((b - a : ℕ) : ℝ) *
                  ‖genericSignedSiblingResidual f a m b‖ ^ 2 := by
              norm_num [hleft0, hright0] at hw ⊢
              exact hw
            _ = (2 * 1 : ℕ) * genericMidpointPacketTreeEnergy f 1 a b := by
              rw [htree1]
              ring
        · have hdpos : 1 ≤ depth := by omega
          have hw := genericChordEnergy_split_weighted
            f depth hdpos (a := a) (m := m) (b := b) hm.1 hm.2
          have hchild :
              genericChordEnergy f a m + genericChordEnergy f m b ≤
                ((2 * depth : ℕ) : ℝ) *
                  (genericMidpointPacketTreeEnergy f depth a m +
                    genericMidpointPacketTreeEnergy f depth m b) := by
            calc
              genericChordEnergy f a m + genericChordEnergy f m b ≤
                  ((2 * depth : ℕ) : ℝ) *
                      genericMidpointPacketTreeEnergy f depth a m +
                    ((2 * depth : ℕ) : ℝ) *
                      genericMidpointPacketTreeEnergy f depth m b :=
                add_le_add hleftIH hrightIH
              _ = ((2 * depth : ℕ) : ℝ) *
                    (genericMidpointPacketTreeEnergy f depth a m +
                      genericMidpointPacketTreeEnergy f depth m b) := by ring
          let kids := genericMidpointPacketTreeEnergy f depth a m +
            genericMidpointPacketTreeEnergy f depth m b
          let root := ((b - a : ℕ) : ℝ) *
            ‖genericSignedSiblingResidual f a m b‖ ^ 2
          have hkids0 : 0 ≤ kids := by
            dsimp [kids]
            exact add_nonneg
              (genericMidpointPacketTreeEnergy_nonneg f depth a m)
              (genericMidpointPacketTreeEnergy_nonneg f depth m b)
          have hroot0 : 0 ≤ root := by dsimp [root]; positivity
          push_cast at hw hchild
          have hqpos : (0 : ℝ) < depth := by exact_mod_cast (by omega : 0 < depth)
          have hscale0 : (0 : ℝ) ≤ depth + 1 := by positivity
          have hchildScaled := mul_le_mul_of_nonneg_left hchild hscale0
          have hmul :
              (depth : ℝ) * genericChordEnergy f a b ≤
                (depth : ℝ) *
                  (2 * ((depth : ℝ) + 1) * (root + kids)) := by
            calc
              (depth : ℝ) * genericChordEnergy f a b ≤
                  (((depth : ℝ) + 1) *
                      (genericChordEnergy f a m + genericChordEnergy f m b) +
                    (depth : ℝ) * (((depth : ℝ) + 1) * root)) := by
                simpa [root, mul_assoc] using hw
              _ ≤ (((depth : ℝ) + 1) * (2 * (depth : ℝ) * kids) +
                    (depth : ℝ) * (((depth : ℝ) + 1) * root)) := by
                exact add_le_add_right hchildScaled _
              _ ≤ (depth : ℝ) *
                    (2 * ((depth : ℝ) + 1) * (root + kids)) := by
                have hextra :
                    0 ≤ (depth : ℝ) * ((depth : ℝ) + 1) * root := by
                  positivity
                have heq :
                    (depth : ℝ) *
                        (2 * ((depth : ℝ) + 1) * (root + kids)) =
                      (((depth : ℝ) + 1) * (2 * (depth : ℝ) * kids) +
                        (depth : ℝ) * (((depth : ℝ) + 1) * root)) +
                        (depth : ℝ) * ((depth : ℝ) + 1) * root := by ring
                rw [heq]
                exact le_add_of_nonneg_right hextra
          have hcancel :
              genericChordEnergy f a b ≤
                2 * ((depth : ℝ) + 1) * (root + kids) :=
            (mul_le_mul_iff_right₀ hqpos).mp hmul
          rw [htree]
          dsimp [root, kids] at hcancel ⊢
          push_cast
          nlinarith
      · have hw : b - a ≤ 1 := by omega
        rw [genericChordEnergy_eq_zero_of_width_le_one f hw]
        exact mul_nonneg (by positivity)
          (genericMidpointPacketTreeEnergy_nonneg f (depth + 1) a b)

/-! ## Prime-discrepancy specialization and public recursive tree -/

private def primeSieveClippedDiscrepancyFunction (y x : ℕ) : ℕ → ℂ :=
  fun d => primeSieveDyadicClippedDiscrepancy y x d

private theorem genericResidual_eq_primeSieveResidual
    (y x a m b : ℕ) :
    genericSignedSiblingResidual (primeSieveClippedDiscrepancyFunction y x) a m b =
      primeSieveSignedSiblingPacketResidual y x a m b := by
  rfl

/-- Recursive midpoint-packet energy on an arbitrary reciprocal-index interval.
This is public so a later contraction argument can use the exact child recursion. -/
def primeSieveDyadicPacketIntervalTreeEnergy
    (y x depth a b : ℕ) : ℝ :=
  genericMidpointPacketTreeEnergy
    (primeSieveClippedDiscrepancyFunction y x) depth a b

@[simp] theorem primeSieveDyadicPacketIntervalTreeEnergy_zero
    (y x a b : ℕ) :
    primeSieveDyadicPacketIntervalTreeEnergy y x 0 a b = 0 := by
  rfl

/-- Exact recursive child decomposition of the packet tree. -/
theorem primeSieveDyadicPacketIntervalTreeEnergy_succ
    (y x depth a b : ℕ) :
    primeSieveDyadicPacketIntervalTreeEnergy y x (depth + 1) a b =
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        ((b - a : ℕ) : ℝ) *
            ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2 +
          primeSieveDyadicPacketIntervalTreeEnergy y x depth a m +
          primeSieveDyadicPacketIntervalTreeEnergy y x depth m b
      else 0 := by
  unfold primeSieveDyadicPacketIntervalTreeEnergy
  simp only [genericMidpointPacketTreeEnergy]
  rfl

/-- More refinement levels can only increase packet-tree energy. -/
theorem primeSieveDyadicPacketIntervalTreeEnergy_mono
    (y x : ℕ) {r s a b : ℕ} (hrs : r ≤ s) :
    primeSieveDyadicPacketIntervalTreeEnergy y x r a b ≤
      primeSieveDyadicPacketIntervalTreeEnergy y x s a b := by
  unfold primeSieveDyadicPacketIntervalTreeEnergy
  exact genericMidpointPacketTreeEnergy_mono _ hrs

/-- Packet-tree energy of one occupied #322 dyadic block. -/
def primeSieveDyadicPacketTreeBlockEnergy
    (y x j depth : ℕ) : ℝ :=
  primeSieveDyadicPacketIntervalTreeEnergy y x depth
    (primeSieveDyadicBlockLeft j)
    (primeSieveDyadicBlockRight y x j + 1)

/-- Full packet-tree energy: a `j`-block is refined through depth `j`. -/
def primeSieveDyadicPacketTreeEnergy (y x : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveDyadicPacketTreeBlockEnergy y x j j

/-- Shallow energy through the first `J` levels of every occupied block. -/
def primeSieveDyadicPacketShallowEnergy (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveDyadicPacketTreeBlockEnergy y x j (min J j)

/-- Deep energy beyond level `J`, localized block by block. -/
def primeSieveDyadicPacketDeepEnergy (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    (primeSieveDyadicPacketTreeBlockEnergy y x j j -
      primeSieveDyadicPacketTreeBlockEnergy y x j (min J j))

/-- Exact shallow/deep partition of the recursive packet energy. -/
theorem primeSieveDyadicPacket_shallow_add_deep
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J +
      primeSieveDyadicPacketDeepEnergy y x J =
        primeSieveDyadicPacketTreeEnergy y x := by
  unfold primeSieveDyadicPacketShallowEnergy
    primeSieveDyadicPacketDeepEnergy primeSieveDyadicPacketTreeEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Shallow energy is bounded by the complete tree energy. -/
theorem primeSieveDyadicPacketShallowEnergy_le_treeEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J ≤
      primeSieveDyadicPacketTreeEnergy y x := by
  unfold primeSieveDyadicPacketShallowEnergy primeSieveDyadicPacketTreeEnergy
  apply Finset.sum_le_sum
  intro j hj
  unfold primeSieveDyadicPacketTreeBlockEnergy
  exact primeSieveDyadicPacketIntervalTreeEnergy_mono
    y x (min_le_right J j)

/-- The localized deep tail is nonnegative. -/
theorem primeSieveDyadicPacketDeepEnergy_nonneg
    (y x J : ℕ) :
    0 ≤ primeSieveDyadicPacketDeepEnergy y x J := by
  unfold primeSieveDyadicPacketDeepEnergy
  apply Finset.sum_nonneg
  intro j hj
  apply sub_nonneg.mpr
  unfold primeSieveDyadicPacketTreeBlockEnergy
  exact primeSieveDyadicPacketIntervalTreeEnergy_mono
    y x (min_le_right J j)

private theorem primeSieveDyadicPacketTreeBlockEnergy_nonneg
    (y x j depth : ℕ) :
    0 ≤ primeSieveDyadicPacketTreeBlockEnergy y x j depth := by
  unfold primeSieveDyadicPacketTreeBlockEnergy
    primeSieveDyadicPacketIntervalTreeEnergy
  exact genericMidpointPacketTreeEnergy_nonneg _ depth _ _

private theorem primeSieveDyadicBlock_width_le_two_pow
    (y x j : ℕ) :
    primeSieveDyadicBlockRight y x j + 1 -
        primeSieveDyadicBlockLeft j ≤ 2 ^ j := by
  unfold primeSieveDyadicBlockRight primeSieveDyadicBlockLeft
  have hright : min (x / (y + 1)) (2 ^ (j + 1) - 1) + 1 ≤ 2 ^ (j + 1) := by
    have hp : 0 < 2 ^ (j + 1) := by positivity
    omega
  rw [pow_succ] at hright ⊢
  omega

private theorem genericChordEnergy_eq_blockChordEnergy
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    genericChordEnergy (primeSieveClippedDiscrepancyFunction y x)
        (primeSieveDyadicBlockLeft j)
        (primeSieveDyadicBlockRight y x j + 1) =
      ∑ d ∈ primeSieveDyadicBlock y x j,
        ‖primeSieveDyadicChordResidual y x j d‖ ^ 2 := by
  have hset :
      Finset.Ico (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1) =
        primeSieveDyadicBlock y x j := by
    rw [primeSieveDyadicBlock_eq_explicitIcc]
    ext d
    simp
    omega
  unfold genericChordEnergy
  rw [hset]
  apply Finset.sum_congr rfl
  intro d hd
  rw [genericResidual_eq_primeSieveResidual]
  rw [primeSieveDyadicRootPacketResidual_eq_chordResidual hj hd]

/-- Per-block deterministic frame inequality. -/
theorem primeSieveDyadicBlockChordEnergy_le_packetTree
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    (∑ d ∈ primeSieveDyadicBlock y x j,
        ‖primeSieveDyadicChordResidual y x j d‖ ^ 2) ≤
      (2 * j : ℕ) * primeSieveDyadicPacketTreeBlockEnergy y x j j := by
  rw [← genericChordEnergy_eq_blockChordEnergy hj]
  unfold primeSieveDyadicPacketTreeBlockEnergy
    primeSieveDyadicPacketIntervalTreeEnergy
  exact genericChordEnergy_le_midpointPacketTreeEnergy
    (primeSieveClippedDiscrepancyFunction y x) j
    (primeSieveDyadicBlockLeft j)
    (primeSieveDyadicBlockRight y x j + 1)
    (by
      have h := primeSieveDyadicBlockLeft_le_right_of_mem_indices hj
      omega)
    (primeSieveDyadicBlock_width_le_two_pow y x j)

/-- Global frame inequality with only the dyadic-depth weight left. -/
theorem primeSieveDyadicChordEnergy_le_weightedPacketTree
    (y x : ℕ) :
    primeSieveDyadicChordEnergy y x ≤
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        (2 * j : ℕ) * primeSieveDyadicPacketTreeBlockEnergy y x j j := by
  unfold primeSieveDyadicChordEnergy
  apply Finset.sum_le_sum
  intro j hj
  exact primeSieveDyadicBlockChordEnergy_le_packetTree hj

/-! ## Deterministic absorption of the depth loss -/

private theorem dyadicPower_divisors_card (j : ℕ) :
    (2 ^ j).divisors.card = j + 1 := by
  have h := congrArg Finset.card (Nat.divisors_prime_pow Nat.prime_two j)
  simpa using h

/-- The dyadic depth is subpolynomial because `j+1` is exactly the divisor count
of `2^j`. -/
private theorem dyadicDepth_succ_le_subpolynomial
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j : ℕ,
        (((j + 1 : ℕ) : ℝ)) ≤
          C * Real.rpow (((2 ^ j : ℕ) : ℝ)) ε := by
  obtain ⟨C, hC, hCb⟩ :=
    RHLean.Proof.card_divisors_le_subpolynomial hε
  refine ⟨C, hC, ?_⟩
  intro j
  have hpow : 1 ≤ 2 ^ j := by
    simpa using (Nat.one_le_pow' j 1)
  have h := hCb (2 ^ j) hpow
  rw [dyadicPower_divisors_card] at h
  exact h

private theorem two_pow_le_x_succ_of_mem_dyadicBlockIndex
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    2 ^ j ≤ x + 1 := by
  have h := primeSieveDyadicBlockLeft_le_right_of_mem_indices hj
  unfold primeSieveDyadicBlockLeft primeSieveDyadicBlockRight at h
  calc
    2 ^ j ≤ min (x / (y + 1)) (2 ^ (j + 1) - 1) := h
    _ ≤ x / (y + 1) := min_le_left _ _
    _ ≤ x := Nat.div_le_self _ _
    _ ≤ x + 1 := by omega

private theorem two_mul_dyadicDepth_le_subpolynomial_on_support
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y x j : ℕ), j ∈ primeSieveDyadicBlockIndices y x →
        (((2 * j : ℕ) : ℝ)) ≤
          C * Real.rpow ((x : ℝ) + 1) ε := by
  obtain ⟨C, hC, hDepth⟩ := dyadicDepth_succ_le_subpolynomial hε
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro y x j hj
  have hs := hDepth j
  have hpowNat := two_pow_le_x_succ_of_mem_dyadicBlockIndex hj
  have hpowCast : (((2 ^ j : ℕ) : ℝ)) ≤ (x : ℝ) + 1 := by
    exact_mod_cast hpowNat
  have hrpow :
      Real.rpow (((2 ^ j : ℕ) : ℝ)) ε ≤
        Real.rpow ((x : ℝ) + 1) ε :=
    Real.rpow_le_rpow (by positivity) hpowCast hε.le
  have hcPow := mul_le_mul_of_nonneg_left hrpow hC
  have hjCast : (j : ℝ) ≤ (((j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.le_succ j)
  calc
    (((2 * j : ℕ) : ℝ)) = 2 * (j : ℝ) := by push_cast; ring
    _ ≤ 2 * (((j + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hjCast (by norm_num)
    _ ≤ 2 * (C * Real.rpow (((2 ^ j : ℕ) : ℝ)) ε) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 2 * (C * Real.rpow ((x : ℝ) + 1) ε) :=
      mul_le_mul_of_nonneg_left hcPow (by norm_num)
    _ = (2 * C) * Real.rpow ((x : ℝ) + 1) ε := by ring

private theorem weightedPacketTree_le_subpolynomial
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y x : ℕ),
        (∑ j ∈ primeSieveDyadicBlockIndices y x,
          (2 * j : ℕ) * primeSieveDyadicPacketTreeBlockEnergy y x j j) ≤
        C * Real.rpow ((x : ℝ) + 1) ε *
          primeSieveDyadicPacketTreeEnergy y x := by
  obtain ⟨C, hC, hDepth⟩ :=
    two_mul_dyadicDepth_le_subpolynomial_on_support hε
  refine ⟨C, hC, ?_⟩
  intro y x
  calc
    (∑ j ∈ primeSieveDyadicBlockIndices y x,
        (2 * j : ℕ) * primeSieveDyadicPacketTreeBlockEnergy y x j j) ≤
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        (C * Real.rpow ((x : ℝ) + 1) ε) *
          primeSieveDyadicPacketTreeBlockEnergy y x j j := by
            apply Finset.sum_le_sum
            intro j hj
            have hd := hDepth y x j hj
            exact mul_le_mul_of_nonneg_right hd
              (primeSieveDyadicPacketTreeBlockEnergy_nonneg y x j j)
    _ = C * Real.rpow ((x : ℝ) + 1) ε *
        primeSieveDyadicPacketTreeEnergy y x := by
          unfold primeSieveDyadicPacketTreeEnergy
          rw [Finset.mul_sum]

/-- A critical estimate for the unweighted recursive tree deterministically
implies the #323 root-packet estimate: the depth loss costs only an epsilon. -/
theorem dyadicSignedRootPacketEnergyBlockBounded_of_packetTree
    (hTree :
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ (k x : ℕ),
            2 ≤ k →
            primorialBlockLower k ≤ x →
            x ≤ primorialBlockUpper k →
            primeSieveDyadicPacketTreeEnergy
                (primorialPNTPrimeSieveCutoff k) x ≤
              C * Real.rpow ((x : ℝ) + 1) (1 + ε)) :
    DyadicSignedRootPacketEnergyBlockBoundedStatement := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨CT, hCT, hTb⟩ := hTree (ε / 2) hhalf
  obtain ⟨CD, hCD, hDb⟩ := weightedPacketTree_le_subpolynomial hhalf
  refine ⟨CD * CT, mul_nonneg hCD hCT, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  have hframe := primeSieveDyadicChordEnergy_le_weightedPacketTree y x
  have hdepth := hDb y x
  have htree := hTb k x hk hlow hup
  have hbase : 0 < (x : ℝ) + 1 := by positivity
  have hfac0 :
      0 ≤ CD * Real.rpow ((x : ℝ) + 1) (ε / 2) :=
    mul_nonneg hCD (Real.rpow_nonneg (by positivity) _)
  calc
    primeSieveDyadicSignedRootPacketEnergy y x =
        primeSieveDyadicChordEnergy y x :=
      primeSieveDyadicSignedRootPacketEnergy_eq_chordEnergy y x
    _ ≤ ∑ j ∈ primeSieveDyadicBlockIndices y x,
        (2 * j : ℕ) * primeSieveDyadicPacketTreeBlockEnergy y x j j := hframe
    _ ≤ CD * Real.rpow ((x : ℝ) + 1) (ε / 2) *
        primeSieveDyadicPacketTreeEnergy y x := hdepth
    _ ≤ (CD * Real.rpow ((x : ℝ) + 1) (ε / 2)) *
        (CT * Real.rpow ((x : ℝ) + 1) (1 + ε / 2)) :=
      mul_le_mul_of_nonneg_left htree hfac0
    _ = (CD * CT) *
        (Real.rpow ((x : ℝ) + 1) (ε / 2) *
          Real.rpow ((x : ℝ) + 1) (1 + ε / 2)) := by ring
    _ = (CD * CT) *
        Real.rpow ((x : ℝ) + 1) ((ε / 2) + (1 + ε / 2)) := by
      exact congrArg (fun z : ℝ => (CD * CT) * z)
        (Real.rpow_add hbase (ε / 2) (1 + ε / 2)).symm
    _ = (CD * CT) * Real.rpow ((x : ℝ) + 1) (1 + ε) := by
      congr 1
      ring

/-! ## Shared-cutoff analytic frontier -/

/-- A single cutoff selector shared by the shallow and deep estimates. -/
def DyadicPacketCutoff := ℕ → ℕ → ℕ

/-- Critical block-uniform bound for the low-depth signed packet modes selected
by `cutoff`. -/
def DyadicPacketShallowEnergyBlockBoundedStatement
    (cutoff : DyadicPacketCutoff) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicPacketShallowEnergy
            (primorialPNTPrimeSieveCutoff k) x (cutoff k x) ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- Critical block-uniform bound for the complementary recursive deep tail at
the same cutoff.  This is the new contraction target. -/
def DyadicPacketDeepTailBlockBoundedStatement
    (cutoff : DyadicPacketCutoff) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicPacketDeepEnergy
            (primorialPNTPrimeSieveCutoff k) x (cutoff k x) ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The two estimates at one shared cutoff control the complete recursive tree. -/
theorem dyadicPacketTreeEnergyBlockBounded_of_shallow_deep
    (cutoff : DyadicPacketCutoff)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement cutoff)
    (hT : DyadicPacketDeepTailBlockBoundedStatement cutoff) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (k x : ℕ),
          2 ≤ k →
          primorialBlockLower k ≤ x →
          x ≤ primorialBlockUpper k →
          primeSieveDyadicPacketTreeEnergy
              (primorialPNTPrimeSieveCutoff k) x ≤
            C * Real.rpow ((x : ℝ) + 1) (1 + ε) := by
  intro ε hε
  obtain ⟨CS, hCS, hSb⟩ := hS ε hε
  obtain ⟨CT, hCT, hTb⟩ := hT ε hε
  refine ⟨CS + CT, add_nonneg hCS hCT, ?_⟩
  intro k x hk hlow hup
  have hs := hSb k x hk hlow hup
  have ht := hTb k x hk hlow hup
  rw [← primeSieveDyadicPacket_shallow_add_deep
    (primorialPNTPrimeSieveCutoff k) x (cutoff k x)]
  have hp := Real.rpow_nonneg
    (by positivity : (0 : ℝ) ≤ (x : ℝ) + 1) (1 + ε)
  nlinarith

/-- **Terminal shallow/deep reduction.**  Apart from the already-existing
coherent-channel and Mobius-dispersion hypotheses, the only new analytic inputs
are the shallow and deep packet estimates at one shared cutoff. -/
theorem riemannHypothesis_of_dyadicPacketShallowDeepAnalyticPackage
    (cutoff : DyadicPacketCutoff)
    (hC : DyadicCoherentChannelRHScale)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement cutoff)
    (hT : DyadicPacketDeepTailBlockBoundedStatement cutoff)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicSignedPacketAnalyticPackage hC
  · apply dyadicSignedRootPacketEnergyBlockBounded_of_packetTree
    exact dyadicPacketTreeEnergyBlockBounded_of_shallow_deep cutoff hS hT
  · exact hD

end RHLean.Analysis
