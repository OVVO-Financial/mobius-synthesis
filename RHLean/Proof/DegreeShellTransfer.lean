import Mathlib

/-!
# Ternary degree shells and the transfer product at `z = 1`

Resolving the distinguished prime-`2` fibre through an odd prime `q` splits every
existing packet into three local classes `C_q`, `S_q`, `W_q` — a **ternary** tree,
not Boolean membership.  Grading the resolved components by the number `d` of
non-`C` coordinates gives the degree shells `E_d`, and adjoining one more prime
acts on the graded family by

```text
E_d^{(j)} = C_q E_d^{(j-1)} + (S_q + W_q) E_{d-1}^{(j-1)}.
```

Packaging the shells as `F_j(z) = sum_d E_d^{(j)} z^d` turns this into

```text
F_j(z) = (C_q + z (S_q + W_q)) F_{j-1}(z),
```

and the physical fibre is the evaluation `P_2 = F_j(1)`.

This module formalizes that grading with `C` and `T = S + W` as genuine additive
operators — not scalars — and proves the two structural facts the transfer
programme needs:

* one prime adjunction raises the degree support by exactly one
  (`supported_shellStep`);
* evaluation at `z = 1` intertwines the graded recursion with the plain operator
  product `C + T` (`sum_shellStep_window`, `sum_shellSteps`).

It also records the two arithmetic cautions attached to the diagnostic at the
`29#` bottleneck:

* the tree is ternary, so a degree-`d` shell carries `choose j d * 2^d` leaves and
  the whole tree `3^j`, not `2^j` — an ordinary alternating subset sum is not an
  admissible substitute (`ternaryLeafCount_nine`, `boolean_lt_ternary_nine`);
* the high-degree tail is not discardable: at the bottleneck the degree `0..4`
  head is more than six times the net it is supposed to approximate, and the
  degree `5..9` tail more than five times (`bottleneckHead_gt`, `bottleneckTail_gt`).

No analytic estimate is asserted here.  The operator statements are exact algebra
and the numeric statements are exact rational arithmetic on reported shell data.
-/

namespace RHLean.Proof

namespace DegreeShell

variable {V : Type*} [AddCommGroup V]

/-- A graded shell family is supported below `n` when every degree `>= n`
vanishes. -/
def Supported (E : ℕ → V) (n : ℕ) : Prop := ∀ d, n ≤ d → E d = 0

/-- One prime adjunction on the degree shells:
`E_d |-> C E_d + T E_{d-1}` with `T = S + W` and `E_{-1} = 0`. -/
def shellStep (C T : V →+ V) (E : ℕ → V) : ℕ → V
  | 0 => C (E 0)
  | (d + 1) => C (E (d + 1)) + T (E d)

theorem shellStep_zero (C T : V →+ V) (E : ℕ → V) :
    shellStep C T E 0 = C (E 0) := rfl

theorem shellStep_succ (C T : V →+ V) (E : ℕ → V) (d : ℕ) :
    shellStep C T E (d + 1) = C (E (d + 1)) + T (E d) := rfl

/-- Each prime adjunction raises the degree support by exactly one coordinate. -/
theorem supported_shellStep {C T : V →+ V} {E : ℕ → V} {n : ℕ}
    (hE : Supported E n) : Supported (shellStep C T E) (n + 1) := by
  intro d hd
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have h1 : E (e + 1) = 0 := hE _ (by omega)
  have h2 : E e = 0 := hE _ (by omega)
  simp [shellStep_succ, h1, h2]

/-- Total mass of one adjunction step over an initial window. -/
theorem sum_shellStep (C T : V →+ V) (E : ℕ → V) (n : ℕ) :
    ∑ d ∈ Finset.range (n + 1), shellStep C T E d =
      C (∑ d ∈ Finset.range (n + 1), E d) + T (∑ d ∈ Finset.range n, E d) := by
  induction n with
  | zero => simp [shellStep_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, shellStep_succ, Finset.sum_range_succ E (n + 1),
      Finset.sum_range_succ E n]
    simp only [map_add]
    abel

/-- **Evaluation at `z = 1`.**  On any window containing the degree support, one
prime adjunction of the graded family is the single operator `C + T` applied to
the total.  This is the exact sense in which the physical fibre is the evaluation
of the transfer polynomial at `z = 1`. -/
theorem sum_shellStep_window (C T : V →+ V) {E : ℕ → V} {n N : ℕ}
    (hE : Supported E n) (hn : n < N) :
    ∑ d ∈ Finset.range N, shellStep C T E d =
      (C + T) (∑ d ∈ Finset.range N, E d) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hEm : E m = 0 := hE m (by omega)
  rw [sum_shellStep, Finset.sum_range_succ E m, hEm, add_zero, AddMonoidHom.add_apply]

/-- One adjunction with the three local classes kept separate, as the programme
states it: `E_d^{(j+1)} = C_q E_d^{(j)} + (S_q + W_q) E_{d-1}^{(j)}`. -/
def shellStepThree (C S W : V →+ V) (E : ℕ → V) : ℕ → V := shellStep C (S + W) E

theorem shellStepThree_succ (C S W : V →+ V) (E : ℕ → V) (d : ℕ) :
    shellStepThree C S W E (d + 1) = C (E (d + 1)) + (S + W) (E d) := rfl

/-- **Evaluation at one, three-operator form.**
`evalOne (step_q E) = (C_q + S_q + W_q) (evalOne E)`. -/
theorem sum_shellStepThree_window (C S W : V →+ V) {E : ℕ → V} {n N : ℕ}
    (hE : Supported E n) (hn : n < N) :
    ∑ d ∈ Finset.range N, shellStepThree C S W E d =
      (C + S + W) (∑ d ∈ Finset.range N, E d) := by
  unfold shellStepThree
  rw [sum_shellStep_window C (S + W) hE hn, add_assoc]

/-- Adjoining a whole list of primes, innermost first. -/
def shellSteps (ops : List ((V →+ V) × (V →+ V))) (E : ℕ → V) : ℕ → V :=
  ops.foldr (fun p F => shellStep p.1 p.2 F) E

/-- The transfer product `prod_q (C_q + T_q)` in the same order. -/
def transferProduct (ops : List ((V →+ V) × (V →+ V))) : V →+ V :=
  ops.foldr (fun p F => (p.1 + p.2).comp F) (AddMonoidHom.id V)

theorem shellSteps_nil (E : ℕ → V) : shellSteps [] E = E := rfl

theorem shellSteps_cons (p : (V →+ V) × (V →+ V))
    (ps : List ((V →+ V) × (V →+ V))) (E : ℕ → V) :
    shellSteps (p :: ps) E = shellStep p.1 p.2 (shellSteps ps E) := rfl

theorem transferProduct_cons (p : (V →+ V) × (V →+ V))
    (ps : List ((V →+ V) × (V →+ V))) (v : V) :
    transferProduct (p :: ps) v = (p.1 + p.2) (transferProduct ps v) := rfl

theorem supported_shellSteps :
    ∀ (ops : List ((V →+ V) × (V →+ V))) {E : ℕ → V} {n : ℕ},
      Supported E n → Supported (shellSteps ops E) (n + ops.length) := by
  intro ops
  induction ops with
  | nil => intro E n hE; simpa [shellSteps] using hE
  | cons p ps ih =>
    intro E n hE
    have h : Supported (shellStep p.1 p.2 (shellSteps ps E)) (n + ps.length + 1) :=
      supported_shellStep (ih hE)
    have hlen : (p :: ps).length = ps.length + 1 := by simp
    rw [shellSteps_cons, hlen, ← Nat.add_assoc]
    exact h

/-- **The transfer product is the evaluation of the graded recursion at `z = 1`.**
Over a window wide enough for the whole degree support, adjoining a list of primes
to the graded shells and then totalling is the same as totalling first and then
applying the product of the legal transfer operators. -/
theorem sum_shellSteps :
    ∀ (ops : List ((V →+ V) × (V →+ V))) {E : ℕ → V} {n N : ℕ},
      Supported E n → n + ops.length < N →
      ∑ d ∈ Finset.range N, shellSteps ops E d =
        transferProduct ops (∑ d ∈ Finset.range N, E d) := by
  intro ops
  induction ops with
  | nil => intro E n N _ _; simp [shellSteps, transferProduct]
  | cons p ps ih =>
    intro E n N hE hN
    have hlen : (p :: ps).length = ps.length + 1 := by simp
    rw [hlen] at hN
    have hlt : n + ps.length < N := by omega
    have hps : Supported (shellSteps ps E) (n + ps.length) := supported_shellSteps ps hE
    rw [shellSteps_cons, sum_shellStep_window p.1 p.2 hps hlt, ih hE hlt,
      transferProduct_cons]

/-! ## The tree is ternary

Grading `{C,S,W}^j` by the number of non-`C` coordinates gives shells of size
`choose j d * 2^d`.  Replacing the resolved tree by ordinary Boolean
inclusion-exclusion would keep only `choose j d` states per degree, discarding
`3^9 - 2^9 = 19171` of the `19683` components present at the `29#` diagnostic. -/

/-- Degree shells of a nine-coordinate ternary tree: `choose 9 d * 2 ^ d` states of
degree `d`, with `choose 9 d` running `1, 9, 36, 84, 126, 126, 84, 36, 9, 1`. -/
theorem ternaryLeafCount_nine :
    1 * 2 ^ 0 + 9 * 2 ^ 1 + 36 * 2 ^ 2 + 84 * 2 ^ 3 + 126 * 2 ^ 4 + 126 * 2 ^ 5 +
        84 * 2 ^ 6 + 36 * 2 ^ 7 + 9 * 2 ^ 8 + 1 * 2 ^ 9 = 3 ^ 9 := by
  norm_num

/-- The same shells under a Boolean subset model keep only `choose 9 d` states. -/
theorem booleanLeafCount_nine :
    1 + 9 + 36 + 84 + 126 + 126 + 84 + 36 + 9 + 1 = 2 ^ 9 := by
  norm_num

/-- A Boolean model therefore discards `19171` of the `19683` components. -/
theorem boolean_lt_ternary_nine : 2 ^ 9 + 19171 = 3 ^ 9 := by norm_num

/-! ## The fibre normalization at the bottleneck

Exact recomputed values at `x_* = 1109331447`: the distinguished prime-`2` fibre is
`P_2 = -59685/4` and its support mass is `m_2 = (3/4) A_2` with `A_2 = 718357949`.
Both normalizations quoted for that point are pinned here by exact rational
sandwiches, which is the form a boundedness statement `|P_2| <= C sqrt(m_2)` needs;
no convergence to a universal constant is asserted. -/

/-- `P_2(x_*)`, exactly. -/
def fibreValue : ℚ := -59685 / 4

/-- `m_2(x_*) = (3/4) A_2`, exactly. -/
def fibreMass : ℚ := 3 / 4 * 718357949

theorem fibreValue_eq : fibreValue = -14921.25 := by
  norm_num [fibreValue]

theorem fibreMass_eq : fibreMass = 538768461.75 := by
  norm_num [fibreMass]

/-- `|P_2| / sqrt(m_2) = 0.642841...`, as an exact rational sandwich. -/
theorem fibre_normalization :
    (0.6428 : ℚ) ^ 2 * fibreMass < fibreValue ^ 2 ∧
      fibreValue ^ 2 < (0.6429 : ℚ) ^ 2 * fibreMass := by
  constructor <;> norm_num [fibreValue, fibreMass]

/-- `alpha_2 sqrt(x_*) = 0.92243...` with `alpha_2 = |P_2|/m_2`, again exactly. -/
theorem fibre_scale :
    (0.9224 : ℚ) ^ 2 < (fibreValue / fibreMass) ^ 2 * 1109331447 ∧
      (fibreValue / fibreMass) ^ 2 * 1109331447 < (0.9225 : ℚ) ^ 2 := by
  constructor <;> norm_num [fibreValue, fibreMass]

/-! ## The high-degree tail is not discardable

The signed degree-shell nets reported at the `29#` normalized bottleneck are

```text
E_0 = +510598.977   E_1 = -1352337.222  E_2 = +1014743.270  E_3 = +80096.189
E_4 = -345576.676   E_5 = +58276.938    E_6 = +21526.179    E_7 = -1187.797
E_8 = -1099.593     E_9 = +38.485
```

and `bottleneckShell_sum` checks that they reproduce the independently recomputed
fibre value `P_2(x_*) = -14921.25` exactly. -/

/-- Low-degree head `E_0 + ... + E_4`. -/
def bottleneckHead : ℚ :=
  510598.977 + (-1352337.222) + 1014743.270 + 80096.189 + (-345576.676)

/-- High-degree tail `E_5 + ... + E_9`. -/
def bottleneckTail : ℚ :=
  58276.938 + 21526.179 + (-1187.797) + (-1099.593) + 38.485

theorem bottleneckHead_eq : bottleneckHead = -92475.462 := by
  norm_num [bottleneckHead]

theorem bottleneckTail_eq : bottleneckTail = 77554.212 := by
  norm_num [bottleneckTail]

/-- The reported shells reproduce the independently recomputed fibre value
`P_2(x_*) = -14921.25`. -/
theorem bottleneckShell_sum : bottleneckHead + bottleneckTail = fibreValue := by
  rw [bottleneckHead_eq, bottleneckTail_eq]
  norm_num [fibreValue]

/-- The degree `0..4` head overshoots the net by more than a factor `6`. -/
theorem bottleneckHead_gt : 6 * (14921.25 : ℚ) < -bottleneckHead := by
  rw [bottleneckHead_eq]
  norm_num

/-- The degree `5..9` tail is more than five times the net it stabilizes, so no
theorem may discard it. -/
theorem bottleneckTail_gt : 5 * (14921.25 : ℚ) < bottleneckTail := by
  rw [bottleneckTail_eq]
  norm_num

/-- The general form of the previous two facts: whenever a truncation `H` of a
decomposition overshoots the total `P` by a factor `c + 1`, the discarded tail is
at least `c` times the total.  A large head forces a large tail. -/
theorem abs_tail_ge_of_abs_head_ge {H T P c : ℚ} (hsum : H + T = P)
    (hH : (c + 1) * |P| ≤ |H|) : c * |P| ≤ |T| := by
  have hHP : H - P = -T := by linarith
  have h : |H| - |P| ≤ |T| := by
    have h0 : |H| - |P| ≤ |H - P| := abs_sub_abs_le_abs_sub H P
    rw [hHP, abs_neg] at h0
    exact h0
  linarith

end DegreeShell

end RHLean.Proof
