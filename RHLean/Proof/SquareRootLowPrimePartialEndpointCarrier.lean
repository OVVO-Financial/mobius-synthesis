import Mathlib
import RHLean.Proof.SquareRootLowPrimeStructuralKey
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome
import RHLean.Proof.SquareRootLowPrimeDescendingPivotStability
import RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv

/-!
# The Partial branch of the no-liberty classifier

The final classifier must send every descending terminal survivor to one tagged
endpoint of

`Head ⊔ Partial ⊔ BornExit ⊔ RootEquality`

injectively and with its native weight unchanged.  This file isolates the
`Partial` branch.

The `Partial` summand of the boundary is the compressed unit carrier

`squareRootLowPrimePartialPacketBoundary R K j = range (toNat V)`,
`V = squareRootCrossingLayerPartialPacketInt R K j`,

and **every** one of its cells carries weight `-1`.  The native processed-seat
weight is `-mu c`.  Therefore a survivor can be tagged `Partial` only when
`mu c = 1`; a shallow survivor with `mu c = -1` has native weight `+1` and must
be routed elsewhere.  That sign side condition is proved below, not assumed.

Accordingly the branch is organised as:

* `squareRootLowPrimeShallowDescendingEndpointCarrier` — every non-head shallow
  survivor of the descending matching.  This is what the classifier actually has
  to dispose of.
* `squareRootLowPrimePartialEndpointCarrier` — the `Partial`-eligible subset
  `mu c = 1`.
* `SquareRootLowPrimePartialEndpointBudget` — the *single* remaining arithmetic
  obligation `#P_terminal ≤ toNat V`, stated as a named `Prop` so that no
  downstream file can discharge it by an arithmetic coding of the seat index.
* Everything else — rank, strict bound, injectivity, membership, exact weight
  preservation — is proved outright from that budget.

The rank is the literal position of the endpoint inside its own finite carrier
(`Finset.equivFin`).  It is *not* the seat index and *not* a Möbius-prefix
encoding, precisely because either of those would silently presuppose the
budget.

Because the carrier is sign-homogeneous it has no internal cancellation, so its
signed mass is exactly minus its cardinality.  The obligation therefore has
three interchangeable forms, all recorded here:

* `SquareRootLowPrimePartialEndpointMassIdentity` — `sum w = -V`, the sharpest;
* `card = toNat V` — equivalent to it under `0 ≤ V`;
* `SquareRootLowPrimePartialEndpointBudget` — `card ≤ toNat V`, implied by
  either, and all the branch needs.

The mass form is the one the repository's exact identities speak; note that it
is genuinely an identity to be proved and not a corollary of a bound, since a
bound of the shape `|mass| ≤ card` runs in the opposite direction.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## The shallow survivors the classifier must dispose of -/

/-- Every non-head shallow state surviving the descending matching. -/
def squareRootLowPrimeShallowDescendingEndpointCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U).filter
    fun x => x ≠ none ∧ SquareRootLowPrimeProcessedStateShallow K x

theorem mem_squareRootLowPrimeShallowDescendingEndpointCarrier
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeShallowDescendingEndpointCarrier R K j U ↔
      x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U ∧
        x ≠ none ∧ SquareRootLowPrimeProcessedStateShallow K x := by
  unfold squareRootLowPrimeShallowDescendingEndpointCarrier
  exact Finset.mem_filter

/-- A shallow survivor lies in the underlying processed carrier. -/
theorem squareRootLowPrimeShallowDescendingEndpointCarrier_subset_carrier
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeShallowDescendingEndpointCarrier R K j U) :
    x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
  have hfront :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
        (squareRootLowPrimeFreshPrimeListDescending K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U) :=
    (mem_squareRootLowPrimeShallowDescendingEndpointCarrier.mp hx).1
  exact squareRootLowPrimeProcessedSeatMatchingFrontier_subset'
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U) hfront

/-! ## The `Partial`-eligible subset -/

/-- Shallow survivors whose native weight is exactly the `Partial` cell weight
`-1`, i.e. `mu c = 1`. -/
def squareRootLowPrimePartialEndpointCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeShallowDescendingEndpointCarrier R K j U).filter
    fun x => μ (squareRootLowPrimeProcessedStateCofactor x) = 1

theorem mem_squareRootLowPrimePartialEndpointCarrier
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimePartialEndpointCarrier R K j U ↔
      x ∈ squareRootLowPrimeShallowDescendingEndpointCarrier R K j U ∧
        μ (squareRootLowPrimeProcessedStateCofactor x) = 1 := by
  unfold squareRootLowPrimePartialEndpointCarrier
  exact Finset.mem_filter

theorem squareRootLowPrimePartialEndpointCarrier_subset {R K j U : ℕ} :
    squareRootLowPrimePartialEndpointCarrier R K j U ⊆
      squareRootLowPrimeShallowDescendingEndpointCarrier R K j U := by
  intro x hx
  exact (mem_squareRootLowPrimePartialEndpointCarrier.mp hx).1

/-- Every `Partial`-eligible survivor has exactly the `Partial` cell weight. -/
theorem squareRootLowPrimePartialEndpointCarrier_weight
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimePartialEndpointCarrier R K j U) :
    squareRootLowPrimeProcessedSeatWeightReal x = -1 := by
  have hdata := mem_squareRootLowPrimePartialEndpointCarrier.mp hx
  have hnone :=
    (mem_squareRootLowPrimeShallowDescendingEndpointCarrier.mp hdata.1).2.1
  cases x with
  | none => exact absurd rfl hnone
  | some z =>
      have hmu : μ z.1 = 1 := hdata.2
      simp only [squareRootLowPrimeProcessedSeatWeightReal, hmu]
      norm_num

/-! ## The sign side condition is genuine

A `Partial` cell can only receive a survivor of native weight `-1`.  This is a
third obligation beyond membership and injectivity, and it is not automatic. -/

/-- Matching the `Partial` cell weight forces `mu c = 1`. -/
theorem squareRootLowPrimePartialTag_weight_forces_moebius_one
    {z : ℕ × ℕ} {s : ℕ}
    (h : squareRootLowPrimeNoLibertyBoundaryWeight
          (Sum.inr (Sum.inl s) : SquareRootLowPrimeProcessedSeatNoLibertyState) =
        squareRootLowPrimeProcessedSeatWeightReal (some z)) :
    μ z.1 = 1 := by
  have h' : (-1 : ℝ) = ((-μ z.1 : ℤ) : ℝ) := h
  have hInt : (-1 : ℤ) = -μ z.1 := by exact_mod_cast h'
  omega

/-- Consequently a shallow survivor with `mu c = -1` can never be tagged
`Partial`: its native weight is `+1`. -/
theorem squareRootLowPrimePartialTag_ne_of_moebius_neg
    {z : ℕ × ℕ} (hmu : μ z.1 = -1) (s : ℕ) :
    squareRootLowPrimeNoLibertyBoundaryWeight
        (Sum.inr (Sum.inl s) : SquareRootLowPrimeProcessedSeatNoLibertyState) ≠
      squareRootLowPrimeProcessedSeatWeightReal (some z) := by
  intro h
  have h1 := squareRootLowPrimePartialTag_weight_forces_moebius_one h
  omega

/-- **Exhaustive sign split of the shallow survivors.**  A shallow survivor is
either `Partial`-eligible or carries native weight `+1`, in which case the
`Partial` summand is closed to it and it must be routed to `Head`, `BornExit`
or `RootEquality`. -/
theorem squareRootLowPrimeShallowDescendingEndpointCarrier_sign_cases
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeShallowDescendingEndpointCarrier R K j U) :
    x ∈ squareRootLowPrimePartialEndpointCarrier R K j U ∨
      squareRootLowPrimeProcessedSeatWeightReal x = 1 := by
  have hnone := (mem_squareRootLowPrimeShallowDescendingEndpointCarrier.mp hx).2.1
  have hcarrier := squareRootLowPrimeShallowDescendingEndpointCarrier_subset_carrier hx
  cases x with
  | none => exact absurd rfl hnone
  | some z =>
      have hatom : z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
        simpa [squareRootLowPrimeProcessedSeatCarrier] using hcarrier
      have hsigned := (mem_squareRootLowPrimeProcessedSeatAtoms.mp hatom).1
      have hmuNe : μ z.1 ≠ 0 := (Finset.mem_filter.mp hsigned).2.2
      rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp hmuNe with hmu | hmu
      · exact Or.inl (mem_squareRootLowPrimePartialEndpointCarrier.mpr ⟨hx, hmu⟩)
      · right
        simp only [squareRootLowPrimeProcessedSeatWeightReal, hmu]
        norm_num

/-! ## Structural-key rigidity on the shallow carrier -/

/-- On the shallow survivors the structural key `(shallowBase, seat)` recovers
the literal state.  This is the shallow rigidity that converts equality of
normalized keys back into equality of processed states. -/
theorem squareRootLowPrimeShallowDescendingEndpointCarrier_structuralKey_injOn
    (R K j U : ℕ) :
    Set.InjOn (squareRootLowPrimeProcessedSeatStructuralKey K)
      (squareRootLowPrimeShallowDescendingEndpointCarrier R K j U) := by
  intro x hx y hy hxy
  have hxData :=
    mem_squareRootLowPrimeShallowDescendingEndpointCarrier.mp (Finset.mem_coe.mp hx)
  have hyData :=
    mem_squareRootLowPrimeShallowDescendingEndpointCarrier.mp (Finset.mem_coe.mp hy)
  have hxCarrier :=
    squareRootLowPrimeShallowDescendingEndpointCarrier_subset_carrier
      (Finset.mem_coe.mp hx)
  have hyCarrier :=
    squareRootLowPrimeShallowDescendingEndpointCarrier_subset_carrier
      (Finset.mem_coe.mp hy)
  cases x with
  | none => exact absurd rfl hxData.2.1
  | some zx =>
      cases y with
      | none => exact absurd rfl hyData.2.1
      | some zy =>
          obtain ⟨cx, sx⟩ := zx
          obtain ⟨cy, sy⟩ := zy
          have hxShallow : canonicalLargestPrimeFactor cx ≤ K := hxData.2.2
          have hyShallow : canonicalLargestPrimeFactor cy ≤ K := hyData.2.2
          have hxKey :=
            squareRootLowPrimeProcessedSeatStructuralKey_eq_state_of_shallow
              hxCarrier hxShallow
          have hyKey :=
            squareRootLowPrimeProcessedSeatStructuralKey_eq_state_of_shallow
              hyCarrier hyShallow
          have hpair : (cx, sx) = (cy, sy) := by
            rw [← hxKey, ← hyKey]
            exact hxy
          rw [hpair]

/-- The same rigidity restricted to the `Partial`-eligible carrier. -/
theorem squareRootLowPrimePartialEndpointCarrier_structuralKey_injOn
    (R K j U : ℕ) :
    Set.InjOn (squareRootLowPrimeProcessedSeatStructuralKey K)
      (squareRootLowPrimePartialEndpointCarrier R K j U) := by
  intro x hx y hy hxy
  have hx' : x ∈ squareRootLowPrimeShallowDescendingEndpointCarrier R K j U :=
    (mem_squareRootLowPrimePartialEndpointCarrier.mp (Finset.mem_coe.mp hx)).1
  have hy' : y ∈ squareRootLowPrimeShallowDescendingEndpointCarrier R K j U :=
    (mem_squareRootLowPrimePartialEndpointCarrier.mp (Finset.mem_coe.mp hy)).1
  exact squareRootLowPrimeShallowDescendingEndpointCarrier_structuralKey_injOn
    R K j U (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy') hxy

/-! ## The single remaining arithmetic obligation -/

/-- **`#P_terminal ≤ toNat V`.**

This is the whole content of the `Partial` branch.  It is deliberately a named
`Prop` rather than a proved theorem: the compressed packet target
`range (toNat V)` is an already-cancelled signed residual, so no coding of the
seat index may be used to manufacture it. -/
def SquareRootLowPrimePartialEndpointBudget (R K j U : ℕ) : Prop :=
  (squareRootLowPrimePartialEndpointCarrier R K j U).card ≤
    Int.toNat (squareRootCrossingLayerPartialPacketInt R K j)

/-- The `Partial` carrier has no internal cancellation: its signed mass is
exactly minus its cardinality. -/
theorem squareRootLowPrimePartialEndpointCarrier_weight_sum
    (R K j U : ℕ) :
    (∑ x ∈ squareRootLowPrimePartialEndpointCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      -((squareRootLowPrimePartialEndpointCarrier R K j U).card : ℝ) := by
  have hconst :
      (∑ x ∈ squareRootLowPrimePartialEndpointCarrier R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ _x ∈ squareRootLowPrimePartialEndpointCarrier R K j U, (-1 : ℝ) :=
    Finset.sum_congr rfl fun x hx =>
      squareRootLowPrimePartialEndpointCarrier_weight hx
  rw [hconst]
  simp

/-- **Mass form of the budget.**  Because the `Partial` carrier is
sign-homogeneous, the cardinality obligation is *equivalent* to the statement
that the signed mass of the shallow `mu = 1` survivors is at least `-V`.  This
is the currency in which the repository's exact identities are stated. -/
theorem squareRootLowPrimePartialEndpointCarrier_budget_iff_mass
    {R K j U : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j) :
    SquareRootLowPrimePartialEndpointBudget R K j U ↔
      -((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) ≤
        ∑ x ∈ squareRootLowPrimePartialEndpointCarrier R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  have hmass := squareRootLowPrimePartialEndpointCarrier_weight_sum R K j U
  have hcast :
      ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℤ) =
        squareRootCrossingLayerPartialPacketInt R K j :=
    Int.toNat_of_nonneg hV0
  have hcastR :
      ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℝ) =
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) := by
    exact_mod_cast hcast
  unfold SquareRootLowPrimePartialEndpointBudget
  rw [hmass]
  constructor
  · intro h
    have hR :
        (((squareRootLowPrimePartialEndpointCarrier R K j U).card : ℕ) : ℝ) ≤
          ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [hcastR] at hR
    linarith
  · intro h
    have hR :
        (((squareRootLowPrimePartialEndpointCarrier R K j U).card : ℕ) : ℝ) ≤
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) := by
      linarith
    rw [← hcastR] at hR
    exact_mod_cast hR

/-! ## Exact signed-mass form of the obligation

The sharper obligation is the *equality* `sum w = -V`.  Because the carrier is
sign-homogeneous this is equivalent to `#P_terminal = toNat V`, and it implies
the budget.  Recording all three forms and their equivalences keeps the eventual
proof from being restated in a weaker shape by accident. -/

/-- **Exact signed-mass identification of the `Partial` carrier.** -/
def SquareRootLowPrimePartialEndpointMassIdentity (R K j U : ℕ) : Prop :=
  (∑ x ∈ squareRootLowPrimePartialEndpointCarrier R K j U,
      squareRootLowPrimeProcessedSeatWeightReal x) =
    -((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ)

/-- The mass identity is exactly the exact-cardinality statement. -/
theorem squareRootLowPrimePartialEndpointCarrier_massIdentity_iff_card_eq
    {R K j U : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j) :
    SquareRootLowPrimePartialEndpointMassIdentity R K j U ↔
      (squareRootLowPrimePartialEndpointCarrier R K j U).card =
        Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) := by
  have hmass := squareRootLowPrimePartialEndpointCarrier_weight_sum R K j U
  have hcast :
      ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℤ) =
        squareRootCrossingLayerPartialPacketInt R K j :=
    Int.toNat_of_nonneg hV0
  have hcastR :
      ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℝ) =
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) := by
    exact_mod_cast hcast
  unfold SquareRootLowPrimePartialEndpointMassIdentity
  rw [hmass]
  constructor
  · intro h
    have hR :
        (((squareRootLowPrimePartialEndpointCarrier R K j U).card : ℕ) : ℝ) =
          ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℝ) := by
      rw [hcastR]
      linarith
    exact_mod_cast hR
  · intro h
    have hR :
        (((squareRootLowPrimePartialEndpointCarrier R K j U).card : ℕ) : ℝ) =
          ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    rw [hcastR] at hR
    linarith

/-- The exact mass identity implies the budget used by the branch. -/
theorem squareRootLowPrimePartialEndpointBudget_of_massIdentity
    {R K j U : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hmass : SquareRootLowPrimePartialEndpointMassIdentity R K j U) :
    SquareRootLowPrimePartialEndpointBudget R K j U := by
  unfold SquareRootLowPrimePartialEndpointBudget
  exact le_of_eq
    ((squareRootLowPrimePartialEndpointCarrier_massIdentity_iff_card_eq
      hV0).mp hmass)

/-! ## Post-rematching presentation of the carrier

The classifier reaches the `Partial` branch only after `Head`, `BornExit` and
the Go strict-crossing/root fallback have been removed.  Whatever concrete
removal predicate that turns out to be, the branch machinery applies verbatim
as soon as the surviving shallow states are sign-homogeneous — which is the
content of "on that carrier every native weight is `-1`". -/

/-- Shallow survivors left after an arbitrary removal pass. -/
def squareRootLowPrimePartialTerminalCarrier
    (R K j U : ℕ)
    (removed : SquareRootLowPrimeProcessedState → Prop) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeShallowDescendingEndpointCarrier R K j U).filter
    fun x => ¬ removed x

theorem mem_squareRootLowPrimePartialTerminalCarrier
    {R K j U : ℕ} {removed : SquareRootLowPrimeProcessedState → Prop}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimePartialTerminalCarrier R K j U removed ↔
      x ∈ squareRootLowPrimeShallowDescendingEndpointCarrier R K j U ∧
        ¬ removed x := by
  unfold squareRootLowPrimePartialTerminalCarrier
  exact Finset.mem_filter

/-- Sign homogeneity of the post-rematching carrier is exactly what places it
inside the `Partial`-eligible carrier. -/
theorem squareRootLowPrimePartialTerminalCarrier_subset_of_sign
    {R K j U : ℕ} {removed : SquareRootLowPrimeProcessedState → Prop}
    (hsign : ∀ x ∈ squareRootLowPrimePartialTerminalCarrier R K j U removed,
      μ (squareRootLowPrimeProcessedStateCofactor x) = 1) :
    squareRootLowPrimePartialTerminalCarrier R K j U removed ⊆
      squareRootLowPrimePartialEndpointCarrier R K j U := by
  intro x hx
  exact mem_squareRootLowPrimePartialEndpointCarrier.mpr
    ⟨(mem_squareRootLowPrimePartialTerminalCarrier.mp hx).1, hsign x hx⟩

/-- A sign-homogeneous post-rematching carrier inherits the whole `Partial`
branch: its own signed mass is minus its cardinality, and the budget for the
larger `Partial`-eligible carrier bounds its rank. -/
theorem squareRootLowPrimePartialTerminalCarrier_weight_sum_of_sign
    {R K j U : ℕ} {removed : SquareRootLowPrimeProcessedState → Prop}
    (hsign : ∀ x ∈ squareRootLowPrimePartialTerminalCarrier R K j U removed,
      μ (squareRootLowPrimeProcessedStateCofactor x) = 1) :
    (∑ x ∈ squareRootLowPrimePartialTerminalCarrier R K j U removed,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      -((squareRootLowPrimePartialTerminalCarrier R K j U removed).card : ℝ) := by
  have hsub := squareRootLowPrimePartialTerminalCarrier_subset_of_sign hsign
  have hconst :
      (∑ x ∈ squareRootLowPrimePartialTerminalCarrier R K j U removed,
          squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ _x ∈ squareRootLowPrimePartialTerminalCarrier R K j U removed,
          (-1 : ℝ) :=
    Finset.sum_congr rfl fun x hx =>
      squareRootLowPrimePartialEndpointCarrier_weight (hsub hx)
  rw [hconst]
  simp

/-! ## Rank inside the carrier

The rank is the position of the endpoint in its own finite carrier.  Nothing
arithmetic enters; in particular the seat index is never used. -/

/-- Position of a `Partial` endpoint inside its own finite carrier. -/
noncomputable def squareRootLowPrimePartialRank
    (R K j U : ℕ)
    (x : ↥(squareRootLowPrimePartialEndpointCarrier R K j U)) : ℕ :=
  ((squareRootLowPrimePartialEndpointCarrier R K j U).equivFin x).val

theorem squareRootLowPrimePartialRank_lt_card
    (R K j U : ℕ)
    (x : ↥(squareRootLowPrimePartialEndpointCarrier R K j U)) :
    squareRootLowPrimePartialRank R K j U x <
      (squareRootLowPrimePartialEndpointCarrier R K j U).card :=
  ((squareRootLowPrimePartialEndpointCarrier R K j U).equivFin x).isLt

/-- **`partialRank_lt`.**  Once the budget is available the rank lands strictly
inside the compressed packet. -/
theorem squareRootLowPrimePartialRank_lt
    {R K j U : ℕ}
    (hbudget : SquareRootLowPrimePartialEndpointBudget R K j U)
    (x : ↥(squareRootLowPrimePartialEndpointCarrier R K j U)) :
    squareRootLowPrimePartialRank R K j U x <
      Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) :=
  lt_of_lt_of_le (squareRootLowPrimePartialRank_lt_card R K j U x) hbudget

theorem squareRootLowPrimePartialRank_injective
    (R K j U : ℕ) :
    Function.Injective (squareRootLowPrimePartialRank R K j U) := by
  intro x y hxy
  have hval :
      ((squareRootLowPrimePartialEndpointCarrier R K j U).equivFin x).val =
        ((squareRootLowPrimePartialEndpointCarrier R K j U).equivFin y).val :=
    hxy
  have hfin :
      ((squareRootLowPrimePartialEndpointCarrier R K j U).equivFin x) =
        ((squareRootLowPrimePartialEndpointCarrier R K j U).equivFin y) :=
    Fin.val_injective hval
  exact ((squareRootLowPrimePartialEndpointCarrier R K j U).equivFin).injective hfin

/-! ## The tagged `Partial` branch -/

/-- The `Partial` constructor of the final tagged boundary. -/
def squareRootLowPrimePartialBoundaryTag (s : ℕ) :
    SquareRootLowPrimeProcessedSeatNoLibertyState :=
  Sum.inr (Sum.inl s)

/-- The classifier map on the `Partial` branch. -/
noncomputable def squareRootLowPrimePartialBranchMap
    (R K j U : ℕ)
    (x : ↥(squareRootLowPrimePartialEndpointCarrier R K j U)) :
    SquareRootLowPrimeProcessedSeatNoLibertyState :=
  squareRootLowPrimePartialBoundaryTag (squareRootLowPrimePartialRank R K j U x)

theorem squareRootLowPrimePartialBranchMap_mem
    {R K j U : ℕ}
    (hbudget : SquareRootLowPrimePartialEndpointBudget R K j U)
    (x : ↥(squareRootLowPrimePartialEndpointCarrier R K j U)) :
    squareRootLowPrimePartialBranchMap R K j U x ∈
      squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U := by
  simpa [squareRootLowPrimePartialBranchMap, squareRootLowPrimePartialBoundaryTag,
    squareRootLowPrimeProcessedSeatNoLibertyBoundary,
    squareRootLowPrimePartialPacketBoundary] using
      squareRootLowPrimePartialRank_lt hbudget x

theorem squareRootLowPrimePartialBranchMap_injective
    (R K j U : ℕ) :
    Function.Injective (squareRootLowPrimePartialBranchMap R K j U) := by
  intro x y hxy
  apply squareRootLowPrimePartialRank_injective R K j U
  simpa [squareRootLowPrimePartialBranchMap, squareRootLowPrimePartialBoundaryTag]
    using hxy

/-- **Exact weight preservation on the `Partial` branch.** -/
theorem squareRootLowPrimePartialBranchMap_weight_eq
    {R K j U : ℕ}
    (x : ↥(squareRootLowPrimePartialEndpointCarrier R K j U)) :
    squareRootLowPrimeNoLibertyBoundaryWeight
        (squareRootLowPrimePartialBranchMap R K j U x) =
      squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState) := by
  rw [squareRootLowPrimePartialEndpointCarrier_weight x.2]
  rfl

/-- Packaged `Partial` branch of the final pointwise classifier. -/
structure SquareRootLowPrimePartialBranchEmbedding (R K j U : ℕ) where
  toFun : ↥(squareRootLowPrimePartialEndpointCarrier R K j U) →
    SquareRootLowPrimeProcessedSeatNoLibertyState
  mem : ∀ x, toFun x ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U
  partialTag : ∀ x, ∃ s : ℕ, toFun x = squareRootLowPrimePartialBoundaryTag s
  injective : Function.Injective toFun
  weight_eq : ∀ x,
    squareRootLowPrimeNoLibertyBoundaryWeight (toFun x) =
      squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState)

/-- **The `Partial` branch is complete modulo the budget.**  Membership,
injectivity and exact weight preservation all follow; nothing else remains. -/
noncomputable def squareRootLowPrimePartialBranchEmbedding_of_budget
    {R K j U : ℕ}
    (hbudget : SquareRootLowPrimePartialEndpointBudget R K j U) :
    SquareRootLowPrimePartialBranchEmbedding R K j U where
  toFun := squareRootLowPrimePartialBranchMap R K j U
  mem x := squareRootLowPrimePartialBranchMap_mem hbudget x
  partialTag x := ⟨squareRootLowPrimePartialRank R K j U x, rfl⟩
  injective := squareRootLowPrimePartialBranchMap_injective R K j U
  weight_eq x := squareRootLowPrimePartialBranchMap_weight_eq x

/-- The tagged `Partial` branch is disjoint from the `Head` and `BornExit`
constructors, so cross-branch injectivity of the final classifier will be
automatic from the `Sum` tags. -/
theorem squareRootLowPrimePartialBoundaryTag_ne_head (s : ℕ) :
    squareRootLowPrimePartialBoundaryTag s ≠
      (Sum.inl () : SquareRootLowPrimeProcessedSeatNoLibertyState) := by
  simp [squareRootLowPrimePartialBoundaryTag]

theorem squareRootLowPrimePartialBoundaryTag_ne_born (s : ℕ) (a : ℕ × ℕ) :
    squareRootLowPrimePartialBoundaryTag s ≠
      (Sum.inr (Sum.inr (Sum.inl a)) :
        SquareRootLowPrimeProcessedSeatNoLibertyState) := by
  simp [squareRootLowPrimePartialBoundaryTag]

theorem squareRootLowPrimePartialBoundaryTag_ne_rootEquality
    (s : ℕ) (w : (ℕ × ℕ) × ℕ) :
    squareRootLowPrimePartialBoundaryTag s ≠
      (Sum.inr (Sum.inr (Sum.inr w)) :
        SquareRootLowPrimeProcessedSeatNoLibertyState) := by
  simp [squareRootLowPrimePartialBoundaryTag]

/-! ## The root fallback is empty for most roots

Membership in `squareRootLowPrimeGoRootEqualityDefectCarrier R` requires
`r * q = R` on the nose, with `r < q` both prime.  So the class is empty unless
`R` is a product of two distinct primes.

This matters for the routing of the shallow survivors.  A shallow survivor with
`mu c = -1` has native weight `+1`, so the `Partial` summand is closed to it by
`squareRootLowPrimePartialTag_ne_of_moebius_neg`.  At a root where the carrier
below is empty there is no root cell either, and the repository's `BornExit`
construction applies only to *deep* processed seats.  Since the downstream
statements quantify over all large `R` — prime roots included — the shallow
residual cannot in general be discharged by "Partial or the root fallback". -/

/-- The root-equality class is empty at every root admitting no factorisation
into two distinct primes. -/
theorem squareRootLowPrimeGoRootEqualityDefectCarrier_eq_empty_of_no_prime_pair
    {R : ℕ}
    (h : ∀ r q : ℕ, r.Prime → q.Prime → r < q → r * q ≠ R) :
    squareRootLowPrimeGoRootEqualityDefectCarrier R = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro z hz
  obtain ⟨⟨r, q⟩, d⟩ := z
  obtain ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hprod, _hcube, _hd⟩ :=
    mem_squareRootLowPrimeGoRootEqualityDefectCarrier.mp hz
  exact h r q hr hq hrq hprod

/-- In particular the root fallback is empty at every prime root. -/
theorem squareRootLowPrimeGoRootEqualityDefectCarrier_eq_empty_of_prime
    {R : ℕ} (hR : R.Prime) :
    squareRootLowPrimeGoRootEqualityDefectCarrier R = ∅ := by
  apply squareRootLowPrimeGoRootEqualityDefectCarrier_eq_empty_of_no_prime_pair
  intro r q hr hq _hrq hprod
  have hrdvd : r ∣ R := ⟨q, hprod.symm⟩
  rcases hR.eq_one_or_self_of_dvd r hrdvd with h1 | hrR
  · exact hr.one_lt.ne' h1
  · rw [hrR] at hprod
    have hq1 : R * q = R * 1 := by simpa using hprod
    exact hq.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hR.pos hq1)

/-- At such a root the tagged boundary loses its whole fourth class, so the
budget sharpens accordingly. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyBoundary_card_eq_of_empty_root
    {R K j U : ℕ}
    (hroot : squareRootLowPrimeGoRootEqualityDefectCarrier R = ∅) :
    (squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U).card =
      1 + (squareRootLowPrimePartialPacketBoundary R K j).card +
        (squareRootLowPrimeBornNoSuccessorAtoms R K U).card := by
  simp only [squareRootLowPrimeProcessedSeatNoLibertyBoundary, hroot,
    Finset.card_disjSum, Finset.card_singleton, Finset.card_empty]
  omega

/-! ## The `4R` bound does not need an injective classifier

The pointwise embedding interface asks for an *injection* of the descending
frontier into the tagged boundary, which forces the boundary to be
cardinality-faithful.  The compressed `Partial` class is not: it represents the
shallow residual by `toNat V` cells of weight `-1`, which is faithful to the
residual's *mass* and lossy on its *cardinality* — the shallow survivors of
either sign both contribute cells, while `V` records only their difference.

But the downstream target `|runningImbalance| ≤ 4R` never used injectivity for
its own sake; it used it only to move mass from the source to the target.  An
aggregate mass identity does that directly, and is strictly weaker: it needs no
exhaustive four-way classification, no injectivity, and no sign homogeneity of
the shallow survivors. -/

/-- **Aggregate mass transfer suffices.**  If the descending terminal frontier
and the tagged boundary carry the same signed mass, the `4R` bound follows —
with no classifier, no injection, and no exhaustiveness claim. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_massTransfer
    {R K j : ℕ} (hR : 2 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hmass :
      (∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j
          (squareRootBornPostTailLowPrimeCutoff R),
          squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j
            (squareRootBornPostTailLowPrimeCutoff R),
          squareRootLowPrimeNoLibertyBoundaryWeight z) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ 4 * (R : ℝ) := by
  rw [← squareRootLowPrimeProcessedSeatDescendingTerminalFrontier_weight_sum hR,
    hmass]
  have hmassLe := abs_squareRootLowPrimeNoLibertyBoundaryMass_le_card
    R K j (squareRootBornPostTailLowPrimeCutoff R)
  have hcard := squareRootLowPrimeProcessedSeatNoLibertyBoundary_card_le_four_root
    (R := R) (K := K) (j := j) (by omega) hKR hV0 hVK
  exact hmassLe.trans (by exact_mod_cast hcard)

/-- The same transfer in the form the classifier work would actually produce:
a weight-preserving injection is one way to get the mass identity, but any
mass-preserving decomposition of the frontier will do. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_massTransfer'
    {R K j : ℕ} (hR : 2 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hmass :
      squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) =
        ∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j
            (squareRootBornPostTailLowPrimeCutoff R),
          squareRootLowPrimeNoLibertyBoundaryWeight z) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ 4 * (R : ℝ) := by
  rw [hmass]
  have hmassLe := abs_squareRootLowPrimeNoLibertyBoundaryMass_le_card
    R K j (squareRootBornPostTailLowPrimeCutoff R)
  have hcard := squareRootLowPrimeProcessedSeatNoLibertyBoundary_card_le_four_root
    (R := R) (K := K) (j := j) (by omega) hKR hV0 hVK
  exact hmassLe.trans (by exact_mod_cast hcard)

/-! ## Closed form of the boundary mass

The tagged boundary is a disjoint sum of four explicit carriers, so its signed
mass has a closed form with no survivor set in it: the head contributes `1`, the
compressed packet contributes `-V`, and the remaining two blocks are sums of
Möbius values over the BornExit atoms and the root-equality incidences.

Combined with `..._DescendingTerminalFrontier_weight_sum`, this turns the whole
mass-transfer programme into **one explicit arithmetic identity** between
already-defined quantities.  In particular it does not require choosing a
shallow/deep decomposition of the frontier — which matters, because the
descending matching does not respect that split: every matched edge
`(c,s) ↔ (p·c,s)` adjoins a prime above `K`, so it is shallow-to-deep or
deep-to-deep.  The shallow block's mass is therefore not preserved by the
cancellation, and no identity for it follows from the packet identity alone. -/

/-- Signed mass of the BornExit block. -/
def squareRootLowPrimeBornExitBoundaryMassReal (R K U : ℕ) : ℝ :=
  ∑ a ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U,
    ((μ (squareRootLowPrimeBadAtomChild a) : ℤ) : ℝ)

/-- Signed mass of the root-equality block. -/
def squareRootLowPrimeRootEqualityBoundaryMassReal (R : ℕ) : ℝ :=
  ∑ w ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R,
    ((μ (w.1.2 * w.2) : ℤ) : ℝ)

/-- The root-equality block vanishes exactly when its carrier is empty, which
by `..._eq_empty_of_prime` is the case at every prime root. -/
@[simp] theorem squareRootLowPrimeRootEqualityBoundaryMassReal_of_empty
    {R : ℕ} (hroot : squareRootLowPrimeGoRootEqualityDefectCarrier R = ∅) :
    squareRootLowPrimeRootEqualityBoundaryMassReal R = 0 := by
  unfold squareRootLowPrimeRootEqualityBoundaryMassReal
  rw [hroot]
  simp

/-- **Closed form of the tagged boundary mass.** -/
theorem squareRootLowPrimeNoLibertyBoundary_mass_closed_form
    {R K j U : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j) :
    (∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        squareRootLowPrimeNoLibertyBoundaryWeight z) =
      1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
        squareRootLowPrimeBornExitBoundaryMassReal R K U +
        squareRootLowPrimeRootEqualityBoundaryMassReal R := by
  have hcast :
      ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℤ) =
        squareRootCrossingLayerPartialPacketInt R K j :=
    Int.toNat_of_nonneg hV0
  have hcastR :
      ((Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℕ) : ℝ) =
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) := by
    exact_mod_cast hcast
  have hhead :
      (∑ u ∈ ({()} : Finset Unit),
        squareRootLowPrimeNoLibertyBoundaryWeight
          (Sum.inl u : SquareRootLowPrimeProcessedSeatNoLibertyState)) = 1 := by
    rw [Finset.sum_singleton]
    exact squareRootLowPrimeNoLibertyBoundaryWeight_head ()
  have hpartial :
      (∑ s ∈ squareRootLowPrimePartialPacketBoundary R K j,
        squareRootLowPrimeNoLibertyBoundaryWeight
          (Sum.inr (Sum.inl s) :
            SquareRootLowPrimeProcessedSeatNoLibertyState)) =
        -((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) := by
    have hconst :
        (∑ s ∈ squareRootLowPrimePartialPacketBoundary R K j,
          squareRootLowPrimeNoLibertyBoundaryWeight
            (Sum.inr (Sum.inl s) :
              SquareRootLowPrimeProcessedSeatNoLibertyState)) =
          ∑ _s ∈ squareRootLowPrimePartialPacketBoundary R K j, (-1 : ℝ) :=
      Finset.sum_congr rfl fun _s _hs => rfl
    rw [hconst, Finset.sum_const, squareRootLowPrimePartialPacketBoundary_card,
      nsmul_eq_mul, mul_neg_one, hcastR]
  have hborn :
      (∑ a ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U,
        squareRootLowPrimeNoLibertyBoundaryWeight
          (Sum.inr (Sum.inr (Sum.inl a)) :
            SquareRootLowPrimeProcessedSeatNoLibertyState)) =
        squareRootLowPrimeBornExitBoundaryMassReal R K U :=
    Finset.sum_congr rfl fun _a _ha => rfl
  have hroot :
      (∑ w ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R,
        squareRootLowPrimeNoLibertyBoundaryWeight
          (Sum.inr (Sum.inr (Sum.inr w)) :
            SquareRootLowPrimeProcessedSeatNoLibertyState)) =
        squareRootLowPrimeRootEqualityBoundaryMassReal R :=
    Finset.sum_congr rfl fun _w _hw => rfl
  unfold squareRootLowPrimeProcessedSeatNoLibertyBoundary
  simp only [Finset.sum_disjSum]
  rw [hhead, hpartial, hborn, hroot]
  ring

/-- **The mass-transfer identity is one explicit arithmetic statement.**  No
frontier, no survivor set, no classifier appears on the right. -/
theorem squareRootLowPrimeMassTransfer_iff_closedForm
    {R K j U : ℕ} (hR : 2 ≤ R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j) :
    ((∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        squareRootLowPrimeNoLibertyBoundaryWeight z) ↔
      squareRootLowPrimeRunningImbalanceReal R K j U =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R := by
  rw [squareRootLowPrimeProcessedSeatDescendingTerminalFrontier_weight_sum hR,
    squareRootLowPrimeNoLibertyBoundary_mass_closed_form hV0]

/-- **The whole remaining programme, in one hypothesis.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_closedForm
    {R K j : ℕ} (hR : 2 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (h : squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K
            (squareRootBornPostTailLowPrimeCutoff R) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ 4 * (R : ℝ) := by
  refine abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_massTransfer'
    hR hKR hV0 hVK ?_
  rw [h, squareRootLowPrimeNoLibertyBoundary_mass_closed_form hV0]

end RHLean.Proof
