import RHLean.Proof.ExceptionalContactFrameEnergyNoGo

/-!
# Physical q^2 bookkeeping synthesis after an earlier layer

This module closes the owner-partition bookkeeping that remains after the exact
arbitrary-prefix q^2 telescope.

The important ordering is unchanged: signed physical reassembly first, energy
second.  In particular, the fibre partition below is an identity for an
arbitrary additive observable.  It is applied to the intact coefficient-level
q^2 daughter only after the least-square owner has been assigned.

Two points are made explicit.

* Prime `2` is not a physical square-contact owner.  Its algebraic two-step
  `q^2` remainder is nevertheless nonzero in general: it is exactly the
  offset-four floor crossing `mu(k+1)`.  Thus the physical owner recursion is
  genuinely an odd-prime recursion; `2` is part of the base mod-four geometry,
  not another contact channel.
* For every prime `q >= 3`, the full physical `q^2` hit carrier partitions
  disjointly by its actual least odd square-prime owner `r <= q`.  Summing the
  genuine q^2 daughter over those owner fibres therefore recovers the
  Mertens daughter exactly, at every cutoff and with no endpoint error.

No frame estimate, selected-prime tensor transfer, or Mertens cancellation is
proved here.  The purpose is to make the all-prime lower-triangular owner
reassembly a literal theorem so that any remaining parent/interior estimate
cannot hide ownership or q=2 bookkeeping.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## 1. Prime two is base geometry, not a physical q^2 contact owner -/

/-- No active physical transition offset is hit by `2^2`. -/
theorem not_physicalSquarePrimeAtEdge_two (k : ℕ) :
    ¬ physicalSquarePrimeAtEdge k 2 := by
  intro h
  have hodd := physicalSquarePrimeAtEdge_odd h
  norm_num at hodd

/-- Consequently the literal physical `2^2` contact carrier is empty. -/
theorem physicalSquareHitCells_two_eq_empty (K : ℕ) :
    physicalSquareHitCells K 2 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hdata := (mem_physicalSquareHitCells_iff Nat.prime_two).mp hk
  exact not_physicalSquarePrimeAtEdge_two k hdata.2

/-- The algebraic two-step `2^2` remainder is not zero: it is the one-step
Möbius increment across the omitted offset-four site.  This is why `q=2` must
not be silently inserted into the physical contact recursion. -/
theorem physicalQ2DaughterCellIncrement_two (k : ℕ) :
    physicalQ2DaughterCellIncrement 2 k = μ (k + 1) := by
  rw [physicalQ2DaughterCellIncrement_eq]
  have hlo : 4 * k / (2 * 2) = k := by omega
  have hhi : 4 * (k + 1) / (2 * 2) = k + 1 := by omega
  rw [hlo, hhi, moebiusPositivePrefix_succ_sub_self]

/-- Executable separation of the two notions at the first cell: the physical
contact sum is zero while the algebraic square-shift daughter is one. -/
theorem physicalQ2Daughter_two_contact_support_noGo :
    (∑ k ∈ physicalSquareHitCells 1 2,
        physicalQ2DaughterCellIncrement 2 k) = 0 ∧
      (∑ k ∈ Finset.range 1,
        physicalQ2DaughterCellIncrement 2 k) = 1 := by
  constructor
  · rw [physicalSquareHitCells_two_eq_empty]
    simp
  · simp [physicalQ2DaughterCellIncrement_two]

/-! ## 2. Generic lower-triangular owner partition for every prime q -/

/-- All possible physical least owners below a current prime `q`.  Prime `2`
is erased because the six-offset physical geometry has no `2^2` contact. -/
def physicalOddPrimeOwnersUpTo (q : ℕ) : Finset ℕ :=
  (primesUpTo q).erase 2

@[simp] theorem mem_physicalOddPrimeOwnersUpTo {r q : ℕ} :
    r ∈ physicalOddPrimeOwnersUpTo q ↔
      r.Prime ∧ r ≤ q ∧ r ≠ 2 := by
  unfold physicalOddPrimeOwnersUpTo
  constructor
  · intro hr
    have herase := Finset.mem_erase.mp hr
    have hp := mem_primesUpTo.mp herase.2
    exact ⟨hp.1, hp.2, herase.1⟩
  · rintro ⟨hrPrime, hrq, hr2⟩
    exact Finset.mem_erase.mpr
      ⟨hr2, mem_primesUpTo.mpr ⟨hrPrime, hrq⟩⟩

/-- Any actual square hit forces the least-square owner to exist. -/
theorem physicalLeastOddSquarePrime_exists_of_squareHit
    {k q : ℕ} (hqhit : physicalSquarePrimeAtEdge k q) :
    ∃ r : ℕ, physicalLeastOddSquarePrime k = some r := by
  cases howner : physicalLeastOddSquarePrime k with
  | none =>
      have hnone := (physicalLeastOddSquarePrime_eq_none_iff k).mp howner
      exact (hnone ⟨q, hqhit⟩).elim
  | some r =>
      exact ⟨r, rfl⟩

/-- If a cell is hit by `q^2`, its least owner is an odd prime no larger than
`q`.  This is the generic version of the special `5 -> {3,5}` and
`7 -> {3,5,7}` triangular partitions. -/
theorem physicalLeastOwner_mem_oddPrimeOwnersUpTo_of_squareHit
    {k q r : ℕ} (hqhit : physicalSquarePrimeAtEdge k q)
    (howner : physicalLeastOddSquarePrime k = some r) :
    r ∈ physicalOddPrimeOwnersUpTo q := by
  have hrhit := physicalLeastOddSquarePrime_some_spec howner
  have hrle := physicalLeastOddSquarePrime_le howner hqhit
  have hrne2 : r ≠ 2 := by
    intro hr2
    subst r
    exact not_physicalSquarePrimeAtEdge_two k hrhit
  exact mem_physicalOddPrimeOwnersUpTo.mpr
    ⟨hrhit.1, hrle, hrne2⟩

/-- The complete `q^2` hit carrier is exactly the union of its genuine least
odd-prime owner fibres.  This holds for every prime `q`; for `q=2` both sides
are empty. -/
theorem physicalSquareHitCells_eq_oddPrimeOwnerPartition
    {K q : ℕ} (hq : q.Prime) :
    physicalSquareHitCells K q =
      (physicalOddPrimeOwnersUpTo q).biUnion fun r =>
        physicalCellsOwnedBy (physicalSquareHitCells K q) r := by
  ext k
  constructor
  · intro hk
    have hdata := (mem_physicalSquareHitCells_iff hq).mp hk
    obtain ⟨r, howner⟩ :=
      physicalLeastOddSquarePrime_exists_of_squareHit hdata.2
    have hr :=
      physicalLeastOwner_mem_oddPrimeOwnersUpTo_of_squareHit hdata.2 howner
    exact Finset.mem_biUnion.mpr
      ⟨r, hr, mem_physicalCellsOwnedBy.mpr ⟨hk, howner⟩⟩
  · intro hk
    rcases Finset.mem_biUnion.mp hk with ⟨r, _hr, hkr⟩
    exact (mem_physicalCellsOwnedBy.mp hkr).1

private theorem option_getD_zero_eq_prime_iff
    {o : Option ℕ} {r : ℕ} (hr : r.Prime) :
    o.getD 0 = r ↔ o = some r := by
  constructor
  · intro h
    cases ho : o with
    | none =>
        simp [ho] at h
        exact (hr.ne_zero h.symm).elim
    | some p =>
        simp [ho] at h
        subst p
        rfl
  · intro h
    rw [h]
    simp

/-- The `getD 0` owner fibre used by `Finset.sum_fiberwise_of_maps_to` is
literally the repository's `physicalCellsOwnedBy` fibre whenever the label is
prime. -/
theorem physicalOwnerGetDFiber_eq_cellsOwnedBy
    (S : Finset ℕ) {r : ℕ} (hr : r.Prime) :
    S.filter (fun k => (physicalLeastOddSquarePrime k).getD 0 = r) =
      physicalCellsOwnedBy S r := by
  ext k
  simp only [Finset.mem_filter, mem_physicalCellsOwnedBy]
  rw [option_getD_zero_eq_prime_iff hr]

/-- **Generic signed owner reassembly.**  The full physical `q^2` hit carrier
is the disjoint fibrewise sum over all possible least owners `r <= q`.  The
observable is arbitrary, so no sign, multiplicity, response, mate, or future
transport weight is changed by this reindexing. -/
theorem physicalSquareHit_sum_eq_sum_oddPrimeOwners
    {A : Type*} [AddCommMonoid A]
    {K q : ℕ} (hq : q.Prime) (f : ℕ → A) :
    (∑ k ∈ physicalSquareHitCells K q, f k) =
      ∑ r ∈ physicalOddPrimeOwnersUpTo q,
        ∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K q) r, f k := by
  let S : Finset ℕ := physicalSquareHitCells K q
  let owner : ℕ → ℕ := fun k => (physicalLeastOddSquarePrime k).getD 0
  have hmaps : ∀ k ∈ S, owner k ∈ physicalOddPrimeOwnersUpTo q := by
    intro k hk
    have hdata := (mem_physicalSquareHitCells_iff hq).mp hk
    obtain ⟨r, howner⟩ :=
      physicalLeastOddSquarePrime_exists_of_squareHit hdata.2
    have hr :=
      physicalLeastOwner_mem_oddPrimeOwnersUpTo_of_squareHit hdata.2 howner
    change (physicalLeastOddSquarePrime k).getD 0 ∈ physicalOddPrimeOwnersUpTo q
    rw [howner]
    exact hr
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := physicalOddPrimeOwnersUpTo q) (g := owner) hmaps f
  have hraw :
      (∑ k ∈ S, f k) =
        ∑ r ∈ physicalOddPrimeOwnersUpTo q,
          ∑ k ∈ S with owner k = r, f k := hfiber.symm
  change (∑ k ∈ S, f k) =
    ∑ r ∈ physicalOddPrimeOwnersUpTo q,
      ∑ k ∈ physicalCellsOwnedBy S r, f k
  rw [hraw]
  apply Finset.sum_congr rfl
  intro r hr
  have hrPrime := (mem_physicalOddPrimeOwnersUpTo.mp hr).1
  rw [physicalOwnerGetDFiber_eq_cellsOwnedBy S hrPrime]

/-! ## 3. An earlier layer plus generic owner partition = exact recursive daughter -/

/-- The fully reassembled physical daughter of current contact prime `q` at
physical cutoff `K`.  Every lower-owner overlap remains inside the signed sum
until the full q-hit carrier has been restored. -/
def physicalReassembledQ2Daughter (K q : ℕ) : ℤ :=
  ∑ r ∈ physicalOddPrimeOwnersUpTo q,
    ∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K q) r,
      physicalQ2DaughterCellIncrement q k

/-- **All-prime lower-triangular q^2 dictionary.**  For every odd prime `q`, not
just `3,5,7`, the fully owner-reassembled physical daughter is literally the
recursive Mertens packet at scale `4K/q^2`.  No endpoint error remains. -/
theorem physicalReassembledQ2Daughter_eq_mertens
    {K q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    physicalReassembledQ2Daughter K q =
      mertensSummatoryInt (4 * K / (q * q)) := by
  unfold physicalReassembledQ2Daughter
  calc
    (∑ r ∈ physicalOddPrimeOwnersUpTo q,
        ∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K q) r,
          physicalQ2DaughterCellIncrement q k) =
      ∑ k ∈ physicalSquareHitCells K q,
        physicalQ2DaughterCellIncrement q k :=
      (physicalSquareHit_sum_eq_sum_oddPrimeOwners hq
        (physicalQ2DaughterCellIncrement q)).symm
    _ = mertensSummatoryInt (4 * K / (q * q)) :=
      physicalQ2Daughter_squareHit_sum_eq_mertens hq hq3

/-- The same whole-packet statement in the recursive energy type.  This square
is taken only after the complete signed owner reassembly above. -/
theorem physicalReassembledQ2Daughter_sq_eq_mertensEnergy
    {K q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    ((physicalReassembledQ2Daughter K q : ℚ) ^ 2) =
      mertensEnergy (4 * K / (q * q)) := by
  rw [physicalReassembledQ2Daughter_eq_mertens hq hq3]
  rfl

/-- The whole odd-prime daughter family can now be rewritten at once to genuine
Mertens daughters.  This is an exact identity of signed packets, not an energy
inequality. -/
theorem sum_physicalReassembledQ2Daughters_eq_sum_mertens
    (K Q : ℕ) :
    (∑ q ∈ (primesUpTo Q).erase 2,
        physicalReassembledQ2Daughter K q) =
      ∑ q ∈ (primesUpTo Q).erase 2,
        mertensSummatoryInt (4 * K / (q * q)) := by
  apply Finset.sum_congr rfl
  intro q hqmem
  have hqPrime := (mem_primesUpTo.mp (Finset.mem_erase.mp hqmem).2).1
  have hq3 : 3 ≤ q := by
    have hq2 := hqPrime.two_le
    have hqNe2 := (Finset.mem_erase.mp hqmem).1
    omega
  exact physicalReassembledQ2Daughter_eq_mertens hqPrime hq3

/-- Likewise the sum of whole reassembled daughter energies is exactly the sum
of recursive Mertens energies.  This is the legitimate replacement for the
false coefficient-L2/Mertens-energy identification guarded against by an earlier layer. -/
theorem sum_physicalReassembledQ2DaughterEnergy_eq_sum_mertensEnergy
    (K Q : ℕ) :
    (∑ q ∈ (primesUpTo Q).erase 2,
        (physicalReassembledQ2Daughter K q : ℚ) ^ 2) =
      ∑ q ∈ (primesUpTo Q).erase 2,
        mertensEnergy (4 * K / (q * q)) := by
  apply Finset.sum_congr rfl
  intro q hqmem
  have hqPrime := (mem_primesUpTo.mp (Finset.mem_erase.mp hqmem).2).1
  have hq3 : 3 ≤ q := by
    have hq2 := hqPrime.two_le
    have hqNe2 := (Finset.mem_erase.mp hqmem).1
    omega
  exact physicalReassembledQ2Daughter_sq_eq_mertensEnergy hqPrime hq3

end RHLean.Proof
