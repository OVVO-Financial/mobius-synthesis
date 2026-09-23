import RHLean.Proof.StableFarOwnedSmoothShell
import RHLean.Proof.CanonicalGapAncestryBridge

/-!
# The owned terminal carrier is the full smooth square shell
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Squarefree integers in the physical square shell whose largest prime stays
inside the inclusive low wheel. -/
def lowWheelFrozenTopFarSmoothShell (R : ℕ) : Finset ℕ :=
  (orderedEulerCutSquarefreeShell R).filter fun n =>
    canonicalLargestPrimeFactor n ≤ R

@[simp] theorem mem_lowWheelFrozenTopFarSmoothShell
    {R n : ℕ} :
    n ∈ lowWheelFrozenTopFarSmoothShell R ↔
      R < n ∧ n < R ^ 2 ∧ Squarefree n ∧
        canonicalLargestPrimeFactor n ≤ R := by
  simp [lowWheelFrozenTopFarSmoothShell, mem_orderedEulerCutSquarefreeShell,
    and_assoc]

/-- **Owned terminal saturation of the whole smooth shell.**  The arithmetic
home carrier of the internal-terminal mate plus frozen-cofactor top image is
exactly every squarefree `R`-smooth integer in `(R,R^2)`. -/
theorem lowWheelFrozenTopFarOwnedProducts_eq_smoothShell
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarOwnedProducts R =
      lowWheelFrozenTopFarSmoothShell R := by
  have hR2 : 2 ≤ R := by omega
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨y, hyOwned, hyChild⟩
    have hyOrdered :=
      lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier hyOwned
    have hactive : n ∈ orderedEulerCutActiveChildren R := by
      unfold orderedEulerCutActiveChildren
      exact Finset.mem_image.mpr ⟨y, hyOrdered, hyChild⟩
    have hshell : n ∈ orderedEulerCutSquarefreeShell R := by
      rw [← orderedEulerCutActiveChildren_eq_squarefreeShell R hR2]
      exact hactive
    have hlpf : canonicalLargestPrimeFactor n ≤ R :=
      lowWheelFrozenTopFarOwnedProduct_largestPrime_le_root hn
    exact Finset.mem_filter.mpr ⟨hshell, hlpf⟩
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hshell, hlpf⟩
    have hactive : n ∈ orderedEulerCutActiveChildren R := by
      rw [orderedEulerCutActiveChildren_eq_squarefreeShell R hR2]
      exact hshell
    unfold orderedEulerCutActiveChildren at hactive
    rcases Finset.mem_image.mp hactive with ⟨y, hyOrdered, hyChild⟩
    rcases y with ⟨t, ⟨c, p⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨(t, (c, p)), ?_, hyChild⟩
    unfold lowWheelFrozenTopFarOwnedSources
    by_cases hc : c = 1
    · subst c
      have hshape := orderedEulerCutShape_of_mem_carrier hyOrdered
      have hp : p.Prime := hshape.1
      have hnData := mem_orderedEulerCutSquarefreeShell.mp hshell
      have hnGt : 1 < n := by omega
      have hpDivChild : p ∣ orderedEulerCutChildInteger (t, (1, p)) := by
        refine ⟨primeFaceProduct t, ?_⟩
        simp [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
          orderedEulerCutPivot, orderedEulerCutLowProduct]
      have hpDivN : p ∣ n := by
        rw [← hyChild]
        exact hpDivChild
      have hpLeTop : p ≤ canonicalLargestPrimeFactor n :=
        prime_dvd_le_canonicalLargestPrimeFactor hnGt hp hpDivN
      have hpR : p ≤ R := hpLeTop.trans hlpf
      exact Finset.mem_union_left _
        (orderedEulerCut_mem_repeatedTerminalInternal_of_cofactor_one
          hR hyOrdered hpR)
    · have hshape := orderedEulerCutShape_of_mem_carrier hyOrdered
      have hc1 : 1 ≤ c := hshape.2.1
      have hcgt : 1 < c := by omega
      exact Finset.mem_union_right _
        (orderedEulerCut_mem_frozenCofactor_of_one_lt hyOrdered hcgt)

end RHLean.Proof
