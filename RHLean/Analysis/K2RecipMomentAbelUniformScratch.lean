import RHLean.Analysis.K2RecipMomentAbelBoundaryScratch

noncomputable section

open Filter Finset Set Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Once the order-two prefixes are `eps`-close to `A` beyond `N`, every
finite Abel transform at `sigma > 1` is uniformly controlled by the fixed
head plus `eps`. -/
theorem k2A2AbelPrefix_centered_abs_le_head_add
    {sigma A eps : ℝ} (hsigma : 1 < sigma) (heps : 0 ≤ eps)
    {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M)
    (hclose : ∀ n : ℕ, N ≤ n → n ≤ M →
      |k2MobiusLogMoment 2 n - A| ≤ eps) :
    |k2A2AbelPrefix sigma M - A| ≤
      |∑ n ∈ Finset.Ico 1 N,
        (k2MobiusLogMoment 2 n - A) *
          (k2AbelBoundaryWeight sigma n -
            k2AbelBoundaryWeight sigma (n + 1))| + eps := by
  let f : ℕ → ℝ := fun n =>
    (k2MobiusLogMoment 2 n - A) *
      (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))
  have habssum : ∀ s : Finset ℕ,
      |∑ n ∈ s, f n| ≤ ∑ n ∈ s, |f n| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (abs_add_le _ _).trans (add_le_add_left ih _)
  have hM : 1 ≤ M := hN.trans hNM
  have hsplit :
      (∑ n ∈ Finset.Ico 1 N, f n) + (∑ n ∈ Finset.Ico N M, f n) =
        ∑ n ∈ Finset.Ico 1 M, f n := by
    simpa only using (Finset.sum_Ico_consecutive (f := f) hN hNM)
  have htail :
      |∑ n ∈ Finset.Ico N M, f n| ≤
        eps * ∑ n ∈ Finset.Ico N M,
          (k2AbelBoundaryWeight sigma n -
            k2AbelBoundaryWeight sigma (n + 1)) := by
    calc
      |∑ n ∈ Finset.Ico N M, f n| ≤
          ∑ n ∈ Finset.Ico N M, |f n| := habssum (Finset.Ico N M)
      _ ≤ ∑ n ∈ Finset.Ico N M,
          eps * (k2AbelBoundaryWeight sigma n -
            k2AbelBoundaryWeight sigma (n + 1)) := by
        apply Finset.sum_le_sum
        intro n hnmem
        have hnN : N ≤ n := (Finset.mem_Ico.mp hnmem).1
        have hnM : n ≤ M := (Finset.mem_Ico.mp hnmem).2.le
        have hn1 : 1 ≤ n := hN.trans hnN
        have hd : 0 ≤ k2AbelBoundaryWeight sigma n -
            k2AbelBoundaryWeight sigma (n + 1) :=
          sub_nonneg.mpr (k2AbelBoundaryWeight_succ_le hsigma hn1)
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hclose n hnN hnM) hd
      _ = eps * ∑ n ∈ Finset.Ico N M,
          (k2AbelBoundaryWeight sigma n -
            k2AbelBoundaryWeight sigma (n + 1)) := by
        rw [Finset.mul_sum]
  have hbM := k2AbelBoundaryWeight_mem_Icc hsigma hM
  have hend :
      |(k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M| ≤
        eps * k2AbelBoundaryWeight sigma M := by
    rw [abs_mul, abs_of_nonneg hbM.1]
    exact mul_le_mul_of_nonneg_right (hclose M hNM le_rfl) hbM.1
  have htel := k2AbelBoundaryWeight_telescopes_Ico sigma hNM
  have hbN := k2AbelBoundaryWeight_mem_Icc hsigma hN
  have hrest :
      |(k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M| +
          |∑ n ∈ Finset.Ico N M, f n| ≤ eps := by
    calc
      |(k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M| +
          |∑ n ∈ Finset.Ico N M, f n| ≤
        eps * k2AbelBoundaryWeight sigma M +
          eps * ∑ n ∈ Finset.Ico N M,
            (k2AbelBoundaryWeight sigma n -
              k2AbelBoundaryWeight sigma (n + 1)) := add_le_add hend htail
      _ = eps * (k2AbelBoundaryWeight sigma M +
          ∑ n ∈ Finset.Ico N M,
            (k2AbelBoundaryWeight sigma n -
              k2AbelBoundaryWeight sigma (n + 1))) := by ring
      _ = eps * k2AbelBoundaryWeight sigma N := by rw [htel]
      _ ≤ eps := mul_le_of_le_one_right heps hbN.2
  rw [k2A2AbelPrefix_centered sigma A hM]
  rw [← hsplit]
  dsimp [f]
  calc
    |(k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M +
        ((∑ n ∈ Finset.Ico 1 N,
            (k2MobiusLogMoment 2 n - A) *
              (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))) +
          ∑ n ∈ Finset.Ico N M,
            (k2MobiusLogMoment 2 n - A) *
              (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1)))|
      ≤ |∑ n ∈ Finset.Ico 1 N,
            (k2MobiusLogMoment 2 n - A) *
              (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))| +
          (|(k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M| +
            |∑ n ∈ Finset.Ico N M,
              (k2MobiusLogMoment 2 n - A) *
                (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))|) := by
        calc
          _ ≤ |(k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M| +
              |(∑ n ∈ Finset.Ico 1 N,
                  (k2MobiusLogMoment 2 n - A) *
                    (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))) +
                ∑ n ∈ Finset.Ico N M,
                  (k2MobiusLogMoment 2 n - A) *
                    (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))| :=
            abs_add_le _ _
          _ ≤ |(k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M| +
              (|∑ n ∈ Finset.Ico 1 N,
                  (k2MobiusLogMoment 2 n - A) *
                    (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))| +
                |∑ n ∈ Finset.Ico N M,
                  (k2MobiusLogMoment 2 n - A) *
                    (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))|) := by
            gcongr
            exact abs_add_le _ _
          _ = |∑ n ∈ Finset.Ico 1 N,
                  (k2MobiusLogMoment 2 n - A) *
                    (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))| +
              (|(k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M| +
                |∑ n ∈ Finset.Ico N M,
                  (k2MobiusLogMoment 2 n - A) *
                    (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))|) := by ring
    _ ≤ |∑ n ∈ Finset.Ico 1 N,
            (k2MobiusLogMoment 2 n - A) *
              (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))| + eps :=
      add_le_add_left hrest _

end RHLean.Analysis
