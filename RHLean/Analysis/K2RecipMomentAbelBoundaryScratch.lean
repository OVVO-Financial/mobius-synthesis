import RHLean.Analysis.K2RecipMomentSummabilityScratch

noncomputable section

open Filter Finset Set Topology
open scoped ArithmeticFunction.Moebius LSeries.notation BigOperators

namespace RHLean.Analysis

/-- The Abel boundary factor taking the order-two reciprocal moment at `s = 1`
to the same Dirichlet series at a real `sigma > 1`. -/
def k2AbelBoundaryWeight (sigma : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 - sigma)

@[simp]
theorem k2AbelBoundaryWeight_one (sigma : ℝ) :
    k2AbelBoundaryWeight sigma 1 = 1 := by
  simp [k2AbelBoundaryWeight]

@[simp]
theorem k2AbelBoundaryWeight_sigma_one (n : ℕ) :
    k2AbelBoundaryWeight 1 n = 1 := by
  simp [k2AbelBoundaryWeight]

/-- For `sigma > 1`, the Abel boundary factors decrease with the integer
endpoint. -/
theorem k2AbelBoundaryWeight_succ_le
    {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ} (hn : 1 ≤ n) :
    k2AbelBoundaryWeight sigma (n + 1) ≤ k2AbelBoundaryWeight sigma n := by
  unfold k2AbelBoundaryWeight
  apply Real.rpow_le_rpow_of_exponent_nonpos
  · exact_mod_cast (by omega : 0 < n)
  · exact_mod_cast (show n ≤ n + 1 by omega)
  · linarith

/-- The Abel factors are positive, hence in `[0,1]` on the right of one. -/
theorem k2AbelBoundaryWeight_mem_Icc
    {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ} (hn : 1 ≤ n) :
    k2AbelBoundaryWeight sigma n ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold k2AbelBoundaryWeight
    exact Real.rpow_nonneg (by positivity) _
  · unfold k2AbelBoundaryWeight
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hn) (by linarith)

/-- At every fixed positive integer, the Abel factor tends to one as
`sigma -> 1`. -/
theorem k2AbelBoundaryWeight_tendsto_one (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun sigma : ℝ => k2AbelBoundaryWeight sigma n)
      (𝓝 (1 : ℝ)) (𝓝 1) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  unfold k2AbelBoundaryWeight
  rw [show (fun sigma : ℝ => (n : ℝ) ^ (1 - sigma)) =
      (fun sigma : ℝ => Real.exp (Real.log (n : ℝ) * (1 - sigma))) by
        funext sigma
        rw [Real.rpow_def_of_pos hnpos]]
  have hsub :
      Tendsto (fun sigma : ℝ => (1 : ℝ) - sigma)
        (𝓝 (1 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds.sub tendsto_id :
      Tendsto (fun sigma : ℝ => (1 : ℝ) - sigma)
        (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)))
  have hmul :
      Tendsto (fun sigma : ℝ => Real.log (n : ℝ) * (1 - sigma))
        (𝓝 (1 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hsub :
      Tendsto (fun sigma : ℝ => Real.log (n : ℝ) * (1 - sigma))
        (𝓝 (1 : ℝ)) (𝓝 (Real.log (n : ℝ) * 0)))
  simpa using Real.continuous_exp.continuousAt.tendsto.comp hmul

/-- Abel differences telescope from one to the endpoint. -/
theorem k2AbelBoundaryWeight_telescopes
    (sigma : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    k2AbelBoundaryWeight sigma M +
        ∑ n ∈ Finset.Ico 1 M,
          (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1)) = 1 := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM]
      rw [← ih]
      ring

/-- The same telescope started at an arbitrary positive prefix. -/
theorem k2AbelBoundaryWeight_telescopes_Ico
    (sigma : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    k2AbelBoundaryWeight sigma M +
        ∑ n ∈ Finset.Ico N M,
          (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1)) =
      k2AbelBoundaryWeight sigma N := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      rw [Finset.sum_Ico_succ_top hNM]
      rw [← ih]
      ring

/-- Finite real Dirichlet prefix corresponding to the order-two Mobius moment
at a real exponent `sigma`. -/
def k2A2AbelPrefix (sigma : ℝ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M,
    (((μ n : ℤ) : ℝ) * k2LogRecipWeight 2 n) *
      k2AbelBoundaryWeight sigma n

/-- Finite Abel summation centered at an arbitrary candidate boundary value.
This is the uniform identity behind the Dirichlet Abel limit. -/
theorem k2A2AbelPrefix_centered
    (sigma A : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    k2A2AbelPrefix sigma M - A =
      (k2MobiusLogMoment 2 M - A) * k2AbelBoundaryWeight sigma M +
        ∑ n ∈ Finset.Ico 1 M,
          (k2MobiusLogMoment 2 n - A) *
            (k2AbelBoundaryWeight sigma n -
              k2AbelBoundaryWeight sigma (n + 1)) := by
  have habel := nativeAbelIccOne
    (fun n : ℕ => ((μ n : ℤ) : ℝ) * k2LogRecipWeight 2 n)
    (k2AbelBoundaryWeight sigma) M
  have htel := k2AbelBoundaryWeight_telescopes sigma hM
  unfold k2A2AbelPrefix k2MobiusLogMoment at *
  rw [habel]
  let S : ℕ → ℝ := fun n =>
    ∑ k ∈ Icc 1 n, ((μ k : ℤ) : ℝ) * k2LogRecipWeight 2 k
  let d : ℕ → ℝ := fun n =>
    k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1)
  have hcenter :
      ∑ n ∈ Ico 1 M, (S n - A) * d n =
        (∑ n ∈ Ico 1 M, S n * d n) - A * (∑ n ∈ Ico 1 M, d n) := by
    calc
      ∑ n ∈ Ico 1 M, (S n - A) * d n =
          ∑ n ∈ Ico 1 M, (S n * d n - A * d n) := by
            apply Finset.sum_congr rfl
            intro n _hn
            ring
      _ = (∑ n ∈ Ico 1 M, S n * d n) -
          ∑ n ∈ Ico 1 M, A * d n := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ Ico 1 M, S n * d n) -
          A * (∑ n ∈ Ico 1 M, d n) := by
            rw [Finset.mul_sum]
  have htel' :
      k2AbelBoundaryWeight sigma M + ∑ n ∈ Ico 1 M, d n = 1 := by
    simpa [d] using htel
  have hAtel :
      A * k2AbelBoundaryWeight sigma M +
          A * (∑ n ∈ Ico 1 M, d n) = A := by
    calc
      A * k2AbelBoundaryWeight sigma M + A * (∑ n ∈ Ico 1 M, d n) =
          A * (k2AbelBoundaryWeight sigma M + ∑ n ∈ Ico 1 M, d n) := by ring
      _ = A := by rw [htel']; ring
  have hcenter' :
      ∑ n ∈ Ico 1 M,
          ((∑ k ∈ Icc 1 n, ((μ k : ℤ) : ℝ) * k2LogRecipWeight 2 k) - A) *
            (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1)) =
        (∑ n ∈ Ico 1 M,
          (∑ k ∈ Icc 1 n, ((μ k : ℤ) : ℝ) * k2LogRecipWeight 2 k) *
            (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))) -
          A * (∑ n ∈ Ico 1 M,
            (k2AbelBoundaryWeight sigma n - k2AbelBoundaryWeight sigma (n + 1))) := by
    simpa [S, d] using hcenter
  rw [hcenter']
  nlinarith [hAtel]

/-- The finite head in the centered Abel formula vanishes as `sigma -> 1`. -/
theorem k2A2AbelHead_tendsto_zero (A : ℝ) (N : ℕ) :
    Tendsto
      (fun sigma : ℝ =>
        ∑ n ∈ Finset.Ico 1 N,
          (k2MobiusLogMoment 2 n - A) *
            (k2AbelBoundaryWeight sigma n -
              k2AbelBoundaryWeight sigma (n + 1)))
      (𝓝 (1 : ℝ)) (𝓝 0) := by
  classical
  let s := Finset.Ico 1 N
  have hs : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    exact (Finset.mem_Ico.mp hn).1
  have hgeneral : ∀ (t : Finset ℕ),
      (∀ n ∈ t, 1 ≤ n) →
      Tendsto
        (fun sigma : ℝ =>
          ∑ n ∈ t,
            (k2MobiusLogMoment 2 n - A) *
              (k2AbelBoundaryWeight sigma n -
                k2AbelBoundaryWeight sigma (n + 1)))
        (𝓝 (1 : ℝ)) (𝓝 0) := by
    intro t ht
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        have ha1 : 1 ≤ a := ht a (Finset.mem_insert_self a t)
        have ht' : ∀ n ∈ t, 1 ≤ n := by
          intro n hn
          exact ht n (Finset.mem_insert_of_mem hn)
        have hdiff :=
          (k2AbelBoundaryWeight_tendsto_one a ha1).sub
            (k2AbelBoundaryWeight_tendsto_one (a + 1) (by omega))
        have hterm :
            Tendsto
              (fun sigma : ℝ =>
                (k2MobiusLogMoment 2 a - A) *
                  (k2AbelBoundaryWeight sigma a -
                    k2AbelBoundaryWeight sigma (a + 1)))
              (𝓝 (1 : ℝ)) (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hdiff :
            Tendsto
              (fun sigma : ℝ =>
                (k2MobiusLogMoment 2 a - A) *
                  (k2AbelBoundaryWeight sigma a -
                    k2AbelBoundaryWeight sigma (a + 1)))
              (𝓝 (1 : ℝ))
              (𝓝 ((k2MobiusLogMoment 2 a - A) * (1 - 1))))
        simpa [Finset.sum_insert ha] using hterm.add (ih ht')
  simpa [s] using hgeneral s hs

end RHLean.Analysis
