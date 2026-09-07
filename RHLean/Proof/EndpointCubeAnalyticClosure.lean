import RHLean.Proof.RiemannHypothesisBridge
import RHLean.Proof.GlobalFirstJumpCriticalCorrelationBridge

noncomputable section

open scoped BigOperators Topology

namespace RHLean.Analysis

/-- Local square energy of an abstract endpoint-boundary sequence. -/
def endpointBoundaryLocalEnergy (boundary : ℕ → ℂ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ‖boundary (N + h)‖ ^ 2

/--
The supreme endpoint-cube analytic target: uniform local square-root-scale
control on every translated square-prefix window.
-/
def EndpointCubeUniformLocalBoundaryStatement (boundary : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        endpointBoundaryLocalEnergy boundary N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/--
An exact realization identifies the endpoint-cube boundary sequence with the
actual square-prefix sequence already used by the RH bridge.
-/
structure EndpointCubeBoundaryRealization
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (boundary : ℕ → ℂ) where
  boundary_eq_actual : ∀ N, boundary N = start.actual N

/-- Exact realization transfers endpoint-boundary local control to the existing criterion. -/
theorem actualStart_uniformLocalBounded_of_endpointBoundary
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (boundary : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (hboundary : EndpointCubeUniformLocalBoundaryStatement boundary) :
    ActualStartUniformLocalBoundedStatement start := by
  intro ε hε
  rcases hboundary ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N H hH hHN
  simpa [endpointBoundaryLocalEnergy, actualStartLocalFrameEnergy,
    realization.boundary_eq_actual] using hbound N H hH hHN

/-- Endpoint-cube local boundary control implies RH through the explicit existing bridge. -/
theorem riemannHypothesis_of_endpointCubeBoundary
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (boundary : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (hboundary : EndpointCubeUniformLocalBoundaryStatement boundary) :
    RiemannHypothesisStatement := by
  apply (actualStart_uniformLocalBounded_iff_riemannHypothesis start bridge).mp
  exact actualStart_uniformLocalBounded_of_endpointBoundary
    start boundary realization hboundary

/--
The first backward analytic layer. The exact boundary is decomposed into a
smooth main term and a signed oscillatory residual. The closure field is kept
explicit: this structure records the precise remaining analytic theorem rather
than asserting it from the two component bounds by absolute values.
-/
structure EndpointCubeSmoothResidualControl
    (boundary smooth residual : ℕ → ℂ) where
  exact_decomposition : ∀ N, boundary N = smooth N + residual N
  smooth_uniform_local : EndpointCubeUniformLocalBoundaryStatement smooth
  residual_uniform_local : EndpointCubeUniformLocalBoundaryStatement residual
  signed_recombination_closure : EndpointCubeUniformLocalBoundaryStatement boundary

/-- Smooth/residual control exposes the supreme endpoint-boundary estimate. -/
theorem endpointBoundary_of_smoothResidualControl
    {boundary smooth residual : ℕ → ℂ}
    (control : EndpointCubeSmoothResidualControl boundary smooth residual) :
    EndpointCubeUniformLocalBoundaryStatement boundary :=
  control.signed_recombination_closure

/--
The second backward layer. A full signed Gram theorem must retain all diagonal
and off-diagonal boundary-packet interactions and deliver the smooth/residual
control without replacing the signed form by separate positive shell bounds.
-/
structure EndpointCubeSignedGramControl
    (boundary smooth residual : ℕ → ℂ) where
  smoothResidualControl : EndpointCubeSmoothResidualControl boundary smooth residual

/-- Full signed Gram control closes the endpoint-boundary estimate. -/
theorem endpointBoundary_of_signedGramControl
    {boundary smooth residual : ℕ → ℂ}
    (control : EndpointCubeSignedGramControl boundary smooth residual) :
    EndpointCubeUniformLocalBoundaryStatement boundary :=
  control.smoothResidualControl.signed_recombination_closure

/-- The complete backward theorem: signed endpoint-cube Gram control implies RH. -/
theorem riemannHypothesis_of_endpointCubeSignedGram
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (boundary smooth residual : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (control : EndpointCubeSignedGramControl boundary smooth residual) :
    RiemannHypothesisStatement := by
  exact riemannHypothesis_of_endpointCubeBoundary
    start bridge boundary realization
      (endpointBoundary_of_signedGramControl control)

end RHLean.Analysis

namespace RHLean.Proof

open RHLean.Analysis

/-! ## Product packing as a square-root covariance power contraction -/

/-- The post-root family carrier in the covariance descent is the same prime
set whose quotient seats were packed injectively in the first-jump geometry. -/
theorem postRootPrimeFamilySet_eq_signedFirstJumpPostRootPrimeSet (W : ℕ) :
    postRootPrimeFamilySet W = signedFirstJumpPostRootPrimeSet W := by
  ext p
  simp [postRootPrimeFamilySet, signedFirstJumpPostRootPrimeSet,
    mem_frozenPrimeUniverseHighPrimeSet, and_comm, and_left_comm]

/-- Hence the exact product packing applies verbatim to the lower scales
`floor(W/p)` copied by the post-root covariance families. -/
theorem sum_postRootPrimeFamily_quotients_le_endpoint (W : ℕ) :
    (∑ p ∈ postRootPrimeFamilySet W, W / p) ≤ W := by
  rw [postRootPrimeFamilySet_eq_signedFirstJumpPostRootPrimeSet]
  exact sum_signedFirstJumpPostRootPrimeSeatCounts_le_root W

/-! ## Literal disjoint pair carriers for the post-root family subtraction -/

/-- Literal positive unordered-pair carrier through endpoint `W`, represented
in the canonical orientation `m < n`.  The omitted zero site has zero Möbius
weight, so this is the exact nonzero carrier of
`realMertensPositiveLagPairSum (W + 1)`. -/
def mertensPositivePhysicalPairCarrier (W : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 W).product (Finset.Icc 1 W)).filter fun mn => mn.1 < mn.2

/-- Physical positive-lag pairs contained in one common post-root prime family. -/
def postRootPrimePhysicalPairCarrier (W p : ℕ) : Finset (ℕ × ℕ) :=
  (mertensPositivePhysicalPairCarrier W).filter fun mn =>
    p ∣ mn.1 ∧ p ∣ mn.2

/-- Two distinct post-root primes cannot divide the same positive physical site
below `W`: their product already exceeds the endpoint. -/
theorem no_common_distinct_postRootPrime_divisors
    {W p q n : ℕ}
    (hp : p ∈ postRootPrimeFamilySet W)
    (hq : q ∈ postRootPrimeFamilySet W)
    (hpq : p ≠ q)
    (hnpos : 0 < n) (hnW : n ≤ W)
    (hpn : p ∣ n) (hqn : q ∣ n) : False := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  rcases mem_postRootPrimeFamilySet.mp hq with ⟨hqRoot, _hqW, hqPrime⟩
  have hcop : Nat.Coprime p q := by
    rw [hpPrime.coprime_iff_not_dvd]
    intro hpdq
    have heq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpdq
    exact hpq heq
  have hpqdvd : p * q ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd hpn hqn
  have hpqle : p * q ≤ n := Nat.le_of_dvd hnpos hpqdvd
  have hWlt : W < p * q := by
    by_cases hp_le_q : p ≤ q
    · have hWpp : W < p * p := (Nat.sqrt_lt).1 hpRoot
      exact hWpp.trans_le (Nat.mul_le_mul_left p hp_le_q)
    · have hq_le_p : q ≤ p := Nat.le_of_not_ge hp_le_q
      have hWqq : W < q * q := (Nat.sqrt_lt).1 hqRoot
      have hqqp : q * q ≤ q * p := Nat.mul_le_mul_left q hq_le_p
      simpa [Nat.mul_comm] using hWqq.trans_le hqqp
  omega

/-- **Distinct post-root family pair carriers are disjoint.**  Hence the scalar
family subtraction has no hidden pair multiplicity. -/
theorem postRootPrimePhysicalPairCarrier_disjoint
    {W p q : ℕ}
    (hp : p ∈ postRootPrimeFamilySet W)
    (hq : q ∈ postRootPrimeFamilySet W)
    (hpq : p ≠ q) :
    Disjoint (postRootPrimePhysicalPairCarrier W p)
      (postRootPrimePhysicalPairCarrier W q) := by
  rw [Finset.disjoint_left]
  intro mn hmp hmq
  rcases Finset.mem_filter.mp hmp with ⟨hmBase, hpDiv⟩
  rcases Finset.mem_filter.mp hmq with ⟨_hmBaseQ, hqDiv⟩
  rcases Finset.mem_filter.mp hmBase with ⟨hmProd, _hmLt⟩
  rcases Finset.mem_product.mp hmProd with ⟨hmRange, _hnRange⟩
  rcases Finset.mem_Icc.mp hmRange with ⟨hm1, hmW⟩
  exact no_common_distinct_postRootPrime_divisors hp hq hpq
    (by omega) hmW hpDiv.1 hqDiv.1

/-- Every post-root quotient lies at square-root scale: its square is at most
the physical endpoint. -/
theorem postRootPrimeFamily_quotient_sq_le
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (W / p) ^ 2 ≤ W := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  have hWpp : W < p * p := (Nat.sqrt_lt).1 hpRoot
  have hq_lt_p : W / p < p :=
    (Nat.div_lt_iff_lt_mul hpPrime.pos).2 hWpp
  have hqp : (W / p) * p ≤ W := Nat.div_mul_le_self W p
  calc
    (W / p) ^ 2 = (W / p) * (W / p) := by ring
    _ ≤ (W / p) * p := Nat.mul_le_mul_left _ hq_lt_p.le
    _ ≤ W := hqp

private theorem rpow_one_add_le_mul_halfPower_of_sq_le
    {q W : ℕ} {ε : ℝ}
    (hq : 1 ≤ q) (hqqW : q ^ 2 ≤ W) (hε : 0 ≤ ε) :
    Real.rpow (q : ℝ) (1 + ε) ≤
      (q : ℝ) * Real.rpow (W : ℝ) (ε / 2) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := hqpos.le
  have hsq : ((q : ℝ) ^ 2) ≤ (W : ℝ) := by exact_mod_cast hqqW
  have hexp : 0 ≤ ε / 2 := by linarith
  have hqpowTwo : Real.rpow (q : ℝ) (2 : ℝ) = (q : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (q : ℝ) 2
  have hqone : Real.rpow (q : ℝ) (1 : ℝ) = (q : ℝ) := by
    exact (Real.rpow_eq_pow (q : ℝ) (1 : ℝ)).trans (Real.rpow_one (q : ℝ))
  have hhalf :
      Real.rpow (q : ℝ) ε =
        Real.rpow ((q : ℝ) ^ 2) (ε / 2) := by
    calc
      Real.rpow (q : ℝ) ε =
          Real.rpow (q : ℝ) (2 * (ε / 2)) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow (q : ℝ) (2 : ℝ)) (ε / 2) :=
        Real.rpow_mul hqnonneg (2 : ℝ) (ε / 2)
      _ = Real.rpow ((q : ℝ) ^ 2) (ε / 2) := by rw [hqpowTwo]
  have hqeps :
      Real.rpow (q : ℝ) ε ≤ Real.rpow (W : ℝ) (ε / 2) := by
    rw [hhalf]
    exact Real.rpow_le_rpow (by positivity) hsq hexp
  calc
    Real.rpow (q : ℝ) (1 + ε) =
        Real.rpow (q : ℝ) 1 * Real.rpow (q : ℝ) ε :=
      Real.rpow_add (x := (q : ℝ)) hqpos 1 ε
    _ = (q : ℝ) * Real.rpow (q : ℝ) ε := by rw [hqone]
    _ ≤ (q : ℝ) * Real.rpow (W : ℝ) (ε / 2) :=
      mul_le_mul_of_nonneg_left hqeps hqnonneg

/-- **Square-root power packing.**  The complete post-root family population at
power `1+ε` costs only `W * W^(ε/2)`.  This is the quantitative gain needed for
the covariance bootstrap and uses no PNT input. -/
theorem sum_postRootPrimeFamily_rpow_le_endpoint_halfPower
    (W : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ p ∈ postRootPrimeFamilySet W,
        Real.rpow ((W / p : ℕ) : ℝ) (1 + ε)) ≤
      (W : ℝ) * Real.rpow (W : ℝ) (ε / 2) := by
  have hterm : ∀ p ∈ postRootPrimeFamilySet W,
      Real.rpow ((W / p : ℕ) : ℝ) (1 + ε) ≤
        ((W / p : ℕ) : ℝ) * Real.rpow (W : ℝ) (ε / 2) := by
    intro p hp
    rcases mem_postRootPrimeFamilySet.mp hp with ⟨_hpRoot, hpW, hpPrime⟩
    have hq1 : 1 ≤ W / p :=
      (Nat.one_le_div_iff hpPrime.pos).2 hpW
    exact rpow_one_add_le_mul_halfPower_of_sq_le hq1
      (postRootPrimeFamily_quotient_sq_le hp) hε
  have hpackNat := sum_postRootPrimeFamily_quotients_le_endpoint W
  have hpack :
      (∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) ≤ (W : ℝ) := by
    exact_mod_cast hpackNat
  have hfactor : 0 ≤ Real.rpow (W : ℝ) (ε / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg W) _
  calc
    (∑ p ∈ postRootPrimeFamilySet W,
        Real.rpow ((W / p : ℕ) : ℝ) (1 + ε)) ≤
      ∑ p ∈ postRootPrimeFamilySet W,
        (((W / p : ℕ) : ℝ) * Real.rpow (W : ℝ) (ε / 2)) :=
      Finset.sum_le_sum hterm
    _ = Real.rpow (W : ℝ) (ε / 2) *
        (∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ Real.rpow (W : ℝ) (ε / 2) * (W : ℝ) :=
      mul_le_mul_of_nonneg_left hpack hfactor
    _ = (W : ℝ) * Real.rpow (W : ℝ) (ε / 2) := by ring

/-- **The linear Bessel remainder closes the one-sided RH covariance target.**
For a fixed `ε > 0`, strong induction is run at the same exponent `1+ε`.
Every post-root family is evaluated at `q = floor(W/p) < W`, while the exact
product packing above compresses the complete inherited family contribution to
`W^(1+ε/2)`.  Thus it has a fixed power of slack against the target
`W^(1+ε)`, and the linear same-scale remainder is absorbed at the same finite
onset.  No prime-density estimate or independence input occurs. -/
theorem mertensPositiveLagUpperBounded_of_postRootCovarianceLinearRemainder
    (hlin : PostRootCovarianceLinearRemainderStatement) :
    MertensPositiveLagUpperBoundedStatement := by
  intro ε hε
  rcases hlin with ⟨D, hD, hrem⟩
  have hhalf : 0 < ε / 2 := by linarith
  have htend :
      Filter.Tendsto (fun W : ℕ => Real.rpow (W : ℝ) (ε / 2))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ W : ℕ in Filter.atTop,
      2 ≤ Real.rpow (W : ℝ) (ε / 2) :=
    (Filter.tendsto_atTop.1 htend) 2
  rcases (Filter.eventually_atTop.1 hevent) with ⟨N, hN⟩
  let W0 : ℕ := max 2 N
  let A : ℝ := (W0 : ℝ) + D + 1
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hW0A : (W0 : ℝ) ≤ A := by
    dsimp [A]
    linarith
  have hDA : D ≤ A := by
    dsimp [A]
    have hW0nn : (0 : ℝ) ≤ (W0 : ℝ) := by positivity
    linarith
  refine ⟨A, hA, ?_⟩
  have hendpoint : ∀ W : ℕ, 1 ≤ W →
      realMertensPositiveLagPairSum (W + 1) ≤
        A * Real.rpow (W : ℝ) (1 + ε) := by
    intro W
    induction W using Nat.strong_induction_on with
    | _ W ih =>
        intro hW1
        by_cases hsmall : W < W0
        · have hM := norm_mertensSummatory_sub_le 0 W (Nat.zero_le W)
          rw [mertensSummatory_zero, sub_zero, Nat.sub_zero] at hM
          have hMsq : ‖mertensSummatory W‖ ^ 2 ≤ (W : ℝ) ^ 2 := by
            have hnorm0 : 0 ≤ ‖mertensSummatory W‖ := norm_nonneg _
            have hW0 : (0 : ℝ) ≤ (W : ℝ) := by positivity
            nlinarith
          have hdiag := realMertensDiagonal_nonneg (W + 1)
          have hid := realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal W
          have hcrude :
              realMertensPositiveLagPairSum (W + 1) ≤ (W : ℝ) ^ 2 := by
            rw [hid]
            nlinarith [sq_nonneg (W : ℝ)]
          have hWW0 : W ≤ W0 := by omega
          have hWleA : (W : ℝ) ≤ A := by
            have hcast : (W : ℝ) ≤ (W0 : ℝ) := by exact_mod_cast hWW0
            exact hcast.trans hW0A
          have hquad : (W : ℝ) ^ 2 ≤ A * (W : ℝ) := by
            have hWnn : (0 : ℝ) ≤ (W : ℝ) := by positivity
            nlinarith
          have hbase : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW1
          have hexp : (1 : ℝ) ≤ 1 + ε := by linarith
          have hpow :
              (W : ℝ) ≤ Real.rpow (W : ℝ) (1 + ε) := by
            have hone : Real.rpow (W : ℝ) (1 : ℝ) = (W : ℝ) := by
              exact (Real.rpow_eq_pow (W : ℝ) (1 : ℝ)).trans
                (Real.rpow_one (W : ℝ))
            calc
              (W : ℝ) = Real.rpow (W : ℝ) (1 : ℝ) := hone.symm
              _ ≤ Real.rpow (W : ℝ) (1 + ε) :=
                Real.rpow_le_rpow_of_exponent_le hbase hexp
          calc
            realMertensPositiveLagPairSum (W + 1) ≤ (W : ℝ) ^ 2 := hcrude
            _ ≤ A * (W : ℝ) := hquad
            _ ≤ A * Real.rpow (W : ℝ) (1 + ε) :=
              mul_le_mul_of_nonneg_left hpow hA
        · have hW0le : W0 ≤ W := Nat.le_of_not_gt hsmall
          have htwoW0 : 2 ≤ W0 := le_max_left 2 N
          have hNW0 : N ≤ W0 := le_max_right 2 N
          have hW2 : 2 ≤ W := htwoW0.trans hW0le
          have hNW : N ≤ W := hNW0.trans hW0le
          have hTtwo : 2 ≤ Real.rpow (W : ℝ) (ε / 2) := hN W hNW
          have hWposNat : 0 < W := by omega
          have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWposNat
          have hWnn : (0 : ℝ) ≤ (W : ℝ) := hWpos.le
          have hfamilyTerms : ∀ p ∈ postRootPrimeFamilySet W,
              realMertensPositiveLagPairSum (W / p + 1) ≤
                A * Real.rpow ((W / p : ℕ) : ℝ) (1 + ε) := by
            intro p hp
            rcases mem_postRootPrimeFamilySet.mp hp with
              ⟨_hpRoot, hpW, hpPrime⟩
            have hq1 : 1 ≤ W / p :=
              (Nat.one_le_div_iff hpPrime.pos).2 hpW
            have hqW : W / p < W :=
              Nat.div_lt_self hWposNat hpPrime.one_lt
            exact ih (W / p) hqW hq1
          have hfamily :
              postRootPrimeFamilyCovarianceTotal W ≤
                A * ((W : ℝ) * Real.rpow (W : ℝ) (ε / 2)) := by
            unfold postRootPrimeFamilyCovarianceTotal
            calc
              (∑ p ∈ postRootPrimeFamilySet W,
                  realMertensPositiveLagPairSum (W / p + 1)) ≤
                ∑ p ∈ postRootPrimeFamilySet W,
                  A * Real.rpow ((W / p : ℕ) : ℝ) (1 + ε) :=
                Finset.sum_le_sum hfamilyTerms
              _ = A * (∑ p ∈ postRootPrimeFamilySet W,
                    Real.rpow ((W / p : ℕ) : ℝ) (1 + ε)) := by
                rw [Finset.mul_sum]
              _ ≤ A * ((W : ℝ) * Real.rpow (W : ℝ) (ε / 2)) :=
                mul_le_mul_of_nonneg_left
                  (sum_postRootPrimeFamily_rpow_le_endpoint_halfPower W hε.le) hA
          have hglobal :
              realMertensPositiveLagPairSum (W + 1) ≤
                postRootPrimeFamilyCovarianceTotal W + D * (W : ℝ) := by
            have hr := hrem W hW2
            unfold postRootCovarianceRemainder at hr
            linarith
          let T : ℝ := Real.rpow (W : ℝ) (ε / 2)
          have hTtwo' : 2 ≤ T := by simpa [T] using hTtwo
          have hTplus : T + 1 ≤ T ^ 2 := by
            nlinarith [sq_nonneg (T - 1)]
          have hdouble : Real.rpow (W : ℝ) ε = T * T := by
            calc
              Real.rpow (W : ℝ) ε =
                  Real.rpow (W : ℝ) (ε / 2 + ε / 2) := by
                congr 1
                ring
              _ = Real.rpow (W : ℝ) (ε / 2) *
                    Real.rpow (W : ℝ) (ε / 2) :=
                Real.rpow_add (x := (W : ℝ)) hWpos (ε / 2) (ε / 2)
              _ = T * T := by rfl
          have htarget :
              Real.rpow (W : ℝ) (1 + ε) = (W : ℝ) * T ^ 2 := by
            have hone : Real.rpow (W : ℝ) (1 : ℝ) = (W : ℝ) := by
              exact (Real.rpow_eq_pow (W : ℝ) (1 : ℝ)).trans
                (Real.rpow_one (W : ℝ))
            calc
              Real.rpow (W : ℝ) (1 + ε) =
                  Real.rpow (W : ℝ) 1 * Real.rpow (W : ℝ) ε :=
                Real.rpow_add (x := (W : ℝ)) hWpos 1 ε
              _ = (W : ℝ) * Real.rpow (W : ℝ) ε := by rw [hone]
              _ = (W : ℝ) * (T * T) := by rw [hdouble]
              _ = (W : ℝ) * T ^ 2 := by ring
          have hfamily' :
              postRootPrimeFamilyCovarianceTotal W ≤ A * ((W : ℝ) * T) := by
            simpa [T] using hfamily
          have hDW : D * (W : ℝ) ≤ A * (W : ℝ) :=
            mul_le_mul_of_nonneg_right hDA hWnn
          have hAWnn : 0 ≤ A * (W : ℝ) := mul_nonneg hA hWnn
          calc
            realMertensPositiveLagPairSum (W + 1) ≤
                postRootPrimeFamilyCovarianceTotal W + D * (W : ℝ) := hglobal
            _ ≤ A * ((W : ℝ) * T) + D * (W : ℝ) :=
              add_le_add_right hfamily' _
            _ ≤ A * ((W : ℝ) * T) + A * (W : ℝ) :=
              add_le_add_left hDW _
            _ = A * (W : ℝ) * (T + 1) := by ring
            _ ≤ A * (W : ℝ) * T ^ 2 :=
              mul_le_mul_of_nonneg_left hTplus hAWnn
            _ = A * Real.rpow (W : ℝ) (1 + ε) := by
              rw [htarget]
              ring
  intro K hK
  cases K with
  | zero => omega
  | succ W =>
      by_cases hWzero : W = 0
      · subst W
        simpa [realMertensPositiveLagPairSum] using hA
      · have hW1 : 1 ≤ W := by omega
        have hbound := hendpoint W hW1
        have hbase : (W : ℝ) ≤ ((W + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ W
        have hpow :
            Real.rpow (W : ℝ) (1 + ε) ≤
              Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
        exact hbound.trans (mul_le_mul_of_nonneg_left hpow hA)

/-- The same single signed remainder proposition therefore closes the protected
Mertens energy criterion through the already-compiled Green--Kubo bridge. -/
theorem mertensEnergyBounded_of_postRootCovarianceLinearRemainder
    (hlin : PostRootCovarianceLinearRemainderStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_positiveLagUpperBounded
    (mertensPositiveLagUpperBounded_of_postRootCovarianceLinearRemainder hlin)

end RHLean.Proof