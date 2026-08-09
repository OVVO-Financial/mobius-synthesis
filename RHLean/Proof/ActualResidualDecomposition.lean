import Mathlib
import RHLean.Proof.HeightShellGram
import RHLean.Analysis.ReducedQuadraticGauss
import RHLean.Proof.ResonantLeakage
import RHLean.Arithmetic.MoebiusDoubling
import RHLean.Geometry.CofactorParabolas
import RHLean.Kernel.FixedPackets

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/--
An explicitly indexed cofactor channel. The lower factor carries the Möbius
weight, while the upper factor remains visible for the exact cofactor geometry.
No primality, ordering, or size hypothesis is built into the channel.
-/
structure ActualCofactorChannel where
  lowerCofactor : ℕ
  upperFactor : ℕ
  deriving DecidableEq

/-- Exact real coordinate of the squared-map cofactor channel. -/
def actualCofactorSquareX (channel : ActualCofactorChannel) : ℝ :=
  RHLean.Geometry.squareMapX
    (channel.lowerCofactor : ℝ) (channel.upperFactor : ℝ)

/-- Exact imaginary coordinate of the squared-map cofactor channel. -/
def actualCofactorSquareY (channel : ActualCofactorChannel) : ℝ :=
  RHLean.Geometry.squareMapY
    (channel.lowerCofactor : ℝ) (channel.upperFactor : ℝ)

/-- Every indexed cofactor channel lies on both exact cofactor parabolas. -/
theorem actualCofactorChannel_mem_bothParabolas
    (channel : ActualCofactorChannel) :
    RHLean.Geometry.LowerCofactorParabola
        (channel.lowerCofactor : ℝ)
        (actualCofactorSquareX channel)
        (actualCofactorSquareY channel) ∧
      RHLean.Geometry.UpperCofactorParabola
        (channel.upperFactor : ℝ)
        (actualCofactorSquareX channel)
        (actualCofactorSquareY channel) := by
  simpa [actualCofactorSquareX, actualCofactorSquareY] using
    RHLean.Geometry.squareMap_mem_bothCofactorParabolas
      (channel.lowerCofactor : ℝ) (channel.upperFactor : ℝ)

/--
Finite data defining the actual residual at scale `M`.

The shell, cofactor channel, denominator-mode label, packet start, packet
length, and packet index remain separate arguments. The mode map lands in the
scale-dependent `ResonantModeIndex`, so every denominator is positive, is
bounded by the scale cutoff, and carries the canonical quadratic modulus `2r`.
The amplitude contains the remaining already-derived scalar coefficient; it is
not a replacement for the Möbius weight, quadratic phase, packet sum, or shell
sum, all of which are applied explicitly below.
-/
structure ActualResidualData (cutoff : ℕ → ℕ) (M : ℕ) where
  shellCount : ℕ
  cofactorChannels : Finset ActualCofactorChannel
  denominatorModes : Finset ℕ
  mode : ℕ → ResonantModeIndex cutoff M
  packetStart : ℕ → ActualCofactorChannel → ℕ → ℕ
  packetLength : ℕ → ActualCofactorChannel → ℕ → ℕ
  amplitude : ℕ → ActualCofactorChannel → ℕ → ℕ → ℂ

/-- The exact reduced quadratic factor attached to one actual denominator mode. -/
def actualResidualReducedModeFactor
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M) (denominatorMode : ℕ) : ℂ :=
  RHLean.QuadraticPrimePhase.normalizedReducedQuadraticGauss
    (data.mode denominatorMode).numerator
    (data.mode denominatorMode).denominator
    (data.mode denominatorMode).denominator_pos

/-- The canonical modulus of every actual denominator mode is exactly `2 * r`. -/
theorem actualResidualMode_modulus
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M) (denominatorMode : ℕ) :
    resonantModeModulus (data.mode denominatorMode) =
      2 * ((data.mode denominatorMode).denominator : ℤ) := by
  rfl

/--
One packet-indexed summand of the actual residual. The lower cofactor receives
its exact Möbius weight, and the denominator mode contributes the already
compiled complex quadratic phase with canonical modulus `2r`.
-/
def actualResidualEntry
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode packetIndex : ℕ) : ℂ :=
  (((μ channel.lowerCofactor : ℤ) : ℂ) *
      data.amplitude shell channel denominatorMode packetIndex) *
    resonantQuadraticMode
      (data.mode denominatorMode) (packetIndex : ℤ)

/-- The fixed packet belonging to one shell/cofactor/denominator channel. -/
def actualResidualPacket
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) : ℂ :=
  RHLean.Kernel.packet
    (actualResidualEntry data shell channel denominatorMode)
    (data.packetStart shell channel denominatorMode)
    (data.packetLength shell channel denominatorMode)

/--
The full shell contribution, retaining the signed joint sum over cofactor
channels and denominator modes.
-/
def actualResidualShell
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M) (shell : ℕ) : ℂ :=
  ∑ channel ∈ data.cofactorChannels,
    ∑ denominatorMode ∈ data.denominatorModes,
      actualResidualPacket data shell channel denominatorMode

/--
The actual residual at scale `M`, with the complete signed shell sum kept
inside a single complex value.
-/
def actualResidual
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M) : ℂ :=
  heightShellSum (actualResidualShell data) data.shellCount

/-- The resonant part of the actual residual is the scale-dependent extraction. -/
def resonantActualResidual
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) : ℂ :=
  resonantComponent skeleton M (actualResidual data)

/-- The nonresonant part is the exact algebraic remainder. -/
def nonresonantActualResidual
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) : ℂ :=
  actualResidual data - resonantActualResidual skeleton M data

/-- The extracted actual resonant residual lies in the declared scale-`M` span. -/
theorem resonantActualResidual_mem_resonantSubspace
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    resonantActualResidual skeleton M data ∈ resonantSubspace skeleton M := by
  simpa [resonantActualResidual] using
    resonantComponent_mem_resonantSubspace skeleton M (actualResidual data)

/--
Exact algebraic recombination of the actual residual. No orthogonality,
idempotence, self-adjointness, cancellation, leakage, or size claim is used.
-/
theorem actualResidual_eq_resonant_add_nonresonant
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    actualResidual data =
      resonantActualResidual skeleton M data +
        nonresonantActualResidual skeleton M data := by
  simp [resonantActualResidual, nonresonantActualResidual]

/--
The actual residual enters the leakage and Lyapunov layers as their already
compiled separately typed state, specialized here to complex-valued rows.
-/
def actualResidualState
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    ResonantNonresonantState ℂ ℂ where
  resonant := resonantActualResidual skeleton M data
  nonresonant := nonresonantActualResidual skeleton M data

/-- The resonant row of the actual residual state is definitionally exact. -/
theorem actualResidualState_resonant
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    (actualResidualState skeleton M data).resonant =
      resonantActualResidual skeleton M data := by
  rfl

/-- The nonresonant row of the actual residual state is definitionally exact. -/
theorem actualResidualState_nonresonant
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    (actualResidualState skeleton M data).nonresonant =
      nonresonantActualResidual skeleton M data := by
  rfl

/-- Recombination expressed directly through the state consumed by later layers. -/
theorem actualResidual_eq_state_sum
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    actualResidual data =
      (actualResidualState skeleton M data).resonant +
        (actualResidualState skeleton M data).nonresonant := by
  simpa [actualResidualState] using
    actualResidual_eq_resonant_add_nonresonant skeleton M data

end RHLean.Analysis
