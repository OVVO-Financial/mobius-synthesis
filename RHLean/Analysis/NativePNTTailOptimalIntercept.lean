import RHLean.Analysis.NativePNTOptimalInterceptCore
import RHLean.Analysis.NativePNTTailAffineEnvelope

noncomputable section

namespace RHLean.Analysis

theorem nativePNTAffineOptimalIntercept_le_of_tail_cutoff
    (M : Nat) (alpha : Real) (halpha : 0 <= alpha)
    (htail : forall N : Nat, M <= N ->
      |nativePNTError N| <= alpha * (N : Real)) :
    nativePNTAffineOptimalIntercept alpha <=
      nativePNTFinitePrefixCoeff * (M : Real) := by
  exact nativePNTAffineOptimalIntercept_le_of_envelope
    (nativePNTAffineEnvelopeAt_of_tail_cutoff M alpha halpha htail)

end RHLean.Analysis
