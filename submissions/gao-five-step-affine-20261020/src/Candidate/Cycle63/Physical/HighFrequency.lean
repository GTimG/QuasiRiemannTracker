import Candidate.Cycle63.Moment.ActualJointDictionary
import Candidate.Cycle63.Moment.CanonicalFirstNorm
import Candidate.Cycle63.Physical.FinalRadius

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63HighFrequency
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentSecondRetainedWidth CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource Cycle63Moment Cycle63FinalRadius

/-- Canonical label units leave only the fixed first factor in the norm. -/
theorem fixed_unit_norm (u₀ u : O) (hu : IsUnit u) : normValue (u₀*u)=normValue u₀ := by
  unfold normValue
  rw [Ideal.span_singleton_mul_right_unit hu]

end
end OAI.SevenEighths.Cycle63HighFrequency
