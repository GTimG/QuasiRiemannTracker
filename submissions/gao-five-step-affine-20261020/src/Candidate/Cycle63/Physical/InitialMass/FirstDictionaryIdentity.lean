import Candidate.Cycle63.Physical.InitialMass.FirstUniformDictionary
import Candidate.Cycle63.Physical.InitialMass.GeometryMainRadius
import Candidate.Cycle63.Physical.InitialMass.SecondEncodedGates

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion

/-- Choose the signed unit once per arithmetic label, before the first
projector, dyads or ray characters. Unsupported labels use the identity. -/
def firstDictionaryUnit (left : Bool)(η : Character)(u₀ : O)(F₀ : NaturalRow η u₀)
    (R : Ideal O)(l : FirstSourceLabel) : Oˣ :=
  if h : Supported l.1.1 then
    if left then Classical.choose (uniform_first_left_natural_parent_mask η u₀ F₀ R fixedBadMask
      l.1.1 l.1.2 h l.2.val)
    else Classical.choose (uniform_first_right_natural_parent_mask η u₀ F₀ R fixedBadMask
      l.1.1 l.1.2 h l.2.val)
  else 1

end
end OAI.SevenEighths.Cycle63InitialMass
