/- Fresh detector-source contract. A supplier must prove this proposition;
the definition itself establishes no analytic estimate. Apache-2.0. -/
import Candidate.Target836.Target836InitialTransport

set_option autoImplicit false
namespace OAI.SevenEighths.Target836InitialTransport
noncomputable section

def DetectorAffineInput : Prop :=
  ∀{D:Cycle25.Weighted.MomentData}(S:Cycle25ProbeFinalAssembly.WeightedSourceData D),
    51/100 ≤ HeckeZeroSupremum.beta → HeckeZeroSupremum.beta ≤ 7/8 →
    (∀j,D.ell j ≤ DetectorAffine.detectorMesh D.t/200) → weighted_AffineFineInput836 S

theorem detector_input_apply (h:DetectorAffineInput)
    {D:Cycle25.Weighted.MomentData}(S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (hlo:51/100 ≤ HeckeZeroSupremum.beta)(hhi:HeckeZeroSupremum.beta ≤ 7/8)
    (hfine:∀j,D.ell j ≤ DetectorAffine.detectorMesh D.t/200) :
    weighted_AffineFineInput836 S := h S hlo hhi hfine

end
end OAI.SevenEighths.Target836InitialTransport
#print axioms OAI.SevenEighths.Target836InitialTransport.detector_input_apply
