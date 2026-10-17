import Candidate.Affine.Supply

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.RecordEndpoint
noncomputable section
open HeckeFamily ProbePhysical CenteredMomentDetectorDictionary Cycle25ProbeFinalAssembly

/-- The principal physical numerator is one literal member of the same
finite detector dictionary; no character replacement is used. -/
theorem principal_detector_label {D : Cycle25.Weighted.MomentData}
    (S : WeightedSourceData D) (η : Character) :
    sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η (Sum.inl true)=
      fixedSourcePrincipal S.S S.exclusions.prime := rfl

end
end OAI.SevenEighths.Target830.Source.RecordEndpoint
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.principal_detector_label
