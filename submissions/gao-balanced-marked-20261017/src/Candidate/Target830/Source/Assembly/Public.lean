import Candidate.Target830.Source.Assembly.InitialSupplier

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open HeckeFamily Cycle25ProbeFinalAssembly

/-- The actual original batch/fiber moment for each new plane, from the
complete source theorem and its common pre-dictionary source mesh. -/
theorem actual_detector_affine_input (plane : SourcePlane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (mesh : ℝ) (hmesh0 : 0 < mesh) (hmesh : mesh ≤ sourceMesh D.t)
    (hfine : ∀j,D.ell j ≤ mesh/200) :
    Physical.InitialTransport.weighted_AffineFineInputAt
      (Physical.InitialTransport.countPlane plane) S := by
  exact Physical.InitialTransport.actual_detector_affine_input_of_initial plane S mesh hmesh0 hfine
    (actual_label_initial_moments plane S hβlo hβhi mesh hmesh0 hmesh)
end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.actual_detector_affine_input
