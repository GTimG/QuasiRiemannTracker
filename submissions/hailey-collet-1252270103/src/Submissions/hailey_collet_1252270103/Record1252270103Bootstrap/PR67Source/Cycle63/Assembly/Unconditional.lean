import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryChosenSetup
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometrySourceBudget
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.CountAffine.Supply
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle63InitialMass

/-- The actual chosen affine input follows from the original main and error
families and the fixed source geometry. -/
theorem chosen_affine_input : ChosenAffineInput :=
  chosen_affine_of_source_geometry actual_weighted_source_geometry_budget

/-- The detector affine moment at the detector mesh. -/
theorem detector_affine_input :
    Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh :=
  Cycle25ProbeFinalAssemblyCertifiedBands.actual_detector_affine_input

end
end Cycle63.FinalAssembly

end Record1252270103Bootstrap.PR67
