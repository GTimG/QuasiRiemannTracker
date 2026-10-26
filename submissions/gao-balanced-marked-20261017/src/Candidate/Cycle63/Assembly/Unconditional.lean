/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryChosenSetup
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceBudget
import Candidate.Affine.Supply

/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                       
                                                        

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle63InitialMass

/-- The actual chosen affine input follows from the original main and error
families and the fixed source geometry. -/
theorem chosen_affine_input : ChosenAffineInput :=
  chosen_affine_of_source_geometry actual_weighted_source_geometry_budget

/-- Cycle63's exact advertised supremum bound. -/
theorem beta_le_rational : HeckeZeroSupremum.beta≤(Cycle63.Arithmetic.theta:ℝ) :=
  beta_le_rational_of_chosen_affine
    Cycle25ProbeFinalAssemblyCertifiedBands.actual_detector_affine_input chosen_affine_input

end
end Cycle63.FinalAssembly
#print axioms Cycle63.FinalAssembly.chosen_affine_input
#print axioms Cycle63.FinalAssembly.beta_le_rational

