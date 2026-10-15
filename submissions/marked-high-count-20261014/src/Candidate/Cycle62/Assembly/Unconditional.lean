/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryChosenSetup
import Candidate.Cycle62.Physical.InitialMass.GeometrySourceBudget

set_option autoImplicit false
namespace Cycle62.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle62InitialMass

/-- The actual chosen affine input follows from the original main and error
families and the fixed source geometry. -/
theorem chosen_affine_input : ChosenAffineInput :=
  chosen_affine_of_source_geometry actual_weighted_source_geometry_budget

/-- Cycle62's exact advertised supremum bound. -/
theorem beta_le_rational : HeckeZeroSupremum.beta≤(437429/500000:ℝ) :=
  beta_le_rational_of_chosen_affine chosen_affine_input

end
end Cycle62.FinalAssembly
#print axioms Cycle62.FinalAssembly.chosen_affine_input
#print axioms Cycle62.FinalAssembly.beta_le_rational
