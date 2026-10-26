/- The .874836 endpoint assembled from actual source and count providers.
Adapted from Hailey Collet, OpenAI, DaysSky and Zhongpai Gao; Apache-2.0. -/
import Candidate.Target836.Target836InitialSupplier
import Candidate.Target836.SourceProvider.WeightedSourceBudget

set_option autoImplicit false
namespace Target836.FinalAssembly
noncomputable section
open OAI.SevenEighths

theorem chosen_affine_input : ChosenAffineInput :=
  chosen_affine_of_source_geometry
    Target874836.SourceProvider.Physical.actual_weighted_source_geometry_budget

theorem beta_le_rational : HeckeZeroSupremum.beta ≤ (218709/250000:ℝ) :=
  beta_le_rational_of_chosen_affine
    Target836InitialSupplier.actual_detector_affine_input chosen_affine_input

end
end Target836.FinalAssembly
#print axioms Target836.FinalAssembly.chosen_affine_input
#print axioms Target836.FinalAssembly.beta_le_rational
