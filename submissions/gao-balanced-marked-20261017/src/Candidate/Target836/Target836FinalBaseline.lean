import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Candidate.Target836.Detector836.Transport.GeometryFacts

set_option autoImplicit false
namespace Target836.FinalAssembly
open OAI.SevenEighths

theorem baseline_beta : HeckeZeroSupremum.beta≤(7/8:ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

theorem moment_parameter_gates (hβ : Arithmetic.theta< HeckeZeroSupremum.beta) :
    (7/10:ℝ)≤2*HeckeZeroSupremum.beta-1 ∧
      2*HeckeZeroSupremum.beta-1≤(3/4:ℝ) ∧ (51/100:ℝ)≤ HeckeZeroSupremum.beta := by
  have ht : (85/100:ℝ)< Arithmetic.theta := by norm_num [Arithmetic.theta]
  have hi:=baseline_beta
  constructor
  · linarith
  constructor <;> linarith
end Target836.FinalAssembly

#print axioms Target836.FinalAssembly.baseline_beta
#print axioms Target836.FinalAssembly.moment_parameter_gates
