import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Cycle25.Assembly.Low.Geometry

/-! The original OpenAI 7/8 initialization supplies only the coarse upper
bound needed to choose the variable moment parameter.  No improved endpoint
is used.  Apache-2.0 OpenAI/math family003 attribution retained. -/
namespace Cycle25.FinalAssembly
open OAI.SevenEighths

theorem baseline_beta : HeckeZeroSupremum.beta ≤ (7/8:ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

theorem moment_parameter_gates (hβ : Cycle25.theta < HeckeZeroSupremum.beta) :
    (7/10:ℝ) ≤ 2*HeckeZeroSupremum.beta-1 ∧
    2*HeckeZeroSupremum.beta-1 ≤ (3/4:ℝ) ∧
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta := by
  have hlo := Cycle25.LowGeometry.theta_coarse
  have hhi := baseline_beta
  constructor
  · linarith
  constructor <;> linarith
end Cycle25.FinalAssembly
