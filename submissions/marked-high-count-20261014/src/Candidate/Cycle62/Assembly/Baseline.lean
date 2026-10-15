import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Candidate.Cycle62.Arithmetic.Constants

/-! Only the original 7/8 endpoint is used to initialize the supremum.
The bound from the earlier quartic submission is not an input here. -/
namespace Cycle62.Assembly

open OAI.SevenEighths Arithmetic

theorem baseline_beta : HeckeZeroSupremum.beta ≤ (7/8 : ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

theorem moment_parameter_gates (hβ : theta < HeckeZeroSupremum.beta) :
    (7/10 : ℝ) ≤ 2*HeckeZeroSupremum.beta-1 ∧
    2*HeckeZeroSupremum.beta-1 ≤ (3/4 : ℝ) ∧
    (51/100 : ℝ) ≤ HeckeZeroSupremum.beta ∧
    kappaStar < 2*HeckeZeroSupremum.beta-1 := by
  have hhi := baseline_beta
  have hlo : (17/20 : ℝ) < theta := by norm_num [theta]
  have hk := kappaStar_eq
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem kappa_gap (β : ℝ) :
    (2*β-1)-kappaStar = 2*(β-theta) := by
  rw [kappaStar_eq]
  ring

end Cycle62.Assembly
