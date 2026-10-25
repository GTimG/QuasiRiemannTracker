/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
Original OpenAI input for the native source cost, with the exact new target
used only to distinguish a trivial beta branch. No improved PR69 endpoint
or new source estimate is imported. This file does not prove the new bound.
-/
import Candidate.Feedback.FourthPower.Parameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.IncumbentInput
noncomputable section
open OAI.SevenEighths

/-- The original unconditional theorem, obtained from its actual certified
bands through the original common-probe construction. -/
theorem baseline_beta : HeckeZeroSupremum.beta ≤ (7/8 : ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

/-- This supplies the hκ input of NativeSlotDeletion and its descendants.
It is distinct from Parameters.kappa, the sharper return feedback exponent. -/
theorem native_kappa_bound : 2*HeckeZeroSupremum.beta-1 ≤ (3/4 : ℝ) := by
  linarith [baseline_beta]

/-- NativeZeroInput's internally chosen maximum also equals the old native
cost, although that theorem did not need this simplification to prove ZeroAt. -/
theorem native_max_eq :
    max (3/4 : ℝ) (2*HeckeZeroSupremum.beta-1) = 3/4 :=
  max_eq_left native_kappa_bound

/-- The complementary branch already lies below the exact requested target. -/
theorem small_branch (hβ : HeckeZeroSupremum.beta < (51/100 : ℝ)) :
    HeckeZeroSupremum.beta ≤ theta := by
  have hfloor : (51/100 : ℝ) ≤ theta := by norm_num [theta]
  exact hβ.le.trans hfloor

/-- In the nontrivial target branch both native analytic hypotheses are
actual consequences, not new assumptions about a moment or a source. -/
theorem contrary_inputs (hβ : theta < HeckeZeroSupremum.beta) :
    (51/100 : ℝ) ≤ HeckeZeroSupremum.beta ∧
      2*HeckeZeroSupremum.beta-1 ≤ (3/4 : ℝ) := by
  have hfloor : (51/100 : ℝ) ≤ theta := by norm_num [theta]
  exact ⟨hfloor.trans hβ.le,native_kappa_bound⟩

/-- Explicit exhaustive split for the final target proof. Only the second
branch still needs the new source and return argument. -/
theorem target_cases : HeckeZeroSupremum.beta ≤ theta ∨
    (theta < HeckeZeroSupremum.beta ∧
      (51/100 : ℝ) ≤ HeckeZeroSupremum.beta ∧
      2*HeckeZeroSupremum.beta-1 ≤ (3/4 : ℝ)) := by
  by_cases hβ : HeckeZeroSupremum.beta ≤ theta
  · exact Or.inl hβ
  · have hcontra := lt_of_not_ge hβ
    exact Or.inr ⟨hcontra,contrary_inputs hcontra⟩

end
end Candidate.Feedback.FourthPower.IncumbentInput
