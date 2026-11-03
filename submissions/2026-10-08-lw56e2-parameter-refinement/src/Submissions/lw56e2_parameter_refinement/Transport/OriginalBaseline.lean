/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/OriginalBaseline.lean
Original SHA-256: 44f726e22352789998a83bc989a82284f8ef8170cbf527c8b6506226ba74b40c
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

/-! The original family boundary, obtained from the pinned complete OpenAI
proof. No new axiom or nonvanishing hypothesis is introduced here. -/

namespace LW56e2.Transport

theorem original_hecke_boundary :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ) := by
  exact OAI.SevenEighths.HeckeCommonProbe.beta_le_seven_eighths
    (OAI.SevenEighths.ProbeFinalAssembly.common_probe_of_chosen_moments
      (OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        OAI.SevenEighths.ProbeFinalAssemblyUnconditional.detector_certified_bands))

end LW56e2.Transport
