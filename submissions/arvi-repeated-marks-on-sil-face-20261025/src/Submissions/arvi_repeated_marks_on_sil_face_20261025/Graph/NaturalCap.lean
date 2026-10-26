/- Repeated marks, single stage: the natural cost `K = 9/2 = 6(2·7/8 − 1)` and its cap.

The source steps and the final return need `6(2β − 1) ≤ K`. With `K = 9/2` this is the baseline's
`β ≤ 7/8` (OpenAI baseline, Apache-2.0), so no bootstrap stage is needed. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
set_option autoImplicit false
namespace QRH.RepeatedMarks
open OAI.SevenEighths HeckeFamily

/-- The natural cost of the chain and of the return. -/
noncomputable def natK : ℝ := 9/2

/-- The baseline's zero-free half-plane `Re s > 7/8`, as a bound on `β`. -/
theorem beta_le_seven_eighths : HeckeZeroSupremum.beta ≤ (7/8:ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

theorem natural_cap : 6*(2*HeckeZeroSupremum.beta-1)≤natK := by
  have h := beta_le_seven_eighths
  unfold natK; linarith

/-- The first parent of the chain: Collet's natural source face (`Record1252270103Finite.natural`)
at the natural cost `9/2`. -/
def natural92 : Record1252270103Finite.Source := ⟨1,9/2,11/200,0,1/10^12,1/10^8,1/10^7⟩

end QRH.RepeatedMarks
