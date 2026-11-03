/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighDetectorBeta.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DetectorZeros
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily

theorem detectorMaximum_le_beta {ι : Type*} [Fintype ι]
    (χ : ι → Character) (T : ℝ)
    (hbeta : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    detectorMaximum χ T ≤ HeckeZeroSupremum.beta := by
  by_cases hmax : (51 / 100 : ℝ) < detectorMaximum χ T
  · obtain ⟨i, s, hz, hpole, _, heq⟩ := detectorMaximum_attained χ T hmax
    rw [← heq]
    apply HeckeZeroSupremum.zero_re_le_beta (χ i) (by linarith)
    · by_cases hs : s = 1
      · exact Or.inr (by intro hχ; exact hpole ⟨hχ, hs⟩)
      · exact Or.inl hs
    · exact hz
  · exact (le_of_not_gt hmax).trans hbeta

end SevenEighths.ProbeHighRowFamily

end

end OAI
