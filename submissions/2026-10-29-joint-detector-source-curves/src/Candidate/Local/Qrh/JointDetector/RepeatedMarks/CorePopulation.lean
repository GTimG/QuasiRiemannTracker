/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatch
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorWitnessRows ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem free_core_population (cores : Finset FreeRow) (Y : ℝ) (hY : 1≤Y)
    (hcores : ∀u∈cores,rowNorm u≤Y) : (cores.card:ℝ)≤128*Y := by
  have hh := OAI.DescentFiberCost.finite_element_count_real
    (cores.image Subtype.val) Y hY (by
      intro z hz
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
      simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,rowNorm] using hcores u hu)
  simpa only [Finset.card_image_of_injective cores Subtype.val_injective] using hh

end
end Qrh.JointDetector.RepeatedMarks
