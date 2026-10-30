/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Composition of the two finite source lines with explicit generalized-seed input. -/
import Candidate.Local.Qrh.PR98Improvement.NativeBudgetCurve
import Candidate.Local.Qrh.PR98Improvement.TightSelectedCurve
import Candidate.Local.Qrh.PR98Improvement.GapAdapters

set_option autoImplicit false
namespace QRH.QrhPR98Improvement
noncomputable section
open QRH.ArviSelectedLeaf QRH.Record1252270103Source OAI.SevenEighths

/-- Full finite source composition; the generalized seed remains explicit. -/
theorem source_of_generalized_seed
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hseed : GlobalSource (99999999999999/100000000000000)
      (93/25) (3/50)) :
    GlobalSource (99999999999999/100000000000000)
      (20000000000001/10000000000000) (3/20) := by
  have hnative : GlobalSource (99999999999999/100000000000000)
      (5143/2000) (1/10) :=
    QrhPR98NativeBudget.refined_end hβ
      (selectedRootEnergy _ (by norm_num [QrhPR98NativeBudget.rK])
        (by norm_num [QrhPR98NativeBudget.rK])) hseed
  exact QrhPR98TightSelected.refined_end hβ
    (selectedRootEnergy_above_half _ (by norm_num [QrhPR98TightSelected.rK])
      (by norm_num [QrhPR98TightSelected.rK])) hnative

end
end QRH.QrhPR98Improvement

#print axioms QRH.QrhPR98Improvement.source_of_generalized_seed
