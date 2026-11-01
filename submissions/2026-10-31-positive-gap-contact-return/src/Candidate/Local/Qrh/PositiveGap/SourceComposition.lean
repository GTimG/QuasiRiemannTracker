/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The reserve-parametric seed and the two finite source lines at smaller fixed positive gaps. -/
import Candidate.Local.Qrh.PR98Improvement.RepairedRestrictedSource
import Candidate.Local.Qrh.PositiveGap.NativeBudgetCurve
import Candidate.Local.Qrh.PositiveGap.TightSelectedCurve
import Candidate.Local.Qrh.PR98Improvement.GapAdapters

set_option autoImplicit false
namespace QRH.PositiveGap
noncomputable section
open QRH.ArviSelectedLeaf QRH.Record1252270103Source OAI.SevenEighths

/-- The seed at reserve `10^-20`, then the native and tight source lines. -/
theorem source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999999999999999999/100000000000000000000)
      (20000000000000000001/10000000000000000000) (3/20) := by
  have hseed : GlobalSource (99999999999999999999/100000000000000000000) (93/25) (3/50) := by
    convert Candidate.PR98.RepairedRestrictedSource.generalized_seed
      (1/100000000000000000000) (by norm_num) (by norm_num) hβ using 1 <;> norm_num
  have hnative : GlobalSource (99999999999999999999/100000000000000000000)
      (5143/2000) (1/10) :=
    PositiveGapNativeBudget.refined_end hβ
      (selectedRootEnergy _ (by norm_num [PositiveGapNativeBudget.rK])
        (by norm_num [PositiveGapNativeBudget.rK])) hseed
  exact PositiveGapTightSelected.refined_end hβ
    (selectedRootEnergy_above_half _ (by norm_num [PositiveGapTightSelected.rK])
      (by norm_num [PositiveGapTightSelected.rK])) hnative

end
end QRH.PositiveGap

#print axioms QRH.PositiveGap.source
