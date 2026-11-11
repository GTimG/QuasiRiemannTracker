import Candidate.Local.Qrh.PR98Improvement.RepairedRestrictedSource
import Candidate.Local.Qrh.PositiveGap.NativeBudgetCurve
import Candidate.Local.Qrh.PositiveGap.TightSelectedCurve
import Candidate.Local.Qrh.PR98Improvement.GapAdapters
set_option autoImplicit false
namespace QRH.PositiveGap
noncomputable section
open QRH.ArviSelectedLeaf QRH.Record1252270103Source OAI.SevenEighths
theorem source (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (1 - ε) (2 + 10 * ε) (PositiveGapTightSelected.rCap (2 + 10 * ε)) := by
  have hseed : GlobalSource (1 - ε) (93/25) (3/50) :=
    Candidate.PR98.RepairedRestrictedSource.generalized_seed ε hε0 (by linarith only [hε1]) hβ
  have hnative : GlobalSource (1 - ε) (5143/2000) (1/10) :=
    PositiveGapNativeBudget.refined_end hε0 hε1 hβ
      (selectedRootEnergy _ (by norm_num [PositiveGapNativeBudget.rK])
        (by norm_num [PositiveGapNativeBudget.rK])) hseed
  exact PositiveGapTightSelected.refined_end hε0 hε1 hβ
    (selectedRootEnergy_above_half _ (by unfold PositiveGapTightSelected.rK; linarith only [hε0])
      (by unfold PositiveGapTightSelected.rK; linarith only [hε1])) hnative
end
end QRH.PositiveGap
