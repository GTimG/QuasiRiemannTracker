/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Original retained full-class and error-mask count transport, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.CountScheme
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.MaskedCount
open QRH.RH20261023Return

namespace QRH.RH20261023Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open OAI OAI.SevenEighths QRH.Record12518109Count
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open OAI.SevenEighths.Cycle25DetectorRowCount
open scoped Classical BigOperators
theorem envelope_count_antitone {δ κ x y : ℝ}
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (hδ : 0≤δ) (hδhi : δ≤3/4)
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) :
    GenericCount.envelope κ δ y ≤ GenericCount.envelope κ δ x := by
  apply QRH.Record12518109Return.finiteEnvelope_antitone
    QRH.Record12518109Return.countingR GenericCount.admittedBranches hxy hy
  rw [QRH.Record12518109Return.countingR_eq_actual hk,
    QRH.Record12518109Return.countingR_eq_actual hk]
  exact rowCount_antitone hδ hδhi hk hk1 hx hxy hy

theorem masked_amplitude_class_count {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(QRH.RH20261023Return.GenericCount.envelope κ δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ)+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(QRH.RH20261023Return.GenericCount.envelope κ δ (q/δ)+loss) := by
  dsimp only
  have hg : ∀j∈slots,0 ≤ HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ∧
      HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j hj
    rw [←amplitude_class_value rows slots U (δ/2) mesh hm width Q bin u hu j hj]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width
    (HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin) δ hw hL hg
  refine ⟨hq0,hq.trans hqtop,?_⟩
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply envelope_count_antitone hk hk1 hδ.le hδtop
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    have h' : HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin ≤ δ/2 := hqtop
    linarith


end
end QRH.RH20261023Return.GenericPhysical.PhysicalDirect
#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.masked_amplitude_class_count
