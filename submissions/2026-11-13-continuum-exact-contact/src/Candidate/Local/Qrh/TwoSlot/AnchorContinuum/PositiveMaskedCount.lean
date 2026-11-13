/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Transport the original amplitude-class count to the masked selection mean.
Adapted from PR137 MaskedCount (Sil and predecessor authors, Apache-2.0).
No fixed-fee physical schedule or reduction of the original row class is used. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.MaskedCount

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open Cycle25DetectorRowCount
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

theorem count_envelope_antitone {delta κ x y : ℝ}
    (hk : (7/10:ℝ) ≤ κ) (hkhi : κ ≤ (3/4:ℝ))
    (hd : 0 ≤ delta) (hdhi : delta ≤ 3/4) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope (line := line) κ delta y ≤
      Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope (line := line) κ delta x := by
  apply QRH.Record12518109Return.finiteEnvelope_antitone
    QRH.Record12518109Return.countingR
    (Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.admittedBranches (line := line)) hxy hy
  rw [QRH.Record12518109Return.countingR_eq_actual hk,
    QRH.Record12518109Return.countingR_eq_actual hk]
  exact rowCount_antitone hd hdhi hk hkhi hx hxy hy

/-- Error-slot masking changes the mean used for selection, while the count
continues to concern the same full original amplitude class. -/
theorem masked_class_count {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U delta κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot → ℝ) (Q : Row → Slot → ℂ)
    (bin : BinLabel slots (delta/2) mesh)
    (hd : 0 < delta) (hdhi : delta ≤ 3/4) (hk : (7/10:ℝ) ≤ κ) (hkhi : κ ≤ (3/4:ℝ))
    (hU : 1 ≤ U) (hw : ∀ j ∈ slots, 0 ≤ width j) (hL : 0 < ∑ j ∈ slots, width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (amplitudeRows rows slots U (delta/2) mesh hm width Q bin).Nonempty)
    (hcard : ((amplitudeRows rows slots U (delta/2) mesh hm width Q bin).card : ℝ) ≤
      C*U^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope (line := line)
        κ delta (classMean slots (delta/2) mesh width bin/delta)+loss)) :
    let g := binValue slots (delta/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ delta/2 ∧
      ((amplitudeRows rows slots U (delta/2) mesh hm width Q bin).card : ℝ) ≤
      C*U^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope (line := line)
        κ delta (q/delta)+loss) := by
  dsimp only
  have hg : ∀ j ∈ slots, 0 ≤ binValue slots (delta/2) mesh bin j ∧
      binValue slots (delta/2) mesh bin j ≤ delta/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j hj
    rw [←amplitude_class_value rows slots U (delta/2) mesh hm width Q bin u hu j hj]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width
    (binValue slots (delta/2) mesh bin) delta hw hL hg
  refine ⟨hq0,hq.trans hqtop,?_⟩
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply count_envelope_antitone hk hkhi hd.le hdhi
  · exact div_nonneg hq0 hd.le
  · exact div_le_div_of_nonneg_right hq hd.le
  · apply (div_le_iff₀ hd).mpr
    have hh : classMean slots (delta/2) mesh width bin ≤ delta/2 := hqtop
    linarith

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.masked_class_count
