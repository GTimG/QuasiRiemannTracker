import Candidate.Local.Qrh.PositiveGap.Return.Tuning.FinalScheme
import Candidate.Local.Qrh.PositiveGap.Return.Facts
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PositiveGap.ReturnTuning
noncomputable section
variable [TargetC]
theorem old_count_eq {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 QRH.Record12518109Return.countingR kappa δ p=countN .old δ p/countJ .old δ p := by
 have hk : (7/10:ℝ)≤kappa := by unfold kappa; linarith [c_hi]
 have hk3 : (2:ℝ)<3*kappa := by unfold kappa; linarith [c_hi]
 have hp2k : 2*p/(3*kappa)≤1 := (div_le_one (by linarith)).mpr (by linarith [hp.2])
 have hD : 0<oldD p := by unfold oldD; linarith [hp.2, hp2k]
 have hJ := countJ_pos .old hδ hp
 unfold QRH.Record12518109Return.countingR QRH.Record12518109Return.rowDen
 rw [QRH.Record12518109Return.canonical_counting_formula hk]
 change 1-δ+δ*(oldC p/oldD p)*V δ/(2*(V δ+δ*(oldC p/oldD p)))=countN .old δ p/countJ .old δ p
 have he : V δ+δ*(oldC p/oldD p)=countJ .old δ p/oldD p := by
  simp only [countJ]
  field_simp [hD.ne']
  <;> ring
 rw [he]
 unfold countN
 field_simp [hD.ne',hJ.ne']
 <;> ring
theorem finiteEnvelope_le_old {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 @GenericCount.envelope finalCountScheme kappa δ p≤countN .old δ p/countJ .old δ p := by
 calc
  _ ≤ QRH.Record12518109Return.countingR kappa δ p :=
   QRH.Record12518109Return.finiteEnvelope_le_base QRH.Record12518109Return.countingR
    (@GenericCount.admittedBranches finalCountScheme) kappa δ p
  _ = _ := old_count_eq hδ hp
theorem finiteEnvelope_le_window (w:ReturnCountWindow) (hw:w∈returnWindows)
 {κ δ p:ℝ} (ha:w.Available δ p) :
 @GenericCount.envelope finalCountScheme κ δ p≤branchCount w.branch δ p := by
 have hw' : ReturnCountWindow.toAdmitted w∈finalCountScheme.windows := by
  change ReturnCountWindow.toAdmitted w∈returnWindows.map ReturnCountWindow.toAdmitted
  exact List.mem_map.mpr ⟨w,hw,rfl⟩
 have hb : (ReturnCountWindow.toAdmitted w).toBranch∈@GenericCount.admittedBranches finalCountScheme :=
  List.mem_map.mpr ⟨ReturnCountWindow.toAdmitted w,hw',rfl⟩
 have ha' : (ReturnCountWindow.toAdmitted w).toBranch.available δ p := ha
 exact QRH.Record12518109Return.finiteEnvelope_le_branch QRH.Record12518109Return.countingR hb ha'
end
end QRH.PositiveGap.Return.Tuning.FinalEdges
