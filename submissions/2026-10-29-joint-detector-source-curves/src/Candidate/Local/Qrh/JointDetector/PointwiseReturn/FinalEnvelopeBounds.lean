/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
/- Repeated marks: fork of Collet's final-stage module FinalEnvelopeBounds (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): namespace Qrh.JointDetector.PointwiseReturn.FinalEdges; three branches -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.FinalScheme
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Facts
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Qrh.JointDetector.PointwiseReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section

theorem old_count_eq {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 QRH.Record12518109Return.countingR kappa δ p=countN .old δ p/countJ .old δ p := by
 have hk : (7/10:ℝ)≤kappa := by norm_num [kappa,theta,c]
 have hD : 0<oldD p := by
  norm_num [oldD,kappa,theta,c]
  nlinarith [hp.2]
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
 have hw' : w.toAdmitted∈finalCountScheme.windows := by
  change w.toAdmitted∈returnWindows.map ReturnCountWindow.toAdmitted
  exact List.mem_map.mpr ⟨w,hw,rfl⟩
 have hb : w.toAdmitted.toBranch∈@GenericCount.admittedBranches finalCountScheme :=
  List.mem_map.mpr ⟨w.toAdmitted,hw',rfl⟩
 have ha' : w.toAdmitted.toBranch.available δ p := ha
 exact QRH.Record12518109Return.finiteEnvelope_le_branch QRH.Record12518109Return.countingR hb ha'
end
end Qrh.JointDetector.PointwiseReturn.FinalEdges
