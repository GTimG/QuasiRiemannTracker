/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module FinalEnvelopeBounds (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): namespace QRH.SilDensitySplit.Return.FinalEdges; three branches -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
/- Modified by ArviFoxy (2026-10-29): forked into Submissions.arvi_return_tuning, namespace QRH.ArviDensity.Return.Tuning, over the reflective windows and edge covers of this package (`w.toAdmitted` written as `ReturnCountWindow.toAdmitted w`). -/
import Candidate.Local.Qrh.PR98Improvement.Return.Tuning.FinalScheme
import Candidate.Local.Qrh.PR98Improvement.Return.Facts
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PR98Improvement.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PR98Improvement.ReturnTuning
noncomputable section

theorem old_count_eq {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 QRH.Record12518109Return.countingR kappa δ p=countN .old δ p/countJ .old δ p := by
 have hk : (7/10:ℝ)≤kappa := by norm_num [kappa,c]
 have hD : 0<oldD p := by
  norm_num [oldD,kappa,c]
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
 have hw' : ReturnCountWindow.toAdmitted w∈finalCountScheme.windows := by
  change ReturnCountWindow.toAdmitted w∈returnWindows.map ReturnCountWindow.toAdmitted
  exact List.mem_map.mpr ⟨w,hw,rfl⟩
 have hb : (ReturnCountWindow.toAdmitted w).toBranch∈@GenericCount.admittedBranches finalCountScheme :=
  List.mem_map.mpr ⟨ReturnCountWindow.toAdmitted w,hw',rfl⟩
 have ha' : (ReturnCountWindow.toAdmitted w).toBranch.available δ p := ha
 exact QRH.Record12518109Return.finiteEnvelope_le_branch QRH.Record12518109Return.countingR hb ha'
end
end QRH.PR98Improvement.Return.Tuning.FinalEdges
