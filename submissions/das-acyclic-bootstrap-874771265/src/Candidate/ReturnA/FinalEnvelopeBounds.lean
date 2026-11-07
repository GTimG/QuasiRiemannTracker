/- Adapted 2026-10-24 for Subhanjan Das, AI-assisted with OpenAI Codex.
Original Hailey Collet/Mark Lewko notices and Apache-2.0 license retained. -/
/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.ReturnA.FinalScheme
import Candidate.ReturnA.Finite.ReturnFacts
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Das.QRH.ReturnA.FinalEdges
open QRH.LewkoStage2Return
noncomputable section
open DasStageAFinite
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
 have hw' : w.toAdmitted∈finalCountScheme.windows := by
  change w.toAdmitted∈returnWindows.map ReturnCountWindow.toAdmitted
  exact List.mem_map.mpr ⟨w,hw,rfl⟩
 have hb : w.toAdmitted.toBranch∈@GenericCount.admittedBranches finalCountScheme :=
  List.mem_map.mpr ⟨w.toAdmitted,hw',rfl⟩
 have ha' : w.toAdmitted.toBranch.available δ p := ha
 exact QRH.Record12518109Return.finiteEnvelope_le_branch QRH.Record12518109Return.countingR hb ha'
end
end Das.QRH.ReturnA.FinalEdges
