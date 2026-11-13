/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module FinalEnvelopeBounds (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): namespace QRH.SilDensitySplit.Return.FinalEdges; three branches -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
/- Modified by ArviFoxy (2026-10-29): forked into Submissions.arvi_return_tuning, namespace QRH.ArviDensity.Return.Tuning, over the reflective windows and edge covers of this package (`w.toAdmitted` written as `ReturnCountWindow.toAdmitted w`). -/
/- Modified by Sil (2026-11-11): bounds of the extended envelope `ImprovedCount.envelope` of `finalImprovedScheme` (old count, native window, improved window). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.Tuning.FinalScheme
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.Facts
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PositiveGap.ReturnTuning
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
 @Qrh.MarkedAnchor.Return.ImprovedCount.envelope finalImprovedScheme kappa δ p≤countN .old δ p/countJ .old δ p := by
 calc
  _ ≤ QRH.Record12518109Return.countingR kappa δ p :=
   @Qrh.MarkedAnchor.Return.ImprovedCount.envelope_le_base finalImprovedScheme kappa δ p
  _ = _ := old_count_eq hδ hp

theorem finiteEnvelope_le_window (w:ReturnCountWindow) (hw:w∈returnWindows)
 {κ δ p:ℝ} (ha:w.Available δ p) :
 @Qrh.MarkedAnchor.Return.ImprovedCount.envelope finalImprovedScheme κ δ p≤branchCount w.branch δ p :=
 @Qrh.MarkedAnchor.Return.ImprovedCount.envelope_le_window finalImprovedScheme
  (ReturnCountWindow.toAdmitted w) (List.mem_map.mpr ⟨w,hw,rfl⟩) κ δ p ha

theorem finiteEnvelope_le_improved {κ δ p:ℝ} (hδ:δ∈Set.Icc (189/512:ℝ) (15/32))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2)) :
 @Qrh.MarkedAnchor.Return.ImprovedCount.envelope finalImprovedScheme κ δ p≤
  Qrh.MarkedAnchor.Return.ImprovedQ.NI δ p/Qrh.MarkedAnchor.Return.ImprovedQ.JI δ p :=
 @Qrh.MarkedAnchor.Return.ImprovedCount.envelope_le_improved finalImprovedScheme
  Qrh.MarkedAnchor.Return.ImprovedQ.window (List.mem_singleton_self _) κ δ p ⟨hδ,hp⟩
end
end QRH.PositiveGap.Return.Tuning.FinalEdges
