import Candidate.Local.Qrh.PositiveGap.Return.Tuning.ContactQ
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.Windows
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.FinalEnvelopeBounds
set_option autoImplicit false
namespace QRH.PositiveGap.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
theorem cover_oldSmall : coverOK .oldSmall winsQ 0 0 (3 / 4) 0 (1 / 2) = true := by decide +kernel
theorem cover_oldSwitch : coverOK .oldSwitch winsQ 1 0 (3 / 4) 0 (1 / 2) = true := by decide +kernel
theorem cover_newSwitch : coverOK .newSwitch winsQ 1 0 (3 / 4) 0 (1 / 2) = true := by decide +kernel
theorem cover_topL : coverOK .newTop winsQ 8 0 (3 / 8) 0 (1 / 2) = true := by decide +kernel
theorem cover_topR : coverOK .newTop winsQ 9 (15 / 32) (3 / 4) 0 (1 / 2) = true := by decide +kernel
theorem cover_topM : coverOK .newTop winsQ 0 (3 / 8) (15 / 32) 0 (7 / 16) = true := by decide +kernel
noncomputable section
variable [TargetC]
theorem env_old (δ p : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4)) (hp : p ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    @GenericCount.envelope finalCountScheme kappa δ p ≤ countN .old δ p / countJ .old δ p :=
  finiteEnvelope_le_old hδ hp
theorem env_window : ∀ w ∈ winsQ, w.branch ≠ .old → ∀ δ p, δ ∈ Set.Icc (w.dlo : ℝ) w.dhi →
    p ∈ Set.Icc (w.plo : ℝ) (1 / 2) →
      @GenericCount.envelope finalCountScheme kappa δ p ≤ countN w.branch δ p / countJ w.branch δ p := by
  intro w hw _ δ p hδ hp
  exact finiteEnvelope_le_window (mkWindow 0 w (ok_of_mem windows_ok hw)) (mkWindow_mem windows_ok hw)
    ⟨hδ, hp⟩
theorem closed_envelope_return_cover (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4))
    (hp : p ∈ Set.Icc 0 (1 / 2)) :
    Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * (@GenericCount.envelope finalCountScheme kappa δ p) <
      theta - reserve := by
  cases e
  · exact edge_of_coverOK .oldSmall winsQ _ env_old env_window 0 cover_oldSmall hδ hp
  · exact edge_of_coverOK .oldSwitch winsQ _ env_old env_window 1 cover_oldSwitch hδ hp
  · exact edge_of_coverOK .newSwitch winsQ _ env_old env_window 1 cover_newSwitch hδ hp
  · rcases le_total δ (3 / 8 : ℝ) with hd | hd
    · exact coverOK_sound .newTop winsQ _ env_old env_window 8 0 (3 / 8) 0 (1 / 2) cover_topL
        (by simpa using hδ.1) (by simpa using hd) (by simpa using hp.1) (by simpa using hp.2) hδ hp
    · rcases le_total (15 / 32 : ℝ) δ with hx0 | hx0
      · exact coverOK_sound .newTop winsQ _ env_old env_window 9 (15 / 32) (3 / 4) 0 (1 / 2) cover_topR
          (by simpa using hx0) (by simpa using hδ.2) (by simpa using hp.1) (by simpa using hp.2) hδ hp
      · rcases le_total p (7 / 16 : ℝ) with hp' | hp'
        · exact coverOK_sound .newTop winsQ _ env_old env_window 0 (3 / 8) (15 / 32) 0 (7 / 16) cover_topM
            (by simpa using hd) (by simpa using hx0) (by simpa using hp.1) (by simpa using hp') hδ hp
        · exact contact_topRR03_row winsQ _ env_window (by simp [winsQ]) hd hx0 hp' hδ hp
end
end QRH.PositiveGap.Return.Tuning.FinalEdges
