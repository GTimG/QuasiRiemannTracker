/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
import Candidate.Local.Qrh.PR99Improvement.Return.Tuning.EdgeParts.topRR33

/-!
# The four conductor edges, certified by kernel-computed covers

`closed_envelope_return_cover` has the statement of `arvi_density`'s `FinalEdges.closed_envelope_return_cover`
(for the reflective windows). Each edge is one `decide +kernel` of `coverOK`: the kernel itself bisects the
box `[0, 3/4] × [0, 1/2]` and, on each box, tries the old count and then each window containing it
(`CoverQ.lean`). This replaces `EdgeCertificates.lean` (90 cover nodes, 47 rows) and the six files
`Rows/Edge_*.lean` (47 Bernstein identities) of `arvi_density`.
-/

set_option autoImplicit false

namespace QRH.PR99Improvement.Return.Tuning.FinalEdges

open QRH.Record1252270103Return QRH.PR99Improvement.Return QRH.PR99Improvement.ReturnTuning

noncomputable section

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
  have key := fun (h : coverOK e winsQ depth 0 (3 / 4) 0 (1 / 2) = true) =>
    edge_of_coverOK e winsQ (@GenericCount.envelope finalCountScheme kappa) env_old env_window depth h hδ hp
  cases e
  · exact key cover_oldSmall
  · exact key cover_oldSwitch
  · exact key cover_newSwitch
  · rcases le_total δ (3 / 8 : ℝ) with hd | hd <;> rcases le_total p (1 / 4 : ℝ) with hp' | hp'
    · exact coverOK_sound _ winsQ _ env_old env_window 46 0 (3/8) 0 (1/4) cover_topLL (by simpa using hδ.1) (by simpa using hd) (by simpa using hp.1) (by simpa using hp') hδ hp
    · exact coverOK_sound _ winsQ _ env_old env_window 46 0 (3/8) (1/4) (1/2) cover_topLR (by simpa using hδ.1) (by simpa using hd) (by simpa using hp') (by simpa using hp.2) hδ hp
    · exact coverOK_sound _ winsQ _ env_old env_window 46 (3/8) (3/4) 0 (1/4) cover_topRL (by simpa using hd) (by simpa using hδ.2) (by simpa using hp.1) (by simpa using hp') hδ hp
    · rcases le_total δ ((15 / 32) : ℝ) with hx0 | hx0
      · rcases le_total p ((5 / 16) : ℝ) with hy0 | hy0
        · exact coverOK_sound _ winsQ _ env_old env_window 46 (3 / 8) (15 / 32) (1 / 4) (5 / 16) cover_topRR00 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
        · rcases le_total p ((3 / 8) : ℝ) with hy1 | hy1
          · exact coverOK_sound _ winsQ _ env_old env_window 46 (3 / 8) (15 / 32) (5 / 16) (3 / 8) cover_topRR01 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
          · rcases le_total p ((7 / 16) : ℝ) with hy2 | hy2
            · exact coverOK_sound _ winsQ _ env_old env_window 46 (3 / 8) (15 / 32) (3 / 8) (7 / 16) cover_topRR02 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
            · exact coverOK_sound _ winsQ _ env_old env_window 46 (3 / 8) (15 / 32) (7 / 16) (1 / 2) cover_topRR03 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
      · rcases le_total δ ((9 / 16) : ℝ) with hx1 | hx1
        · rcases le_total p ((5 / 16) : ℝ) with hy0 | hy0
          · exact coverOK_sound _ winsQ _ env_old env_window 46 (15 / 32) (9 / 16) (1 / 4) (5 / 16) cover_topRR10 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
          · rcases le_total p ((3 / 8) : ℝ) with hy1 | hy1
            · exact coverOK_sound _ winsQ _ env_old env_window 46 (15 / 32) (9 / 16) (5 / 16) (3 / 8) cover_topRR11 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
            · rcases le_total p ((7 / 16) : ℝ) with hy2 | hy2
              · exact coverOK_sound _ winsQ _ env_old env_window 46 (15 / 32) (9 / 16) (3 / 8) (7 / 16) cover_topRR12 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
              · exact coverOK_sound _ winsQ _ env_old env_window 46 (15 / 32) (9 / 16) (7 / 16) (1 / 2) cover_topRR13 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
        · rcases le_total δ ((21 / 32) : ℝ) with hx2 | hx2
          · rcases le_total p ((5 / 16) : ℝ) with hy0 | hy0
            · exact coverOK_sound _ winsQ _ env_old env_window 46 (9 / 16) (21 / 32) (1 / 4) (5 / 16) cover_topRR20 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
            · rcases le_total p ((3 / 8) : ℝ) with hy1 | hy1
              · exact coverOK_sound _ winsQ _ env_old env_window 46 (9 / 16) (21 / 32) (5 / 16) (3 / 8) cover_topRR21 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
              · rcases le_total p ((7 / 16) : ℝ) with hy2 | hy2
                · exact coverOK_sound _ winsQ _ env_old env_window 46 (9 / 16) (21 / 32) (3 / 8) (7 / 16) cover_topRR22 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
                · exact coverOK_sound _ winsQ _ env_old env_window 46 (9 / 16) (21 / 32) (7 / 16) (1 / 2) cover_topRR23 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
          · rcases le_total p ((5 / 16) : ℝ) with hy0 | hy0
            · exact coverOK_sound _ winsQ _ env_old env_window 46 (21 / 32) (3 / 4) (1 / 4) (5 / 16) cover_topRR30 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
            · rcases le_total p ((3 / 8) : ℝ) with hy1 | hy1
              · exact coverOK_sound _ winsQ _ env_old env_window 46 (21 / 32) (3 / 4) (5 / 16) (3 / 8) cover_topRR31 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
              · rcases le_total p ((7 / 16) : ℝ) with hy2 | hy2
                · exact coverOK_sound _ winsQ _ env_old env_window 46 (21 / 32) (3 / 4) (3 / 8) (7 / 16) cover_topRR32 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp
                · exact coverOK_sound _ winsQ _ env_old env_window 46 (21 / 32) (3 / 4) (7 / 16) (1 / 2) cover_topRR33 (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) (by norm_num at * <;> linarith) hδ hp

end

end QRH.PR99Improvement.Return.Tuning.FinalEdges
