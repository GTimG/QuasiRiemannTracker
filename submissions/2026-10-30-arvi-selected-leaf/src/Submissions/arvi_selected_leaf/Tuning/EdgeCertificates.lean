import Submissions.arvi_selected_leaf.Tuning.FinalEnvelopeBounds

/-!
# The four conductor edges, certified by kernel-computed covers

`closed_envelope_return_cover` has the statement of `arvi_density`'s `FinalEdges.closed_envelope_return_cover`
(for the reflective windows). Each edge is one `decide +kernel` of `coverOK`: the kernel itself bisects the
box `[0, 3/4] × [0, 1/2]` and, on each box, tries the old count and then each window containing it
(`CoverQ.lean`). This replaces `EdgeCertificates.lean` (90 cover nodes, 47 rows) and the six files
`Rows/Edge_*.lean` (47 Bernstein identities) of `arvi_density`.
-/

set_option autoImplicit false

namespace QRH.ArviDensity.Return.Tuning.FinalEdges

open QRH.Record1252270103Return QRH.ArviDensity.Return QRH.ArviReturnTuning

/-- Bisection fuel (the deepest box of the cover is 17 bisections deep). -/
abbrev depth : ℕ := 30

theorem cover_oldSmall : coverOK .oldSmall winsQ depth 0 (3 / 4) 0 (1 / 2) = true := by decide +kernel
theorem cover_oldSwitch : coverOK .oldSwitch winsQ depth 0 (3 / 4) 0 (1 / 2) = true := by decide +kernel
theorem cover_newSwitch : coverOK .newSwitch winsQ depth 0 (3 / 4) 0 (1 / 2) = true := by decide +kernel
theorem cover_newTop : coverOK .newTop winsQ depth 0 (3 / 4) 0 (1 / 2) = true := by decide +kernel

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
  · exact key cover_newTop

end

end QRH.ArviDensity.Return.Tuning.FinalEdges
