/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Modified by Sil (2026-11-11): the four conductor edges at theta = 10916833 / 12500000 by one kernel-computed
cover `coverOK2` each (native window and improved window as leaf alternatives, depth 16). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.Tuning.FinalEnvelopeBounds
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Return.ImprovedWindowQ

/-!
# The four conductor edges, certified by kernel-computed covers

`closed_envelope_return_cover` bounds the row exponent of every conductor edge at the extended count
envelope. Each edge is one `decide +kernel` of `coverOK2`: on each box the kernel tries the old count,
then the native window and the improved window containing it, and otherwise bisects.
-/

set_option autoImplicit false

namespace QRH.PositiveGap.Return.Tuning.FinalEdges

open QRH.Record1252270103Return QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
open Qrh.MarkedAnchor.Return.ImprovedQ

/-- The improved window `(dlo, dhi, plo)`. -/
def impsQ : List (ℚ×ℚ×ℚ) := [(189/512, 15/32, 15/32)]

theorem cover_oldSmall : coverOK2 .oldSmall winsQ impsQ 16 0 (3/4) 0 (1/2) = true := by decide +kernel
theorem cover_oldSwitch : coverOK2 .oldSwitch winsQ impsQ 16 0 (3/4) 0 (1/2) = true := by decide +kernel
theorem cover_newSwitch : coverOK2 .newSwitch winsQ impsQ 16 0 (3/4) 0 (1/2) = true := by decide +kernel
theorem cover_newTop : coverOK2 .newTop winsQ impsQ 16 0 (3/4) 0 (1/2) = true := by decide +kernel

noncomputable section

theorem env_old (δ p : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4)) (hp : p ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    @Qrh.MarkedAnchor.Return.ImprovedCount.envelope finalImprovedScheme kappa δ p ≤
      countN .old δ p / countJ .old δ p :=
  finiteEnvelope_le_old hδ hp

theorem env_window : ∀ w ∈ winsQ, w.branch ≠ .old → ∀ δ p, δ ∈ Set.Icc (w.dlo : ℝ) w.dhi →
    p ∈ Set.Icc (w.plo : ℝ) (1 / 2) →
      @Qrh.MarkedAnchor.Return.ImprovedCount.envelope finalImprovedScheme kappa δ p ≤
        countN w.branch δ p / countJ w.branch δ p := by
  intro w hw _ δ p hδ hp
  exact finiteEnvelope_le_window (mkWindow 0 w (ok_of_mem windows_ok hw)) (mkWindow_mem windows_ok hw)
    ⟨hδ, hp⟩

theorem env_improved : ∀ w ∈ impsQ, ∀ δ p, δ ∈ Set.Icc (w.1 : ℝ) w.2.1 →
    p ∈ Set.Icc (w.2.2 : ℝ) (1 / 2) →
      @Qrh.MarkedAnchor.Return.ImprovedCount.envelope finalImprovedScheme kappa δ p ≤ NI δ p / JI δ p := by
  intro w hw δ p hδ hp
  simp only [impsQ, List.mem_singleton] at hw
  subst hw
  exact finiteEnvelope_le_improved (by simpa using hδ) (by simpa using hp)

theorem closed_envelope_return_cover (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4))
    (hp : p ∈ Set.Icc 0 (1 / 2)) :
    Ebase (edgeD e) (edgeC e) δ p +
      3 / 4 * edgeD e * (@Qrh.MarkedAnchor.Return.ImprovedCount.envelope finalImprovedScheme kappa δ p) <
      theta - reserve := by
  have key := fun (h : coverOK2 e winsQ impsQ 16 0 (3 / 4) 0 (1 / 2) = true) =>
    edge_of_coverOK2 e winsQ impsQ (@Qrh.MarkedAnchor.Return.ImprovedCount.envelope finalImprovedScheme kappa)
      env_old env_window env_improved 16 h hδ hp
  cases e
  · exact key cover_oldSmall
  · exact key cover_oldSwitch
  · exact key cover_newSwitch
  · exact key cover_newTop

end

end QRH.PositiveGap.Return.Tuning.FinalEdges
