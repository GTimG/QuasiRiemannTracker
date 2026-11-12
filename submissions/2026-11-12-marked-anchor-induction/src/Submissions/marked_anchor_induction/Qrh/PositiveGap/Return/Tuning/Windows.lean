/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Modified by Sil (2026-11-11): one native window `<.C, 15/64, 9/16, 9/32>` at theta = 2183367/2500000 (count cap 3/20). -/
import Submissions.marked_anchor_induction.Qrh.PositiveGap.Return.Tuning.CoverQ

/-!
# The native rational count window

The return at theta = 2183367/2500000 uses one uncapped count-face window `.C` on
`[15/64, 9/16] × [9/32, 1/2]`; its bounds and fifteen admission guards are checked below. The improved
window is `Qrh.MarkedAnchor.Return.ImprovedQ.window`.
-/

set_option autoImplicit false

namespace QRH.PositiveGap.ReturnTuning

open QRH.PositiveGap.Return QRH.ArviReturnTuning

/-- Window data `(branch, dlo, dhi, plo)` of the native window. -/
def winsQ : List WinQ :=
  [⟨.C, 15 / 64, 9 / 16, 9 / 32⟩]

/-- The bounds and the fifteen guards of the window (no subdivision needed). -/
theorem windows_ok : winsQ.all (WinQ.ok 0) = true := by decide +kernel

noncomputable section

/-- The windows of the return. -/
def returnWindows : List ReturnCountWindow := mkWindows 0 winsQ windows_ok

end

end QRH.PositiveGap.ReturnTuning
