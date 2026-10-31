/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
import Candidate.Local.Qrh.PR98Improvement.Return.Tuning.CoverQ

/-!
# The five rational count windows

The fixed return uses three uncapped count-face windows and two capped physical-face windows.
The bounds and fifteen admission guards on each window are checked together below.
-/

set_option autoImplicit false

namespace QRH.PR98Improvement.ReturnTuning

open QRH.PR98Improvement.Return QRH.ArviReturnTuning

/-- Window data `(branch, dlo, dhi, plo)` for the five supplied rectangles. -/
def winsQ : List WinQ :=
  [⟨.C, 9 / 25, 49 / 100, 0⟩,
   ⟨.C, 9 / 25, 57 / 100, 3 / 8⟩,
   ⟨.capP, 1 / 16384, 3273 / 8192, 3 / 8⟩,
   ⟨.capP, 9 / 32, 3 / 8, 5 / 16⟩,
   ⟨.C, 45 / 128, 3 / 8, 15 / 32⟩]

/-- The bounds and the fifteen guards of every window (no subdivision needed). -/
theorem windows_ok : winsQ.all (WinQ.ok 0) = true := by decide +kernel

noncomputable section

/-- The windows of the return. -/
def returnWindows : List ReturnCountWindow := mkWindows 0 winsQ windows_ok

end

end QRH.PR98Improvement.ReturnTuning
