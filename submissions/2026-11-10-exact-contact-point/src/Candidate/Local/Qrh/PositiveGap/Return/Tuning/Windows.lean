import Candidate.Local.Qrh.PositiveGap.Return.Tuning.CoverQ
set_option autoImplicit false
namespace QRH.PositiveGap.ReturnTuning
open QRH.PositiveGap.Return QRH.ArviReturnTuning
def winsQ : List WinQ :=
  [⟨.C, 9 / 25, 49 / 100, 0⟩,
   ⟨.C, 9 / 25, 57 / 100, 3 / 8⟩,
   ⟨.capP, 1 / 16384, 3273 / 8192, 3 / 8⟩,
   ⟨.capP, 9 / 32, 3 / 8, 5 / 16⟩,
   ⟨.C, 45 / 128, 3 / 8, 15 / 32⟩]
theorem windows_ok : winsQ.all (WinQ.ok 0) = true := by decide +kernel
noncomputable section
variable [TargetC]
def returnWindows : List ReturnCountWindow := mkWindows 0 winsQ windows_ok
end
end QRH.PositiveGap.ReturnTuning
