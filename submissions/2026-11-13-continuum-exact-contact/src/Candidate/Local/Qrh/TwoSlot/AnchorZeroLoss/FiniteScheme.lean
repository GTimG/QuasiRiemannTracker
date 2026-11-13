/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The two native windows and the improved window of the frozen finite return.
Uses Sil's PR137 count-window contracts, Hailey Collet's admitted-window
interface and ArviFoxy's exact rational admission checker (Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FiniteWindow
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.Tuning.FinalWindows

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.Finite
noncomputable section
open QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
open QRH.Record1252270103Return

/-- The additional low native window is part of the written 40-guard return. -/
def nativeQ : List WinQ :=
  [⟨.C,15/64,9/16,9/32⟩,⟨.C,15/64,1/2,3/16⟩]

theorem native_ok : nativeQ.all (WinQ.ok 0) = true := by decide +kernel

def nativeWindows : List (AdmittedWindow (naturalK/6)) :=
  (mkWindows 0 nativeQ native_ok).map QRH.PositiveGap.Return.Tuning.ReturnCountWindow.toAdmitted

/-- The line and its moments are supplied by the actual finite induction.
This data structure only records count admission, not the physical return. -/
@[instance_reducible] def scheme : Affine.Return.ImprovedCountScheme finiteLine where
  naturalκ := naturalK/6
  natural_lo := by norm_num [naturalK]
  natural_hi := by norm_num [naturalK]
  windows := nativeWindows
  toCapacityBounds := finite_capacity
  improved := [Affine.Return.FiniteQ.window]
  improved_face := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    have hm : (⟨.C,15/64,9/16,9/32⟩:WinQ) ∈ nativeQ := by simp [nativeQ]
    exact ⟨QRH.PositiveGap.Return.Tuning.ReturnCountWindow.toAdmitted (mkWindow 0 _ (ok_of_mem native_ok hm)),
      List.mem_map.mpr ⟨_,mkWindow_mem native_ok hm,rfl⟩,rfl⟩

end
end Qrh.TwoSlot.AnchorZeroLoss.Finite
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Finite.native_ok
