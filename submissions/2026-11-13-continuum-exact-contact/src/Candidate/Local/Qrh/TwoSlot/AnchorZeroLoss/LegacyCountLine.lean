/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Backward-compatible adapter for the frozen 256-stage count line.
The explicit-line return is otherwise independent of the frozen endpoint. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.AffineCountBatch
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.FiberImproved

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorZeroLoss.Affine
open scoped Classical BigOperators
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch

abbrev legacyLine : Line where
  g0 := Qrh.MarkedAnchor.Interface.lineG0
  g1 := Qrh.MarkedAnchor.Interface.lineG1
  slope_nonneg := by norm_num [Qrh.MarkedAnchor.Interface.lineG1]
  slope_le := by norm_num [Qrh.MarkedAnchor.Interface.lineG1]

instance legacy_capacity : Return.CapacityBounds legacyLine where
  bounds := by
    intro w h1 h2
    unfold markCap legacyLine Qrh.MarkedAnchor.Interface.anchorLeft
      Qrh.MarkedAnchor.Interface.anchorTop Qrh.MarkedAnchor.Interface.lineG0
      Qrh.MarkedAnchor.Interface.lineG1 at *
    constructor <;> linarith

namespace Return
/-- The old window is definitionally the same scalar contract at its own line. -/
def legacyWindow {κ : ℝ} (w : Qrh.MarkedAnchor.Return.ImprovedWindow κ) :
    ImprovedWindow legacyLine κ :=
  ⟨w.B,w.lam,w.cap,w.sourceCap,w.mHi,w.lam_gt_one,w.mHi_lo,w.mHi_hi,w.cap_le_source,w.cap_small,w.value,w.cutoff,w.crossing,w.deltaLo,w.deltaHi,w.pLo,w.deltaBounds,w.pBounds,w.cutoff_bounds,w.crossing_left,w.plain_left,w.slope_nonneg,w.inverse_crossing,w.ordinary_crossing,w.native_top,w.plain_top,w.natural_tail,w.widths,w.long_crossing,w.antitone⟩

instance (priority := 100) legacy_scheme [S : Qrh.MarkedAnchor.Return.ImprovedCountScheme] :
    ImprovedCountScheme legacyLine where
  toCountScheme := S.toCountScheme
  toCapacityBounds := legacy_capacity
  improved := S.improved.map legacyWindow
  improved_face := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    obtain ⟨u,hu,he⟩ := S.improved_face v hv
    exact ⟨u,hu,he⟩

@[simp] theorem legacy_branches [S : Qrh.MarkedAnchor.Return.ImprovedCountScheme] :
    ImprovedCount.admittedBranches (line := legacyLine) (S := legacy_scheme (S := S)) =
      Qrh.MarkedAnchor.Return.ImprovedCount.admittedBranches := by
  change S.windows.map QRH.Record1252270103Return.AdmittedWindow.toBranch ++
      (S.improved.map legacyWindow).map ImprovedWindow.toBranch =
    S.windows.map QRH.Record1252270103Return.AdmittedWindow.toBranch ++
      S.improved.map Qrh.MarkedAnchor.Return.ImprovedWindow.toBranch
  simp only [List.map_map]
  congr 1
end Return

variable {M : Ideal HeckeFamily.O} {H : Subgroup (HeckeFamily.O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

@[simp] theorem legacy_moments_iff
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (ν C height εm : ℝ) :
    ImprovedMoments legacyLine F ν C height εm ↔
      Qrh.MarkedAnchor.Interface.ImprovedMoments F ν C height εm :=
  ⟨fun h => ⟨h.inverse,h.ordinary⟩,fun h => ⟨h.inverse,h.ordinary⟩⟩

@[simp] theorem legacy_fine_iff {D : Cycle25.Weighted.MomentData}
    (S : Cycle25ProbeFinalAssembly.WeightedSourceData D) :
    ImprovedFineInput legacyLine S ↔ Qrh.MarkedAnchor.Interface.ImprovedFineInput S := by
  simp only [ImprovedFineInput,Qrh.MarkedAnchor.Interface.ImprovedFineInput,legacy_moments_iff]

@[simp] theorem legacy_fiber_iff :
    ImprovedFiberMoments legacyLine ↔ Qrh.MarkedAnchor.Interface.ImprovedFiberMoments := by
  simp only [ImprovedFiberMoments,Qrh.MarkedAnchor.Interface.ImprovedFiberMoments,legacy_fine_iff]

end Qrh.TwoSlot.AnchorZeroLoss.Affine
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Affine.legacy_fiber_iff
