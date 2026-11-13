/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.SourceComposition
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Price.Gates
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Contract

/-!
# Driver.Parent

The parent face `G(1-10^-12, 2+10^-11, 3/20)` (`Price.pr103Face`) of the ordinary anchor
step, as a restriction of PR103's proved source `G(1-10^-256, 2+10^-255, 3/20)`
(`QRH.PositiveGap.source`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Driver
noncomputable section

open OAI OAI.SevenEighths
open QRH.Record12518109Source QRH.Record1252270103Source
open Qrh.MarkedAnchor.Interface.Contract (uniformUnitFaceSource_restrict)
open Qrh.MarkedAnchor.Price (pr103Face)

/-- The parent face of the ordinary step. -/
theorem pr103_parent (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource pr103Face.B₀ pr103Face.L₀ pr103Face.c₀ := by
  have hs := QRH.PositiveGap.source hβ
  exact uniformUnitFaceSource_restrict (by constructor <;> norm_num [globalFace, pr103Face]) hs

end
end Qrh.MarkedAnchor.Driver

#print axioms Qrh.MarkedAnchor.Driver.pr103_parent
