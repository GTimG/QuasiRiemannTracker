/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The parent source of the reference lane: `G(.99, 49/20, .14)`, a restriction of
PR103's proved source `G(1-10^-256, 2+10^-255, 3/20)` (`QRH.PositiveGap.source`). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.SourceComposition
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Contract

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.Reference
noncomputable section
open OAI.SevenEighths QRH.Record12518109Source QRH.Record1252270103Source
open Qrh.MarkedAnchor.Interface.Contract

/-- The reference parent `B_ref`. -/
def Bref : ℝ := 99/100
/-- The reference parent `L_ref`. -/
def Lref : ℝ := 49/20
/-- The reference parent mark cap `c_ref`. -/
def cref : ℝ := 14/100

/-- PR103's face restricts to the reference parent face: the `lam` grows, the budget and
the mark cap shrink, all lower edges are `0`. -/
theorem pr103_restricts_ref :
    (globalFace
      (9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
      (2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
      (3/20)).Restricts (globalFace Bref Lref cref) := by
  constructor <;> norm_num [globalFace, Bref, Lref, cref]

/-- **The reference parent** `G(.99, 49/20, .14)`, unconditional under the
contrary hypothesis. -/
theorem parent_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource Bref Lref cref :=
  uniformUnitFaceSource_restrict pr103_restricts_ref (QRH.PositiveGap.source hβ)

end
end Qrh.MarkedAnchor.Ordinary.Reference
