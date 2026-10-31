/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.EdgeParts.topRR10
set_option autoImplicit false
namespace QRH.PositiveGap.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
theorem cover_topRR11 : coverOK .newTop winsQ 54 (15 / 32) (9 / 16) (5 / 16) (3 / 8) = true := by decide +kernel
end QRH.PositiveGap.Return.Tuning.FinalEdges
