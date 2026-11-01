/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.EdgeParts.topRR02
set_option autoImplicit false
namespace QRH.PositiveGap.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
theorem cover_topRR03 : coverOK .newTop winsQ 54 (3 / 8) (15 / 32) (7 / 16) (1 / 2) = true := by decide +kernel
end QRH.PositiveGap.Return.Tuning.FinalEdges
