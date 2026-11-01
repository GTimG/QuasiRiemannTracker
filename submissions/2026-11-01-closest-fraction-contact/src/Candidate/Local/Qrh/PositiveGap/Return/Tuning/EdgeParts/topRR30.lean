/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.EdgeParts.topRR23
set_option autoImplicit false
namespace QRH.PositiveGap.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
theorem cover_topRR30 : coverOK .newTop winsQ 54 (21 / 32) (3 / 4) (1 / 4) (5 / 16) = true := by decide +kernel
end QRH.PositiveGap.Return.Tuning.FinalEdges
