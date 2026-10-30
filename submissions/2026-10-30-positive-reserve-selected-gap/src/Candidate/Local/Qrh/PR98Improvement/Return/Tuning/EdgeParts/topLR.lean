/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PR98Improvement.Return.Tuning.EdgeParts.topLL
set_option autoImplicit false
namespace QRH.PR98Improvement.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PR98Improvement.Return QRH.PR98Improvement.ReturnTuning
theorem cover_topLR : coverOK .newTop winsQ 38 0 (3 / 8) (1 / 4) (1 / 2) = true := by decide +kernel
end QRH.PR98Improvement.Return.Tuning.FinalEdges
