/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PR98Improvement.Return.Tuning.EdgeParts.topRR02
set_option autoImplicit false
namespace QRH.PR98Improvement.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PR98Improvement.Return QRH.PR98Improvement.ReturnTuning
theorem cover_topRR03 : coverOK .newTop winsQ 34 (3 / 8) (15 / 32) (7 / 16) (1 / 2) = true := by decide +kernel
end QRH.PR98Improvement.Return.Tuning.FinalEdges
