/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PR98Improvement.Return.Tuning.EdgeParts.topRR03
set_option autoImplicit false
namespace QRH.PR98Improvement.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PR98Improvement.Return QRH.PR98Improvement.ReturnTuning
theorem cover_topRR10 : coverOK .newTop winsQ 34 (15 / 32) (9 / 16) (1 / 4) (5 / 16) = true := by decide +kernel
end QRH.PR98Improvement.Return.Tuning.FinalEdges
