/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PR98Improvement.Return.Tuning.EdgeParts.oldSmall
set_option autoImplicit false
namespace QRH.PR98Improvement.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PR98Improvement.Return QRH.PR98Improvement.ReturnTuning
theorem cover_oldSwitch : coverOK .oldSwitch winsQ depth 0 (3 / 4) 0 (1 / 2) = true := by decide +kernel
end QRH.PR98Improvement.Return.Tuning.FinalEdges
