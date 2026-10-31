/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PR99Improvement.Return.Tuning.EdgeParts.topLR
set_option autoImplicit false
namespace QRH.PR99Improvement.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PR99Improvement.Return QRH.PR99Improvement.ReturnTuning
theorem cover_topRL : coverOK .newTop winsQ 46 (3 / 8) (3 / 4) 0 (1 / 4) = true := by decide +kernel
end QRH.PR99Improvement.Return.Tuning.FinalEdges
