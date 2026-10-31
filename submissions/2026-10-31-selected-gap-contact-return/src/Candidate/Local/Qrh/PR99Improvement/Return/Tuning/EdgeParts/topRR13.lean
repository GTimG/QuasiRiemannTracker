/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PR99Improvement.Return.Tuning.EdgeParts.topRR12
set_option autoImplicit false
namespace QRH.PR99Improvement.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PR99Improvement.Return QRH.PR99Improvement.ReturnTuning
theorem cover_topRR13 : coverOK .newTop winsQ 46 (15 / 32) (9 / 16) (7 / 16) (1 / 2) = true := by decide +kernel
end QRH.PR99Improvement.Return.Tuning.FinalEdges
