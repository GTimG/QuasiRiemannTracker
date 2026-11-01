/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.EdgeParts.topRR02
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.ContactQ
set_option autoImplicit false
namespace QRH.PositiveGap.Return.Tuning.FinalEdges
open QRH.Record1252270103Return QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
/-- The box holding the contact, by the discriminant certificate. -/
theorem contact_topRR03 :
    contactOK (rowBrQ .newTop (toQ .C)) (3 / 8) (15 / 32) (7 / 16) = true := by
  decide +kernel
end QRH.PositiveGap.Return.Tuning.FinalEdges
