/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact hash-bound join of O.2 data to the actual final PR141 source stage. -/
import Candidate.C092.transport.TangentExtensionData
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorZeroLoss.CertificateData
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.TangentExtension.Certificate
abbrev oldStage := Qrh.TwoSlot.AnchorZeroLoss.Certificate.stage

/-- The entry gain is the actual old output, not just its weaker tangent. -/
theorem entry_exact : (stage 0).R=(oldStage 8191).left ∧
    (stage 0).gain=(oldStage 8191).Y (oldStage 8191).left ∧
    (stage 0).a0=(oldStage 8191).a0 ∧ (stage 0).a1=(oldStage 8191).a1 := by
  decide +kernel

theorem join_minorant_checked :
    (stage 0).line (oldStage 8191).left+pad < (oldStage 8191).Y (oldStage 8191).left ∧
    (stage 0).line (oldStage 8191).R+pad < (oldStage 8191).Y (oldStage 8191).R := by
  decide +kernel


end QRH.Cycle092.TangentExtension.Certificate
#print axioms QRH.Cycle092.TangentExtension.Certificate.entry_exact
