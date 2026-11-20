/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Joseph Bebel’s PR141 rational target, compared exactly with the upper
contact constant used by the marked count. -/
import Candidate.C092.transport.DirectAll

namespace QRH.Cycle092.Incumbent
noncomputable section
set_option autoImplicit false

def pr141 : ℝ := 9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717/11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700

theorem pr141_bracket : (QRH.ContactCertificate.alphaLo:ℝ) < pr141 ∧
    pr141 < (QRH.ContactCertificate.alphaHi:ℝ) := by
  norm_num [pr141,QRH.ContactCertificate.alphaLo,QRH.ContactCertificate.alphaHi]

theorem moment_of_pr141 {β : ℝ} (hb : β ≤ pr141) : 2*β-1 ≤ Direct.kap := by
  unfold Direct.kap
  linarith only [hb,pr141_bracket.2]

#print axioms moment_of_pr141
end
end QRH.Cycle092.Incumbent
