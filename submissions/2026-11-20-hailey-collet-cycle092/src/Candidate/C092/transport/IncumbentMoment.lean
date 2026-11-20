/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Use the accepted Joseph Bebel PR141 Hecke bound to supply the literal
previous-contact parameter in the saved and native counts. -/
import Candidate.C092.transport.IncumbentRational
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorContinuum.ClosestEndpoint

namespace QRH.Cycle092.Incumbent
open OAI OAI.SevenEighths Qrh.TwoSlot.AnchorContinuum.ClosestRational

theorem established_moment : 2*HeckeZeroSupremum.beta-1 ≤ Direct.kap := by
  apply moment_of_pr141
  simpa only [target,numerator,denominator,pr141,Nat.cast_ofNat] using beta_le_target

#print axioms established_moment
end QRH.Cycle092.Incumbent
