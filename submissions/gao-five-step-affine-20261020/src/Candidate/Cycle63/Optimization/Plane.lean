/- Closed forms of Collet's coupled plane, and sign criteria that locate the class bound of the
top-row certificate. Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.TopRow
import Candidate.Cycle63.Certificate.Tactic

set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-- The quadratic factor `24 q^2 - (24 κ + 16) q + 60 κ - 10` of the coupled plane, for the slot
price `κ`; it has no real roots. -/
def planeQuadratic (q : ℝ) : ℝ := 24*q^2 - (24*slotPrice + 16)*q + 60*slotPrice - 10

end

end Cycle63.Optimization
