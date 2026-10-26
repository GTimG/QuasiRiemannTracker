import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TopRow
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Tactic
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Closed forms of Collet's coupled plane, and sign criteria that locate the class bound of the
top-row certificate. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-- The quadratic factor `24 q^2 - (24 κ + 16) q + 60 κ - 10` of the coupled plane, for the slot
price `κ`; it has no real roots. -/
def planeQuadratic (q : ℝ) : ℝ := 24*q^2 - (24*slotPrice + 16)*q + 60*slotPrice - 10

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
