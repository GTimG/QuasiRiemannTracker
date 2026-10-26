import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.Final
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The bound on the real parts of the zeros that the slot prices use. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Assembly

open OAI.SevenEighths

/-- The slot prices use Akash Levy's bound `β ≤ 10499/12000`. -/
theorem beta_le_betaBound : HeckeZeroSupremum.beta ≤ Optimization.betaBound := by
  unfold Optimization.betaBound
  exact WeightedQRH.beta_le_theta

/-- The slot price is admissible for the moment bounds of the LOW half: `2 β - 1 ≤ κ`. -/
theorem slotPrice_admissible : 2*HeckeZeroSupremum.beta - 1 ≤ Optimization.slotPrice := by
  unfold Optimization.slotPrice
  linarith [beta_le_betaBound]

end Cycle63.Assembly

end Record1252270103Bootstrap.PR67
