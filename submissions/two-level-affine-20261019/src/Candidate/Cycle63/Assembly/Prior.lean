/- The bound on the real parts of the zeros that the slot prices use. Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Candidate.Cycle63.Arithmetic.Constants
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.Final

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
