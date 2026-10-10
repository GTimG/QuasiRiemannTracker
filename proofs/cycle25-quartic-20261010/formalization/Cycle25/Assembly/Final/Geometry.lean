import Cycle25.Assembly.Weighted.Target
import Cycle25.Assembly.Final.SourceContract

namespace Cycle25.FinalAssembly
open OAI.SevenEighths

theorem weighted_target_identity :
    weightedTarget = signal theta+(HeckeZeroSupremum.beta-theta)/2 := by
  dsimp [weightedTarget,signal]
  ring

theorem weighted_target_lower (hβ : theta ≤ HeckeZeroSupremum.beta) :
    signal theta ≤ weightedTarget := by rw [weighted_target_identity]; linarith

theorem weighted_target_gap :
    HeckeZeroSupremum.beta-(4+b)/6-weightedTarget =
      (HeckeZeroSupremum.beta-theta)/2 := by
  dsimp [weightedTarget,signal]
  ring

theorem weighted_target_saving
    (D : HighParameters.HighData (HeckeZeroSupremum.beta-theta))
    (hβ : theta < HeckeZeroSupremum.beta) :
    D.sigma+D.t/8+D.t/8 ≤ HeckeZeroSupremum.beta-(4+b)/6-weightedTarget := by
  rw [weighted_target_gap]
  linarith [D.high_saving]
end Cycle25.FinalAssembly
