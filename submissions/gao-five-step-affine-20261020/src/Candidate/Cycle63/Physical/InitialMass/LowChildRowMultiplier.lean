/- The multiplier that presents a row of the second expansion of the children of the first labels in the fixed
dictionary: the child multiplier of the prefix of the row. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.DepthTwoRowFibre

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment IdealMobiusDivisorSum CenteredMomentCommonRadialData

/-- The multiplier that presents the row `r` of the second expansion of the children of the first labels `first` in the
fixed dictionary: the child multiplier of the prefix of `r`, which consists of the first label of its first-stage row
and the arithmetic label of its second block, for the orientation `left`, the fixed row `u₀` and the units `unit`. -/
def firstRowMultiplier {α : Type*} [Fintype α] [DecidableEq α] {Label : Type*} {slots : Label → Finset α}
    {s : (l : Label) → Input (slots l)} {R seed : Label → Ideal O} {K Tsec : Label → ℝ} {Z ξ : ℝ}
    (first : Label → FirstSourceLabel) (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (r : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ) : O :=
  childMultiplier left u₀ unit (secondBlockPrefix slots s R seed K Tsec Z ξ first r)

end
end OAI.SevenEighths.Cycle63InitialMass
