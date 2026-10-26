/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.HighMass

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Both unequal normalizations reduce their own physical mass. This permits
reuse of the original unrestricted-height estimate without a new loss. -/
theorem uneven_first_high_mass_le (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z ξ ε : ℝ) (hK : 0<Z^D) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK key)) (hZ : 1<Z) :
    unevenFirstHighMass reflected s R seed W D Z ξ ε hK key j ≤
      geometryFirstHighMass reflected s R seed W D Z ξ ε hK key j := by
  have ha := Target830.Source.Uneven.actual_allocation_nonneg reflected s R seed (Z^D) Z ξ hZ j.1.val
  have hp : Z^(-Target830.Source.Uneven.allocation reflected
      (geometryExponents s R seed (Z^D) Z ξ j.1.val))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  exact (mul_le_mul_of_nonneg_left hp
    (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ ε hK key j)).trans_eq (mul_one _)

end OAI.SevenEighths.TargetHigh830
