import Candidate.Research.RecursiveAffine.PhysicalWeightedSelection
import Candidate.Cycle63.Moment.LowBranch.FinalDictionary

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153SourceReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open Cycle63Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The weighted selector's energy is the native finalPositiveEnergy of the
same common allocation, residual ideal, active allocation and orientation.
There is no surrogate source or assumed energy equality. -/
theorem physicalDaughterEnergy_eq_native
    (s : Input α) (C R : Ideal O) (Ds : Finset (Ideal O))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (rad : ℝ)
    (d : PhysicalDaughter s C R Ds) :
    physicalDaughterEnergy s C R Ds keep Φ rad d =
      finalPositiveEnergy (commonData s C R d.1) d.2.2.2 d.2.1.1 d.2.2.1.1 keep Φ rad := by
  rfl

end
end OAI.SevenEighths.Cycle153SourceReturn

#print axioms OAI.SevenEighths.Cycle153SourceReturn.physicalDaughterEnergy_eq_native
