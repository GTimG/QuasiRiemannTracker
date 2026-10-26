import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.FinalDictionary
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.AllocationClipping
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentRetainedProfile
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem source_plain_positive (s : Data α) (second : Bool) (j : Fin 2) :
    0 < Cycle63.Physical.sourcePlainScales s.toSource second j := by
  cases second <;> fin_cases j
  · exact s.X₁_pos
  · exact s.X₂_pos
  · exact s.Y₁_pos
  · exact s.Y₂_pos

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
