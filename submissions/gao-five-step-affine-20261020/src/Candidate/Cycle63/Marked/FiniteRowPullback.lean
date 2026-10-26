import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FiniteRows
noncomputable section
open scoped Classical BigOperators

variable {Label Raw : Type*} [Nonempty Label] [DecidableEq Raw]

def pullback (labels : Finset Label) (row : Label→Raw) : Raw→Label :=
  Function.invFunOn row (↑labels:Set Label)

theorem pullback_mem (labels : Finset Label) (row : Label→Raw)
    {u : Raw} (hu : u∈labels.image row) : pullback labels row u∈labels := by
  obtain ⟨l,hl,he⟩:=Finset.mem_image.mp hu
  exact Function.invFunOn_mem ⟨l,hl,he⟩

theorem row_pullback (labels : Finset Label) (row : Label→Raw)
    {u : Raw} (hu : u∈labels.image row) : row (pullback labels row u)=u := by
  obtain ⟨l,hl,he⟩:=Finset.mem_image.mp hu
  exact Function.invFunOn_eq ⟨l,hl,he⟩

omit [DecidableEq Raw] in
theorem pullback_row (labels : Finset Label) (row : Label→Raw)
    (hinj : Set.InjOn row (↑labels:Set Label)) {l : Label} (hl : l∈labels) :
    pullback labels row (row l)=l := hinj.leftInvOn_invFunOn hl

end
end OAI.SevenEighths.Cycle63FiniteRows
