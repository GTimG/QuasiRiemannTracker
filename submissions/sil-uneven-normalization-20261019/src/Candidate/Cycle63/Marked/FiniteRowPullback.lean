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

theorem pullback_row (labels : Finset Label) (row : Label→Raw)
    (hinj : Set.InjOn row (↑labels:Set Label)) {l : Label} (hl : l∈labels) :
    pullback labels row (row l)=l := hinj.leftInvOn_invFunOn hl

theorem sum_pullback (labels : Finset Label) (row : Label→Raw)
    (hinj : Set.InjOn row (↑labels:Set Label)) (f : Label→ℝ) :
    (∑u∈labels.image row,f (pullback labels row u))=∑l∈labels,f l := by
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl (fun l hl=>by rw [pullback_row labels row hinj hl])

/-- Row-dependent data may be carried through any estimate on distinct raw
frequencies. No global injectivity outside the finite population is needed. -/
theorem bound_of_raw_estimate (labels : Finset Label) (row : Label→Raw)
    (hinj : Set.InjOn row (↑labels:Set Label)) (f : Label→ℝ) (E : ℝ)
    (hE : (∑u∈labels.image row,f (pullback labels row u))≤E) :
    (∑l∈labels,f l)≤E := by
  rwa [sum_pullback labels row hinj f] at hE

/-- A dependent proposition involving both the original label and its raw
frequency transports without replacing the label's actual chosen height. -/
theorem predicates_pullback (labels : Finset Label) (row : Label→Raw)
    (P : Label→Raw→Prop) (hP : ∀l∈labels,P l (row l)) :
    ∀u∈labels.image row,P (pullback labels row u) u := by
  intro u hu
  simpa only [row_pullback labels row hu] using hP _ (pullback_mem labels row hu)

end
end OAI.SevenEighths.Cycle63FiniteRows
#print axioms OAI.SevenEighths.Cycle63FiniteRows.sum_pullback
#print axioms OAI.SevenEighths.Cycle63FiniteRows.predicates_pullback
