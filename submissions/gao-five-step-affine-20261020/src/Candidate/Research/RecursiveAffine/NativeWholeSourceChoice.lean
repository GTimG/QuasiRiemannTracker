/- Choose the whole actual source once, preserving every dependent source record. Apache-2.0. -/
import Mathlib.Logic.Function.Basic
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
/-- Simultaneous source choice preserves the complete proposition attached
to each actual row. It creates no new source or energy estimate. -/
theorem choose_actual_source {Rows : Type*}{A : Rows→Type*}
    {F : (r : Rows)→A r→Type*}{P : ∀r a,F r a→Prop}
    (h : ∀r,∃a,∃f,P r a f) :
    ∃(a : ∀r,A r)(f : ∀r,F r (a r)),∀r,P r (a r) (f r) :=by
  let a:=fun r=>Classical.choose (h r)
  let f:=fun r=>Classical.choose (Classical.choose_spec (h r))
  exact ⟨a,f,fun r=>Classical.choose_spec (Classical.choose_spec (h r))⟩
/-- Add a proved quantitative consequence without replacing any chosen
source, family or attached metadata. -/
theorem strengthen_actual_source {A : Type*}{F : A→Type*}{P Q : ∀a,F a→Prop}
    (h : ∃a,∃f,P a f)(consequence : ∀a f,P a f→Q a f) :
    ∃a,∃f,P a f ∧ Q a f:=by
  obtain ⟨a,f,hgood⟩:=h
  exact ⟨a,f,hgood,consequence a f hgood⟩

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.choose_actual_source
#print axioms OAI.SevenEighths.Cycle153ActualColumn.strengthen_actual_source
