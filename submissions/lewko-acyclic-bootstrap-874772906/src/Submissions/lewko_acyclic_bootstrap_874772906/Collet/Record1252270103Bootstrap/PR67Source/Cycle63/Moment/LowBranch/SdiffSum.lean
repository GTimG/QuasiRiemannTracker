import Mathlib
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The sum of the slots that remain after the deletion of a subset, for the classical decidable equality of the
statement of the dispatch. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators

/-- The sum over the slots that remain after the deletion of a subset of the slots is the difference of the sums, and it
is not negative. The set difference has the classical decidable equality, which is the one of the statement of
`low_state_dispatch`; a statement with another decidable equality is not definitionally equal to it, and the
unifier then unfolds the whole statement before it fails. -/
theorem sum_sdiff_eq_sub {α : Type*} (J R : Finset α) (w : α → ℝ) (hw : ∀ j, 0 ≤ w j) (hRJ : R ⊆ J) :
    (∑ j ∈ J, w j) - ∑ j ∈ R, w j = ∑ j ∈ J \ R, w j ∧ 0 ≤ ∑ j ∈ J \ R, w j :=
  ⟨by linarith only [Finset.sum_sdiff hRJ (f := w)], Finset.sum_nonneg fun j _ => hw j⟩

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
