/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The native common bank subclass and the original moment subtype are the
same finite marked family. Restriction uses only nonnegative energy. -/
import Candidate.C092.transport.MixedMiddleReturnCauchy
import Candidate.C092.transport.MixedMiddleReturnTuple
import Candidate.C092.transport.MixedOffsetCountCentered

set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ProbeHighRowFamily HeckeInverseAmplification

/-- Original source subtype indices whose physical free row lies in common. -/
def commonIndices (rows common : Finset FreeRow) : Finset rows :=
  Finset.univ.filter (fun u=>u.val∈common)

theorem commonIndices_card (rows common : Finset FreeRow) (hsub : common⊆rows) :
    (commonIndices rows common).card=common.card := by
  classical
  apply Finset.card_bij (fun u _=>u.val)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u hu v hv he
    exact Subtype.ext he
  · intro u hu
    exact ⟨⟨u,hsub hu⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,rfl⟩

theorem common_energy (rows common : Finset FreeRow) (f : rows→ℂ) :
    (∑u∈commonIndices rows common,‖f u‖^2)≤∑u : rows,‖f u‖^2 :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun u _ _=>sq_nonneg _)

#print axioms commonIndices_card
end
end QRH.Cycle092.MixedMiddleReturn
