/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The exact P4 element-row subtype is equivalent to the retained FreeRow subtype. -/
import Candidate.C092.transport.WitnessRowSupActualRows

set_option autoImplicit false
namespace QRH.Cycle092.WitnessRowSup.Actual
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification

def sourceRow {rows : Finset FreeRow} (u : rows) : rows.image Subtype.val :=
  ⟨u.val.val,Finset.mem_image.mpr ⟨u.val,u.property,rfl⟩⟩

/-- Original O-valued P4 rows and FreeRow-valued source rows have exactly the
same members. This equivalence also transports dependent witness records. -/
def sourceRowEquiv (rows : Finset FreeRow) : rows ≃ rows.image Subtype.val :=
  Equiv.ofBijective sourceRow ⟨by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : rows.image Subtype.val => z.val) h,by
    intro z
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨u,hu⟩,Subtype.ext he⟩⟩

@[simp] theorem sourceRow_val {rows : Finset FreeRow} (u : rows) :
    (sourceRowEquiv rows u).val = u.val.val := rfl

/-- This holds for arbitrary dependent witness expressions in f. -/
theorem sourceRow_sum (rows : Finset FreeRow) (f : rows.image Subtype.val → ℝ) :
    (∑ z : rows.image Subtype.val,f z) = ∑ u : rows,f (sourceRowEquiv rows u) :=
  (Equiv.sum_comp (sourceRowEquiv rows) f).symm

#print axioms sourceRowEquiv
#print axioms sourceRow_sum
end
end QRH.Cycle092.WitnessRowSup.Actual
